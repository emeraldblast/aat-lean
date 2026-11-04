import AatLean.CMap

/-!
# Цепочка полномочий AAT-02 (шаг 4, первый проход)

Звено — токен: кто выдал, кому выдан, какие инструменты с какими картами
ограничений аргументов (§3.3). Ограничения — первый проход (`wildcard`,
`exact`, `one_of`, `range`, `AatLean/Constraint.lean`). Подписей, времени,
глубины, `par_hash`, PoP и `aud` в этой модели пока нет.

Цепочка хранится от корня к листу: `c[0]` — корень, `c[c.length-1]` — лист.

Разделение, на котором держится смысл Т1:
* `Permits` — денотация: звено допускает вызов, если инструмент в нём есть и
  его карта допускает аргументы по шагу 6b (`permitsArgs`: закрытый мир, `"*"`,
  обязательные аргументы, `check` каждого ограничения).
* `Narrows` — спецификация (`Prop`): «любой вызов, разрешённый ребёнку,
  разрешён родителю» — это C(child) ⊆ C(parent) из §4.1. Текст не меняется.
* `narrowsB` — структурная проверка шага 4p (4p1: инструменты ребёнка есть у
  родителя; 4p2–4p4: `narrowsMapB` по картам; таблица 4: `subsumes`).
Связь — только в одну сторону: `narrowsB_sound` (`narrowsB → Narrows`).
Обратное неверно по замыслу спецификации (§4.1: правила «conservative»),
свидетель — `incompleteness_witness`. Поэтому Т1 — корректность структурных
правил §4.5 относительно ненормативной модели C(T) из §4.1, для цепочки любой
длины.

`verify` пока не получает ни запроса, ни предъявителя, ни получателя: `allow`
значит «цепочка корректна», а не «этот вызов разрешён». Привязка запроса к
правам листа — Т2. Привязка предъявителя (PoP, Т9) и получателя (`aud`, Т8)
— позже.

`Linked` сравнивает имена (`child.issuer = parent.holder`), а не ссылку на
конкретный родительский токен (`par_hash`, I5) — позже.
-/

namespace AAT

abbrev Tool := String
abbrev Key := String

structure Link where
  issuer : Key
  holder : Key
  /-- Инструменты и их карты ограничений (§3.3). Идентификаторы уникальны
      (§3.3.1, предусловие разбора). -/
  tools  : List (Tool × CMap)
deriving Repr

/-- Вызов инструмента с аргументами. -/
structure Call where
  tool : Tool
  args : Args
deriving Repr

inductive Decision where
  | allow
  | deny
deriving Repr, DecidableEq

def Link.getTool (l : Link) (t : Tool) : Option CMap :=
  (l.tools.find? (·.1 == t)).map (·.2)

/-! ## Спецификация -/

/-- Звено разрешает вызов (шаг 6b для этого звена). -/
def Permits (l : Link) (call : Call) : Prop :=
  match l.getTool call.tool with
  | some m => permitsArgs m.norm call.args = true
  | none   => False

/-- То же как `Bool` — только чтобы ядро могло вычислять `Permits` в
    примерах; эквивалентность — `permits_iff`. -/
def permitsB (l : Link) (call : Call) : Bool :=
  match l.getTool call.tool with
  | some m => permitsArgs m.norm call.args
  | none   => false

theorem permits_iff (l : Link) (call : Call) : Permits l call ↔ permitsB l call = true := by
  unfold Permits permitsB
  cases l.getTool call.tool <;> simp

instance (l : Link) (call : Call) : Decidable (Permits l call) :=
  decidable_of_iff _ (permits_iff l call).symm

/-- Любой вызов, разрешённый ребёнку, разрешён и родителю. -/
def Narrows (parent child : Link) : Prop :=
  ∀ call, Permits child call → Permits parent call

/-- Ребёнок выдан тем, кто держал родителя. -/
def Linked (parent child : Link) : Prop :=
  child.issuer = parent.holder

/-- Издатель корня входит в реестр доверенных корней.
    Это ещё не Т3: Т3 требует, чтобы издатель совпадал с ключом подписи,
    а подписей в модели пока нет. -/
def RootTrusted (trustedRoots : List Key) (root : Link) : Prop :=
  root.issuer ∈ trustedRoots

/-! ## Исполняемый верификатор -/

/-- Шаг 4p: «Verify every tool in child_aat.tools is also present in
    parent_aat.tools» (4p1) и правила карт 4p2–4p4 после нормализации. -/
def narrowsB (parent child : Link) : Bool :=
  child.tools.all (fun (t, cm) =>
    match parent.getTool t with
    | some pm => narrowsMapB pm.norm cm.norm
    | none    => false)

def linkedB (parent child : Link) : Bool :=
  child.issuer == parent.holder

/-- Проверка всех соседних пар цепочки. -/
def checkPairs : List Link → Bool
  | p :: c :: rest => narrowsB p c && linkedB p c && checkPairs (c :: rest)
  | _ => true

/-- Пустая цепочка отклоняется; иначе проверяются корень и все пары. -/
def verify (trustedRoots : List Key) (chain : List Link) : Decision :=
  match chain with
  | [] => .deny
  | root :: _ =>
    if trustedRoots.contains root.issuer && checkPairs chain then .allow else .deny

/-! ## Связь Bool-проверок со спецификацией -/

theorem mem_of_getTool {l : Link} {t : Tool} {m : CMap} (h : l.getTool t = some m) :
    (t, m) ∈ l.tools := by
  unfold Link.getTool at h
  cases hf : l.tools.find? (·.1 == t) with
  | none => simp [hf] at h
  | some kv =>
    simp only [hf, Option.map_some, Option.some.injEq] at h
    have hm := List.mem_of_find?_eq_some hf
    have hk := List.find?_some hf
    simp only [beq_iff_eq] at hk
    subst h; subst hk
    exact hm

/-- **Корректность шага 4p.** Структурная проверка влечёт сужение по смыслу. -/
theorem narrowsB_sound (p c : Link) (h : narrowsB p c = true) : Narrows p c := by
  intro call hc
  unfold Permits at hc ⊢
  cases hcg : c.getTool call.tool with
  | none => rw [hcg] at hc; exact hc.elim
  | some cm =>
    rw [hcg] at hc
    simp only [narrowsB, List.all_eq_true] at h
    have ht := h _ (mem_of_getTool hcg)
    simp only at ht
    cases hpg : p.getTool call.tool with
    | none => rw [hpg] at ht; simp at ht
    | some pm =>
      rw [hpg] at ht
      exact narrowsMapB_sound _ _ ht _ hc

theorem linkedB_iff (p c : Link) : linkedB p c = true ↔ Linked p c := by
  simp [linkedB, Linked]

/-- `checkPairs` принимает ровно те цепочки, где каждая соседняя пара проходит
    структурную проверку 4p и связана по ключу. -/
theorem checkPairs_iff : ∀ (c : List Link),
    checkPairs c = true ↔
      ∀ i (h : i + 1 < c.length), narrowsB c[i] c[i+1] = true ∧ Linked c[i] c[i+1]
  | [] => by simp [checkPairs]
  | [_] => by simp [checkPairs]
  | p :: q :: rest => by
    simp only [checkPairs, Bool.and_eq_true, linkedB_iff, checkPairs_iff (q :: rest)]
    constructor
    · rintro ⟨⟨hn, hl⟩, hrest⟩ i hi
      cases i with
      | zero => exact ⟨hn, hl⟩
      | succ j => exact hrest j (by simp at hi ⊢; omega)
    · intro h
      refine ⟨h 0 (by simp), fun j hj => ?_⟩
      exact h (j + 1) (by simp at hj ⊢; omega)

/-- **Соответствие алгоритму §8** (в объёме модели): `verify` принимает ровно
    непустые цепочки с доверенным корнем, где все пары проходят шаг 4p и
    связаны по ключу. Оракул для векторов. -/
theorem verify_allow_iff (trustedRoots : List Key) (c : List Link) :
    verify trustedRoots c = .allow ↔
      c ≠ [] ∧
      (∀ h : 0 < c.length, RootTrusted trustedRoots c[0]) ∧
      ∀ i (h : i + 1 < c.length), narrowsB c[i] c[i+1] = true ∧ Linked c[i] c[i+1] := by
  rw [← checkPairs_iff]
  cases c with
  | nil => simp [verify]
  | cons root rest =>
    simp [verify, RootTrusted]

/-- Принятая цепочка непуста. -/
theorem length_pos_of_allow {trustedRoots : List Key} {c : List Link}
    (hv : verify trustedRoots c = .allow) : 0 < c.length := by
  have := ((verify_allow_iff trustedRoots c).mp hv).1
  cases c <;> simp_all

/-- Принятая цепочка прошла проверку пар. -/
theorem checkPairs_of_allow {trustedRoots : List Key} {c : List Link}
    (hv : verify trustedRoots c = .allow) : checkPairs c = true := by
  cases c with
  | nil => simp [verify] at hv
  | cons root rest =>
    simp only [verify] at hv
    split at hv <;> simp_all

/-! ## Т1. Монотонное сужение (любая длина цепочки) -/

/-- **Т1, ядро.** Если проверка пар прошла, права каждого звена — подмножество
    прав его родителя. Не зависит от параметров `verify`: при смене сигнатуры
    `verify` (§8 AAT-02) меняется только `checkPairs_of_allow`, а не Т1. -/
theorem t1_core (c : List Link) (h : checkPairs c = true)
    (i : Nat) (hi : i + 1 < c.length) : Narrows c[i] c[i+1] :=
  narrowsB_sound _ _ ((checkPairs_iff c).mp h i hi).1

/-- **Т1** (утверждённая формулировка). Если `verify` принял цепочку, права
    каждого звена — подмножество прав его родителя. Никакого ограничения на
    длину `c`. Следствие `t1_core`. -/
theorem t1_monotone (trustedRoots : List Key) (c : List Link)
    (hv : verify trustedRoots c = .allow)
    (i : Nat) (hi : i + 1 < c.length) : Narrows c[i] c[i+1] :=
  t1_core c (checkPairs_of_allow hv) i hi

/-- **Т1′ (следствие).** Права любого звена принятой цепочки — подмножество
    прав корня. -/
theorem t1_root_bound (trustedRoots : List Key) (c : List Link)
    (hv : verify trustedRoots c = .allow)
    (j : Nat) (hj : j < c.length) : Narrows (c[0]'(by omega)) c[j] := by
  induction j with
  | zero => intro call h; exact h
  | succ k ih =>
    intro call h
    exact ih (by omega) call (t1_monotone trustedRoots c hv k hj call h)

/-- Издатель корня принятой цепочки — из реестра доверенных корней.
    Заготовка места для Т3. -/
theorem root_trusted (trustedRoots : List Key) (c : List Link)
    (hv : verify trustedRoots c = .allow) :
    RootTrusted trustedRoots (c[0]'(length_pos_of_allow hv)) :=
  ((verify_allow_iff trustedRoots c).mp hv).2.1 _

/-- Обратное направление соответствия §8: цепочка, прошедшая все
    смоделированные шаги, принимается. -/
theorem verify_complete (trustedRoots : List Key) (c : List Link) (hne : c ≠ [])
    (hr : ∀ h : 0 < c.length, RootTrusted trustedRoots c[0])
    (h : ∀ i (h : i + 1 < c.length), narrowsB c[i] c[i+1] = true ∧ Linked c[i] c[i+1]) :
    verify trustedRoots c = .allow :=
  (verify_allow_iff trustedRoots c).mpr ⟨hne, hr, h⟩

/-! ## Теоремы-ловушки (проверяются ядром через `decide +kernel`) -/

/-- Инструмент без ограничений аргументов: `{}`. -/
def free (t : Tool) : Tool × CMap := (t, ⟨[], false⟩)

def roots : List Key := ["root-key"]
def human : Link := { issuer := "root-key", holder := "agentA", tools := [free "pay", free "email"] }
def aToB  : Link := { issuer := "agentA",   holder := "agentB", tools := [free "pay"] }

/-- Корректная цепочка из трёх звеньев принимается. -/
example : verify roots [human, aToB, { issuer := "agentB", holder := "agentC", tools := [] }]
    = .allow := by decide +kernel

/-- Ребёнок расширил права (добавил `"deploy"`) — отклоняется. -/
example : verify roots [human, { aToB with tools := [free "pay", free "deploy"] }] = .deny := by
  decide +kernel

/-- Расширение на третьем звене, а не на первом, — тоже отклоняется. -/
example : verify roots [human, aToB, { issuer := "agentB", holder := "agentC", tools := [free "email"] }]
    = .deny := by decide +kernel

/-- Звено выдано не тем, кто держал родителя, — отклоняется. -/
example : verify roots [human, { aToB with issuer := "mallory" }] = .deny := by decide +kernel

/-- Самозваный корень — отклоняется, даже если пары в порядке. -/
example : verify roots [{ human with issuer := "mallory-root" }, aToB] = .deny := by decide +kernel

/-- Пустая цепочка отклоняется. -/
example : verify roots [] = .deny := by decide +kernel

def l3 : Link := { issuer := "agentB", holder := "agentC", tools := [free "pay"] }
def l4 : Link := { issuer := "agentC", holder := "agentD", tools := [free "pay"] }

/-- Корректная цепочка из пяти звеньев принимается. -/
example : verify roots [human, aToB, l3, l4, { issuer := "agentD", holder := "agentE", tools := [] }]
    = .allow := by decide +kernel

/-- Расширение в середине цепочки (пара 1 из 3), а не на последней паре.
    Ловит `checkPairs`, проверяющий только последнюю пару: без этого примера
    такую ошибку замечало только доказательство `checkPairs_iff`. -/
example : verify roots [human, aToB,
    { issuer := "agentB", holder := "agentC", tools := [free "pay", free "deploy"] },
    { issuer := "agentC", holder := "agentD", tools := [free "pay", free "deploy"] }]
    = .deny := by decide +kernel

/-- Ребёнок короче родителя, но с чужим инструментом — отклоняется.
    Ловит `narrowsB`, принимающий «меньше инструментов» за сужение. -/
example : verify roots [human, { aToB with tools := [free "deploy"] }] = .deny := by decide +kernel

/-- Ребёнок выдан издателем родителя, а не его держателем, — отклоняется.
    Ловит `linkedB`, сравнивающий ещё и с `parent.issuer`. -/
example : verify roots [human, { aToB with issuer := "root-key" }] = .deny := by decide +kernel

/-- Расширение на пятом звене из пяти — отклоняется. -/
example : verify roots [human, aToB, l3, l4, { issuer := "agentD", holder := "agentE", tools := [free "email"] }]
    = .deny := by decide +kernel

/-! ### Ограничения аргументов в цепочке -/

def payCap (n : Rat) : Tool × CMap :=
  ("pay", ⟨[("amount", { c := .range none (some ⟨n, true⟩) })], false⟩)

/-- Ребёнок ограничивает аргумент инструмента, который у родителя без
    ограничений, — принимается (родительская `{}` нормализуется в `"*"`). -/
example : verify roots [human, { aToB with tools := [payCap 100] }] = .allow := by decide +kernel

/-- Лимит суммы сужается по цепочке — принимается. -/
example : verify roots [{ human with tools := [payCap 1000] },
    { aToB with tools := [payCap 100] }] = .allow := by decide +kernel

/-- Контрпример DeepSeek (раунд 1, §4): у ребёнка лимит 1000 при лимите
    родителя 100 — теперь отклоняется. -/
example : verify roots [{ human with tools := [payCap 100] },
    { aToB with tools := [payCap 1000] }] = .deny := by decide +kernel

/-- Ребёнок снимает ограничение (пустая карта = любые аргументы) — отклоняется. -/
example : verify roots [{ human with tools := [payCap 100] }, aToB] = .deny := by decide +kernel

/-- Общая ловушка: если на любом звене есть вызов, который ребёнку разрешён,
    а родителю нет, `verify` отклоняет — при любой длине. -/
theorem widening_rejected (trustedRoots : List Key) (c : List Link)
    (i : Nat) (hi : i + 1 < c.length)
    (call : Call) (hc : Permits c[i+1] call) (hp : ¬ Permits c[i] call) :
    verify trustedRoots c = .deny := by
  cases h : verify trustedRoots c with
  | deny => rfl
  | allow => exact absurd (t1_monotone trustedRoots c h i hi call hc) hp

/-- Ловушка на уровне спецификации: через `Permits` показываем, что пятое
    звено разрешает вызов, которого четвёртое не разрешает, и отсюда (через
    Т1) выводим `deny`. -/
example : verify roots [human, aToB, l3, l4, { issuer := "agentD", holder := "agentE", tools := [free "email"] }]
    = .deny :=
  widening_rejected roots _ 3 (by decide) ⟨"email", []⟩
    (by decide +kernel) (by decide +kernel)

/-- `Narrows` доказано напрямую из `Permits`, без `narrowsB_sound`:
    `aToB` разрешает только `pay` с любыми аргументами, и `human` тоже. -/
example : Narrows human aToB := by
  intro ⟨t, args⟩ h
  by_cases ht : t = "pay"
  · subst ht
    simp [Permits, Link.getTool, human, free, CMap.norm, permitsArgs, CMap.get]
  · have ht' : ¬ "pay" = t := fun e => ht e.symm
    simp [Permits, Link.getTool, aToB, free, ht'] at h

/-- И отрицание напрямую: ребёнок с `"email"` не сужает `aToB`. -/
example : ¬ Narrows aToB { aToB with tools := [free "email"] } := by
  intro h
  exact absurd (h ⟨"email", []⟩ (by decide +kernel)) (by decide +kernel)

/-- **Свидетель неполноты на уровне цепочки** (§4.1, B1 Давлятшина): ребёнок
    по смыслу уже родителя, но `verify` отклоняет — `verify_complete`
    относительно `Narrows` неверна по замыслу спецификации. -/
theorem incompleteness_witness :
    let p : Link := { human with tools := [("pay", ⟨[("amount", { c := r0to10 })], false⟩)] }
    let c : Link := { aToB with tools := [("pay", ⟨[("amount", { c := oneOf12 })], false⟩)] }
    Narrows p c ∧ verify roots [p, c] = .deny := by
  intro p c
  refine ⟨?_, by decide +kernel⟩
  intro ⟨t, args⟩ h
  by_cases ht : t = "pay"
  · subst ht
    simp only [Permits, Link.getTool, p, c, List.find?_cons, beq_self_eq_true,
      Option.map_some, CMap.norm, List.isEmpty_cons, Bool.false_and, Bool.false_eq_true,
      ite_false, permitsArgs, Bool.and_eq_true, List.all_eq_true, CMap.get] at h ⊢
    obtain ⟨hargs, hreq⟩ := h
    refine ⟨fun ⟨k, v⟩ hkv => ?_, fun kv hkv => ?_⟩
    · have hx := hargs ⟨k, v⟩ hkv
      by_cases hk : k = "amount"
      · subst hk
        simp only [beq_self_eq_true, Option.map_some] at hx ⊢
        exact oneOf12_semantically_narrower _ hx
      · have hk' : ("amount" == k) = false := by simp [Ne.symm hk]
        simp [hk'] at hx
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hkv
      subst hkv
      have := hreq ("amount", { c := oneOf12 }) (by simp)
      simpa using this
  · have ht' : ¬ "pay" = t := fun e => ht e.symm
    simp [Permits, Link.getTool, c, ht'] at h

end AAT
