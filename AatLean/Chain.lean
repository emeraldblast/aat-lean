import AatLean.CMap

/-!
# Звено цепочки AAT-02 и сужение прав (ядро Т1)

Звено — токен с полями §3.2 AAT-02. Алгоритм проверки §8 целиком — в
`AatLean/Verify.lean`; здесь — только то, на чём держится Т1, без параметров
`verify`.

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
свидетель — `incompleteness_witness` в `Verify.lean`. Т1 — корректность
структурных правил §4.5 относительно ненормативной модели C(T) из §4.1, для
цепочки любой длины.

Подписи и хэш — идеальные (допущения 1 и 5): `sigBy` — ключи (отпечатки
`jwk_thumbprint_uri`), под которыми подпись токена верна; `selfHash` —
SHA-256 его JWS Signing Input. Размеры, заголовки и разбор claims (дубликаты
JSON, типы, форма `cnf.jwk`) — `Parse.lean`; `Link` — уже разобранное звено.
-/

namespace AAT

abbrev Tool := String
abbrev Key := String

structure Link where
  /-- `iss`: URI корневого издателя или отпечаток ключа подписи (§3.2). -/
  issuer : Key
  /-- `jwk_thumbprint_uri(cnf.jwk)` — держатель (§4.2, I1). -/
  holder : Key
  /-- Инструменты и их карты ограничений (§3.3). Идентификаторы уникальны
      (§3.3.1, предусловие разбора). -/
  tools  : List (Tool × CMap)
  jti         : String := ""
  delDepth    : Nat := 0
  delMaxDepth : Nat := 0
  iat         : Int := 0
  exp         : Int := 0
  /-- `par_hash`; `none` — отсутствует (обязательно для корня, шаг 3d). -/
  parHash     : Option String := none
  /-- SHA-256 JWS Signing Input этого токена (то, с чем сравнивается
      `par_hash` ребёнка, шаг 4q). -/
  selfHash    : String := ""
  /-- Ключи, под которыми подпись токена верна (допущение 1). -/
  sigBy       : List Key := []
  /-- `aud`: `none` — отсутствует; иначе значения (§3.2). Значение, которое
      не строка и не массив строк, разбор кодирует как `some []` (шаг 6c
      отклоняет его так же, как массив без нужного значения). -/
  aud         : Option (List String) := none

/-- Вызов инструмента с аргументами. -/
structure Call where
  tool : Tool
  args : Args

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

/-- Ребёнок выдан тем, кто держал родителя (I1, шаг 4c). -/
def Linked (parent child : Link) : Prop :=
  child.issuer = parent.holder

/-! ## Структурная проверка сужения -/

/-- Шаг 4p: «Verify every tool in child_aat.tools is also present in
    parent_aat.tools» (4p1) и правила карт 4p2–4p4 после нормализации. -/
def narrowsB (parent child : Link) : Bool :=
  child.tools.all (fun (t, cm) =>
    match parent.getTool t with
    | some pm => narrowsMapB pm.norm cm.norm
    | none    => false)

def linkedB (parent child : Link) : Bool :=
  child.issuer == parent.holder

/-- Шаг 4p по всем соседним парам — без остальных шагов §8. -/
def checkNarrows : List Link → Bool
  | p :: c :: rest => narrowsB p c && checkNarrows (c :: rest)
  | _ => true

/-! ## Связь структурной проверки со смыслом -/

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

theorem checkNarrows_iff : ∀ (c : List Link),
    checkNarrows c = true ↔ ∀ i (h : i + 1 < c.length), narrowsB c[i] c[i+1] = true
  | [] => by simp [checkNarrows]
  | [_] => by simp [checkNarrows]
  | p :: q :: rest => by
    simp only [checkNarrows, Bool.and_eq_true, checkNarrows_iff (q :: rest)]
    constructor
    · rintro ⟨hn, hrest⟩ i hi
      cases i with
      | zero => exact hn
      | succ j => exact hrest j (by simp at hi ⊢; omega)
    · intro h
      refine ⟨h 0 (by simp), fun j hj => ?_⟩
      exact h (j + 1) (by simp at hj ⊢; omega)

/-! ## Т1, ядро -/

/-- **Т1, ядро.** Если шаг 4p прошёл на всех парах, права каждого звена —
    подмножество прав его родителя. Не зависит от параметров `verify`: при
    смене сигнатуры `verify` меняется только `checkNarrows_of_allow`
    (`Verify.lean`), а не Т1. -/
theorem t1_core (c : List Link) (h : checkNarrows c = true)
    (i : Nat) (hi : i + 1 < c.length) : Narrows c[i] c[i+1] :=
  narrowsB_sound _ _ ((checkNarrows_iff c).mp h i hi)

/-! ## Ловушки на уровне звеньев -/

/-- Инструмент без ограничений аргументов: `{}`. -/
def free (t : Tool) : Tool × CMap := (t, ⟨[], false⟩)

def human : Link := { issuer := "root-key", holder := "agentA", tools := [free "pay", free "email"] }
def aToB  : Link := { issuer := "agentA",   holder := "agentB", tools := [free "pay"] }

def payCap (n : Rat) : Tool × CMap :=
  ("pay", ⟨[("amount", { c := .range none (some ⟨n, true⟩) })], false⟩)

example : narrowsB human aToB = true := by decide +kernel
example : narrowsB human { aToB with tools := [free "pay", free "deploy"] } = false := by
  decide +kernel
example : narrowsB human { aToB with tools := [free "deploy"] } = false := by decide +kernel
example : narrowsB human { aToB with tools := [payCap 100] } = true := by decide +kernel
example : narrowsB { human with tools := [payCap 100] } { aToB with tools := [payCap 1000] } = false := by
  decide +kernel
example : narrowsB { human with tools := [payCap 100] } aToB = false := by decide +kernel
example : linkedB human aToB = true := by decide +kernel
example : linkedB human { aToB with issuer := "root-key" } = false := by decide +kernel
example : linkedB human { aToB with issuer := "mallory" } = false := by decide +kernel

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

end AAT
