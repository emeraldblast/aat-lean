/-!
# Минимальная модель цепочки полномочий (тест осуществимости)

Звено — это токен: кто выдал, кому выдан, на какие инструменты.
Ограничений аргументов, времени, nonce и отзыва в этой модели нет.

Цепочка хранится от корня к листу: `c[0]` — корень, `c[c.length-1]` — лист.

Разделение, на котором держится смысл Т1:
* `Permits` — что значит «звено разрешает вызов». Меняется, когда появятся
  ограничения аргументов.
* `Narrows` — спецификация (`Prop`): «любой вызов, разрешённый ребёнку,
  разрешён родителю». Определена через `Permits`; её текст не меняется.
* `narrowsB` — то, что реально исполняет верификатор (`Bool`). Меняется вместе
  с `Permits`, и `narrowsB_iff` (а за ней Т1) доказывается заново.
Т1 говорит о `Narrows`, а не о `narrowsB`. Пока права — список имён, `Narrows`
почти дословно повторяет то, что решает `narrowsB`, так что гарантия малая:
проверка решает то утверждение, ради которого написана. Содержательной Т1
станет на шаге 4, когда `Permits` получит семантику ограничений AAT.

`verify` пока не получает ни запроса, ни предъявителя, ни получателя: `allow`
значит «цепочка корректна», а не «этот вызов разрешён». Привязка запроса к
правам листа — Т2. Привязка предъявителя (proof-of-possession) и получателя
(`aud`) в Т1–Т5 не входит — открытый вопрос.

`Linked` сравнивает имена (`child.issuer = parent.holder`), а не ссылку на
конкретный родительский токен: один и тот же ребёнок проходит под любым
родителем с тем же держателем.
-/

namespace AAT

abbrev Tool := String
abbrev Key := String

structure Link where
  issuer : Key
  holder : Key
  tools  : List Tool
deriving Repr, DecidableEq

/-- Вызов инструмента. Аргументы появятся на шаге 4. -/
structure Call where
  tool : Tool
deriving Repr, DecidableEq

inductive Decision where
  | allow
  | deny
deriving Repr, DecidableEq

/-! ## Спецификация -/

/-- Звено разрешает вызов. -/
def Permits (l : Link) (call : Call) : Prop :=
  call.tool ∈ l.tools

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

def narrowsB (parent child : Link) : Bool :=
  child.tools.all (fun x => parent.tools.contains x)

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

theorem narrowsB_iff (p c : Link) : narrowsB p c = true ↔ Narrows p c := by
  simp only [narrowsB, Narrows, Permits, List.all_eq_true, List.contains_iff_mem]
  constructor
  · intro h call hc; exact h _ hc
  · intro h x hx; exact h ⟨x⟩ hx

theorem linkedB_iff (p c : Link) : linkedB p c = true ↔ Linked p c := by
  simp [linkedB, Linked]

/-- `checkPairs` принимает ровно те цепочки, где каждая соседняя пара сужает
    права и связана по ключу. -/
theorem checkPairs_iff : ∀ (c : List Link),
    checkPairs c = true ↔
      ∀ i (h : i + 1 < c.length), Narrows c[i] c[i+1] ∧ Linked c[i] c[i+1]
  | [] => by simp [checkPairs]
  | [_] => by simp [checkPairs]
  | p :: q :: rest => by
    simp only [checkPairs, Bool.and_eq_true, narrowsB_iff, linkedB_iff,
      checkPairs_iff (q :: rest)]
    constructor
    · rintro ⟨⟨hn, hl⟩, hrest⟩ i hi
      cases i with
      | zero => exact ⟨hn, hl⟩
      | succ j => exact hrest j (by simp at hi ⊢; omega)
    · intro h
      refine ⟨h 0 (by simp), fun j hj => ?_⟩
      exact h (j + 1) (by simp at hj ⊢; omega)

/-- `verify` принимает ровно непустые цепочки с доверенным корнем,
    где все пары сужают права и связаны по ключу. -/
theorem verify_allow_iff (trustedRoots : List Key) (c : List Link) :
    verify trustedRoots c = .allow ↔
      c ≠ [] ∧
      (∀ h : 0 < c.length, RootTrusted trustedRoots c[0]) ∧
      ∀ i (h : i + 1 < c.length), Narrows c[i] c[i+1] ∧ Linked c[i] c[i+1] := by
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

/-! ## Т1. Монотонное сужение (любая длина цепочки) -/

/-- **Т1.** Если `verify` принял цепочку, права каждого звена — подмножество
    прав его родителя. Никакого ограничения на длину `c`. -/
theorem t1_monotone (trustedRoots : List Key) (c : List Link)
    (hv : verify trustedRoots c = .allow)
    (i : Nat) (hi : i + 1 < c.length) : Narrows c[i] c[i+1] := by
  exact (((verify_allow_iff trustedRoots c).mp hv).2.2 i hi).1

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

/-- Обратное направление: верификатор не отклоняет корректные цепочки
    (проверка не «пустая», т.е. не сводится к `deny` для всех). -/
theorem verify_complete (trustedRoots : List Key) (c : List Link) (hne : c ≠ [])
    (hr : ∀ h : 0 < c.length, RootTrusted trustedRoots c[0])
    (h : ∀ i (h : i + 1 < c.length), Narrows c[i] c[i+1] ∧ Linked c[i] c[i+1]) :
    verify trustedRoots c = .allow :=
  (verify_allow_iff trustedRoots c).mpr ⟨hne, hr, h⟩

/-! ## Теоремы-ловушки (проверяются ядром через `decide`) -/

def roots : List Key := ["root-key"]
def human : Link := { issuer := "root-key", holder := "agentA", tools := ["pay", "email"] }
def aToB  : Link := { issuer := "agentA",   holder := "agentB", tools := ["pay"] }

/-- Корректная цепочка из трёх звеньев принимается. -/
example : verify roots [human, aToB, { issuer := "agentB", holder := "agentC", tools := [] }]
    = .allow := by decide

/-- Ребёнок расширил права (добавил `"deploy"`) — отклоняется. -/
example : verify roots [human, { aToB with tools := ["pay", "deploy"] }] = .deny := by decide

/-- Расширение на третьем звене, а не на первом, — тоже отклоняется. -/
example : verify roots [human, aToB, { issuer := "agentB", holder := "agentC", tools := ["email"] }]
    = .deny := by decide

/-- Звено выдано не тем, кто держал родителя, — отклоняется. -/
example : verify roots [human, { aToB with issuer := "mallory" }] = .deny := by decide

/-- Самозваный корень — отклоняется, даже если пары в порядке. -/
example : verify roots [{ human with issuer := "mallory-root" }, aToB] = .deny := by decide

/-- Пустая цепочка отклоняется. -/
example : verify roots [] = .deny := by decide

def l3 : Link := { issuer := "agentB", holder := "agentC", tools := ["pay"] }
def l4 : Link := { issuer := "agentC", holder := "agentD", tools := ["pay"] }

/-- Корректная цепочка из пяти звеньев принимается. -/
example : verify roots [human, aToB, l3, l4, { issuer := "agentD", holder := "agentE", tools := [] }]
    = .allow := by decide

/-- Расширение в середине цепочки (пара 1 из 3), а не на последней паре.
    Ловит `checkPairs`, проверяющий только последнюю пару: без этого примера
    такую ошибку замечало только доказательство `checkPairs_iff`. -/
example : verify roots [human, aToB,
    { issuer := "agentB", holder := "agentC", tools := ["pay", "deploy"] },
    { issuer := "agentC", holder := "agentD", tools := ["pay", "deploy"] }]
    = .deny := by decide

/-- Расширение на пятом звене из пяти — отклоняется. -/
example : verify roots [human, aToB, l3, l4, { issuer := "agentD", holder := "agentE", tools := ["email"] }]
    = .deny := by decide

/-- Общая ловушка: если на любом звене есть вызов, который ребёнку разрешён,
    а родителю нет, `verify` отклоняет — при любой длине. -/
theorem widening_rejected (trustedRoots : List Key) (c : List Link)
    (i : Nat) (hi : i + 1 < c.length)
    (call : Call) (hc : Permits c[i+1] call) (hp : ¬ Permits c[i] call) :
    verify trustedRoots c = .deny := by
  cases h : verify trustedRoots c with
  | deny => rfl
  | allow => exact absurd (t1_monotone trustedRoots c h i hi call hc) hp

/-- Ловушка на уровне спецификации, а не только вывода кода: сначала
    показываем через `Permits`, что пятое звено разрешает вызов, которого
    четвёртое не разрешает, и отсюда (через Т1) выводим `deny`. -/
example : verify roots [human, aToB, l3, l4, { issuer := "agentD", holder := "agentE", tools := ["email"] }]
    = .deny :=
  widening_rejected roots _ 3 (by decide) ⟨"email"⟩
    (by simp [Permits]) (by simp [Permits, l4])

/-- `Narrows` доказано напрямую из `Permits`, без `narrowsB_iff`:
    спецификация проверяется независимо от Bool-проверки. -/
example : Narrows human aToB := by
  intro call h
  simp only [Permits, aToB, human, List.mem_cons, List.not_mem_nil, or_false] at h ⊢
  exact Or.inl h

/-- И отрицание напрямую: ребёнок с `"email"` не сужает `aToB`. -/
example : ¬ Narrows aToB { aToB with tools := ["email"] } := by
  intro h
  have := h ⟨"email"⟩ (by simp [Permits])
  simp [Permits, aToB] at this

end AAT
