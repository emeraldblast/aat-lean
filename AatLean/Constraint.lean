/-!
# Ограничения аргументов AAT-02, первый проход

Типы: `wildcard`, `exact`, `one_of`, `range` (§3.4, таблица 2).
Второй проход: `not_one_of`, `contains`, `subset`, `all`, `any`.

Порядок определений — правило шага 4:
1. `check` — денотация: какие значения ограничение допускает (§3.4, таблица 2).
   Определена без `subsumes` и ничего о нём не знает.
2. `subsumes` — структурное отношение `⊑` (§4.5, таблица 4): перечень
   разрешённых пар (родитель, ребёнок), всё остальное — `false`.
3. `subsumes_sound` — структурное отношение корректно относительно денотации:
   то, что §4.1 утверждает без доказательства.

Допущение 6 (CONTEXT.md): все сравнения значений — по JCS, все числа
допустимы (§3.4). Поэтому число — точное рациональное `Rat`, и равенство чисел
по JCS совпадает с равенством значений. Составные значения (массивы, объекты)
хранятся в JCS-форме; ограничения первого прохода внутрь них не смотрят.
-/

namespace AAT

/-- JSON-значение аргумента или ограничения. -/
inductive Value where
  | str (s : String)
  | num (q : Rat)
  | bool (b : Bool)
  | null
  /-- Массив или объект в JCS-форме: равенство строк = JCS-равенство. -/
  | compound (jcs : String)
deriving DecidableEq, Repr

/-- Граница `range`: значение и включена ли она (`min_inclusive` /
    `max_inclusive`, по умолчанию `true` — подставляется при разборе). -/
structure Bound where
  val  : Rat
  incl : Bool
deriving DecidableEq, Repr

inductive Constraint where
  | wildcard
  | exact (v : Value)
  | oneOf (vs : List Value)
  /-- `none` — граница отсутствует (не ограничено). -/
  | range (lo hi : Option Bound)
deriving Repr

/-! ## 1. Денотация (§3.4, таблица 2) -/

def Bound.lowerOk (b : Bound) (x : Rat) : Bool :=
  if b.incl then decide (b.val ≤ x) else decide (b.val < x)

def Bound.upperOk (b : Bound) (x : Rat) : Bool :=
  if b.incl then decide (x ≤ b.val) else decide (x < b.val)

/-- Допускает ли ограничение значение аргумента. -/
def check : Constraint → Value → Bool
  -- «Any value is accepted.»
  | .wildcard, _ => true
  -- «Argument MUST equal value exactly.»
  | .exact v, x => x == v
  -- «Argument MUST be a member of values.»
  | .oneOf vs, x => vs.contains x
  -- «Argument MUST be a number satisfying the specified bounds.»
  | .range lo hi, .num x => lo.all (·.lowerOk x) && hi.all (·.upperOk x)
  | .range _ _, _ => false

/-! ## 2. Структурное отношение `⊑` (§4.5, таблица 4 и правила для `range`) -/

/-- Нижняя граница ребёнка не слабее родительской (§4.5, *range*). -/
def lowerTighter : Option Bound → Option Bound → Bool
  -- «A missing bound on the parent is treated as unbounded»
  | none, _ => true
  -- «a missing bound on the derived constraint is only valid if the parent
  -- bound is also missing»
  | some _, none => false
  -- строго внутри — любая включённость; равная граница не может быть
  -- включённой там, где у родителя исключённая
  | some p, some c => decide (p.val < c.val) || (decide (p.val = c.val) && (p.incl || !c.incl))

/-- Верхняя граница ребёнка не слабее родительской. -/
def upperTighter : Option Bound → Option Bound → Bool
  | none, _ => true
  | some _, none => false
  | some p, some c => decide (c.val < p.val) || (decide (c.val = p.val) && (p.incl || !c.incl))

/-- `subsumes parent child` — строка таблицы 4 разрешает пару.
    «Every other pair is invalid and MUST be rejected.» -/
def subsumes : Constraint → Constraint → Bool
  -- wildcard: any constraint
  | .wildcard, _ => true
  -- exact: exact with the same value
  | .exact v, .exact w => w == v
  -- range: range at least as tight; exact whose value is a number the parent
  -- range accepts
  | .range plo phi, .range clo chi => lowerTighter plo clo && upperTighter phi chi
  | .range plo phi, .exact (.num x) => check (.range plo phi) (.num x)
  -- one_of: one_of whose values are a non-empty subset of the parent's;
  -- exact whose value is a member of the parent's values
  | .oneOf pv, .oneOf cv => !cv.isEmpty && cv.all pv.contains
  | .oneOf pv, .exact w => pv.contains w
  | _, _ => false

/-! ## 3. Корректность: `⊑` → включение денотаций -/

theorem lowerTighter_sound {p c : Option Bound} (h : lowerTighter p c = true)
    {x : Rat} (hx : c.all (·.lowerOk x) = true) : p.all (·.lowerOk x) = true := by
  cases p with
  | none => rfl
  | some pb =>
    cases c with
    | none => simp [lowerTighter] at h
    | some cb =>
      simp only [Option.all_some, Bound.lowerOk] at hx ⊢
      simp only [lowerTighter, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq,
        Bool.not_eq_true'] at h
      cases hp : pb.incl <;> cases hc : cb.incl <;> simp_all <;> grind

theorem upperTighter_sound {p c : Option Bound} (h : upperTighter p c = true)
    {x : Rat} (hx : c.all (·.upperOk x) = true) : p.all (·.upperOk x) = true := by
  cases p with
  | none => rfl
  | some pb =>
    cases c with
    | none => simp [upperTighter] at h
    | some cb =>
      simp only [Option.all_some, Bound.upperOk] at hx ⊢
      simp only [upperTighter, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq,
        Bool.not_eq_true'] at h
      cases hp : pb.incl <;> cases hc : cb.incl <;> simp_all <;> grind

/-- **Корректность таблицы 4 (первый проход).** Если пара разрешена
    структурно, каждое значение, которое допускает ребёнок, допускает и
    родитель. -/
theorem subsumes_sound (p c : Constraint) (h : subsumes p c = true)
    (x : Value) (hx : check c x = true) : check p x = true := by
  cases p with
  | wildcard => rfl
  | exact v =>
    cases c <;> simp_all [subsumes, check]
  | oneOf pv =>
    cases c with
    | oneOf cv =>
      simp only [subsumes, Bool.and_eq_true, List.all_eq_true] at h
      simp only [check, List.contains_iff_mem] at hx ⊢
      exact List.contains_iff_mem.mp (h.2 x hx)
    | exact w => simp_all [subsumes, check]
    | _ => simp [subsumes] at h
  | range plo phi =>
    cases c with
    | range clo chi =>
      simp only [subsumes, Bool.and_eq_true] at h
      cases x with
      | num q =>
        simp only [check, Bool.and_eq_true] at hx ⊢
        exact ⟨lowerTighter_sound h.1 hx.1, upperTighter_sound h.2 hx.2⟩
      | _ => simp [check] at hx
    | exact w =>
      cases w with
      | num q =>
        simp only [check, beq_iff_eq] at hx
        subst hx
        simpa [subsumes] using h
      | _ => simp [subsumes] at h
    | _ => simp [subsumes] at h

/-! ## 4. Свидетель неполноты (B1 в отчёте Давлятшина; векторы J.19.x, J.8.4)

`one_of` из значений внутри `range`: по смыслу это сужение, но таблица 4
разрешает под `range` только `range` и `exact`. -/

def r0to10 : Constraint := .range (some ⟨0, true⟩) (some ⟨10, true⟩)
def oneOf12 : Constraint := .oneOf [.num 1, .num 2]

/-- По смыслу ребёнок уже родителя: каждое допустимое ребёнку значение
    допустимо родителю. -/
theorem oneOf12_semantically_narrower :
    ∀ x, check oneOf12 x = true → check r0to10 x = true := by
  intro x hx
  simp only [oneOf12, check, List.contains_cons, List.contains_nil, Bool.or_false,
    Bool.or_eq_true, beq_iff_eq] at hx
  rcases hx with rfl | rfl <;> decide +kernel

/-- …но структурно пара отвергается. -/
theorem oneOf12_structurally_rejected : subsumes r0to10 oneOf12 = false := rfl

/-! ## 5. Ловушки (ядро, `decide +kernel`) -/

-- exact
example : subsumes (.exact (.str "a")) (.exact (.str "a")) = true := by decide +kernel
example : subsumes (.exact (.str "a")) (.exact (.str "b")) = false := by decide +kernel
example : subsumes (.exact (.str "a")) .wildcard = false := by decide +kernel
-- wildcard: родитель — любое; ребёнок-wildcard под не-wildcard — нет
example : subsumes .wildcard (.oneOf []) = true := by decide +kernel
example : subsumes (.oneOf [.str "a"]) .wildcard = false := by decide +kernel
-- one_of
example : subsumes (.oneOf [.str "a", .str "b"]) (.oneOf [.str "b"]) = true := by decide +kernel
example : subsumes (.oneOf [.str "a"]) (.oneOf [.str "a", .str "b"]) = false := by decide +kernel
-- «A derived one_of cannot be empty»
example : subsumes (.oneOf [.str "a"]) (.oneOf []) = false := by decide +kernel
example : subsumes (.oneOf [.str "a"]) (.exact (.str "a")) = true := by decide +kernel
example : subsumes (.oneOf [.str "a"]) (.exact (.str "c")) = false := by decide +kernel
-- range: сужение, равная граница, включённость
example : subsumes r0to10 (.range (some ⟨1, true⟩) (some ⟨9, true⟩)) = true := by decide +kernel
example : subsumes r0to10 (.range (some ⟨0, true⟩) (some ⟨10, false⟩)) = true := by decide +kernel
example : subsumes (.range (some ⟨0, false⟩) none) (.range (some ⟨0, true⟩) none) = false := by
  decide +kernel
example : subsumes r0to10 (.range (some ⟨0, true⟩) (some ⟨11, true⟩)) = false := by decide +kernel
-- отсутствующая граница ребёнка допустима, только если у родителя её тоже нет
example : subsumes r0to10 (.range (some ⟨0, true⟩) none) = false := by decide +kernel
example : subsumes r0to10 (.range none (some ⟨10, true⟩)) = false := by decide +kernel
example : subsumes (.range none none) (.range none none) = true := by decide +kernel
-- дробные границы
example : subsumes (.range (some ⟨1/10, true⟩) none) (.range (some ⟨1/5, true⟩) none) = true := by
  decide +kernel
-- range → exact: число внутри / вне / не число
example : subsumes r0to10 (.exact (.num 5)) = true := by decide +kernel
example : subsumes r0to10 (.exact (.num 11)) = false := by decide +kernel
example : subsumes r0to10 (.exact (.str "5")) = false := by decide +kernel
-- check: range не принимает не-числа; "5" ≠ 5
example : check r0to10 (.str "5") = false := by decide +kernel
example : check (.exact (.num 5)) (.str "5") = false := by decide +kernel
example : check (.range (some ⟨0, false⟩) none) (.num 0) = false := by decide +kernel

end AAT
