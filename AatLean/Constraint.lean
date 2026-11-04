/-!
# Ограничения аргументов AAT-02 (§3.4, §4.5)

Все девять типов ядра: `wildcard`, `exact`, `one_of`, `not_one_of`, `range`,
`contains`, `subset`, `all`, `any`. Тип, которого точка проверки не знает, или
плохо сформированное ограничение — `malformed` (fail-closed, §3.4).

Порядок определений — правило шага 4:
1. `check` — денотация: какие значения ограничение допускает (§3.4, таблица 2).
   Определена без `subsumes` и ничего о нём не знает.
2. `subsumes` — структурное отношение `⊑` (§4.5, таблица 4): перечень
   разрешённых пар (родитель, ребёнок), всё остальное — `false`.
3. `subsumes_sound` — структурное отношение корректно относительно денотации:
   то, что §4.1 утверждает без доказательства.
4. `wf` — well-formedness (§3.4; шаги 3n и 4o) с пределом
   `MAX_CONSTRAINT_DEPTH`.

Допущение 6 (CONTEXT.md): все сравнения значений — по JCS, все числа
допустимы (§3.4). Поэтому число — точное рациональное `Rat`. Массив верхнего
уровня — список элементов `Scalar`; вложенные массивы и объекты хранятся в
JCS-форме (равенство строк = JCS-равенство). Объект верхнего уровня — тоже
JCS-форма.
-/

namespace AAT

/-- Элемент массива: скаляр или вложенное значение в JCS-форме. -/
inductive Scalar where
  | str (s : String)
  | num (q : Rat)
  | bool (b : Bool)
  | null
  /-- Вложенный массив или объект в JCS-форме. -/
  | compound (jcs : String)
deriving DecidableEq, Repr

/-- JSON-значение аргумента или ограничения. -/
inductive Value where
  | str (s : String)
  | num (q : Rat)
  | bool (b : Bool)
  | null
  /-- Массив: `contains` и `subset` смотрят на его элементы. -/
  | arr (xs : List Scalar)
  /-- Объект в JCS-форме. -/
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
  | notOneOf (vs : List Value)
  /-- `none` — граница отсутствует (не ограничено). -/
  | range (lo hi : Option Bound)
  | contains (req : List Scalar)
  | subset (allowed : List Scalar)
  | all (cs : List Constraint)
  | any (cs : List Constraint)
  /-- Неизвестный тип или плохо сформированное ограничение (fail-closed). -/
  | malformed

/-! ## 1. Денотация (§3.4, таблица 2) -/

def Bound.lowerOk (b : Bound) (x : Rat) : Bool :=
  if b.incl then decide (b.val ≤ x) else decide (b.val < x)

def Bound.upperOk (b : Bound) (x : Rat) : Bool :=
  if b.incl then decide (x ≤ b.val) else decide (x < b.val)

mutual
/-- Допускает ли ограничение значение аргумента. -/
def check : Constraint → Value → Bool
  -- «Any value is accepted.»
  | .wildcard, _ => true
  -- «Argument MUST equal value exactly.»
  | .exact v, x => x == v
  -- «Argument MUST be a member of values.»
  | .oneOf vs, x => vs.contains x
  -- «Argument MUST NOT be a member of excluded.»
  | .notOneOf vs, x => !vs.contains x
  -- «Argument MUST be a number satisfying the specified bounds.»
  | .range lo hi, .num x => lo.all (·.lowerOk x) && hi.all (·.upperOk x)
  | .range _ _, _ => false
  -- «Argument, which MUST be an array, MUST contain every element listed in
  -- required.»
  | .contains req, .arr xs => req.all xs.contains
  | .contains _, _ => false
  -- «Argument, which MUST be an array, MUST be a subset of allowed.»
  | .subset al, .arr xs => xs.all al.contains
  | .subset _, _ => false
  -- «Logical AND of nested constraints.» / «Logical OR …»
  | .all cs, x => checkAll cs x
  | .any cs, x => checkAny cs x
  | .malformed, _ => false

def checkAll : List Constraint → Value → Bool
  | [], _ => true
  | c :: cs, x => check c x && checkAll cs x

def checkAny : List Constraint → Value → Bool
  | [], _ => false
  | c :: cs, x => check c x || checkAny cs x
end

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

mutual
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
  -- not_one_of: not_one_of whose excluded values are a superset of the parent's
  | .notOneOf pv, .notOneOf cv => pv.all cv.contains
  -- contains: contains whose required elements are a superset of the parent's
  | .contains pr, .contains cr => pr.all cr.contains
  -- subset: subset whose allowed elements are a subset of the parent's
  | .subset pa, .subset ca => ca.all pa.contains
  -- all: all in which every parent clause subsumes at least one derived clause
  | .all ps, .all ds => coverAll ps ds
  -- any: any in which every derived clause is subsumed by at least one parent
  -- clause
  | .any ps, .any ds => ds.all (fun d => coveredBy ps d)
  | _, _ => false

/-- Каждое предложение родителя подчиняет хотя бы одно предложение ребёнка. -/
def coverAll : List Constraint → List Constraint → Bool
  | [], _ => true
  | p :: ps, ds => ds.any (fun d => subsumes p d) && coverAll ps ds

/-- Предложение ребёнка подчинено хотя бы одним предложением родителя. -/
def coveredBy : List Constraint → Constraint → Bool
  | [], _ => false
  | p :: ps, d => subsumes p d || coveredBy ps d
end

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

theorem checkAll_mem : ∀ (ds : List Constraint) x, checkAll ds x = true →
    ∀ d ∈ ds, check d x = true
  | [], _, _, d, hd => by simp at hd
  | e :: es, x, h, d, hd => by
    simp only [checkAll, Bool.and_eq_true] at h
    simp only [List.mem_cons] at hd
    rcases hd with rfl | hd
    · exact h.1
    · exact checkAll_mem es x h.2 d hd

theorem checkAny_exists : ∀ (ds : List Constraint) x, checkAny ds x = true →
    ∃ d ∈ ds, check d x = true
  | [], _, h => by simp [checkAny] at h
  | e :: es, x, h => by
    simp only [checkAny, Bool.or_eq_true] at h
    rcases h with h | h
    · exact ⟨e, by simp, h⟩
    · obtain ⟨d, hd, hdx⟩ := checkAny_exists es x h
      exact ⟨d, by simp [hd], hdx⟩

mutual
/-- **Корректность таблицы 4.** Если пара разрешена структурно, каждое
    значение, которое допускает ребёнок, допускает и родитель. -/
theorem subsumes_sound : ∀ (p c : Constraint), subsumes p c = true →
    ∀ x, check c x = true → check p x = true
  | .wildcard, _, _, x, _ => by simp [check]
  | .exact v, c, h, x, hx => by
    cases c <;> simp_all [subsumes, check]
  | .oneOf pv, c, h, x, hx => by
    cases c with
    | oneOf cv =>
      simp only [subsumes, Bool.and_eq_true, List.all_eq_true] at h
      simp only [check, List.contains_iff_mem] at hx ⊢
      exact List.contains_iff_mem.mp (h.2 x hx)
    | exact w => simp_all [subsumes, check]
    | _ => simp [subsumes] at h
  | .notOneOf pv, c, h, x, hx => by
    cases c with
    | notOneOf cv =>
      simp only [subsumes, List.all_eq_true, List.contains_iff_mem] at h
      simp only [check, Bool.not_eq_true'] at hx ⊢
      cases hc : pv.contains x with
      | false => rfl
      | true =>
        have hm := h x (List.contains_iff_mem.mp hc)
        rw [List.contains_iff_mem.mpr hm] at hx
        exact absurd hx (by decide)
    | _ => simp [subsumes] at h
  | .range plo phi, c, h, x, hx => by
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
  | .contains pr, c, h, x, hx => by
    cases c with
    | contains cr =>
      cases x with
      | arr xs =>
        simp only [subsumes, List.all_eq_true, List.contains_iff_mem] at h
        simp only [check, List.all_eq_true, List.contains_iff_mem] at hx ⊢
        exact fun e he => hx e (h e he)
      | _ => simp [check] at hx
    | _ => simp [subsumes] at h
  | .subset pa, c, h, x, hx => by
    cases c with
    | subset ca =>
      cases x with
      | arr xs =>
        simp only [subsumes, List.all_eq_true, List.contains_iff_mem] at h
        simp only [check, List.all_eq_true, List.contains_iff_mem] at hx ⊢
        exact fun e he => h e (hx e he)
      | _ => simp [check] at hx
    | _ => simp [subsumes] at h
  | .all ps, c, h, x, hx => by
    cases c with
    | all ds =>
      simp only [subsumes] at h
      simp only [check] at hx ⊢
      exact coverAll_sound ps ds h x hx
    | _ => simp [subsumes] at h
  | .any ps, c, h, x, hx => by
    cases c with
    | any ds =>
      simp only [subsumes, List.all_eq_true] at h
      simp only [check] at hx ⊢
      obtain ⟨d, hd, hdx⟩ := checkAny_exists ds x hx
      exact coveredBy_sound ps d (h d hd) x hdx
    | _ => simp [subsumes] at h
  | .malformed, _, h, _, _ => by simp [subsumes] at h

theorem coverAll_sound : ∀ (ps ds : List Constraint), coverAll ps ds = true →
    ∀ x, checkAll ds x = true → checkAll ps x = true
  | [], _, _, _, _ => by simp [checkAll]
  | p :: ps, ds, h, x, hx => by
    simp only [coverAll, Bool.and_eq_true, List.any_eq_true] at h
    obtain ⟨⟨d, hd, hpd⟩, hrest⟩ := h
    simp only [checkAll, Bool.and_eq_true]
    exact ⟨subsumes_sound p d hpd x (checkAll_mem ds x hx d hd), coverAll_sound ps ds hrest x hx⟩

theorem coveredBy_sound : ∀ (ps : List Constraint) (d : Constraint), coveredBy ps d = true →
    ∀ x, check d x = true → checkAny ps x = true
  | [], _, h, _, _ => by simp [coveredBy] at h
  | p :: ps, d, h, x, hx => by
    simp only [coveredBy, Bool.or_eq_true] at h
    simp only [checkAny, Bool.or_eq_true]
    rcases h with h | h
    · exact Or.inl (subsumes_sound p d h x hx)
    · exact Or.inr (coveredBy_sound ps d h x hx)
end

/-! ## 4. Well-formedness (§3.4; шаги 3n и 4o) -/

/-- Ограничение хорошо сформировано и его глубина не больше `n`
    (`MAX_CONSTRAINT_DEPTH`): «A constraint other than all or any has depth 1;
    an all or any has depth one more than its deepest clause.» Члены, которых
    тип не определяет, и `optional` внутри `all`/`any` отсекает разбор
    (`malformed`). -/
def wf : Nat → Constraint → Bool
  | 0, _ => false
  | _ + 1, .wildcard => true
  | _ + 1, .exact _ => true
  -- «one_of.values is a non-empty array»
  | _ + 1, .oneOf vs => !vs.isEmpty
  | _ + 1, .notOneOf _ => true
  -- «min is not greater than max»
  | _ + 1, .range (some lo) (some hi) => decide (lo.val ≤ hi.val)
  | _ + 1, .range _ _ => true
  | _ + 1, .contains _ => true
  | _ + 1, .subset _ => true
  -- «no all or any constraint has an empty constraints array»
  | n + 1, .all cs => !cs.isEmpty && cs.attach.all (fun ⟨c, _⟩ => wf n c)
  | n + 1, .any cs => !cs.isEmpty && cs.attach.all (fun ⟨c, _⟩ => wf n c)
  | _ + 1, .malformed => false

/-! ## 5. Свидетели неполноты (B1, B2 в отчёте Давлятшина; векторы J.19.x, J.8.4)

По смыслу ребёнок уже родителя, но таблица 4 пару не разрешает. -/

def r0to10 : Constraint := .range (some ⟨0, true⟩) (some ⟨10, true⟩)
def oneOf12 : Constraint := .oneOf [.num 1, .num 2]

/-- `one_of` из значений внутри `range`: по смыслу сужение… -/
theorem oneOf12_semantically_narrower :
    ∀ x, check oneOf12 x = true → check r0to10 x = true := by
  intro x hx
  simp only [oneOf12, check, List.contains_cons, List.contains_nil, Bool.or_false,
    Bool.or_eq_true, beq_iff_eq] at hx
  rcases hx with rfl | rfl <;> decide +kernel

/-- …но структурно пара отвергается. -/
theorem oneOf12_structurally_rejected : subsumes r0to10 oneOf12 = false := rfl

def anyPdfCsv : Constraint := .any [.exact (.str "pdf"), .exact (.str "csv")]

/-- Пример из самого §4.1: `exact` под `any` — по смыслу сужение… -/
theorem exactPdf_semantically_narrower :
    ∀ x, check (.exact (.str "pdf")) x = true → check anyPdfCsv x = true := by
  intro x hx
  simp only [check, beq_iff_eq] at hx
  subst hx
  decide +kernel

/-- …но таблица 4 разрешает под `any` только `any` (B2, вектор J.19.1). -/
theorem exactPdf_structurally_rejected : subsumes anyPdfCsv (.exact (.str "pdf")) = false := rfl

/-! ## 6. Ловушки (ядро, `decide +kernel`) -/

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
-- «A derived not_one_of under a parent one_of is invalid»
example : subsumes (.oneOf [.str "a", .str "b"]) (.notOneOf [.str "c"]) = false := by decide +kernel
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
-- not_one_of: исключённых у ребёнка не меньше
example : subsumes (.notOneOf [.str "a"]) (.notOneOf [.str "a", .str "b"]) = true := by decide +kernel
example : subsumes (.notOneOf [.str "a", .str "b"]) (.notOneOf [.str "a"]) = false := by decide +kernel
example : check (.notOneOf [.str "a"]) (.str "a") = false := by decide +kernel
example : check (.notOneOf [.str "a"]) (.str "b") = true := by decide +kernel
-- contains: требуемых у ребёнка не меньше
example : subsumes (.contains [.str "a"]) (.contains [.str "a", .str "b"]) = true := by decide +kernel
example : subsumes (.contains [.str "a", .str "b"]) (.contains [.str "a"]) = false := by decide +kernel
example : check (.contains [.str "a"]) (.arr [.str "b", .str "a"]) = true := by decide +kernel
example : check (.contains [.str "a"]) (.arr [.str "b"]) = false := by decide +kernel
example : check (.contains [.str "a"]) (.str "a") = false := by decide +kernel
-- должны присутствовать все требуемые, а не хотя бы один
example : check (.contains [.str "a", .str "b"]) (.arr [.str "a"]) = false := by decide +kernel
-- subset: разрешённых у ребёнка не больше
example : subsumes (.subset [.str "a", .str "b"]) (.subset [.str "a"]) = true := by decide +kernel
example : subsumes (.subset [.str "a"]) (.subset [.str "a", .str "b"]) = false := by decide +kernel
example : check (.subset [.str "a", .str "b"]) (.arr [.str "a"]) = true := by decide +kernel
example : check (.subset [.str "a"]) (.arr [.str "a", .str "b"]) = false := by decide +kernel
example : check (.subset [.str "a"]) (.str "a") = false := by decide +kernel
-- all: каждое предложение родителя подчиняет хотя бы одно предложение ребёнка
example : subsumes (.all [.wildcard, .wildcard]) (.all [.exact (.num 5)]) = true := by decide +kernel
example : subsumes (.all [r0to10, .exact (.num 5)]) (.all [.exact (.num 5)]) = true := by decide +kernel
example : subsumes (.all [r0to10, .exact (.num 5)]) (.all [r0to10]) = false := by decide +kernel
example : check (.all [r0to10, .notOneOf [.num 3]]) (.num 3) = false := by decide +kernel
-- any: каждое предложение ребёнка подчинено хотя бы одним предложением родителя
example : subsumes anyPdfCsv (.any [.exact (.str "pdf")]) = true := by decide +kernel
example : subsumes anyPdfCsv (.any [.exact (.str "pdf"), .exact (.str "docx")]) = false := by
  decide +kernel
example : check anyPdfCsv (.str "csv") = true := by decide +kernel
example : check anyPdfCsv (.str "docx") = false := by decide +kernel
-- B2: exact под any — нет (вектор J.19.1)
example : subsumes anyPdfCsv (.exact (.str "pdf")) = false := by decide +kernel
-- B2: all под any — нет
example : subsumes anyPdfCsv (.all [.exact (.str "pdf")]) = false := by decide +kernel
-- malformed: fail-closed
example : check .malformed (.str "a") = false := by decide +kernel
example : subsumes .wildcard .malformed = true := by decide +kernel
example : wf 32 .malformed = false := by decide +kernel
-- well-formedness
example : wf 32 (.oneOf []) = false := by decide +kernel
example : wf 32 (.range (some ⟨20, true⟩) (some ⟨5, true⟩)) = false := by decide +kernel
example : wf 32 (.all []) = false := by decide +kernel
example : wf 32 (.any [.all [], .wildcard]) = false := by decide +kernel
example : wf 32 (.any [.all [.wildcard], .wildcard]) = true := by decide +kernel
-- глубина: all глубины 3 при пределе 2 — отказ
example : wf 2 (.all [.all [.wildcard]]) = false := by decide +kernel
example : wf 3 (.all [.all [.wildcard]]) = true := by decide +kernel

end AAT
