import AatLean.Constraint

/-!
# Карты ограничений инструмента (AAT-02 §3.3, §4.5, §8 шаги 4p и 6b)

Порядок — тот же, что для ограничений:
1. `permitsArgs` — денотация: какие аргументы вызова карта допускает (шаг 6b,
   закрытый мир). Определена без структурных правил.
2. `narrowsMapB` — структурные правила ключей и ограничений (шаги 4p2–4p4).
3. `narrowsMapB_sound` — правила корректны относительно денотации.

Ключ `"*"` хранится отдельным флагом `star`: по §3.3 его значение — всегда
`wildcard` без `optional`, и он не называет аргумент (аргумент с буквальным
именем `"*"` считается неназванным). Предусловие: ключи карты и аргументов
уникальны (дубликаты отвергаются при разборе, §3.3.1, шаги 3b/4b/6b).
-/

namespace AAT

abbrev ArgName := String

/-- Запись карты: ограничение и `optional` (по умолчанию `false`). -/
structure Entry where
  c        : Constraint
  optional : Bool := false
deriving Repr

/-- Карта ограничений одного инструмента. -/
structure CMap where
  named : List (ArgName × Entry)
  /-- Есть ли запись `"*": {"constraint_type": "wildcard"}`. -/
  star  : Bool
deriving Repr

def CMap.get (m : CMap) (k : ArgName) : Option Entry :=
  (m.named.find? (·.1 == k)).map (·.2)

/-- «An empty constraint map is equivalent to {"*": wildcard}» (§3.3). -/
def CMap.norm (m : CMap) : CMap :=
  if m.named.isEmpty && !m.star then { m with star := true } else m

abbrev Args := List (ArgName × Value)

def argsHas (args : Args) (k : ArgName) : Bool := args.any (·.1 == k)

/-! ## 1. Денотация: шаг 6b для одного инструмента -/

/-- Допускает ли (нормализованная) карта аргументы вызова.
    «For each argument in args: if M names it, verify its value satisfies that
    constraint; otherwise, if M contains "*", verify the value satisfies M's
    "*" constraint; otherwise DENY (closed-world mode). For each argument M
    names that is required, if it is absent from args, DENY.» -/
def permitsArgs (m : CMap) (args : Args) : Bool :=
  args.all (fun (k, v) =>
    match m.get k with
    | some e => check e.c v
    | none   => m.star) &&
  m.named.all (fun (k, _) =>
    match m.get k with
    | some e => e.optional || argsHas args k
    | none   => true)

/-! ## 2. Структурные правила: шаги 4p2–4p4 -/

/-- Сужение карты родителя `p` картой ребёнка `c` (обе нормализованы). -/
def narrowsMapB (p c : CMap) : Bool :=
  -- 4p2: every key the child names is named by the parent unless the parent
  -- contains "*"
  c.named.all (fun (k, _) => (p.get k).isSome || p.star) &&
  -- 4p2: every key other than "*" that the parent names and the child omits is
  -- optional in the parent, and the child then does not contain "*"
  p.named.all (fun (k, pe) => (c.get k).isSome || (pe.optional && !c.star)) &&
  -- 4p2: the child contains "*" only if the parent does
  (!c.star || p.star) &&
  -- 4p3: for each argument key named in both maps, the child's constraint is
  -- required if the parent's is
  c.named.all (fun (k, ce) =>
    match p.get k with
    | some pe => pe.optional || !ce.optional
    | none    => true) &&
  -- 4p4: for each argument key named in the child's map, the parent's
  -- constraint for that key, or the parent's "*" constraint if the parent does
  -- not name it, subsumes the child's
  c.named.all (fun (k, ce) =>
    match p.get k with
    | some pe => subsumes pe.c ce.c
    | none    => subsumes .wildcard ce.c)

/-! ## 3. Корректность -/

theorem get_isSome_of_mem {m : CMap} {k : ArgName} {e : Entry} (h : (k, e) ∈ m.named) :
    (m.get k).isSome = true := by
  unfold CMap.get
  cases hf : m.named.find? (·.1 == k) with
  | none =>
    rw [List.find?_eq_none] at hf
    exact absurd (by simp) (hf _ h)
  | some _ => rfl

theorem mem_of_get {m : CMap} {k : ArgName} {e : Entry} (h : m.get k = some e) :
    (k, e) ∈ m.named := by
  unfold CMap.get at h
  cases hf : m.named.find? (·.1 == k) with
  | none => simp [hf] at h
  | some kv =>
    simp only [hf, Option.map_some, Option.some.injEq] at h
    have hm := List.mem_of_find?_eq_some hf
    have hk := List.find?_some hf
    simp only [beq_iff_eq] at hk
    subst h; subst hk
    exact hm

/-- **Корректность правил 4p2–4p4.** Если карта ребёнка структурно сужает
    карту родителя, всякий вызов, допустимый ребёнку, допустим родителю. -/
theorem narrowsMapB_sound (p c : CMap) (h : narrowsMapB p c = true)
    (args : Args) (hc : permitsArgs c args = true) : permitsArgs p args = true := by
  simp only [narrowsMapB, Bool.and_eq_true, List.all_eq_true] at h
  obtain ⟨⟨⟨⟨hKeys, hOmit⟩, hStar⟩, hReq⟩, hSub⟩ := h
  simp only [permitsArgs, Bool.and_eq_true, List.all_eq_true] at hc ⊢
  obtain ⟨hArgs, hNamed⟩ := hc
  constructor
  · -- каждый аргумент допустим родителю
    intro ⟨k, v⟩ hkv
    have hcv := hArgs _ hkv
    simp only at hcv ⊢
    cases hcg : c.get k with
    | some ce =>
      rw [hcg] at hcv
      have hmem := mem_of_get hcg
      have hs := hSub _ hmem
      simp only at hs
      cases hpg : p.get k with
      | some pe =>
        rw [hpg] at hs
        exact subsumes_sound _ _ hs _ hcv
      | none =>
        have hk := hKeys _ hmem
        simp only [hpg, Option.isSome_none, Bool.false_or] at hk
        exact hk
    | none =>
      rw [hcg] at hcv
      -- ребёнок допускает аргумент только через "*", значит у родителя "*"
      have hps : p.star = true := by
        simp only [Bool.or_eq_true, Bool.not_eq_true'] at hStar
        rcases hStar with h | h
        · simp [h] at hcv
        · exact h
      cases hpg : p.get k with
      | none => exact hps
      | some pe =>
        -- родитель называет ключ, ребёнок — нет: по 4p2 у ребёнка нет "*"
        have ho := hOmit _ (mem_of_get hpg)
        simp only [hcg, Option.isSome_none, Bool.false_or, Bool.and_eq_true,
          Bool.not_eq_true'] at ho
        simp [ho.2] at hcv
  · -- обязательные аргументы родителя присутствуют
    intro ⟨k, _⟩ hk
    simp only
    cases hpg : p.get k with
    | none => rfl
    | some pe =>
      simp only [Bool.or_eq_true]
      cases hopt : pe.optional with
      | true => exact Or.inl rfl
      | false =>
        right
        cases hcg : c.get k with
        | none =>
          have ho := hOmit _ (mem_of_get hpg)
          simp [hcg, hopt] at ho
        | some ce =>
          have hmem := mem_of_get hcg
          have hr := hReq _ hmem
          have hn := hNamed _ hmem
          simp only [hpg, hopt, Bool.false_or, Bool.not_eq_true'] at hr
          simp only [hcg, hr, Bool.false_or] at hn
          exact hn

/-! ## 4. Ловушки (ядро, `decide +kernel`) -/

def wc : Entry := { c := .wildcard }
def exA : Entry := { c := .exact (.str "a") }
def r100 : Entry := { c := .range none (some ⟨100, true⟩) }
def r100opt : Entry := { r100 with optional := true }

-- денотация (6b)
-- пустая карта после нормализации допускает любые аргументы
example : permitsArgs (CMap.norm ⟨[], false⟩) [("x", .num 1)] = true := by decide +kernel
-- закрытый мир: неназванный аргумент без "*" — отказ
example : permitsArgs ⟨[("path", exA)], false⟩ [("path", .str "a"), ("x", .num 1)] = false := by
  decide +kernel
-- "*" допускает неназванный аргумент
example : permitsArgs ⟨[("path", exA)], true⟩ [("path", .str "a"), ("x", .num 1)] = true := by
  decide +kernel
-- обязательный аргумент отсутствует — отказ; необязательный — можно опустить
example : permitsArgs ⟨[("path", exA)], false⟩ [] = false := by decide +kernel
example : permitsArgs ⟨[("limit", r100opt)], false⟩ [] = true := by decide +kernel
-- необязательный, но присутствует — обязан удовлетворять ограничению
example : permitsArgs ⟨[("limit", r100opt)], false⟩ [("limit", .num 500)] = false := by
  decide +kernel
-- значение нарушает ограничение
example : permitsArgs ⟨[("path", exA)], false⟩ [("path", .str "b")] = false := by decide +kernel

-- структурные правила (4p2–4p4)
-- сужение значения: ok
example : narrowsMapB ⟨[("path", wc)], false⟩ ⟨[("path", exA)], false⟩ = true := by decide +kernel
-- ребёнок называет ключ, которого нет у родителя без "*" — отказ
example : narrowsMapB ⟨[("path", wc)], false⟩ ⟨[("path", wc), ("x", wc)], false⟩ = false := by
  decide +kernel
-- …а при "*" у родителя — можно
example : narrowsMapB ⟨[("path", wc)], true⟩ ⟨[("path", wc), ("x", exA)], true⟩ = true := by
  decide +kernel
-- ребёнок опускает обязательный ключ родителя — отказ
example : narrowsMapB ⟨[("path", exA)], false⟩ ⟨[], false⟩ = false := by decide +kernel
-- опускает необязательный (без "*") — можно: аргумент становится запрещённым
example : narrowsMapB ⟨[("limit", r100opt)], false⟩ ⟨[], false⟩ = true := by decide +kernel
-- опускает необязательный, но держит "*" — отказ (аргумент вернулся бы через "*")
example : narrowsMapB ⟨[("limit", r100opt)], true⟩ ⟨[], true⟩ = false := by decide +kernel
-- добавляет "*", которого нет у родителя — отказ
example : narrowsMapB ⟨[("path", wc)], false⟩ ⟨[("path", wc)], true⟩ = false := by decide +kernel
-- обязательный → необязательный — отказ; необязательный → обязательный — можно
example : narrowsMapB ⟨[("limit", r100)], false⟩ ⟨[("limit", r100opt)], false⟩ = false := by
  decide +kernel
example : narrowsMapB ⟨[("limit", r100opt)], false⟩ ⟨[("limit", r100)], false⟩ = true := by
  decide +kernel
-- ограничение ребёнка шире — отказ (4p4)
example : narrowsMapB ⟨[("path", exA)], false⟩ ⟨[("path", wc)], false⟩ = false := by decide +kernel
-- ключ под "*" родителя: ограничить можно (wildcard подчиняет всё)
example : narrowsMapB ⟨[], true⟩ ⟨[("x", exA)], false⟩ = true := by decide +kernel

end AAT
