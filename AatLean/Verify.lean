import AatLean.Chain

/-!
# Алгоритм проверки цепочки AAT-02 §8 (в объёме модели) и теоремы Т1–Т7

Входы — как в §8: параметры точки проверки (`now` — окружение спецификации,
явный параметр ради чистоты функции), доверенные якоря `(issuer, key)`,
цепочка; для `authorize` — ещё вызов. Состояние σ (nonce, PoP `jti`), PoP JWT
и `aud` — позже (Т8, Т9).

Смоделированные шаги: 1, 2c, 3b–3n, 4b–4q, 5, 6b. Размеры и заголовки
(2a, 2b, 3a, 4a, 7a) и разбор claims (3b, 3j, 3l, 3m, 4b1–4b5, 4n: типы,
наличие, форма) — `Parse.lean`; здесь — проверки над разобранными звеньями.
-/

namespace AAT

/-- Параметры точки проверки (§4.3, §4.4). -/
structure Params where
  now                : Int
  maxIatSkew         : Int
  maxTokenLifetime   : Int
  maxDelegationDepth : Nat
  maxConstraintDepth : Nat
  /-- `MAX_TOKEN_SIZE`, `MAX_CHAIN_SIZE` (§4.3, шаги 2a, 2b) — байты. -/
  maxTokenSize       : Nat
  maxChainSize       : Nat
deriving Repr

/-- Доверенный якорь: издатель и ключ (отпечаток), §8 Inputs. -/
structure Anchor where
  iss : Key
  key : Key
deriving Repr

/-! ## Шаги §8 -/

/-- Шаг 3: корень. -/
def rootOk (P : Params) (anchors : List Anchor) (r : Link) : Bool :=
  -- 3b + 3k: подпись верна под ключом якоря, и `iss` корня — издатель этого
  -- якоря (прочтение автора для C6: доверие — ключу, 3k проверяет, что корень
  -- называет издателя, для которого этот ключ доверен)
  anchors.any (fun a => a.iss == r.issuer && r.sigBy.contains a.key) &&
  r.delDepth == 0 &&                                    -- 3c
  r.parHash.isNone &&                                   -- 3d
  decide (P.now < r.exp) &&                             -- 3e
  decide (r.iat ≤ P.now + P.maxIatSkew) &&              -- 3f
  decide (r.iat < r.exp) &&                             -- 3g
  decide (r.exp ≤ r.iat + P.maxTokenLifetime) &&        -- 3h
  decide (r.delMaxDepth ≤ P.maxDelegationDepth)         -- 3i

/-- Шаг 4 для пары без шагов 4e и 4f (их избыточность — Т7). -/
def pairCore (P : Params) (p c : Link) : Bool :=
  c.sigBy.contains p.holder &&                          -- 4b: подпись под parent.cnf.jwk
  linkedB p c &&                                        -- 4c (I1)
  c.delDepth == p.delDepth + 1 &&                       -- 4d
  decide (c.delMaxDepth ≤ p.delMaxDepth) &&             -- 4g
  decide (c.exp ≤ p.exp) &&                             -- 4h
  decide (P.now < c.exp) &&                             -- 4i
  decide (p.iat ≤ c.iat) &&                             -- 4j
  decide (c.iat ≤ P.now + P.maxIatSkew) &&              -- 4k
  decide (c.iat < c.exp) &&                             -- 4l
  decide (c.delDepth ≤ c.delMaxDepth) &&                -- 4m
  narrowsB p c &&                                       -- 4p (I4)
  c.parHash == some p.selfHash                          -- 4q (I5)

/-- Шаги 4e и 4f. -/
def pairRedundant (P : Params) (p c : Link) : Bool :=
  decide (c.delDepth ≤ p.delMaxDepth) &&                -- 4e
  decide (c.delDepth ≤ P.maxDelegationDepth)            -- 4f

/-- Шаг 4 для пары целиком. -/
def pairOk (P : Params) (p c : Link) : Bool := pairCore P p c && pairRedundant P p c

/-- Проверка всех соседних пар. -/
def allPairs (f : Link → Link → Bool) : List Link → Bool
  | p :: c :: rest => f p c && allPairs f (c :: rest)
  | _ => true

/-- Шаги 3n и 4o: каждое ограничение в каждой карте звена хорошо
    сформировано и не глубже `MAX_CONSTRAINT_DEPTH`. -/
def mapsWF (P : Params) (l : Link) : Bool :=
  l.tools.all (fun (_, m) => m.named.all (fun (_, e) => wf P.maxConstraintDepth e.c))

/-- Шаги 3n и 4o для всей цепочки. -/
def allWF (P : Params) (c : List Link) : Bool := c.all (mapsWF P)

/-- Шаг 2c: «if any value appears more than once in the presented chain, DENY». -/
def jtiNoDup (c : List Link) : Bool := decide (c.map (·.jti)).Nodup

/-- Шаг 5: `len(chain) = leaf.del_depth + 1`. -/
def step5 (c : List Link) : Bool :=
  match c.getLast? with
  | some leaf => c.length == leaf.delDepth + 1
  | none => false

/-- Шаги 1–5. -/
def verify (P : Params) (anchors : List Anchor) (chain : List Link) : Decision :=
  match chain with
  | [] => .deny                                         -- 1
  | root :: _ =>
    if allWF P chain && jtiNoDup chain && rootOk P anchors root && allPairs (pairOk P) chain &&
      step5 chain
    then .allow else .deny

/-- Те же шаги без 4e, 4f и 5. -/
def verifyCore (P : Params) (anchors : List Anchor) (chain : List Link) : Decision :=
  match chain with
  | [] => .deny
  | root :: _ =>
    if allWF P chain && jtiNoDup chain && rootOk P anchors root && allPairs (pairCore P) chain
    then .allow else .deny

/-- Шаг 3 без 3c. -/
def rootOkNo3c (P : Params) (anchors : List Anchor) (r : Link) : Bool :=
  anchors.any (fun a => a.iss == r.issuer && r.sigBy.contains a.key) &&
  r.parHash.isNone &&
  decide (P.now < r.exp) && decide (r.iat ≤ P.now + P.maxIatSkew) &&
  decide (r.iat < r.exp) && decide (r.exp ≤ r.iat + P.maxTokenLifetime) &&
  decide (r.delMaxDepth ≤ P.maxDelegationDepth)

/-- Шаги 1–5 без 3c. -/
def verifyNo3c (P : Params) (anchors : List Anchor) (chain : List Link) : Decision :=
  match chain with
  | [] => .deny
  | root :: _ =>
    if allWF P chain && jtiNoDup chain && rootOkNo3c P anchors root &&
      allPairs (pairOk P) chain && step5 chain
    then .allow else .deny

/-- Шаг 6b: «If any JSON object in args, as written in the invocation, has
    duplicate member names, DENY» — для имён аргументов верхнего уровня. -/
def argsNoDup (args : Args) : Bool :=
  let ks := args.map (·.1)
  ks.length == ks.eraseDups.length

/-- Шаг 6b поверх шагов 1–5: вызов проверяется против **листа** принятой
    цепочки. -/
def authorize (P : Params) (anchors : List Anchor) (chain : List Link) (call : Call) : Decision :=
  match verify P anchors chain, chain.getLast? with
  | .allow, some leaf => if argsNoDup call.args && permitsB leaf call then .allow else .deny
  | _, _ => .deny

/-! ## Соответствие §8 -/

theorem allPairs_iff (f : Link → Link → Bool) : ∀ (c : List Link),
    allPairs f c = true ↔ ∀ i (h : i + 1 < c.length), f c[i] c[i+1] = true
  | [] => by simp [allPairs]
  | [_] => by simp [allPairs]
  | p :: q :: rest => by
    simp only [allPairs, Bool.and_eq_true, allPairs_iff f (q :: rest)]
    constructor
    · rintro ⟨hn, hrest⟩ i hi
      cases i with
      | zero => exact hn
      | succ j => exact hrest j (by simp at hi ⊢; omega)
    · intro h
      refine ⟨h 0 (by simp), fun j hj => ?_⟩
      exact h (j + 1) (by simp at hj ⊢; omega)

/-- **Соответствие алгоритму §8** (в объёме модели). Оракул для векторов. -/
theorem verify_allow_iff (P : Params) (anchors : List Anchor) (c : List Link) :
    verify P anchors c = .allow ↔
      c ≠ [] ∧ allWF P c = true ∧ jtiNoDup c = true ∧
      (∀ h : 0 < c.length, rootOk P anchors c[0] = true) ∧
      (∀ i (h : i + 1 < c.length), pairOk P c[i] c[i+1] = true) ∧
      step5 c = true := by
  rw [← allPairs_iff]
  cases c with
  | nil => simp [verify]
  | cons r rest =>
    simp only [verify, ne_eq, reduceCtorEq, not_false_eq_true, true_and, List.length_cons,
      List.getElem_cons_zero, Nat.zero_lt_succ, forall_const]
    split <;> simp_all

variable {P : Params} {anchors : List Anchor} {c : List Link}

theorem length_pos_of_allow (hv : verify P anchors c = .allow) : 0 < c.length := by
  have := ((verify_allow_iff P anchors c).mp hv).1
  cases c <;> simp_all

theorem root_of_allow (hv : verify P anchors c = .allow) :
    rootOk P anchors (c[0]'(length_pos_of_allow hv)) = true :=
  ((verify_allow_iff P anchors c).mp hv).2.2.2.1 _

theorem pair_of_allow (hv : verify P anchors c = .allow) (i : Nat) (hi : i + 1 < c.length) :
    pairOk P c[i] c[i+1] = true :=
  ((verify_allow_iff P anchors c).mp hv).2.2.2.2.1 i hi

theorem core_of_allow (hv : verify P anchors c = .allow) (i : Nat) (hi : i + 1 < c.length) :
    pairCore P c[i] c[i+1] = true := by
  have := pair_of_allow hv i hi
  simp only [pairOk, Bool.and_eq_true] at this
  exact this.1

/-- Разворачивает `pairCore` в утверждения о полях. -/
theorem pairCore_spec {p ch : Link} (h : pairCore P p ch = true) :
    p.holder ∈ ch.sigBy ∧ Linked p ch ∧ ch.delDepth = p.delDepth + 1 ∧
    ch.delMaxDepth ≤ p.delMaxDepth ∧ ch.exp ≤ p.exp ∧ P.now < ch.exp ∧ p.iat ≤ ch.iat ∧
    ch.iat ≤ P.now + P.maxIatSkew ∧ ch.iat < ch.exp ∧ ch.delDepth ≤ ch.delMaxDepth ∧
    narrowsB p ch = true ∧ ch.parHash = some p.selfHash := by
  simp only [pairCore, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq, linkedB_iff,
    List.contains_iff_mem] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩, h8⟩, h9⟩, h10⟩, h11⟩, h12⟩ := h
  exact ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12⟩

/-- Разворачивает `rootOk`. -/
theorem rootOk_spec {r : Link} (h : rootOk P anchors r = true) :
    (∃ a ∈ anchors, a.iss = r.issuer ∧ a.key ∈ r.sigBy) ∧ r.delDepth = 0 ∧
    r.parHash = none ∧ P.now < r.exp ∧ r.iat ≤ P.now + P.maxIatSkew ∧ r.iat < r.exp ∧
    r.exp ≤ r.iat + P.maxTokenLifetime ∧ r.delMaxDepth ≤ P.maxDelegationDepth := by
  simp only [rootOk, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq, List.any_eq_true,
    List.contains_iff_mem, Option.isNone_iff_eq_none] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨a, ha, hi, hk⟩, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩, h8⟩ := h
  exact ⟨⟨a, ha, hi, hk⟩, h2, h3, h4, h5, h6, h7, h8⟩

/-- Индукция по позициям цепочки от корня. -/
theorem chain_ind (Q : (j : Nat) → j < c.length → Prop)
    (h0 : ∀ h, Q 0 h) (hs : ∀ i (h : i + 1 < c.length), Q i (by omega) → Q (i + 1) h) :
    ∀ j h, Q j h := by
  intro j
  induction j with
  | zero => exact h0
  | succ k ih => intro h; exact hs k h (ih (by omega))

/-! ## Т1 -/

theorem checkNarrows_of_allow (hv : verify P anchors c = .allow) : checkNarrows c = true :=
  (checkNarrows_iff c).mpr fun i hi => (pairCore_spec (core_of_allow hv i hi)).2.2.2.2.2.2.2.2.2.2.1

/-- **Т1** (утверждённая формулировка; параметры `verify` — по §8). Если
    `verify` принял цепочку, права каждого звена — подмножество прав его
    родителя. Никакого ограничения на длину `c`. Следствие `t1_core`. -/
theorem t1_monotone (P : Params) (anchors : List Anchor) (c : List Link)
    (hv : verify P anchors c = .allow)
    (i : Nat) (hi : i + 1 < c.length) : Narrows c[i] c[i+1] :=
  t1_core c (checkNarrows_of_allow hv) i hi

/-- **Т1′.** Права любого звена принятой цепочки — подмножество прав корня. -/
theorem t1_root_bound (P : Params) (anchors : List Anchor) (c : List Link)
    (hv : verify P anchors c = .allow)
    (j : Nat) (hj : j < c.length) : Narrows (c[0]'(by omega)) c[j] := by
  induction j with
  | zero => intro call h; exact h
  | succ k ih =>
    intro call h
    exact ih (by omega) call (t1_monotone P anchors c hv k hj call h)

/-! ## Т2. Покрытие действия (шаг 6b) -/

theorem authorize_allow_iff (P : Params) (anchors : List Anchor) (c : List Link) (call : Call) :
    authorize P anchors c call = .allow ↔
      verify P anchors c = .allow ∧ argsNoDup call.args = true ∧
      ∃ h : 0 < c.length, Permits (c[c.length - 1]'(by omega)) call := by
  unfold authorize
  cases hv : verify P anchors c with
  | deny => simp
  | allow =>
    have hpos := length_pos_of_allow hv
    rw [List.getLast?_eq_getElem?, List.getElem?_eq_getElem (by omega)]
    simp only [permits_iff, true_and]
    split <;> simp_all

/-- **Т2.** Если вызов разрешён, его допускает каждое звено цепочки. -/
theorem t2_coverage (P : Params) (anchors : List Anchor) (c : List Link) (call : Call)
    (ha : authorize P anchors c call = .allow)
    (j : Nat) (hj : j < c.length) : Permits c[j] call := by
  obtain ⟨hv, _, hpos, hleaf⟩ := (authorize_allow_iff P anchors c call).mp ha
  have key : ∀ d (hd : d < c.length), Permits (c[c.length - 1 - d]'(by omega)) call := by
    intro d
    induction d with
    | zero => intro _; simpa using hleaf
    | succ k ih =>
      intro hd
      have hn := t1_monotone P anchors c hv (c.length - 1 - (k + 1)) (by omega)
      have hidx : c.length - 1 - (k + 1) + 1 = c.length - 1 - k := by omega
      simp only [hidx] at hn
      exact hn call (ih (by omega))
  have := key (c.length - 1 - j) (by omega)
  have hidx : c.length - 1 - (c.length - 1 - j) = j := by omega
  simpa only [hidx] using this

/-! ## Т3. Привязка корня, I1, I5, 2c -/

/-- **Т3.** Подпись корня принятой цепочки верна под ключом доверенного якоря,
    и `iss` корня — издатель этого якоря (шаги 3b, 3k). -/
theorem t3_root (hv : verify P anchors c = .allow) :
    ∃ a ∈ anchors, a.iss = (c[0]'(length_pos_of_allow hv)).issuer ∧
      a.key ∈ (c[0]'(length_pos_of_allow hv)).sigBy :=
  (rootOk_spec (root_of_allow hv)).1

/-- **I1.** Каждое звено ниже корня подписано ключом держателя родителя, и его
    `iss` — отпечаток этого ключа (шаги 4b, 4c). -/
theorem i1_signed (hv : verify P anchors c = .allow) (i : Nat) (hi : i + 1 < c.length) :
    c[i].holder ∈ c[i+1].sigBy ∧ Linked c[i] c[i+1] :=
  let h := pairCore_spec (core_of_allow hv i hi)
  ⟨h.1, h.2.1⟩

/-- **I5.** Каждое звено ниже корня привязано к экземпляру родителя через
    `par_hash` (шаг 4q). С инъективным хэшем (допущение 5) это исключает
    «пересадку» под другого родителя того же держателя. -/
theorem i5_bound (hv : verify P anchors c = .allow) (i : Nat) (hi : i + 1 < c.length) :
    c[i+1].parHash = some c[i].selfHash :=
  (pairCore_spec (core_of_allow hv i hi)).2.2.2.2.2.2.2.2.2.2.2

/-- **2c.** В принятой цепочке нет повторов `jti` (повторного экземпляра
    токена). -/
theorem jti_nodup (hv : verify P anchors c = .allow) : (c.map (·.jti)).Nodup := by
  have := ((verify_allow_iff P anchors c).mp hv).2.2.1
  simpa [jtiNoDup] using this

/-! ## Т6. Глубина (I2) -/

/-- **Т6.** Глубина звена принятой цепочки равна его позиции. -/
theorem t6_depth (hv : verify P anchors c = .allow) :
    ∀ j (hj : j < c.length), c[j].delDepth = j :=
  chain_ind (fun j hj => c[j].delDepth = j)
    (fun _ => (rootOk_spec (root_of_allow hv)).2.1)
    (fun i hi ih => by have := (pairCore_spec (core_of_allow hv i hi)).2.2.1; omega)

/-- **Т6′.** Длина принятой цепочки не больше `MAX_DELEGATION_DEPTH + 1`. -/
theorem t6_length (hv : verify P anchors c = .allow) :
    c.length ≤ P.maxDelegationDepth + 1 := by
  have hpos := length_pos_of_allow hv
  by_cases h1 : c.length = 1
  · omega
  · have hp := pair_of_allow hv (c.length - 2) (by omega)
    simp only [pairOk, pairRedundant, Bool.and_eq_true, decide_eq_true_eq] at hp
    have hd := t6_depth hv (c.length - 2 + 1) (by omega)
    omega

/-! ## Т4. Срок действия (I3) -/

/-- **Т4.** Каждое звено принятой цепочки действительно в момент `now`, не
    переживает корень и выпущено не раньше корня. -/
theorem t4_ttl (hv : verify P anchors c = .allow) :
    ∀ j (hj : j < c.length),
      P.now < c[j].exp ∧ c[j].iat ≤ P.now + P.maxIatSkew ∧ c[j].iat < c[j].exp ∧
      c[j].exp ≤ (c[0]'(length_pos_of_allow hv)).exp ∧
      (c[0]'(length_pos_of_allow hv)).iat ≤ c[j].iat := by
  have hr := rootOk_spec (root_of_allow hv)
  refine chain_ind _ (fun _ => ⟨hr.2.2.2.1, hr.2.2.2.2.1, hr.2.2.2.2.2.1, Int.le_refl _,
    Int.le_refl _⟩) ?_
  intro i hi ih
  have h := pairCore_spec (core_of_allow hv i hi)
  refine ⟨h.2.2.2.2.2.1, h.2.2.2.2.2.2.2.1, h.2.2.2.2.2.2.2.2.1, ?_, ?_⟩
  · exact Int.le_trans h.2.2.2.2.1 ih.2.2.2.1
  · exact Int.le_trans ih.2.2.2.2 h.2.2.2.2.2.2.1

/-! ## Т7. Утверждения «по индукции» из §8 (B9, B10 Давлятшина)

Заметки к §8: «Two requirements hold by induction and need no step of their
own»; шаг 5 — «defense in depth»; отчёт Давлятшина, B9: шаги 4e, 4f и 5
следуют из остальных; B10: предел срока жизни выполняется по индукции.
Автор AAT: «by design». Ниже — механизированные доказательства. -/

/-- Каждый `del_max_depth` ≤ `MAX_DELEGATION_DEPTH` — из 3i и 4g. -/
theorem t7_maxDepth (hc : allPairs (pairCore P) c = true) (h0 : ∀ h : 0 < c.length,
    c[0].delMaxDepth ≤ P.maxDelegationDepth) :
    ∀ j (hj : j < c.length), c[j].delMaxDepth ≤ P.maxDelegationDepth :=
  chain_ind _ h0 fun i hi ih => by
    have := (pairCore_spec ((allPairs_iff _ c).mp hc i hi)).2.2.2.1
    omega

/-- Каждый `exp` ≤ `iat + MAX_TOKEN_LIFETIME` — из 3h, 4h и 4j. -/
theorem t7_lifetime (hc : allPairs (pairCore P) c = true) (h0 : ∀ h : 0 < c.length,
    c[0].exp ≤ c[0].iat + P.maxTokenLifetime) :
    ∀ j (hj : j < c.length), c[j].exp ≤ c[j].iat + P.maxTokenLifetime :=
  chain_ind _ h0 fun i hi ih => by
    have h := pairCore_spec ((allPairs_iff _ c).mp hc i hi)
    have := h.2.2.2.2.1
    have := h.2.2.2.2.2.2.1
    omega

/-- Глубина = позиция — из 3c и 4d. -/
theorem t7_depth (hc : allPairs (pairCore P) c = true) (h0 : ∀ h : 0 < c.length,
    c[0].delDepth = 0) :
    ∀ j (hj : j < c.length), c[j].delDepth = j :=
  chain_ind _ h0 fun i hi ih => by
    have := (pairCore_spec ((allPairs_iff _ c).mp hc i hi)).2.2.1
    omega

/-- **Т7.** Шаги 4e, 4f и 5 не меняют ни одного вердикта: `verify` равна
    проверке без них на всех входах. Поэтому ни один тестовый вектор не может
    проверить их как единственную ошибку (B9). -/
theorem t7_redundant (P : Params) (anchors : List Anchor) (c : List Link) :
    verify P anchors c = verifyCore P anchors c := by
  cases c with
  | nil => rfl
  | cons r rest =>
    simp only [verify, verifyCore]
    by_cases hw : allWF P (r :: rest) = true
    rotate_left
    · simp [hw]
    by_cases hj : jtiNoDup (r :: rest) = true
    · by_cases hr : rootOk P anchors r = true
      · by_cases hp : allPairs (pairCore P) (r :: rest) = true
        · -- ядро прошло: доказываем 4e, 4f и шаг 5
          have hrs := rootOk_spec hr
          have hdepth := t7_depth hp (fun _ => hrs.2.1)
          have hmax := t7_maxDepth hp (fun _ => hrs.2.2.2.2.2.2.2)
          have hall : allPairs (pairOk P) (r :: rest) = true := by
            rw [allPairs_iff]
            intro i hi
            have hc := (allPairs_iff _ _).mp hp i hi
            have h := pairCore_spec hc
            have hmi := hmax i (by omega)
            simp only [pairOk, pairRedundant, hc, Bool.true_and, Bool.and_eq_true,
              decide_eq_true_eq]
            omega
          have h5 : step5 (r :: rest) = true := by
            have hlast := hdepth rest.length (by simp)
            simp only [step5, List.getLast?_eq_getElem?, List.length_cons, Nat.add_sub_cancel]
            rw [List.getElem?_eq_getElem (by simp)]
            simp [hlast]
          simp [hw, hj, hr, hp, hall, h5]
        · -- ядро не прошло: тогда не прошла и полная проверка пар
          have hall : allPairs (pairOk P) (r :: rest) = false := by
            cases h : allPairs (pairOk P) (r :: rest) with
            | false => rfl
            | true =>
              exfalso; apply hp
              rw [allPairs_iff] at h ⊢
              intro i hi
              have := h i hi
              simp only [pairOk, Bool.and_eq_true] at this
              exact this.1
          simp [hw, hj, hr, hp, hall]
      · simp [hr]
    · simp [hj]

/-- Глубина = глубина корня + позиция — из 4d. -/
theorem depth_from_root (hc : allPairs (pairOk P) c = true) :
    ∀ j (hj : j < c.length), c[j].delDepth = (c[0]'(by omega)).delDepth + j :=
  chain_ind _ (fun _ => by simp) fun i hi ih => by
    have hp := (allPairs_iff _ c).mp hc i hi
    simp only [pairOk, Bool.and_eq_true] at hp
    have := (pairCore_spec hp.1).2.2.1
    omega

/-- **Т7′ (новое: обратное направление B9).** Шаг 3c тоже не меняет ни одного
    вердикта: «корень на глубине 0» следует из шага 5 и 4d. Вместе с
    `t7_redundant`: 3c и шаг 5 избыточны взаимно — достаточно любого одного. -/
theorem t7_3c_redundant (P : Params) (anchors : List Anchor) (c : List Link) :
    verify P anchors c = verifyNo3c P anchors c := by
  cases c with
  | nil => rfl
  | cons r rest =>
    simp only [verify, verifyNo3c]
    have hsplit : rootOk P anchors r = (r.delDepth == 0 && rootOkNo3c P anchors r) := by
      simp only [rootOk, rootOkNo3c]
      cases r.delDepth == 0 <;> simp [Bool.and_assoc]
    rw [hsplit]
    cases hw : allWF P (r :: rest) <;> cases hj : jtiNoDup (r :: rest) <;>
      cases hn : rootOkNo3c P anchors r <;>
      cases hp : allPairs (pairOk P) (r :: rest) <;> cases h5 : step5 (r :: rest) <;> simp
    -- всё, кроме 3c, прошло: выводим 3c из шага 5 и 4d
    have hdr := depth_from_root hp rest.length (by simp)
    simp only [step5, List.getLast?_eq_getElem?, List.length_cons, Nat.add_sub_cancel] at h5
    rw [List.getElem?_eq_getElem (by simp)] at h5
    simp only [beq_iff_eq] at h5
    simp only [List.getElem_cons_zero] at hdr
    omega

/-! ## Ловушки (ядро, `decide +kernel`) -/

def PT : Params := ⟨50, 30, 1000, 8, 32, 1000, 1500⟩
def anchorsT : List Anchor := [⟨"root-key", "anchor-key"⟩]

/-- Заполняет поля §3.2 согласованно: глубина = позиция, `par_hash` — хэш
    родителя, подпись — ключом якоря (корень) или держателя родителя. -/
def mkAux : Nat → Option (String × Key) → List Link → List Link
  | _, _, [] => []
  | i, prev, l :: rest =>
    { l with jti := s!"j{i}", delDepth := i, delMaxDepth := 8, iat := 0, exp := 100,
             selfHash := s!"h{i}", parHash := prev.map (·.1),
             sigBy := [(prev.map (·.2)).getD "anchor-key"] } ::
    mkAux (i + 1) (some (s!"h{i}", l.holder)) rest

def mk (ls : List Link) : List Link := mkAux 0 none ls

def l3 : Link := { issuer := "agentB", holder := "agentC", tools := [free "pay"] }
def l4 : Link := { issuer := "agentC", holder := "agentD", tools := [free "pay"] }
def l5 (t : List (Tool × CMap)) : Link := { issuer := "agentD", holder := "agentE", tools := t }

-- сужение (Т1)
example : verify PT anchorsT (mk [human, aToB, { l3 with tools := [] }]) = .allow := by decide +kernel
example : verify PT anchorsT (mk [human, { aToB with tools := [free "pay", free "deploy"] }]) = .deny := by
  decide +kernel
example : verify PT anchorsT (mk [human, aToB, { l3 with tools := [free "email"] }]) = .deny := by
  decide +kernel
example : verify PT anchorsT (mk [human, aToB, l3, l4, l5 []]) = .allow := by decide +kernel
example : verify PT anchorsT (mk [human, aToB, l3, l4, l5 [free "email"]]) = .deny := by decide +kernel
-- середина цепочки
example : verify PT anchorsT (mk [human, aToB, { l3 with tools := [free "pay", free "deploy"] },
    { l4 with tools := [free "pay", free "deploy"] }]) = .deny := by decide +kernel
example : verify PT anchorsT (mk [human, { aToB with tools := [free "deploy"] }]) = .deny := by
  decide +kernel
example : verify PT anchorsT (mk [{ human with tools := [payCap 100] },
    { aToB with tools := [payCap 1000] }]) = .deny := by decide +kernel
-- пустая цепочка
example : verify PT anchorsT [] = .deny := by decide +kernel
-- 4c: издатель ребёнка ≠ держатель родителя
example : verify PT anchorsT (mk [human, { aToB with issuer := "mallory" }]) = .deny := by decide +kernel
example : verify PT anchorsT (mk [human, { aToB with issuer := "root-key" }]) = .deny := by decide +kernel
-- 3k: самозваный корень
example : verify PT anchorsT (mk [{ human with issuer := "mallory-root" }, aToB]) = .deny := by
  decide +kernel

/-- Изменить одно поле одного звена готовой цепочки. -/
def upd (c : List Link) (i : Nat) (f : Link → Link) : List Link := c.modify i f

def good : List Link := mk [human, aToB, l3]

example : verify PT anchorsT good = .allow := by decide +kernel
-- 3b: подпись корня не под ключом якоря
example : verify PT anchorsT (upd good 0 ({ · with sigBy := ["attacker"] })) = .deny := by decide +kernel
-- 4b: подпись ребёнка не под ключом держателя родителя
example : verify PT anchorsT (upd good 1 ({ · with sigBy := ["attacker"] })) = .deny := by decide +kernel
def good1 : List Link := mk [human]
-- 3e, 3f, 3g на цепочке из одного токена (в длинных их перекрывают 4h–4l)
example : verify { PT with now := 100 } anchorsT good1 = .deny := by decide +kernel
example : verify { PT with now := -40 } anchorsT good1 = .deny := by decide +kernel
example : verify PT anchorsT (upd good1 0 ({ · with iat := 60, exp := 60 })) = .deny := by decide +kernel
-- 4d на звене в середине (на листе её перекрывает шаг 5)
example : verify PT anchorsT (upd good 1 ({ · with delDepth := 5 })) = .deny := by decide +kernel
-- 4k: ребёнок выпущен в будущем, остальное в порядке
example : verify PT anchorsT (upd good 2 ({ · with iat := 90 })) = .deny := by decide +kernel
-- 4l: exp ≤ iat у ребёнка, остальное в порядке
example : verify PT anchorsT (upd good 2 ({ · with iat := 60, exp := 60 })) = .deny := by decide +kernel
-- 3c: корень не на глубине 0; 3d: у корня есть par_hash
example : verify PT anchorsT (upd good 0 ({ · with delDepth := 1 })) = .deny := by decide +kernel
example : verify PT anchorsT (upd good 0 ({ · with parHash := some "x" })) = .deny := by decide +kernel
-- 4d: глубина ребёнка не на 1 больше
example : verify PT anchorsT (upd good 2 ({ · with delDepth := 3 })) = .deny := by decide +kernel
-- 4g: ребёнок поднял del_max_depth
example : verify PT anchorsT (upd good 1 ({ · with delMaxDepth := 9 })) = .deny := by decide +kernel
-- 4m: глубина ребёнка больше его del_max_depth
example : verify PT anchorsT (upd (upd good 2 ({ · with delMaxDepth := 1 })) 2 id) = .deny := by
  decide +kernel
-- 3i: del_max_depth корня больше MAX
example : verify { PT with maxDelegationDepth := 7 } anchorsT good = .deny := by decide +kernel
-- 3e/4i: истёк
example : verify { PT with now := 100 } anchorsT good = .deny := by decide +kernel
example : verify PT anchorsT (upd good 2 ({ · with exp := 40 })) = .deny := by decide +kernel
-- 4h: ребёнок переживает родителя
example : verify PT anchorsT (upd good 1 ({ · with exp := 200 })) = .deny := by decide +kernel
-- 4j: ребёнок выпущен раньше родителя
example : verify PT anchorsT (upd good 1 ({ · with iat := -1 })) = .deny := by decide +kernel
-- 3f/4k: выпущен в будущем сверх допуска
example : verify { PT with now := -40 } anchorsT good = .deny := by decide +kernel
-- 3g/4l: exp ≤ iat
example : verify PT anchorsT (upd good 2 ({ · with iat := 100 })) = .deny := by decide +kernel
-- 3h: срок жизни корня больше MAX_TOKEN_LIFETIME
example : verify { PT with maxTokenLifetime := 99 } anchorsT good = .deny := by decide +kernel
-- 4q: par_hash не равен хэшу родителя
example : verify PT anchorsT (upd good 2 ({ · with parHash := some "h0" })) = .deny := by decide +kernel
-- 2c: повтор jti
example : verify PT anchorsT (upd good 2 ({ · with jti := "j0" })) = .deny := by decide +kernel

-- 3n/4o: плохо сформированное ограничение у корня / у ребёнка
def badMap : Tool × CMap := ("pay", ⟨[("amount", { c := .oneOf [] })], false⟩)
example : verify PT anchorsT (mk [{ human with tools := [badMap] }]) = .deny := by decide +kernel
example : verify PT anchorsT (mk [human, { aToB with tools := [badMap] }]) = .deny := by decide +kernel
-- глубина ограничения сверх MAX_CONSTRAINT_DEPTH
def deepMap : Tool × CMap := ("pay", ⟨[("amount", { c := .all [.all [.wildcard]] })], false⟩)
example : verify { PT with maxConstraintDepth := 2 } anchorsT (mk [{ human with tools := [deepMap] }])
    = .deny := by decide +kernel
example : verify PT anchorsT (mk [{ human with tools := [deepMap] }]) = .allow := by decide +kernel

-- шаг 6b: вызов против листа
def payReq (n : Rat) : Call := ⟨"pay", [("amount", .num n)]⟩
example : authorize PT anchorsT (mk [{ human with tools := [payCap 1000] },
    { aToB with tools := [payCap 100] }]) (payReq 50) = .allow := by decide +kernel
example : authorize PT anchorsT (mk [{ human with tools := [payCap 1000] },
    { aToB with tools := [payCap 100] }]) (payReq 500) = .deny := by decide +kernel
example : authorize PT anchorsT (mk [human, aToB]) ⟨"email", []⟩ = .deny := by decide +kernel
example : authorize PT anchorsT (mk [{ human with tools := [payCap 1000] }]) ⟨"pay", []⟩ = .deny := by
  decide +kernel
example : authorize PT anchorsT (mk [{ human with tools := [payCap 1000] }])
    ⟨"pay", [("amount", .num 1), ("memo", .str "x")]⟩ = .deny := by decide +kernel
example : authorize PT anchorsT (mk [human, aToB])
    ⟨"pay", [("amount", .num 1), ("amount", .num 2)]⟩ = .deny := by decide +kernel
example : authorize PT anchorsT (mk [{ human with tools := [payCap 100] },
    { aToB with tools := [payCap 1000] }]) (payReq 50) = .deny := by decide +kernel

/-- Общая ловушка: если на любом звене есть вызов, который ребёнку разрешён,
    а родителю нет, `verify` отклоняет — при любой длине. -/
theorem widening_rejected (P : Params) (anchors : List Anchor) (c : List Link)
    (i : Nat) (hi : i + 1 < c.length)
    (call : Call) (hc : Permits c[i+1] call) (hp : ¬ Permits c[i] call) :
    verify P anchors c = .deny := by
  cases h : verify P anchors c with
  | deny => rfl
  | allow => exact absurd (t1_monotone P anchors c h i hi call hc) hp

/-- **Свидетель неполноты на уровне цепочки** (§4.1, B1 Давлятшина): ребёнок
    по смыслу уже родителя, но `verify` отклоняет. -/
theorem incompleteness_witness :
    let p : Link := { human with tools := [("pay", ⟨[("amount", { c := r0to10 })], false⟩)] }
    let c : Link := { aToB with tools := [("pay", ⟨[("amount", { c := oneOf12 })], false⟩)] }
    Narrows p c ∧ verify PT anchorsT (mk [p, c]) = .deny := by
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
