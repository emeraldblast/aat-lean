import AatLean.Verify

/-!
# Вызов целиком: `aud` (шаг 6c, Т8) и proof of possession (шаг 7, Т9)

`invoke` — шаги 1–7h, чистая функция. Состояние σ — принятые PoP `jti`
(шаг 7i) — «outside the inputs of this algorithm» (§8), поэтому оно в обёртке
`invokeWithState`, которая возвращает вердикт и новое состояние.

Вне модели: допустимость чисел в `hta` (допущение 6). Заголовок PoP (7a) и
разбор PoP JWT (7b–7c) — `Parse.lean`.
-/

namespace AAT

/-- Конфигурация точки проверки для шагов 6c и 7. -/
structure Endpoint where
  /-- Идентификатор этой точки проверки (`aud`, `aat_aud`). -/
  audience        : String
  /-- Окно `iat` PoP, секунды в обе стороны (§9.9). -/
  popWindow       : Int
  /-- «requires chain audience restriction» (6c, §9.5). -/
  requireChainAud : Bool
  /-- «requires PoP audience binding» (7d, §9.5). -/
  requirePopAud   : Bool
  /-- Выданный и ещё принимаемый nonce, если точка его требует (7h). -/
  nonce           : Option String
  /-- Отслеживает ли точка PoP `jti` (7i). -/
  trackJti        : Bool

/-- PoP JWT (§7.2). -/
structure PoP where
  jti     : String
  aatId   : String
  aatHash : String
  aatTool : String
  iat     : Int
  /-- `hta`: аргументы вызова; `none` — отсутствует или не объект. -/
  hta     : Option Args
  /-- `aat_aud`: `none` — отсутствует; не строка — `some ""`. -/
  aatAud  : Option String
  nonce   : Option String
  /-- Ключи, под которыми подпись PoP верна (допущение 1). -/
  sigBy   : List Key

/-! ## Шаги 6c и 7 -/

/-- Шаг 6c: каждый `aud` в цепочке называет эту точку; если точка требует
    ограничения аудитории — хотя бы один токен его несёт. -/
def audOk (E : Endpoint) (c : List Link) : Bool :=
  c.all (fun l => l.aud.all (·.contains E.audience)) &&
  (!E.requireChainAud || c.any (·.aud.isSome))

/-- Шаг 7f: `hta` совпадает с аргументами вызова как JCS-объект (одинаковые
    пары ключ–значение; дубликатов нет — 6b и разбор). -/
def htaEq (hta args : Args) : Bool :=
  hta.length == args.length && hta.all args.contains

/-- Шаги 7b–7h для листа и вызова. -/
def popOk (E : Endpoint) (now : Int) (leaf : Link) (call : Call) (pop : PoP) : Bool :=
  pop.sigBy.contains leaf.holder &&                                   -- 7b (I6)
  !pop.jti.isEmpty && !pop.aatId.isEmpty && !pop.aatHash.isEmpty &&    -- 7c
  !pop.aatTool.isEmpty &&
  pop.aatId == leaf.jti && pop.aatHash == leaf.selfHash &&             -- 7c
  (match pop.aatAud with                                              -- 7d
   | some a => a == E.audience
   | none   => !E.requirePopAud) &&
  pop.aatTool == call.tool &&                                         -- 7e
  (match pop.hta with                                                 -- 7c, 7f
   | some h => htaEq h call.args
   | none   => false) &&
  decide (now - E.popWindow ≤ pop.iat) && decide (pop.iat ≤ now + E.popWindow) && -- 7g
  (match E.nonce with                                                 -- 7h
   | some n => pop.nonce == some n
   | none   => true)

/-- Шаги 1–7h. -/
def invoke (P : Params) (E : Endpoint) (anchors : List Anchor) (chain : List Link)
    (call : Call) (pop : PoP) : Decision :=
  match authorize P anchors chain call, chain.getLast? with
  | .allow, some leaf => if audOk E chain && popOk E P.now leaf call pop then .allow else .deny
  | _, _ => .deny

/-- Шаг 7i с состоянием: PoP `jti` не встречался; запись — только после того,
    как прошли все остальные проверки. -/
def invokeWithState (P : Params) (E : Endpoint) (anchors : List Anchor) (chain : List Link)
    (call : Call) (pop : PoP) (seen : List String) : Decision × List String :=
  match invoke P E anchors chain call pop with
  | .deny  => (.deny, seen)
  | .allow =>
    if E.trackJti then
      if seen.contains pop.jti then (.deny, seen) else (.allow, pop.jti :: seen)
    else (.allow, seen)

/-! ## Соответствие и теоремы -/

theorem invoke_allow_iff (P : Params) (E : Endpoint) (anchors : List Anchor) (c : List Link)
    (call : Call) (pop : PoP) :
    invoke P E anchors c call pop = .allow ↔
      authorize P anchors c call = .allow ∧ audOk E c = true ∧
      ∃ leaf, c.getLast? = some leaf ∧ popOk E P.now leaf call pop = true := by
  unfold invoke
  cases ha : authorize P anchors c call <;> cases hl : c.getLast? <;> simp

/-- Разрешённый вызов прошёл `authorize`: на него распространяются Т1 и Т2. -/
theorem invoke_authorizes {P : Params} {E : Endpoint} {anchors : List Anchor} {c : List Link}
    {call : Call} {pop : PoP} (h : invoke P E anchors c call pop = .allow) :
    authorize P anchors c call = .allow :=
  ((invoke_allow_iff P E anchors c call pop).mp h).1

/-- **Т8.** Каждый `aud` в цепочке разрешённого вызова называет эту точку
    проверки; если точка требует ограничения аудитории, хотя бы один токен его
    несёт. Производный токен может добавить или сузить `aud`, но не снять
    (§3.2). -/
theorem t8_aud {P : Params} {E : Endpoint} {anchors : List Anchor} {c : List Link}
    {call : Call} {pop : PoP} (h : invoke P E anchors c call pop = .allow) :
    (∀ l ∈ c, ∀ auds, l.aud = some auds → E.audience ∈ auds) ∧
    (E.requireChainAud = true → ∃ l ∈ c, l.aud.isSome) := by
  have ha := ((invoke_allow_iff P E anchors c call pop).mp h).2.1
  simp only [audOk, Bool.and_eq_true, List.all_eq_true, Bool.or_eq_true, Bool.not_eq_true',
    List.any_eq_true] at ha
  refine ⟨fun l hl auds hauds => ?_, fun hr => ?_⟩
  · have := ha.1 l hl
    simp only [hauds, Option.all_some, List.contains_iff_mem] at this
    exact this
  · rcases ha.2 with h' | h'
    · simp [hr] at h'
    · exact h'

/-- **Т9.** PoP разрешённого вызова подписан ключом держателя листа, называет
    именно этот лист (его `jti` и хэш, то есть через `par_hash` — всю цепочку
    выше, I5), именно этот инструмент и именно эти аргументы, и выпущен в
    пределах окна. -/
theorem t9_pop {P : Params} {E : Endpoint} {anchors : List Anchor} {c : List Link}
    {call : Call} {pop : PoP} (h : invoke P E anchors c call pop = .allow) :
    ∃ leaf, c.getLast? = some leaf ∧
      leaf.holder ∈ pop.sigBy ∧ pop.aatId = leaf.jti ∧ pop.aatHash = leaf.selfHash ∧
      pop.aatTool = call.tool ∧ (∃ hta, pop.hta = some hta ∧ htaEq hta call.args = true) ∧
      P.now - E.popWindow ≤ pop.iat ∧ pop.iat ≤ P.now + E.popWindow := by
  obtain ⟨_, _, leaf, hl, hp⟩ := (invoke_allow_iff P E anchors c call pop).mp h
  refine ⟨leaf, hl, ?_⟩
  simp only [popOk, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq, List.contains_iff_mem] at hp
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨hs, _⟩, _⟩, _⟩, _⟩, hid⟩, hhash⟩, _⟩, htool⟩, hhta⟩, hlo⟩, hhi⟩, _⟩ := hp
  refine ⟨hs, hid, hhash, htool, ?_, hlo, hhi⟩
  cases hh : pop.hta with
  | none => simp [hh] at hhta
  | some h => exact ⟨h, rfl, by simpa [hh] using hhta⟩

/-- **Т9′ (повтор).** Если точка отслеживает PoP `jti`, тот же PoP, принятый
    один раз, во второй раз отклоняется. -/
theorem t9_replay (P : Params) (E : Endpoint) (anchors : List Anchor) (c : List Link)
    (call : Call) (pop : PoP) (seen : List String) (ht : E.trackJti = true)
    (h1 : (invokeWithState P E anchors c call pop seen).1 = .allow) :
    (invokeWithState P E anchors c call pop (invokeWithState P E anchors c call pop seen).2).1
      = .deny := by
  unfold invokeWithState at h1 ⊢
  cases hi : invoke P E anchors c call pop with
  | deny => simp
  | allow =>
    simp only [hi, ht, ite_true] at h1 ⊢
    by_cases hs : pop.jti ∈ seen
    · simp [hs] at h1
    · simp [hs]

/-! ## Ловушки -/

def ET : Endpoint := ⟨"ep", 30, false, false, none, false⟩

/-- Корректный PoP для листа цепочки `mk ls` и вызова. -/
def popFor (ls : List Link) (call : Call) : PoP :=
  let c := mk ls
  match c.getLast? with
  | some leaf => ⟨"p1", leaf.jti, leaf.selfHash, call.tool, 50, some call.args, some "ep", none,
                  [leaf.holder]⟩
  | none => ⟨"", "", "", "", 0, none, none, none, []⟩

def chainT : List Link := [{ human with tools := [payCap 1000] }, { aToB with tools := [payCap 100] }]
def callT : Call := payReq 50
def popT : PoP := popFor chainT callT

example : invoke PT ET anchorsT (mk chainT) callT popT = .allow := by decide +kernel
-- 7b: PoP подписан не ключом листа
example : invoke PT ET anchorsT (mk chainT) callT { popT with sigBy := ["attacker"] } = .deny := by
  decide +kernel
-- 7c: PoP для другого листа (jti, хэш)
example : invoke PT ET anchorsT (mk chainT) callT { popT with aatId := "j0" } = .deny := by decide +kernel
example : invoke PT ET anchorsT (mk chainT) callT { popT with aatHash := "h0" } = .deny := by decide +kernel
example : invoke PT ET anchorsT (mk chainT) callT { popT with jti := "" } = .deny := by decide +kernel
-- 7d: aat_aud — другая точка; отсутствует при требовании
example : invoke PT ET anchorsT (mk chainT) callT { popT with aatAud := some "other" } = .deny := by
  decide +kernel
example : invoke PT { ET with requirePopAud := true } anchorsT (mk chainT) callT
    { popT with aatAud := none } = .deny := by decide +kernel
example : invoke PT ET anchorsT (mk chainT) callT { popT with aatAud := none } = .allow := by
  decide +kernel
-- 7e: другой инструмент
example : invoke PT ET anchorsT (mk chainT) callT { popT with aatTool := "email" } = .deny := by
  decide +kernel
-- 7f: hta — другие аргументы; отсутствует
example : invoke PT ET anchorsT (mk chainT) callT { popT with hta := some [("amount", .num 51)] }
    = .deny := by decide +kernel
example : invoke PT ET anchorsT (mk chainT) callT { popT with hta := none } = .deny := by decide +kernel
example : invoke PT ET anchorsT (mk chainT) callT { popT with hta := some [] } = .deny := by decide +kernel
-- 7g: iat вне окна с обеих сторон, граница включена
example : invoke PT ET anchorsT (mk chainT) callT { popT with iat := 81 } = .deny := by decide +kernel
example : invoke PT ET anchorsT (mk chainT) callT { popT with iat := 19 } = .deny := by decide +kernel
example : invoke PT ET anchorsT (mk chainT) callT { popT with iat := 80 } = .allow := by decide +kernel
example : invoke PT ET anchorsT (mk chainT) callT { popT with iat := 20 } = .allow := by decide +kernel
-- 7h: nonce требуется
example : invoke PT { ET with nonce := some "n1" } anchorsT (mk chainT) callT popT = .deny := by
  decide +kernel
example : invoke PT { ET with nonce := some "n1" } anchorsT (mk chainT) callT
    { popT with nonce := some "n1" } = .allow := by decide +kernel
example : invoke PT { ET with nonce := some "n1" } anchorsT (mk chainT) callT
    { popT with nonce := some "n2" } = .deny := by decide +kernel
-- 6c: aud звена — другая точка; требование аудитории без aud
example : invoke PT ET anchorsT (upd (mk chainT) 1 ({ · with aud := some ["other"] })) callT popT
    = .deny := by decide +kernel
example : invoke PT ET anchorsT (upd (mk chainT) 1 ({ · with aud := some ["other", "ep"] })) callT popT
    = .allow := by decide +kernel
example : invoke PT ET anchorsT (upd (mk chainT) 0 ({ · with aud := some [] })) callT popT
    = .deny := by decide +kernel
example : invoke PT { ET with requireChainAud := true } anchorsT (mk chainT) callT popT = .deny := by
  decide +kernel
-- отвергнутая цепочка или вызов не спасаются верным PoP
example : invoke PT ET anchorsT (mk chainT) (payReq 500) (popFor chainT (payReq 500)) = .deny := by
  decide +kernel
-- 7i: повтор PoP jti
def ETt : Endpoint := { ET with trackJti := true }
example : invokeWithState PT ETt anchorsT (mk chainT) callT popT [] = (.allow, ["p1"]) := by
  decide +kernel
example : (invokeWithState PT ETt anchorsT (mk chainT) callT popT ["p1"]).1 = .deny := by
  decide +kernel
-- отклонённый вызов не записывается в состояние
example : invokeWithState PT ETt anchorsT (mk chainT) callT { popT with iat := 0 } [] = (.deny, []) := by
  decide +kernel

end AAT
