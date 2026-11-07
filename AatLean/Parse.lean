import AatLean.Invoke

/-!
# Разбор claims токенов и PoP (шаги 3b–3m, 4b–4n, 7b–7c)

Модель получает подписанную часть каждого JWS как дерево JSON (`JVal`) — с
повторами имён и числами в виде литералов, как они записаны, — и сама
выполняет шаги разбора §8:

- 3b, 4b, 7b — «rejecting any JSON object with duplicate member names» (на
  любой глубине);
- 3b, 4b5, 7c — `iat`/`exp` — NumericDate: число без дроби и экспоненты (§3.2);
- 3c, 3i, 4b4 — `del_depth`, `del_max_depth` — целые, неотрицательные;
- 3j, 4b1 (и 2c) — `jti` — непустая строка;
- 3k, 4b5 — `iss` — строка; 4b5 — `par_hash` у производного — строка;
- 3l, 4b2 — `cnf.jwk` — открытый ключ Ed25519 (прочтение ниже);
- 3m, 4b3, 4n — `authorization_details`: массив ровно с одной записью типа
  `attenuating_agent_token`, `tools` — объект, значения которого — объекты.

Остаётся снаружи (декодер, допущения 1, 5, 6): подпись (`sigBy`), SHA-256
signing input (`selfHash`), отпечаток `cnf.jwk` (`thumb`), содержимое карт
ограничений (`maps`, второй этап) и значения аргументов `hta` (JCS).

**Прочтение 3l/4b2.** Точка проверки разрешает только Ed25519 (как в наборе
векторов, §3.2: «MUST support Ed25519»): `jwk` «encodes a public key», если
`kty = "OKP"`, `crv = "Ed25519"`, `x` — base64url без дополнения длины 43
(32 байта) и нет закрытого параметра `d`.

`verify` и теоремы Т1–Т9 не меняются: `invokeTokens` — разбор, затем
`invokeWithState`; `invokeTokens_allow` переносит все теоремы на разобранную
цепочку.
-/

namespace AAT

/-- JSON-значение как записано: объект — список пар (повторы видны), число —
    литерал. -/
inductive JVal where
  | null
  | bool (b : Bool)
  | num (lit : String)
  | str (s : String)
  | arr (xs : List JVal)
  | obj (kvs : List (String × JVal))
deriving Repr, Inhabited

mutual
/-- Ни в одном объекте на любой глубине нет повторяющихся имён. -/
def JVal.noDup : JVal → Bool
  | .arr xs => JVal.noDupList xs
  | .obj kvs => decide (kvs.map (·.1)).Nodup && JVal.noDupObj kvs
  | _ => true
def JVal.noDupList : List JVal → Bool
  | [] => true
  | x :: xs => x.noDup && JVal.noDupList xs
def JVal.noDupObj : List (String × JVal) → Bool
  | [] => true
  | (_, v) :: kvs => v.noDup && JVal.noDupObj kvs
end

/-- Член объекта по имени (`none` — нет или не объект). -/
def JVal.field (v : JVal) (k : String) : Option JVal :=
  match v with
  | .obj kvs => (kvs.find? (·.1 == k)).map (·.2)
  | _ => none

def JVal.asStr : JVal → Option String
  | .str s => some s
  | _ => none

def JVal.isObj : JVal → Bool
  | .obj _ => true
  | _ => false

/-- Цифры десятичного литерала; `none` — пусто или не цифра. -/
def digitsVal : List Char → Option Nat → Option Nat
  | [], acc => acc
  | c :: cs, acc =>
    if c.isDigit then digitsVal cs (some (acc.getD 0 * 10 + (c.toNat - '0'.toNat))) else none

/-- Целый литерал JSON без дроби и экспоненты (§3.2); иначе `none`. -/
def intLit (s : String) : Option Int :=
  match s.toList with
  | '-' :: cs => (digitsVal cs none).map (fun n => -(n : Int))
  | cs => (digitsVal cs none).map (fun n => (n : Int))

def JVal.asInt : JVal → Option Int
  | .num l => intLit l
  | _ => none

def JVal.asNat (v : JVal) : Option Nat :=
  v.asInt.bind fun i => if 0 ≤ i then some i.toNat else none

/-- Непустая строка (3j, 4b1). -/
def JVal.asNonEmpty (v : JVal) : Option String :=
  v.asStr.bind fun s => if s.isEmpty then none else some s

/-- Символ base64url. -/
def b64uChar (c : Char) : Bool := c.isAlphanum || c == '-' || c == '_'

/-- 3l, 4b2: `jwk` — открытый ключ Ed25519 (прочтение в шапке модуля). -/
def jwkOk (j : JVal) : Bool :=
  (j.field "kty" >>= JVal.asStr) == some "OKP" &&
  (j.field "crv" >>= JVal.asStr) == some "Ed25519" &&
  (match j.field "x" >>= JVal.asStr with
   | some x => x.length == 43 && x.toList.all b64uChar
   | none => false) &&
  (j.field "d").isNone

/-- 3m, 4b3, 4n: имена инструментов единственной записи AAT. -/
def aatTools (ad : JVal) : Option (List Tool) :=
  match ad with
  | .arr xs =>
    match xs.filter (fun e => (e.field "type" >>= JVal.asStr) == some "attenuating_agent_token") with
    | [e] =>
      match e.field "tools" with
      | some (.obj kvs) => if kvs.all (fun (_, m) => m.isObj) then some (kvs.map (·.1)) else none
      | _ => none
    | _ => none
  | _ => none

/-- `aud` (§3.2): строка — одно значение; массив строк — значения; иначе
    `some []` (шаг 6c отклоняет). -/
def audOf : Option JVal → Option (List String)
  | none => none
  | some (.str s) => some [s]
  | some (.arr xs) => some ((xs.mapM JVal.asStr).getD [])
  | some _ => some []

/-- Токен цепочки, как его видит модель. -/
structure RawToken where
  payload  : JVal
  /-- `jwk_thumbprint_uri(cnf.jwk)` (допущение 5); `none` — не вычислим. -/
  thumb    : Option Key
  selfHash : String
  sigBy    : List Key
  /-- Карты ограничений по имени инструмента (разбор ограничений — снаружи). -/
  maps     : List (Tool × CMap)

/-- Разбор одного токена (`isRoot` — корень: шаги 3; иначе 4b, 4n). -/
def parseLink (isRoot : Bool) (t : RawToken) : Option Link := do
  let p := t.payload
  guard p.noDup                                                      -- 3b, 4b
  let jti ← p.field "jti" >>= JVal.asNonEmpty                        -- 3j, 4b1
  let jwk ← p.field "cnf" >>= (·.field "jwk")                        -- 3l, 4b2
  guard (jwkOk jwk)
  let holder ← t.thumb
  let names ← p.field "authorization_details" >>= aatTools           -- 3m, 4b3, 4n
  let tools ← names.mapM (fun n => (t.maps.lookup n).map (n, ·))
  let dd ← p.field "del_depth" >>= JVal.asNat                        -- 3c, 4b4
  let dmd ← p.field "del_max_depth" >>= JVal.asNat                   -- 3i, 4b4
  let iss ← p.field "iss" >>= JVal.asStr                             -- 3k, 4b5
  let iat ← p.field "iat" >>= JVal.asInt                             -- 3b, 4b5
  let exp ← p.field "exp" >>= JVal.asInt                             -- 3b, 4b5
  let parHash ←
    if isRoot then
      -- 3d проверяет отсутствие; не строка — тоже «присутствует»
      pure ((p.field "par_hash").map (fun v => v.asStr.getD ""))
    else (p.field "par_hash" >>= JVal.asStr).map some                -- 4b5
  pure { issuer := iss, holder, tools, jti, delDepth := dd, delMaxDepth := dmd, iat, exp, parHash,
         selfHash := t.selfHash, sigBy := t.sigBy, aud := audOf (p.field "aud") }

/-- Разбор цепочки: корень, затем производные. -/
def parseChain : List RawToken → Option (List Link)
  | [] => some []
  | r :: rest => do
    let l ← parseLink true r
    let ls ← rest.mapM (parseLink false)
    pure (l :: ls)

/-- PoP JWT, как его видит модель. -/
structure RawPoP where
  payload : JVal
  sigBy   : List Key
  /-- `hta` как аргументы (значения по JCS — снаружи, допущение 6). -/
  hta     : Option Args

/-- Шаги 7b–7c (разбор). Отсутствующие строковые члены — `""`: `popOk`
    отвергает пустые. -/
def parsePoP (q : RawPoP) : Option PoP := do
  let p := q.payload
  guard p.noDup                                                      -- 7b
  let iat ← p.field "iat" >>= JVal.asInt                             -- 7c
  let s := fun k => (p.field k >>= JVal.asStr).getD ""
  let opt := fun k => (p.field k).map (fun v => v.asStr.getD "")
  let hta := match p.field "hta" with
    | some (.obj _) => q.hta
    | _ => none
  pure { jti := s "jti", aatId := s "aat_id", aatHash := s "aat_hash", aatTool := s "aat_tool",
         iat, hta, aatAud := opt "aat_aud", nonce := opt "nonce", sigBy := q.sigBy }

/-- Шаги 1–7i на токенах как они записаны: разбор, затем `invokeWithState`.
    Ошибка разбора — DENY, состояние не меняется. -/
def invokeTokens (P : Params) (E : Endpoint) (anchors : List Anchor) (raw : List RawToken)
    (call : Call) (rp : RawPoP) (seen : List String) : Decision × List String :=
  match parseChain raw, parsePoP rp with
  | some chain, some pop => invokeWithState P E anchors chain call pop seen
  | _, _ => (.deny, seen)

/-! ## Перенос теорем -/

/-- Если `invokeTokens` разрешил вызов, то токены разобраны в цепочку и PoP,
    на которых `invokeWithState` разрешает тот же вызов, — поэтому на них
    действуют Т1–Т9. -/
theorem invokeTokens_allow {P : Params} {E : Endpoint} {anchors : List Anchor}
    {raw : List RawToken} {call : Call} {rp : RawPoP} {seen : List String}
    (h : (invokeTokens P E anchors raw call rp seen).1 = .allow) :
    ∃ chain pop, parseChain raw = some chain ∧ parsePoP rp = some pop ∧
      (invokeWithState P E anchors chain call pop seen).1 = .allow := by
  unfold invokeTokens at h
  split at h
  · rename_i chain pop hc hp
    exact ⟨chain, pop, hc, hp, h⟩
  · simp at h

/-! ## Ловушки (ядро, `decide +kernel`) -/

def xT : String := "gTl3Dqh9F19Wo1Rmw0x-zMuNipG07jeiXfYPW4_Js5Q"
def jwkT : JVal := .obj [("kty", .str "OKP"), ("crv", .str "Ed25519"), ("x", .str xT)]
def adT (tools : List (String × JVal)) : JVal :=
  .arr [.obj [("type", .str "attenuating_agent_token"), ("tools", .obj tools)]]

/-- Полезная нагрузка звена: числа — литералы. -/
def payloadT (l : Link) (iat exp dd dmd : String) : JVal :=
  .obj ([("jti", .str l.jti), ("iss", .str l.issuer), ("iat", .num iat), ("exp", .num exp),
         ("del_depth", .num dd), ("del_max_depth", .num dmd), ("cnf", .obj [("jwk", jwkT)]),
         ("authorization_details", adT (l.tools.map (fun (t, _) => (t, .obj []))))] ++
        (match l.parHash with | some h => [("par_hash", .str h)] | none => []))

def rawT (l : Link) (iat exp dd dmd : String) : RawToken :=
  { payload := payloadT l iat exp dd dmd, thumb := some l.holder, selfHash := l.selfHash,
    sigBy := l.sigBy, maps := l.tools }

/-- Замена члена верхнего уровня (или добавление в конец). -/
def JVal.set (v : JVal) (k : String) (x : JVal) : JVal :=
  match v with
  | .obj kvs => if kvs.any (·.1 == k) then .obj (kvs.map (fun (a, b) => if a == k then (a, x) else (a, b)))
                else .obj (kvs ++ [(k, x)])
  | v => v

def JVal.drop (v : JVal) (k : String) : JVal :=
  match v with
  | .obj kvs => .obj (kvs.filter (·.1 != k))
  | v => v

-- Цепочка `mk chainT` и PoP `popT` из `Invoke.lean`; числа в литералах — её поля.
def linkT (i : Nat) : Link := (mk chainT).getD i human
def rootRawT : RawToken := rawT (linkT 0) "0" "100" "0" "8"
def childRawT : RawToken := rawT (linkT 1) "0" "100" "1" "8"

/-- PoP как записан: те же поля, что `popT`. -/
def popPayloadT : JVal :=
  .obj [("jti", .str popT.jti), ("aat_id", .str popT.aatId), ("aat_hash", .str popT.aatHash),
        ("aat_tool", .str popT.aatTool), ("iat", .num "50"), ("aat_aud", .str "ep"), ("hta", .obj [])]
def popRawT : RawPoP := { payload := popPayloadT, sigBy := popT.sigBy, hta := popT.hta }

def runT (r c : RawToken) (q : RawPoP := popRawT) : Decision :=
  (invokeTokens PT ET anchorsT [r, c] callT q []).1

def withRoot (f : JVal → JVal) : RawToken := { rootRawT with payload := f rootRawT.payload }
def withChild (f : JVal → JVal) : RawToken := { childRawT with payload := f childRawT.payload }
def withPoP (f : JVal → JVal) : RawPoP := { popRawT with payload := f popRawT.payload }
def setJwk (k : String) (x : JVal) : JVal → JVal := fun p => p.set "cnf" (.obj [("jwk", jwkT.set k x)])

-- исходные токены проходят
example : runT rootRawT childRawT = .allow := by decide +kernel
-- 3b/4b/7b: повтор имени — на верхнем уровне и вложенный
example : runT (withRoot fun p => match p with | .obj kvs => .obj (kvs ++ [("jti", .str "x")]) | v => v)
    childRawT = .deny := by decide +kernel
example : runT rootRawT (withChild fun p => p.set "cnf" (.obj [("jwk", jwkT), ("jwk", jwkT)])) = .deny := by
  decide +kernel
example : runT rootRawT childRawT
    (withPoP fun p => p.set "hta" (.obj [("amount", .num "50"), ("amount", .num "50")])) = .deny := by
  decide +kernel
-- 3b/4b5/7c: NumericDate с дробью или экспонентой
example : runT (withRoot (·.set "exp" (.num "1e2"))) childRawT = .deny := by decide +kernel
example : runT rootRawT (withChild (·.set "iat" (.num "0.0"))) = .deny := by decide +kernel
example : runT rootRawT childRawT (withPoP (·.set "iat" (.num "5e1"))) = .deny := by decide +kernel
-- 7c: hta — объект
example : runT rootRawT childRawT (withPoP (·.set "hta" (.arr []))) = .deny := by decide +kernel
-- 3c/3i/4b4: целые неотрицательные, присутствуют
example : runT (withRoot (·.set "del_depth" (.bool false))) childRawT = .deny := by decide +kernel
example : runT (withRoot (·.drop "del_max_depth")) childRawT = .deny := by decide +kernel
example : runT rootRawT (withChild (·.set "del_max_depth" (.num "-1"))) = .deny := by decide +kernel
example : runT (withRoot (·.set "del_depth" (.num "-1"))) childRawT = .deny := by decide +kernel
-- 3j/4b1: jti непустая строка
example : runT (withRoot (·.set "jti" (.str ""))) childRawT = .deny := by decide +kernel
example : runT rootRawT (withChild (·.set "jti" (.num "7"))) = .deny := by decide +kernel
-- 3l/4b2: открытый ключ Ed25519
example : runT (withRoot (setJwk "d" (.str xT))) childRawT = .deny := by decide +kernel
example : runT rootRawT (withChild (setJwk "kty" (.str "EC"))) = .deny := by decide +kernel
example : runT rootRawT (withChild (setJwk "crv" (.str "X25519"))) = .deny := by decide +kernel
example : runT rootRawT (withChild (setJwk "x" (.str "gTl3Dqh9F19Wo1Rmw0x"))) = .deny := by decide +kernel
example : runT rootRawT (withChild (setJwk "x" (.str "gTl3Dqh9F19Wo1Rmw0x-zMuNipG07jeiXfYPW4_Js5="))) = .deny := by
  decide +kernel
example : runT rootRawT (withChild (·.set "cnf" (.obj []))) = .deny := by decide +kernel
-- 3m/4b3/4n: ровно одна запись AAT; tools — объект объектов
example : runT (withRoot (·.set "authorization_details" (.arr []))) childRawT = .deny := by decide +kernel
example : runT rootRawT (withChild (·.set "authorization_details"
    (match adT [("pay", .obj [])] with | .arr xs => .arr (xs ++ xs) | v => v))) = .deny := by decide +kernel
example : runT rootRawT (withChild (·.set "authorization_details" (.obj []))) = .deny := by decide +kernel
example : runT rootRawT (withChild (·.set "authorization_details" (adT [("pay", .arr [])]))) = .deny := by
  decide +kernel
example : runT (withRoot (·.set "authorization_details"
    (.arr [.obj [("type", .str "attenuating_agent_token"), ("tools", .arr [])]]))) childRawT = .deny := by
  decide +kernel
-- записи других типов игнорируются
example : runT rootRawT (withChild (·.set "authorization_details"
    (match adT [("pay", .obj [])] with | .arr xs => .arr (.obj [("type", .str "other")] :: xs) | v => v)))
    = .allow := by decide +kernel
-- 4b5: iss и par_hash у производного
example : runT rootRawT (withChild (·.drop "iss")) = .deny := by decide +kernel
example : runT rootRawT (withChild (·.drop "par_hash")) = .deny := by decide +kernel
example : runT rootRawT (withChild (·.set "par_hash" (.num "1"))) = .deny := by decide +kernel
-- 3d: par_hash у корня, даже не строка
example : runT (withRoot (·.set "par_hash" (.null))) childRawT = .deny := by decide +kernel

end AAT
