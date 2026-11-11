import AatLean.Invoke
import AatLean.Number

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

До разбора claims (`framesOk`): 2a, 2b — размеры токенов и цепочки; 3a, 4a,
7a — заголовок JWS (`alg = "Ed25519"`, `typ`, `crit`), тоже как записан.

Остаётся снаружи (декодер, допущения 1, 5, 6): подпись (`sigBy`), SHA-256
signing input (`selfHash`), отпечаток `cnf.jwk` (`thumb`), содержимое карт
ограничений (`maps`, второй этап) и JCS-строки вложенных значений. Числа
приходят точными значениями; их допустимость (§3.4) — здесь и в `Number.lean`.

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

/-- Символ, допустимый в URI (RFC 3986 §2: unreserved, reserved, `%`). -/
def uriChar (c : Char) : Bool := c.isAlphanum || "-._~:/?#[]@!$&'()*+,;=%".toList.contains c

/-- Схема URI до `:` (RFC 3986 §3.1): после первой буквы — буквы, цифры, `+`, `-`, `.`. -/
def schemeRest : List Char → Bool
  | [] => false
  | ':' :: _ => true
  | c :: cs => (c.isAlphanum || c == '+' || c == '-' || c == '.') && schemeRest cs

/-- 3k: «is a URI» — схема RFC 3986 §3.1, затем `:`, и все символы
    допустимы в URI (прочтение: синтаксис остальных частей не разбирается). -/
def isUri (s : String) : Bool :=
  s.toList.all uriChar &&
  (match s.toList with
   | c :: cs => c.isAlpha && schemeRest cs
   | [] => false)

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
  /-- JWS Protected Header как записан. -/
  header   : JVal
  /-- Размер компактной сериализации в байтах (шаги 2a, 2b). -/
  size     : Nat
  payload  : JVal
  /-- `jwk_thumbprint_uri(cnf.jwk)` (допущение 5); `none` — не вычислим. -/
  thumb    : Option Key
  selfHash : String
  sigBy    : List Key
  /-- Карты ограничений по имени инструмента (разбор ограничений — снаружи). -/
  maps     : List (Tool × CMap)

/-- Разбор одного токена без держателя, `iss` и `par_hash` (их задаёт
    `parseLinkCore`); `isRoot` — корень: шаги 3, иначе 4b, 4n. -/
def parseFields (isRoot : Bool) (t : RawToken) : Option Link := do
  let p := t.payload
  guard p.noDup                                                      -- 3b, 4b
  let jti ← p.field "jti" >>= JVal.asNonEmpty                        -- 3j, 4b1
  let jwk ← p.field "cnf" >>= (·.field "jwk")                        -- 3l, 4b2
  guard (jwkOk jwk)
  let names ← p.field "authorization_details" >>= aatTools           -- 3m, 4b3, 4n
  let tools ← names.mapM (fun n => (t.maps.lookup n).map (n, ·))
  guard (tools.all (fun (_, m) => m.named.all (fun (_, e) => e.c.admissible)))  -- 3n, 4o (§3.4)
  let dd ← p.field "del_depth" >>= JVal.asNat                        -- 3c, 4b4
  let dmd ← p.field "del_max_depth" >>= JVal.asNat                   -- 3i, 4b4
  if isRoot then guard ((p.field "iss" >>= JVal.asStr).any isUri)   -- 3k
  let iat ← p.field "iat" >>= JVal.asInt                             -- 3b, 4b5
  let exp ← p.field "exp" >>= JVal.asInt                             -- 3b, 4b5
  pure { issuer := "", holder := "", tools, jti, delDepth := dd, delMaxDepth := dmd, iat, exp,
         parHash := none, selfHash := t.selfHash, sigBy := t.sigBy, aud := audOf (p.field "aud") }

/-- `iss`; не строка или нет — `""` (у корня это уже отвергнуто, 3k). -/
def issOf (t : RawToken) : String := (t.payload.field "iss" >>= JVal.asStr).getD ""

/-- `par_hash`. У корня 3d проверяет отсутствие, поэтому не строка — тоже
    «присутствует»; у производного — строка или `none`. -/
def parHashOf (isRoot : Bool) (t : RawToken) : Option String :=
  if isRoot then (t.payload.field "par_hash").map (fun v => v.asStr.getD "")
  else t.payload.field "par_hash" >>= JVal.asStr

/-- Разбор звена без шага 4b5. -/
def parseLinkCore (isRoot : Bool) (t : RawToken) : Option Link := do
  let holder ← t.thumb
  let l ← parseFields isRoot t
  pure { l with holder, issuer := issOf t, parHash := parHashOf isRoot t }

/-- Часть шага 4b5 для производного: `iss` и `par_hash` присутствуют и строки.
    Другая часть 4b5 — `iat`, `exp` как NumericDate — в `parseFields`. -/
def check4b5 (isRoot : Bool) (t : RawToken) : Bool :=
  isRoot || ((t.payload.field "iss" >>= JVal.asStr).isSome &&
             (t.payload.field "par_hash" >>= JVal.asStr).isSome)

/-- Разбор одного токена (`isRoot` — корень: шаги 3; иначе 4b, 4n). -/
def parseLink (isRoot : Bool) (t : RawToken) : Option Link := do
  let l ← parseLinkCore isRoot t
  guard (check4b5 isRoot t)                                          -- 4b5
  pure l

/-- Разбор цепочки: корень, затем производные. -/
def parseChain : List RawToken → Option (List Link)
  | [] => some []
  | r :: rest => do
    let l ← parseLink true r
    let ls ← rest.mapM (parseLink false)
    pure (l :: ls)

/-- Разбор цепочки без шага 4b5. -/
def parseChainCore : List RawToken → Option (List Link)
  | [] => some []
  | r :: rest => do
    let l ← parseLinkCore true r
    let ls ← rest.mapM (parseLinkCore false)
    pure (l :: ls)

/-- PoP JWT, как его видит модель. -/
structure RawPoP where
  header  : JVal
  payload : JVal
  sigBy   : List Key
  /-- `hta` как аргументы: числа — точные значения (допустимость — 7f здесь),
      вложенные значения — JCS-строкой от декодера (допущение 6). -/
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
  guard ((hta.getD []).all (fun (_, v) => v.admissible))           -- 7f (§3.4)
  pure { jti := s "jti", aatId := s "aat_id", aatHash := s "aat_hash", aatTool := s "aat_tool",
         iat, hta, aatAud := opt "aat_aud", nonce := opt "nonce", sigBy := q.sigBy }

/-- Параметры `crit`, которые понимает эта точка проверки (§3.5): никаких. -/
def critUnderstood : List String := []

/-- Шаги 3a, 4a, 7a. `alg` — `Ed25519` (единственный в списке разрешённых;
    ключи — только OKP/Ed25519, прочтение 3l, поэтому `alg` согласован с
    ключом); `typ` — ровно `typ`; `crit`, если есть, — непустой массив
    строк из `critUnderstood`. Повтор имени в заголовке — отказ (RFC 7515 §4
    разрешает отвергать). -/
def headerOk (typ : String) (h : JVal) : Bool :=
  h.noDup &&
  (h.field "alg" >>= JVal.asStr) == some "Ed25519" &&
  (h.field "typ" >>= JVal.asStr) == some typ &&
  (match h.field "crit" with
   | none => true
   | some (.arr xs) =>
     !xs.isEmpty && xs.all (fun x => match x.asStr with
       | some s => critUnderstood.contains s
       | none => false)
   | some _ => false)

/-- Шаги 2a, 2b: размер каждого токена и цепочки. -/
def sizesOk (P : Params) (raw : List RawToken) : Bool :=
  raw.all (fun t => decide (t.size ≤ P.maxTokenSize)) &&
  decide ((raw.map (·.size)).sum ≤ P.maxChainSize)

/-- Шаги 2a, 2b, 3a, 4a, 7a — до разбора claims. -/
def framesOk (P : Params) (raw : List RawToken) (rp : RawPoP) : Bool :=
  sizesOk P raw &&                                                   -- 2a, 2b
  raw.all (fun t => headerOk "aat+jwt" t.header) &&                  -- 3a, 4a
  headerOk "aat-pop+jwt" rp.header                                   -- 7a

/-- Шаги 1–7i на токенах как они записаны: размеры и заголовки, разбор, затем
    `invokeWithState`. Любой отказ до `invokeWithState` — DENY, состояние не
    меняется. -/
def invokeTokens (P : Params) (E : Endpoint) (anchors : List Anchor) (raw : List RawToken)
    (call : Call) (rp : RawPoP) (seen : List String) : Decision × List String :=
  if framesOk P raw rp then
    match parseChain raw, parsePoP rp with
    | some chain, some pop => invokeWithState P E anchors chain call pop seen
    | _, _ => (.deny, seen)
  else (.deny, seen)

/-- Вызов как записан: `call` — инструмент и аргументы верхнего уровня
    (числа — точные значения, вложенные — JCS-строкой, допущение 6); `args` — объект аргументов,
    как он записан в вызове. -/
structure RawCall where
  call : Call
  args : JVal

/-- Шаг 6b, дубликаты: «If any JSON object in args, as written in the
    invocation, has duplicate member names, DENY» — на любой глубине; затем
    `invokeTokens`. -/
def invokeCall (P : Params) (E : Endpoint) (anchors : List Anchor) (raw : List RawToken)
    (rc : RawCall) (rp : RawPoP) (seen : List String) : Decision × List String :=
  if rc.args.noDup then
    if rc.call.args.all (fun (_, v) => v.admissible) then             -- 6b (§3.4)
      invokeTokens P E anchors raw rc.call rp seen
    else (.deny, seen)
  else (.deny, seen)

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
  by_cases hf : framesOk P raw rp = true
  · simp only [hf, ite_true] at h
    split at h
    · rename_i chain pop hc hp
      exact ⟨chain, pop, hc, hp, h⟩
    · simp at h
  · simp [hf] at h

/-- Если `invokeCall` разрешил вызов, то в аргументах, как они записаны, нет
    повторов имён ни на какой глубине, и `invokeTokens` разрешает тот же вызов —
    поэтому действует `invokeTokens_allow`, а с ней Т1–Т9. -/
theorem invokeCall_allow {P : Params} {E : Endpoint} {anchors : List Anchor}
    {raw : List RawToken} {rc : RawCall} {rp : RawPoP} {seen : List String}
    (h : (invokeCall P E anchors raw rc rp seen).1 = .allow) :
    rc.args.noDup = true ∧ (invokeTokens P E anchors raw rc.call rp seen).1 = .allow := by
  unfold invokeCall at h
  by_cases hd : rc.args.noDup = true
  · simp only [hd, ite_true] at h
    by_cases ha : rc.call.args.all (fun (_, v) => v.admissible) = true
    · simp only [ha, ite_true] at h
      exact ⟨hd, h⟩
    · simp [ha] at h
  · simp [hd] at h

/-- `invokeTokens` без шага 4b5. -/
def invokeTokensCore (P : Params) (E : Endpoint) (anchors : List Anchor) (raw : List RawToken)
    (call : Call) (rp : RawPoP) (seen : List String) : Decision × List String :=
  if framesOk P raw rp then
    match parseChainCore raw, parsePoP rp with
    | some chain, some pop => invokeWithState P E anchors chain call pop seen
    | _, _ => (.deny, seen)
  else (.deny, seen)

theorem parseLink_core {b : Bool} {t : RawToken} {l : Link} (h : parseLink b t = some l) :
    parseLinkCore b t = some l := by
  unfold parseLink at h
  cases hc : parseLinkCore b t with
  | none => simp [hc] at h
  | some l' =>
    simp only [hc, Option.bind_eq_bind, Option.bind_some] at h
    cases h4 : check4b5 b t <;> simp_all [guard, failure]

theorem parseLink_of_core {b : Bool} {t : RawToken} {l : Link} (h : parseLinkCore b t = some l)
    (h4 : check4b5 b t = true) : parseLink b t = some l := by
  simp [parseLink, h, h4, guard]

theorem core_spec {b : Bool} {t : RawToken} {l : Link} (h : parseLinkCore b t = some l) :
    t.thumb = some l.holder ∧ l.issuer = issOf t ∧ l.parHash = parHashOf b t := by
  unfold parseLinkCore at h
  cases ht : t.thumb with
  | none => simp [ht] at h
  | some k =>
    cases hf : parseFields b t with
    | none => simp [ht, hf] at h
    | some l0 =>
      simp only [ht, hf, Option.bind_eq_bind, Option.bind_some, Option.pure_def,
        Option.some.injEq] at h
      subst h
      exact ⟨rfl, rfl, rfl⟩

theorem mapM_core : ∀ (ts : List RawToken) (ls : List Link),
    ts.mapM (parseLink false) = some ls → ts.mapM (parseLinkCore false) = some ls
  | [], ls, h => by simpa using h
  | t :: ts, ls, h => by
    simp only [List.mapM_cons, Option.bind_eq_bind, Option.pure_def] at h ⊢
    cases hl : parseLink false t with
    | none => simp [hl] at h
    | some l =>
      cases hr : ts.mapM (parseLink false) with
      | none => simp [hl, hr] at h
      | some ls' =>
        simp [hl, hr] at h
        simp [parseLink_core hl, mapM_core ts ls' hr, h]

theorem chain_core {raw : List RawToken} {c : List Link} (h : parseChain raw = some c) :
    parseChainCore raw = some c := by
  cases raw with
  | nil => simpa [parseChain, parseChainCore] using h
  | cons r rest =>
    simp only [parseChain, parseChainCore, Option.bind_eq_bind, Option.pure_def] at h ⊢
    cases hl : parseLink true r with
    | none => simp [hl] at h
    | some l =>
      cases hr : rest.mapM (parseLink false) with
      | none => simp [hl, hr] at h
      | some ls => simp [hl, hr] at h; simp [parseLink_core hl, mapM_core rest ls hr, h]

/-- Производный токен, прошедший шаги 4c и 4q, прошёл бы и 4b5. -/
theorem check4b5_of {t : RawToken} {l : Link} (h : parseLinkCore false t = some l)
    (hi : l.issuer ≠ "") (hp : l.parHash.isSome) : check4b5 false t = true := by
  obtain ⟨_, hiss, hph⟩ := core_spec h
  simp only [check4b5, Bool.false_or, Bool.and_eq_true]
  refine ⟨?_, ?_⟩
  · rw [hiss] at hi
    cases hx : (t.payload.field "iss" >>= JVal.asStr) <;> simp_all [issOf]
  · rw [hph] at hp
    simpa [parHashOf] using hp

theorem mapM_lift (P : Params) : ∀ (parent : Link) (ts : List RawToken) (ls : List Link),
    parent.holder ≠ "" → (∀ t ∈ ts, t.thumb ≠ some "") →
    ts.mapM (parseLinkCore false) = some ls → allPairs (pairOk P) (parent :: ls) = true →
    ts.mapM (parseLink false) = some ls
  | _, [], ls, _, _, h, _ => by simpa using h
  | parent, t :: ts, ls, hpar, hk, h, hp => by
    simp only [List.mapM_cons, Option.bind_eq_bind, Option.pure_def] at h ⊢
    cases hl : parseLinkCore false t with
    | none => simp [hl] at h
    | some l =>
      cases hr : ts.mapM (parseLinkCore false) with
      | none => simp [hl, hr] at h
      | some ls' =>
        simp [hl, hr] at h
        subst h
        simp only [allPairs, Bool.and_eq_true] at hp
        obtain ⟨hpair, hrest⟩ := hp
        have hc := (pairCore_spec (by simp only [pairOk, Bool.and_eq_true] at hpair; exact hpair.1))
        have hiss : l.issuer = parent.holder := hc.2.1
        have hph : l.parHash = some parent.selfHash := hc.2.2.2.2.2.2.2.2.2.2.2
        have h4 := check4b5_of hl (by rw [hiss]; exact hpar) (by simp [hph])
        have hhold : l.holder ≠ "" := by
          intro he
          have := (core_spec hl).1
          rw [he] at this
          exact hk t (by simp) this
        have ih := mapM_lift P l ts ls' hhold (fun t' ht' => hk t' (by simp [ht'])) hr hrest
        simp [parseLink_of_core hl h4, ih]

theorem invokeWithState_deny (P : Params) (E : Endpoint) (anchors : List Anchor) (c : List Link)
    (call : Call) (pop : PoP) (seen : List String)
    (h : (invokeWithState P E anchors c call pop seen).1 ≠ .allow) :
    invokeWithState P E anchors c call pop seen = (.deny, seen) := by
  unfold invokeWithState at h ⊢
  cases hi : invoke P E anchors c call pop with
  | deny => rfl
  | allow =>
    simp only [hi] at h ⊢
    by_cases ht : E.trackJti <;> by_cases hs : seen.contains pop.jti <;> simp_all

theorem verify_of_state {P : Params} {E : Endpoint} {anchors : List Anchor} {c : List Link}
    {call : Call} {pop : PoP} {seen : List String}
    (h : (invokeWithState P E anchors c call pop seen).1 = .allow) : verify P anchors c = .allow := by
  have hi : invoke P E anchors c call pop = .allow := by
    unfold invokeWithState at h
    cases hi : invoke P E anchors c call pop <;> simp_all
  exact ((authorize_allow_iff P anchors c call).mp (invoke_authorizes hi)).1

theorem allPairs_of_verify {P : Params} {anchors : List Anchor} {c : List Link}
    (hv : verify P anchors c = .allow) : allPairs (pairOk P) c = true :=
  (allPairs_iff (pairOk P) c).mpr (fun i hi => pair_of_allow hv i hi)

/-- **Т7″.** Проверка `iss`/`par_hash` из шага 4b5 (присутствуют и строки у
    производного; проверка NumericDate `iat`/`exp` из 4b5 сюда не входит) не
    меняет ни одного вердикта, если отпечатки ключей непусты: без `iss`
    отказывает 4c (`iss` = отпечаток ключа родителя), без `par_hash` — 4q. -/
theorem t7_4b5_redundant (P : Params) (E : Endpoint) (anchors : List Anchor) (raw : List RawToken)
    (call : Call) (rp : RawPoP) (seen : List String) (hk : ∀ t ∈ raw, t.thumb ≠ some "") :
    invokeTokens P E anchors raw call rp seen = invokeTokensCore P E anchors raw call rp seen := by
  unfold invokeTokens invokeTokensCore
  by_cases hf : framesOk P raw rp = true
  rotate_left
  · simp [hf]
  simp only [hf, ite_true]
  cases hpc : parseChain raw with
  | some c => simp [chain_core hpc]
  | none =>
    cases hcc : parseChainCore raw with
    | none => simp
    | some c =>
      cases hpp : parsePoP rp with
      | none => simp
      | some pop =>
        simp only
        symm
        apply invokeWithState_deny
        intro hallow
        -- разрешение на ядре → разбор с 4b5 тоже проходит: противоречие с `hpc`
        have hp := allPairs_of_verify (verify_of_state hallow)
        cases raw with
        | nil => simp [parseChain] at hpc
        | cons r rest =>
          simp only [parseChainCore, Option.bind_eq_bind, Option.pure_def] at hcc
          cases hl : parseLinkCore true r with
          | none => simp [hl] at hcc
          | some l =>
            cases hr : rest.mapM (parseLinkCore false) with
            | none => simp [hl, hr] at hcc
            | some ls =>
              simp [hl, hr] at hcc
              subst hcc
              have hhold : l.holder ≠ "" := by
                intro he
                have := (core_spec hl).1
                rw [he] at this
                exact hk r (by simp) this
              have hlift := mapM_lift P l rest ls hhold (fun t ht => hk t (by simp [ht])) hr hp
              have hroot : parseLink true r = some l := parseLink_of_core hl (by simp [check4b5])
              simp [parseChain, hroot, hlift] at hpc

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

def hdrT (typ : String) : JVal := .obj [("alg", .str "Ed25519"), ("typ", .str typ)]

def rawT (l : Link) (iat exp dd dmd : String) : RawToken :=
  { header := hdrT "aat+jwt", size := 100, payload := payloadT l iat exp dd dmd,
    thumb := some l.holder, selfHash := l.selfHash, sigBy := l.sigBy, maps := l.tools }

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
-- корень называет издателя-URI (3k); якорь — тот же издатель с ключом `anchor-key`
def issT : String := "https://root.example"
def anchorsUT : List Anchor := [⟨issT, "anchor-key"⟩]
def rootRawT : RawToken := rawT { linkT 0 with issuer := issT } "0" "100" "0" "8"
def childRawT : RawToken := rawT (linkT 1) "0" "100" "1" "8"

/-- PoP как записан: те же поля, что `popT`. -/
def popPayloadT : JVal :=
  .obj [("jti", .str popT.jti), ("aat_id", .str popT.aatId), ("aat_hash", .str popT.aatHash),
        ("aat_tool", .str popT.aatTool), ("iat", .num "50"), ("aat_aud", .str "ep"), ("hta", .obj [])]
def popRawT : RawPoP := { header := hdrT "aat-pop+jwt", payload := popPayloadT, sigBy := popT.sigBy,
                          hta := popT.hta }

def runT (r c : RawToken) (q : RawPoP := popRawT) : Decision :=
  (invokeTokens PT ET anchorsUT [r, c] callT q []).1

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
-- 2a, 2b: размеры (PT: токен ≤ 1000, цепочка ≤ 1500)
example : runT { rootRawT with size := 1000 } childRawT = .allow := by decide +kernel
example : runT { rootRawT with size := 1001 } childRawT = .deny := by decide +kernel
example : runT { rootRawT with size := 800 } { childRawT with size := 800 } = .deny := by decide +kernel
-- 3a, 4a, 7a: alg, typ, crit
def withHdr (t : RawToken) (f : JVal → JVal) : RawToken := { t with header := f t.header }
def withPoPHdr (f : JVal → JVal) : RawPoP := { popRawT with header := f popRawT.header }
example : runT (withHdr rootRawT (·.set "alg" (.str "EdDSA"))) childRawT = .deny := by decide +kernel
example : runT (withHdr rootRawT (·.set "alg" (.str "none"))) childRawT = .deny := by decide +kernel
example : runT rootRawT (withHdr childRawT (·.drop "typ")) = .deny := by decide +kernel
example : runT rootRawT (withHdr childRawT (·.set "typ" (.str "aat-pop+jwt"))) = .deny := by decide +kernel
example : runT rootRawT childRawT (withPoPHdr (·.set "typ" (.str "aat+jwt"))) = .deny := by decide +kernel
example : runT rootRawT childRawT (withPoPHdr (·.set "alg" (.str "EdDSA"))) = .deny := by decide +kernel
example : runT (withHdr rootRawT (·.set "crit" (.arr [.str "urn:example:unknown"]))) childRawT = .deny := by
  decide +kernel
example : runT rootRawT (withHdr childRawT (·.set "crit" (.arr []))) = .deny := by decide +kernel
example : runT rootRawT childRawT (withPoPHdr (·.set "crit" (.str "x"))) = .deny := by decide +kernel
example : runT (withHdr rootRawT (fun h => match h with
    | .obj kvs => .obj (kvs ++ [("typ", .str "x")]) | v => v)) childRawT = .deny := by decide +kernel
-- другие параметры заголовка игнорируются (§3.5)
example : runT (withHdr rootRawT (·.set "kid" (.str "k1"))) childRawT = .allow := by decide +kernel
-- 3k: iss корня — URI, даже если якорь настроен с тем же не-URI
example : runT (withRoot (·.set "iss" (.str "not a URI"))) childRawT = .deny := by decide +kernel
example : (invokeTokens PT ET [⟨"root-key", "anchor-key"⟩]
    [withRoot (·.set "iss" (.str "root-key")), childRawT] callT popRawT []).1 = .deny := by decide +kernel
example : isUri "https://auth.example.com" = true := by decide +kernel
example : isUri "urn:ietf:params:oauth:jwk-thumbprint:sha-256:abc" = true := by decide +kernel
example : isUri "not a URI" = false := by decide +kernel
example : isUri ":x" = false := by decide +kernel
example : isUri "1a:b" = false := by decide +kernel
example : isUri "https://a b" = false := by decide +kernel
-- 6b: повтор имени в аргументах на любой глубине (`callT` — `amount: 50`)
def runCall (args : JVal) : Decision :=
  (invokeCall PT ET anchorsUT [rootRawT, childRawT] ⟨callT, args⟩ popRawT []).1
example : runCall (.obj [("amount", .num "50")]) = .allow := by decide +kernel
example : runCall (.obj [("amount", .num "50"), ("meta", .obj [("a", .null), ("a", .null)])]) = .deny := by
  decide +kernel
example : runCall (.obj [("amount", .num "50"), ("tags", .arr [.obj [("b", .null), ("b", .null)]])]) = .deny := by
  decide +kernel
-- §3.4: недопустимые числа — в ограничении (3n), в hta (7f), в аргументах (6b)
example : runT { rootRawT with maps := [payCap 9007199254740993] } childRawT = .deny := by decide +kernel
example : runT { rootRawT with maps := [payCap 9007199254740992] } childRawT = .allow := by decide +kernel
example : runT rootRawT childRawT { popRawT with hta := some [("amount", .num 9007199254740993)] } = .deny := by
  decide +kernel
-- §3.4 + 7f по JCS: 1.00000000000000001 и 1 сериализуются одинаково, поэтому
-- hta и аргументы равны, и недопустимое число отвергает только своя проверка
def runNums (args hta : Args) : Decision :=
  (invokeCall PT ET anchorsUT [rootRawT, childRawT] ⟨⟨"pay", args⟩, .obj []⟩
    { popRawT with hta := some hta } []).1
def oneish : Rat := 100000000000000001 / 100000000000000000
example : runNums [("amount", .num 1)] [("amount", .num 1)] = .allow := by decide +kernel
example : runNums [("amount", .num oneish)] [("amount", .num 1)] = .deny := by decide +kernel    -- 6b
example : runNums [("amount", .num 1)] [("amount", .num oneish)] = .deny := by decide +kernel    -- 7f
-- 3d: par_hash у корня, даже не строка
example : runT (withRoot (·.set "par_hash" (.null))) childRawT = .deny := by decide +kernel

end AAT
