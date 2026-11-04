import AatLean
import Lean.Data.Json

/-!
# Прогон модели на векторах

Читает `vectors/out/model-input.json` (вывод `vectors/decode.py`) и для каждого
вектора в зоне модели печатает `id<TAB>PERMIT|DENY` — вердикт `authorize`,
той самой функции, о которой доказаны Т1 и Т2. Ошибка разбора входа — `ERROR`.
-/

open Lean AAT

def rat (j : Json) : Except String Rat := do
  let n ← (← j.getObjVal? "n").getInt?
  let d ← (← j.getObjVal? "d").getInt?
  pure ((n : Rat) / (d : Rat))

def scalar (j : Json) : Except String Scalar :=
  match j.getObjVal? "str", j.getObjVal? "num", j.getObjVal? "bool",
        j.getObjVal? "null", j.getObjVal? "compound" with
  | .ok s, _, _, _, _ => return .str (← s.getStr?)
  | _, .ok n, _, _, _ => return .num (← rat n)
  | _, _, .ok b, _, _ => return .bool (← b.getBool?)
  | _, _, _, .ok _, _ => return .null
  | _, _, _, _, .ok c => return .compound (← c.getStr?)
  | _, _, _, _, _ => throw s!"bad scalar {j.compress}"

def scalars (j : Json) : Except String (List Scalar) := do (← j.getArr?).toList.mapM scalar

def value (j : Json) : Except String Value :=
  match j.getObjVal? "arr" with
  | .ok xs => return .arr (← scalars xs)
  | .error _ => do
    match ← scalar j with
    | .str s => pure (.str s)
    | .num q => pure (.num q)
    | .bool b => pure (.bool b)
    | .null => pure .null
    | .compound c => pure (.compound c)

def bound (j : Json) : Except String (Option Bound) :=
  match j with
  | .null => pure none
  | _ => do pure (some ⟨← rat (← j.getObjVal? "val"), ← (← j.getObjVal? "incl").getBool?⟩)

partial def constraint (j : Json) : Except String Constraint := do
  if (j.getObjVal? "wildcard").isOk then return .wildcard
  if (j.getObjVal? "malformed").isOk then return .malformed
  if let .ok v := j.getObjVal? "exact" then return .exact (← value v)
  if let .ok vs := j.getObjVal? "oneOf" then return .oneOf (← (← vs.getArr?).toList.mapM value)
  if let .ok vs := j.getObjVal? "notOneOf" then return .notOneOf (← (← vs.getArr?).toList.mapM value)
  if let .ok r := j.getObjVal? "range" then
    return .range (← bound (← r.getObjVal? "lo")) (← bound (← r.getObjVal? "hi"))
  if let .ok xs := j.getObjVal? "contains" then return .contains (← scalars xs)
  if let .ok xs := j.getObjVal? "subset" then return .subset (← scalars xs)
  if let .ok cs := j.getObjVal? "all" then return .all (← (← cs.getArr?).toList.mapM constraint)
  if let .ok cs := j.getObjVal? "any" then return .any (← (← cs.getArr?).toList.mapM constraint)
  throw s!"bad constraint {j.compress}"

def pair (j : Json) : Except String (Json × Json) := do
  let a ← j.getArr?
  if h : a.size = 2 then pure (a[0], a[1]) else throw "bad pair"

def cmap (j : Json) : Except String CMap := do
  let named ← (← (← j.getObjVal? "named").getArr?).toList.mapM fun e => do
    let (k, v) ← pair e
    pure ((← k.getStr?), ({ c := ← constraint (← v.getObjVal? "c"),
                            optional := ← (← v.getObjVal? "optional").getBool? } : Entry))
  pure ⟨named, ← (← j.getObjVal? "star").getBool?⟩

def str (j : Json) (k : String) : Except String String := do (← j.getObjVal? k).getStr?
def int (j : Json) (k : String) : Except String Int := do (← j.getObjVal? k).getInt?
def nat (j : Json) (k : String) : Except String Nat := do (← j.getObjVal? k).getNat?

def link (j : Json) : Except String Link := do
  let tools ← (← (← j.getObjVal? "tools").getArr?).toList.mapM fun e => do
    let (t, m) ← pair e
    pure ((← t.getStr?), ← cmap m)
  let parHash ← match j.getObjVal? "parHash" with
    | .ok .null => pure none
    | .ok v => pure (some (← v.getStr?))
    | .error _ => pure none
  let aud ← match j.getObjVal? "aud" with
    | .ok .null => pure none
    | .ok v => pure (some (← (← v.getArr?).toList.mapM (·.getStr?)))
    | .error _ => pure none
  pure { issuer := ← str j "issuer", holder := ← str j "holder", tools, aud,
         jti := ← str j "jti", delDepth := ← nat j "delDepth", delMaxDepth := ← nat j "delMaxDepth",
         iat := ← int j "iat", exp := ← int j "exp", parHash, selfHash := ← str j "selfHash",
         sigBy := ← (← (← j.getObjVal? "sigBy").getArr?).toList.mapM (·.getStr?) }

def optStr (j : Json) (k : String) : Except String (Option String) :=
  match j.getObjVal? k with
  | .ok .null => pure none
  | .ok v => do pure (some (← v.getStr?))
  | .error _ => pure none

def argsOf (j : Json) : Except String Args := do
  (← j.getArr?).toList.mapM fun e => do
    let (k, v) ← pair e
    pure ((← k.getStr?), ← value v)

def runOne (j : Json) : Except String (Decision × List String) := do
  let p ← j.getObjVal? "params"
  let P : Params := ⟨← int p "now", ← int p "maxIatSkew", ← int p "maxTokenLifetime",
                     ← nat p "maxDelegationDepth", ← nat p "maxConstraintDepth"⟩
  let e ← j.getObjVal? "endpoint"
  let E : Endpoint := ⟨← str e "audience", ← int e "popWindow",
    ← (← e.getObjVal? "requireChainAud").getBool?, ← (← e.getObjVal? "requirePopAud").getBool?,
    ← optStr e "nonce", ← (← e.getObjVal? "trackJti").getBool?⟩
  let anchors ← (← (← j.getObjVal? "anchors").getArr?).toList.mapM fun a => do
    pure ({ iss := ← str a "iss", key := ← str a "key" } : Anchor)
  let chain ← (← (← j.getObjVal? "chain").getArr?).toList.mapM link
  let call ← j.getObjVal? "call"
  let callV : Call := ⟨← str call "tool", ← argsOf (← call.getObjVal? "args")⟩
  let q ← j.getObjVal? "pop"
  let hta ← match q.getObjVal? "hta" with
    | .ok .null => pure none
    | .ok v => pure (some (← argsOf v))
    | .error _ => pure none
  let pop : PoP := ⟨← str q "jti", ← str q "aatId", ← str q "aatHash", ← str q "aatTool",
    ← int q "iat", hta, ← optStr q "aatAud", ← optStr q "nonce",
    ← (← (← q.getObjVal? "sigBy").getArr?).toList.mapM (·.getStr?)⟩
  let seen ← (← (← j.getObjVal? "seen").getArr?).toList.mapM (·.getStr?)
  pure (invokeWithState P E anchors chain callV pop seen)

def main (argv : List String) : IO UInt32 := do
  let path := argv.headD "vectors/out/model-input.json"
  let recs ← IO.ofExcept ((Json.parse (← IO.FS.readFile path)) >>= (·.getArr?))
  for r in recs do
    let id := (r.getObjVal? "id" >>= (·.getStr?)).toOption.getD "?"
    if (r.getObjVal? "scope" >>= (·.getStr?)).toOption != some "in" then continue
    match r.getObjVal? "input" >>= runOne with
    | .ok (d, st) =>
      let v := match d with | .allow => "PERMIT" | .deny => "DENY"
      IO.println s!"{id}\t{v}\t{",".intercalate st.reverse}"
    | .error e => IO.println s!"{id}\tERROR {e}\t"
  pure 0
