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

def value (j : Json) : Except String Value :=
  match j.getObjVal? "str", j.getObjVal? "num", j.getObjVal? "bool",
        j.getObjVal? "null", j.getObjVal? "compound" with
  | .ok s, _, _, _, _ => return .str (← s.getStr?)
  | _, .ok n, _, _, _ => return .num (← rat n)
  | _, _, .ok b, _, _ => return .bool (← b.getBool?)
  | _, _, _, .ok _, _ => return .null
  | _, _, _, _, .ok c => return .compound (← c.getStr?)
  | _, _, _, _, _ => throw s!"bad value {j.compress}"

def bound (j : Json) : Except String (Option Bound) :=
  match j with
  | .null => pure none
  | _ => do pure (some ⟨← rat (← j.getObjVal? "val"), ← (← j.getObjVal? "incl").getBool?⟩)

def constraint (j : Json) : Except String Constraint :=
  match j.getObjVal? "wildcard", j.getObjVal? "exact", j.getObjVal? "oneOf", j.getObjVal? "range" with
  | .ok _, _, _, _ => pure .wildcard
  | _, .ok v, _, _ => return .exact (← value v)
  | _, _, .ok vs, _ => return .oneOf (← (← vs.getArr?).toList.mapM value)
  | _, _, _, .ok r => return .range (← bound (← r.getObjVal? "lo")) (← bound (← r.getObjVal? "hi"))
  | _, _, _, _ => throw s!"bad constraint {j.compress}"

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
  pure { issuer := ← str j "issuer", holder := ← str j "holder", tools,
         jti := ← str j "jti", delDepth := ← nat j "delDepth", delMaxDepth := ← nat j "delMaxDepth",
         iat := ← int j "iat", exp := ← int j "exp", parHash, selfHash := ← str j "selfHash",
         sigBy := ← (← (← j.getObjVal? "sigBy").getArr?).toList.mapM (·.getStr?) }

def runOne (j : Json) : Except String Decision := do
  let p ← j.getObjVal? "params"
  let P : Params := ⟨← int p "now", ← int p "maxIatSkew", ← int p "maxTokenLifetime",
                     ← nat p "maxDelegationDepth"⟩
  let anchors ← (← (← j.getObjVal? "anchors").getArr?).toList.mapM fun a => do
    pure ({ iss := ← str a "iss", key := ← str a "key" } : Anchor)
  let chain ← (← (← j.getObjVal? "chain").getArr?).toList.mapM link
  let call ← j.getObjVal? "call"
  let args ← (← (← call.getObjVal? "args").getArr?).toList.mapM fun e => do
    let (k, v) ← pair e
    pure ((← k.getStr?), ← value v)
  pure (authorize P anchors chain ⟨← (← call.getObjVal? "tool").getStr?, args⟩)

def main (argv : List String) : IO UInt32 := do
  let path := argv.headD "vectors/out/model-input.json"
  let recs ← IO.ofExcept ((Json.parse (← IO.FS.readFile path)) >>= (·.getArr?))
  for r in recs do
    let id := (r.getObjVal? "id" >>= (·.getStr?)).toOption.getD "?"
    if (r.getObjVal? "scope" >>= (·.getStr?)).toOption != some "in" then continue
    match r.getObjVal? "input" >>= runOne with
    | .ok .allow => IO.println s!"{id}\tPERMIT"
    | .ok .deny  => IO.println s!"{id}\tDENY"
    | .error e   => IO.println s!"{id}\tERROR {e}"
  pure 0
