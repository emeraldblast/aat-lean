import AatLean.Constraint

/-!
# Допустимость чисел (§3.4)

«A JSON number is admissible when the JCS serialization of its double-precision
value denotes the same mathematical value as the input number.» JCS ([RFC8785]
§3.2.2.3) записывает double по правилу ECMAScript `Number::toString`: из всех
десятичных `s × 10^q`, которые округляются в этот double, — с наименьшим числом
цифр `k`, а среди них — ближайшее к double (при равенстве — с чётным `s`).

Модель вычисляет это в точных рациональных числах, без `Float`:

1. `toDouble` — округление к ближайшему, при равенстве к чётному (IEEE 754
   binary64): 53 бита мантиссы, денормализованные числа до `2^-1074`;
   `none` — переполнение (значение округляется в бесконечность);
2. `shortest` — кратчайшее десятичное `s × 10^q` в интервале округления этого
   double (границы включены, если мантисса чётная);
3. `admissible x` — `x = 0` или `shortest (toDouble |x|) = |x|`.

Знак не влияет: JCS пишет `-` перед записью модуля; `-0` записывается как `0`
и обозначает то же значение.
-/

namespace AAT

/-- `2^z` для целого `z`. -/
def pow2 (z : Int) : Rat :=
  if 0 ≤ z then ((2 ^ z.toNat : Nat) : Rat) else 1 / ((2 ^ (-z).toNat : Nat) : Rat)

/-- `10^z` для целого `z`. -/
def pow10 (z : Int) : Rat :=
  if 0 ≤ z then ((10 ^ z.toNat : Nat) : Rat) else 1 / ((10 ^ (-z).toNat : Nat) : Rat)

/-- `⌊log₂ a⌋` для `a > 0`: по длинам числителя и знаменателя, с поправкой
    (`a ∈ (2^(n-m-1), 2^(n-m+1))`). -/
def log2Floor (a : Rat) : Int :=
  let l : Int := (Nat.log2 a.num.natAbs : Int) - (Nat.log2 a.den : Int)
  if a < pow2 l then l - 1 else l

/-- `⌊log₁₀ a⌋` для `a > 0`: оценка `d₀ = ⌊L · 0.30103⌋` по `L = ⌊log₂ a⌋`,
    затем одна поправка вниз и одна вверх. `0.30103 > log₁₀ 2` на `4.4·10⁻⁹`:
    при `L > 0` оценка не ниже истинного `⌊L log₁₀ 2⌋` и выше не больше чем на 1,
    при `L < 0` — не выше и ниже не больше чем на 1 (`|L| ≤ 1100`); поэтому
    `⌊log₁₀ a⌋ - d₀ ∈ {-1, 0, 1}`. -/
def log10Floor (a : Rat) : Int :=
  let d0 : Int := (log2Floor a * 30103) / 100000
  let d1 := if a < pow10 d0 then d0 - 1 else d0
  if pow10 (d1 + 1) ≤ a then d1 + 1 else d1

/-- Округление к ближайшему целому, при равенстве — к чётному. -/
def roundEven (r : Rat) : Int :=
  let f := r.floor
  let frac := r - f
  if frac < 1/2 then f else if 1/2 < frac then f + 1 else if f % 2 == 0 then f else f + 1

/-- Ближайший double к `a > 0`: `some (m, e)`, значение `m · 2^e`, `m < 2^53`;
    `none` — переполнение. -/
def toDouble (a : Rat) : Option (Nat × Int) :=
  let e : Int := max (log2Floor a - 52) (-1074)
  let m := (roundEven (a / pow2 e)).toNat
  let (m, e) := if m == 2 ^ 53 then (2 ^ 52, e + 1) else (m, e)
  if pow2 1024 ≤ (m : Rat) * pow2 e then none else some (m, e)

/-- Кандидат с `k` цифрами при показателе `q`: целые `s` с `s · 10^q` в
    интервале `[lo, hi]` (концы включены, если `closed`), `10^(k-1) ≤ s < 10^k`;
    из них — ближайшее к `d / 10^q` (при равенстве — чётное). -/
def candidate (d lo hi : Rat) (closed : Bool) (k : Nat) (q : Int) : Option Rat :=
  let p := pow10 q
  let sLo0 := (lo / p).ceil
  let sLo := if !closed && (sLo0 : Rat) * p == lo then sLo0 + 1 else sLo0
  let sHi0 := (hi / p).floor
  let sHi := if !closed && (sHi0 : Rat) * p == hi then sHi0 - 1 else sHi0
  let sLo := max sLo ((10 ^ (k - 1) : Nat) : Int)
  let sHi := min sHi ((10 ^ k : Nat) - 1 : Int)
  if sLo ≤ sHi then
    let s := min sHi (max sLo (roundEven (d / p)))
    some ((s : Rat) * p)
  else none

/-- Ближе к `d`; при равенстве — то, у которого `s` чётно (`s = v / 10^q`),
    как в ECMAScript `Number::toString`. Ни одно из почти 200 000 проверенных
    чисел (дифференциальный тест против Python) не дошло до этого равенства;
    правило оставлено по спецификации, но тестом не подтверждено. -/
def closer (d : Rat) (q : Int) (a b : Rat) : Rat :=
  let da := if a < d then d - a else a - d
  let db := if b < d then d - b else b - d
  if da < db then a else if db < da then b
  else if (a / pow10 q).floor % 2 == 0 then a else b

/-- Лучший кандидат с `k` цифрами: показатели `q` вокруг `⌊log₁₀ d⌋ - k + 1`
    (интервал может пересекать степень 10). -/
def bestOfK (d lo hi : Rat) (closed : Bool) (dexp : Int) (k : Nat) : Option Rat :=
  let qs : List Int := [dexp - k, dexp - k + 1, dexp - k + 2]
  qs.foldl (fun acc q =>
    match acc, candidate d lo hi closed k q with
    | none, c => c
    | some a, none => some a
    | some a, some b => some (closer d q a b)) none

/-- Запись JCS double `m · 2^e` (`m > 0`): значение кратчайшего десятичного. -/
def shortest (m : Nat) (e : Int) : Option Rat :=
  let d : Rat := (m : Rat) * pow2 e
  let below := if m == 2 ^ 52 && -1074 < e then pow2 (e - 2) else pow2 (e - 1)
  let lo := d - below
  let hi := d + pow2 (e - 1)
  let closed := m % 2 == 0
  let dexp := log10Floor d
  (List.range 17).findSome? (fun i => bestOfK d lo hi closed dexp (i + 1))

/-- §3.4: число допустимо. -/
def admissible (x : Rat) : Bool :=
  if x == 0 then true
  else
    let a := if x < 0 then -x else x
    match toDouble a with
    | none => false
    | some (0, _) => false
    | some (m, e) => shortest m e == some a

/-- Значение JCS-записи числа: кратчайшее десятичное его double (со знаком);
    при переполнении — само число (такое число недопустимо и отвергается
    раньше). -/
def jcsValue (x : Rat) : Rat :=
  if x == 0 then 0
  else
    let a := if x < 0 then -x else x
    match toDouble a with
    | some (m, e) =>
      match shortest m e with
      | some v => if x < 0 then -v else v
      | none => x
    | none => x

def Scalar.jcs : Scalar → Scalar
  | .num q => .num (jcsValue q)
  | s => s

/-- Значение после JCS: числа заменены значениями их JCS-записей. Сравнение
    `a.jcs == b.jcs` — сравнение JCS-сериализаций (§3.4, шаг 7f). -/
def Value.jcs : Value → Value
  | .num q => .num (jcsValue q)
  | .arr xs => .arr (xs.map Scalar.jcs)
  | v => v

/-! ## Все числа значения и ограничения -/

def Scalar.admissible : Scalar → Bool
  | .num q => AAT.admissible q
  | _ => true

def Value.admissible : Value → Bool
  | .num q => AAT.admissible q
  | .arr xs => xs.all Scalar.admissible
  | _ => true

def Bound.admissible? : Option Bound → Bool
  | some b => AAT.admissible b.val
  | none => true

mutual
/-- «every number in it is admissible» (§3.4, well-formed). -/
def Constraint.admissible : Constraint → Bool
  | .exact v => v.admissible
  | .oneOf vs => vs.all Value.admissible
  | .notOneOf vs => vs.all Value.admissible
  | .range lo hi => Bound.admissible? lo && Bound.admissible? hi
  | .contains xs => xs.all Scalar.admissible
  | .subset xs => xs.all Scalar.admissible
  | .all cs => Constraint.admissibleList cs
  | .any cs => Constraint.admissibleList cs
  | _ => true
def Constraint.admissibleList : List Constraint → Bool
  | [] => true
  | c :: cs => c.admissible && Constraint.admissibleList cs
end

/-! ## Ловушки (ядро): примеры §3.4 и края double -/

example : admissible (1/10) = true := by decide +kernel
example : admissible (10 ^ 20) = true := by decide +kernel
example : admissible 9007199254740994 = true := by decide +kernel
example : admissible 9007199254740993 = false := by decide +kernel
example : admissible (100000000000000001 / 100000000000000000) = false := by decide +kernel
example : admissible 9007199254740992 = true := by decide +kernel
example : admissible (-1/10) = true := by decide +kernel
example : admissible 0 = true := by decide +kernel
-- найдены дифференциальным тестом против Python: каждая ловит свою ошибку алгоритма
example : admissible (2814749767106561 / 5) = true := by decide +kernel          -- равенство → к чётному
example : admissible (16 / 10 ^ 325) = false := by decide +kernel                -- денормализованные
example : admissible (2 * 10 ^ 308) = false := by decide +kernel                 -- переполнение
example : admissible 18446744073709552000 = true := by decide +kernel            -- шаг ниже степени 2
example : admissible 18014398509481988 = true := by decide +kernel               -- граница открыта (нечётная)
example : admissible 18014398509481990 = true := by decide +kernel               -- граница закрыта (чётная)
example : admissible (1 / 1000000) = true := by decide +kernel                   -- окно показателей
example : admissible 590295810358705650000 = false := by decide +kernel          -- 2^53 → 2^52, e + 1
-- JCS-значение: 9007199254740993 и 9007199254740992 сериализуются одинаково (§3.4)
example : jcsValue 9007199254740993 = 9007199254740992 := by decide +kernel
example : jcsValue (-1/10) = -1/10 := by decide +kernel

end AAT
