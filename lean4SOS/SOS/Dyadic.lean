import Init.Core
import Init.Data.Int
import Init.System.IO

structure Dyadic := (m : Int) (e : Int)

namespace Dyadic

syntax term "₂" term : term 
macro_rules | `($m ₂ $e) => `(mk $m $e)

instance : ToString Dyadic where
  toString x := s!"{x.m}₂{x.e}"

-- Definitions.

def Neg : Dyadic → Dyadic :=
  fun x => { m := -x.m, e := x.e }

def Add : Dyadic → Dyadic → Dyadic := fun x y =>
  if x.e ≤ y.e
  then { m := x.m + y.m * 2 ^ (Int.toNat (y.e - x.e)), e := x.e }
  else { m := y.m + x.m * 2 ^ (Int.toNat (x.e - y.e)), e := y.e }

def Sub : Dyadic → Dyadic → Dyadic := fun x y =>
  Add x (Neg y)

def Mul : Dyadic → Dyadic → Dyadic := fun x y => 
  { m := x.m * y.m, e := x.e + y.e }

def Div (p : Nat) : Dyadic → Dyadic → Dyadic := fun x y =>
  if x.e ≤ y.e
  then { m := ((x.m * 2 ^ p) / (y.m * 2 ^ Int.toNat (y.e - x.e))), e := -p }
  else { m := ((x.m * 2 ^ Int.toNat (x.e - y.e) * 2 ^ p) / y.m), e := -p }

-- Instances.

instance : OfNat Dyadic n where
  ofNat := { m := n, e := 0 }

instance : HAdd Dyadic Dyadic Dyadic where
  hAdd := Add

instance : HSub Dyadic Dyadic Dyadic where
  hSub := Sub

instance : HMul Dyadic Dyadic Dyadic where
  hMul := Mul

instance : HDiv Dyadic Dyadic Dyadic where 
  hDiv := Div 10

instance : HasLessEq Dyadic where
  LessEq x y :=
  if x.e ≤ y.e
  then x.m ≤ y.m * 2 ^ (Int.toNat (y.e - x.e))
  else x.m * 2 ^ (Int.toNat (x.e - y.e)) ≤ y.m

end Dyadic

#eval 12345789101112 / (-1234578910111)

def main : IO Unit :=
let r := Dyadic.mk 12345789101112 (-100) + Dyadic.mk (-1234578910111) (-7898) 
let q := Dyadic.mk 12345789101112 (-100) / Dyadic.mk (-1234578910111) (-7898) 
timeit "test1" (IO.println (toString r)) *>
timeit "test2" (IO.println (toString q))

