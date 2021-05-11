import Init.Core
import Init.Data.Int

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
  else { m := x.m * 2 ^ (Int.toNat (x.e - y.e)) + y.e, e := y.e }

def Sub : Dyadic → Dyadic → Dyadic := fun x y =>
  Add x (Neg y)

def Mul : Dyadic → Dyadic → Dyadic :=
  fun x y => { m := x.m * y.m, e := x.e + y.e }

-- Instances.

instance : OfNat Dyadic n where
  ofNat := { m := n, e := 0 }

instance : HAdd Dyadic Dyadic Dyadic where
  hAdd := Add

instance : HSub Dyadic Dyadic Dyadic where
  hSub := Sub

instance : HMul Dyadic Dyadic Dyadic where
  hMul := Mul

instance : HasLessEq Dyadic where
  LessEq x y :=
  if x.e ≤ y.e
  then x.m ≤ y.m * 2 ^ (Int.toNat (y.e - x.e))
  else x.m * 2 ^ (Int.toNat (x.e - y.e)) ≤ y.m

-- Lemmas.

theorem mul_same_nonneg (x : Dyadic) : 0 ≤ x * x := sorry 
theorem add_nonneg_of_nonneg {x y : Dyadic} (hx : 0 ≤ x) (hy : 0 ≤ y) : 0 ≤ x + y := sorry

-- theorem mul_nonneg_of_nonneg (x y : Dyadic) (hx : 0 ≤ x) (hy : 0 ≤ y) : 0 ≤ x * y := sorry 

-- theorem zero_mul (a : Int) : 0 * a = 0 := sorry
-- theorem nonneg_of_mul_pow {a : Int} {e : Nat} (h : 0 ≤ a * 2 ^ e) : 0 ≤ a := sorry
-- theorem nonneg_mul_pow_of_nonneg {a : Int} (e : Nat) (h : 0 ≤ a) : 0 ≤ a * 2 ^ e := sorry

-- theorem nonneg_iff_mantissa_nonneg (x : Dyadic) : 0 ≤ x ↔ 0 ≤ x.m :=
--   Iff.intro
--   (fun h =>
--     if he : (0 : Dyadic).e ≤ x.e 
--     then by { 
--       simp [LessEq] at h
--       erw [ifPos he] at h
--       exact nonneg_of_mul_pow h } 
--     else by { 
--       simp [LessEq] at h
--       erw [ifNeg he] at h
--       simp at he
--       erw [zero_mul] at h
--       exact h
--      })
--   (fun h => 
--     if he : (0 : Dyadic).e ≤ x.e 
--     then by { 
--       simp [LessEq]
--       erw [ifPos he];
--       exact nonneg_mul_pow_of_nonneg _ h }
--     else by {
--       simp [LessEq]
--       erw [ifNeg he, zero_mul];
--       exact h
--     })

end Dyadic
