import Init.Data.Nat
import SOS.Dyadic

inductive Poly
| C : Dyadic → Poly
| X : Fin 3 → Poly
| Mul : Poly → Poly → Poly
| Add : Poly → Poly → Poly

namespace Poly 

syntax "X[" term "]" : term
syntax "C[" term "]" : term
macro_rules 
  | `(C[$c]) => `(C $c)
  | `(X[$n]) => `(X $n)

def toString : Poly → String 
| C f => ToString.toString f
| X i => s!"x{i}"
| Mul p q => s!"{toString p} * {toString q}"
| Add p q => s!"{toString p} + {toString q}"

instance : ToString Poly where 
  toString := toString

-- instance : Repr Poly where 
--   reprPrec p n := toString p

instance : OfNat Poly n where 
  ofNat := C[0]

instance : HAdd Poly Poly Poly where 
  hAdd := Add

instance : HMul Poly Poly Poly where 
  hMul := Mul

def Eval (v : Fin 3 → Dyadic) : Poly → Dyadic 
| C f => f 
| X i => v i 
| Mul p q => (Eval v p) * (Eval v q)
| Add p q => (Eval v p) + (Eval v q)

def Reduce : Poly → Poly 
| C f => C f 
| X i => X i 
| Mul (C f) (C g) => C (f * g)
| Mul (X i) (C f) => Mul (C f) (X i) 
| Mul (X i) (X j) => if i ≤ j then Mul (X i) (X j) else Mul (X j) (X i)
| Mul (Add p q) r => Add (Mul (Reduce p) (Reduce r)) (Mul (Reduce q) (Reduce r))
| Mul p (Add q r) => Add (Mul (Reduce p) (Reduce q)) (Mul (Reduce p) (Reduce r))
| Mul p q => Mul (Reduce p) (Reduce q)
| Add p q => Add (Reduce p) (Reduce q)

instance : HasLessEq Poly where 
  LessEq p q := ∀ (v : Fin 3 → Dyadic), Eval v p ≤ Eval v q

theorem mul_same_nonneg (p : Poly) : 0 ≤ p * p := by 
  intro v; simp [Eval] at *; exact Dyadic.mul_same_nonneg _

theorem add_nonneg_of_nonneg {p q : Poly} (hp : 0 ≤ p) (hq : 0 ≤ q) : 0 ≤ p + q := by 
  intro v; simp [Eval] at *; exact Dyadic.add_nonneg_of_nonneg (hp v) (hq v)

end Poly

inductive SOSPoly
| Sqr : Poly → SOSPoly
| Add : SOSPoly → SOSPoly → SOSPoly

namespace SOSPoly

def ToPoly : SOSPoly → Poly
| Sqr p => Poly.Mul p p 
| Add p q => Poly.Add (ToPoly p) (ToPoly q)

theorem sos_nonneg (s : SOSPoly) : 0 ≤ ToPoly s := by 
  induction s;
  { simp [ToPoly]; exact Poly.mul_same_nonneg _ }
  { simp [ToPoly]; exact Poly.add_nonneg_of_nonneg (by assumption) (by assumption) }

end SOSPoly
