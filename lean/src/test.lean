import data.real.basic
import data.mv_polynomial.basic
import .sos

open mv_polynomial

instance {σ R} [comm_semiring R] [has_le R] : has_le (mv_polynomial σ R) :=
{ le := λ p q, ∀ v, eval v p ≤ eval v q }

example : (C (0 : ℝ)) ≤ (X 5) * (X 1):= begin 
  sos, sorry,
end 