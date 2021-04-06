import data.real.basic
import data.mv_polynomial.basic
import .sos

open mv_polynomial 

instance {σ R} [comm_semiring R] [has_le R] : has_le (mv_polynomial σ R) :=
{ le := λ p q, ∀ v, eval v p ≤ eval v q }

noncomputable def square_polys : list (mv_polynomial ℕ ℝ) → list (mv_polynomial ℕ ℝ) :=
λ l, list.map (λ q, q * q) l

noncomputable def sum_polys : list (mv_polynomial ℕ ℝ) → mv_polynomial ℕ ℝ :=
λ l, list.foldl (+) 0 l

def is_sos (p : mv_polynomial ℕ ℝ) : Prop :=
∃ l, p = sum_polys (square_polys l)

lemma nonneg_of_sos (p : mv_polynomial ℕ ℝ) : is_sos p → 0 ≤ p := 
begin 
  sorry,
end 

example : (C (0 : ℝ)) ≤ (X 5) * (X 1):= begin 
  sos, sorry,
end 