/-
  Testing out the tactic.
-/

import data.real.basic
import data.mv_polynomial.basic
import .sos

open mv_polynomial

-- Test intermediate steps.

noncomputable def p : mv_polynomial ℕ ℝ := (X 1) * (X 1)
noncomputable def ms : fin 1 → mv_polynomial ℕ ℝ := λ _, X 1
def Q : fin 1 → fin 1 → ℝ := λ _ _, 1

lemma Qsymmetric : matrix.symmetric Q := 
by prove_symmetric

lemma Qsymmetric2 : matrix.symmetric (λ _ _, 3 : matrix (fin 1) (fin 1) ℝ) :=
by prove_symmetric 

lemma Qmsp : p = matrix.dot_product ms (matrix.mul_vec (matrix.to_poly Q) ms) :=
by prove_poly_eq

lemma Qcholesky : cholesky_decomposition Q Qsymmetric :=
by prove_cholesky ``(λ _ _, 1)

-- Test whole thing.

example : (C (0 : ℝ)) ≤ (X 1) * (X 1):= begin 
  sos, 
  sorry,
end 