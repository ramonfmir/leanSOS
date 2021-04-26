/-
  Testing out the tactic.
-/

import tactic.ring2
import tactic.ring
import data.real.basic
import data.mv_polynomial.basic
import .poly .psd .sos .float

open mv_polynomial poly

-- Test intermediate steps.

noncomputable def p : mv_polynomial ℕ ℝ := (X 1) * (X 1)
noncomputable def ms : fin 1 → mv_polynomial ℕ ℝ := λ _, X 1
def Q : fin 1 → fin 1 → ℝ := λ _ _, 1

lemma Qsymmetric : matrix.symmetric Q := 
by prove_symmetric

lemma Qsymmetric2 : matrix.symmetric (λ _ _, 1 : matrix (fin 1) (fin 1) ℝ) :=
by prove_symmetric 

lemma Qmsp : p = matrix.dot_product ms (matrix.mul_vec (matrix.to_poly Q) ms) :=
by prove_poly_eq

lemma Qcholesky : @cholesky_decomposition (fin 1) _ (fin 1) _ ℝ _ Q Qsymmetric :=
by prove_cholesky ``(λ _ _, 1) 

-- Experiments with the ring tactic.

example : (C 1) + (C 1) = ((C 2) : mv_polynomial ℕ ℝ) := 
begin 
  simp; ring,
end

example : (X 1) + (X 1) = ((C 2) * (X 1) : mv_polynomial ℕ ℝ) := 
begin 
  simp; ring,
end

example : finset.univ.sum (λ x : fin 2, (C 1 : mv_polynomial ℕ ℚ)) = C 2 :=
begin 
  simp,
end  

-- example : 
--   ((X 1) * (X 1) + (C 2) * (X 1) * (X 2) + (X 2) * (X 2) : mv_polynomial ℕ ℚ)
--   = matrix.dot_product 
--     (list_to_vector 2 (list_to_monomials [[1], [2]]) (by simp)) 
--     ((matrix.to_poly 
--       (list_to_matrix 2 2 [[1, 1], [1, 1]] (by simp) (λ i, by fin_cases i; simp)) 
--       : matrix (fin 2) (fin 2) (mv_polynomial ℕ ℚ)).mul_vec 
--     (list_to_vector 2 (list_to_monomials [[1], [2]]) (by simp))) :=
-- begin 
--   prove_poly_eq,
-- end 

-- Test whole thing.

set_option trace.app_builder true
set_option timeout 1000000

-- 0 ≤ x^2
example : (C (0 : float)) ≤ (X 1) * (X 1) := 
begin 
  sos,
  { simp [matrix.dot_product, matrix.mul_vec, matrix.to_poly],
    simp [matrix.map, float.mk, list_to_vector, list_to_monomials, list_to_matrix, list_to_monomial, fin.sum_univ_succ], 
    ring!, },
end 

-- 0 ≤ x^2 + 2xy + y^2
example : (C (0 : ℚ)) ≤ (((X 1) * (X 1)) + ((C 2) * (X 1) * (X 2)) + ((X 2) * (X 2)) : mv_polynomial ℕ ℚ) :=
begin
  --sos,
  sorry, 
end 

