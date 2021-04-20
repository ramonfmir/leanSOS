/-
  Testing out the tactic.
-/

import data.real.basic
import data.mv_polynomial.basic
import .poly .psd .sos

open mv_polynomial poly

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

lemma Qcholesky : @cholesky_decomposition (fin 1) _ (fin 1) _ ℝ _ Q Qsymmetric :=
by prove_cholesky ``(λ _ _, 1)

-- Test whole thing.

example : (C (0 : ℝ)) ≤ (X 1) * (X 1):= begin 
  sorry,
end 

-- Trying to help ring with some extra lemmas.#check

example : finset.univ.sum (λ x : fin 2, (C 1 : mv_polynomial ℕ ℚ)) = C 2 :=
begin 
  sorry, --try_for 100000 { ring },
end  

#check finset.attach_fin
#check @finset.sum_insert 
#check fin.eq_insert_nth_iff
#check finset.univ

--lemma insert_fin (n : ℕ) : insert (finset.univ : finset (fin n)) n = (finset.univ (finset ))

#check fin.cast_succ.to_embedding
#print fin

lemma finset_sum_succ {R} [comm_ring R] (n : ℕ) (f : fin (n + 1) → R) 
: finset.univ.sum (λ i : fin (n + 1), f i) 
= (f n) + (finset.map fin.cast_succ.to_embedding (finset.univ : finset (fin n))).sum (λ i : fin (n + 1), f i) := 
begin 
  --apply finset.sum_insert,
  sorry,
end 

example : 
  ((X 1) * (X 1) + (C 2) * (X 1) * (X 2) + (X 2) * (X 2) : mv_polynomial ℕ ℚ)
  = matrix.dot_product 
    (list_to_vector 2 (list_to_monomials [[1], [2]]) (by simp)) 
    ((matrix.to_poly 
      (list_to_matrix 2 2 [[1, 1], [1, 1]] (by simp) (λ i, by fin_cases i; simp)) 
      : matrix (fin 2) (fin 2) (mv_polynomial ℕ ℚ)).mul_vec 
    (list_to_vector 2 (list_to_monomials [[1], [2]]) (by simp))) :=
begin 
  simp [
      matrix.dot_product, matrix.mul_vec, matrix.to_poly,
      list_to_vector, list_to_monomials, list_to_matrix, list_to_monomial
  ],
  sorry,
end 
