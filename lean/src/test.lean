/-
  Testing out the tactic.
-/

import tactic.ring2
import tactic.ring
import tactic.show_term
import data.real.basic
import data.mv_polynomial.basic
import .poly .psd .sos .float

open mv_polynomial poly

-- Test intermediate steps.

-- noncomputable def p : mv_polynomial ℕ ℝ := (X 1) * (X 1)
-- noncomputable def ms : fin 1 → mv_polynomial ℕ ℝ := λ _, X 1
-- def Q : fin 1 → fin 1 → ℝ := λ _ _, 1

-- lemma Qsymmetric : matrix.symmetric Q := 
-- by prove_symmetric

-- lemma Qsymmetric2 : matrix.symmetric (λ _ _, 1 : matrix (fin 1) (fin 1) ℝ) :=
-- by prove_symmetric 

-- lemma Qmsp : p = matrix.dot_product ms (matrix.mul_vec (matrix.to_poly Q) ms) :=
-- by prove_poly_eq

-- lemma Qcholesky : @cholesky_decomposition (fin 1) _ (fin 1) _ ℝ _ Q Qsymmetric :=
-- by prove_cholesky ``(λ _ _, 1) 

-- -- Experiments with the ring tactic.

-- example : (C 1) + (C 1) = ((C 2) : mv_polynomial ℕ ℝ) := 
-- begin 
--   simp; ring,
-- end

-- example : (X 1) + (X 1) = ((C 2) * (X 1) : mv_polynomial ℕ ℝ) := 
-- begin 
--   simp; ring,
-- end

-- example : finset.univ.sum (λ x : fin 2, (C 1 : mv_polynomial ℕ ℚ)) = C 2 :=
-- begin 
--   simp,
-- end  

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

#check real.of_cauchy

set_option timeout 1000000

#eval if ((C (float.mk2 1 0)) = (1 : mv_polynomial ℕ float)) then 0 else 1

#eval if ((C (1 : ℝ)) = (1 : mv_polynomial ℕ ℝ)) then 0 else 1

example : (C (rat.of_int 1 : ℚ)) = (1 : mv_polynomial ℕ ℚ) :=
begin 
  refl,
end 

example : (C (float.mk ⟨1, 0⟩)) = (1 : mv_polynomial ℕ float) :=
begin 
  show_term { refl, }
end 

example : (C (1 : ℝ)) * (X 1) = (X 1 : mv_polynomial ℕ ℝ) :=
begin 
  simp,
end 

example {α} [linear_ordered_comm_ring α] 
: (C (1 : α)) * (X 1) = (X 1 : mv_polynomial ℕ α) :=
begin 
  show_term { simp, }
end 

example : (C (rat.of_int 1 : ℚ)) * (X 1) = (X 1 : mv_polynomial ℕ ℚ) :=
begin 
  simp, sorry,
end 

example : (C (1 : float)) * (X 1) = (X 1 : mv_polynomial ℕ float) :=
begin 
  simp,
end 

example : (1 : float) • (X 1) = (X 1 : mv_polynomial ℕ float) :=
begin 
  show_term {
  simp, }
end 

#check one_smul

example : C (1 + 0) * (X 1) = (X 1 : mv_polynomial ℕ ℚ) :=
begin
  simp,
end 

@[simp] lemma avo : float.mk ⟨1, 0⟩ = 1 := rfl

example : (C (float.mk ⟨1, 0⟩)) * (X 1) = (X 1 : mv_polynomial ℕ float) :=
begin 
  simp,
end 

example : (rat.of_int 1) + (rat.of_int 2) = rat.of_int 3 :=
begin 
  simp [rat.of_int], ring,
end 

@[simp] theorem add_def (a b c d : ℤ)
: (float.mk ⟨a, b⟩) + (float.mk ⟨c, d⟩) =
float.mk (if b ≤ d 
then ⟨a + c * 2 ^ int.to_nat (d - b), b⟩ 
else ⟨c + a * 2 ^ int.to_nat (b - d), d⟩ ) :=
begin 
  sorry,
end  

example : (float.mk ⟨1, -1⟩) + (float.mk ⟨3, -1⟩) = float.mk ⟨2, 0⟩ :=
begin 
  simp [add_def], split_ifs; try {contradiction}, simp [float.mk], show to_rat _ = _,
  simp [to_rat], norm_num, 
end 

example : 
(C (float.mk ⟨1, 1⟩)) * (X 1) + (C (float.mk ⟨3, 1⟩)) * (X 1) 
= (C (float.mk ⟨2, 0⟩)) * (X 1 : mv_polynomial ℕ float) :=
begin 
  simp, ring,
end 

-- Test whole thing.

-- set_option trace.app_builder true
-- set_option timeout 1000000

#eval if (1 : ℕ) = 2 then 1 else 0
#eval if (((C (float.mk2 1 0)) : mv_polynomial ℕ float) = (C (1 : float))) then 1 else 0



-- 0 ≤ x^2
example : (C (0 : float)) ≤ (X 1) * (X 1) := 
begin 
  sos,
  { simp [matrix.dot_product, matrix.mul_vec, matrix.to_poly],
    simp only [matrix.map, list.map, list.foldl, float.mk, list_to_vector, 
    list_to_monomials, list_to_matrix, list_to_monomial, fin.sum_univ_succ], dsimp,
    ring, sorry, },
  sorry,
end 

-- 0 ≤ x^2 + 2xy + y^2
example : (C (0 : ℚ)) ≤ (((X 1) * (X 1)) + ((C 2) * (X 1) * (X 2)) + ((X 2) * (X 2)) : mv_polynomial ℕ ℚ) :=
begin
  --sos,
  sorry, 
end 

-- 0 ≤ 1 + x + x^2 ([[1,1/2],[1,1/2]])

