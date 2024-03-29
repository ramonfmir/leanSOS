import data.matrix.basic
import linear_algebra.matrix
import linear_algebra.eigenspace

variables {γ : Type*} [fintype γ] [decidable_eq γ]
variables {μ : Type*} [fintype μ] [decidable_eq μ]
variables {R : Type*} 

open_locale big_operators
open_locale matrix

namespace matrix 

-- Properties of symmetric matrices. 

def symmetric (M : matrix γ γ R) : Prop :=
∀ i j, M i j = M j i

lemma symmetric_diagonal [ring R] (D : γ → R)
: symmetric (diagonal D) :=
begin 
  intros i j, unfold diagonal, by_cases (i = j),
  { split_ifs, { rw h, }, { exfalso, exact h_1 h.symm, }, },
  { split_ifs, { exfalso, exact h h_1.symm, }, { refl, }, },
end 

lemma symmetric_sum 
  [ring R]
  {A B : matrix γ γ R}
  (hA : symmetric A) (hB : symmetric B)
: symmetric (A + B) :=
begin
  intros i j, simp, rw [hA i j, hB i j],
end 

lemma symmetric_LDLT 
  [comm_ring R] (L : matrix γ γ R) (h : symmetric L) (D : γ → R)
: symmetric (Lᵀ ⬝ diagonal D ⬝ L) := 
begin 
  intros i j, rw ←matrix.transpose_apply (Lᵀ ⬝ diagonal D ⬝ L) j i,
  rw [matrix.transpose_mul _ L, matrix.transpose_mul Lᵀ _],
  rw [matrix.diagonal_transpose, matrix.transpose_transpose],
  rw [matrix.mul_assoc],
end 

-- Properties of the dot product.
-- TODO: to_mathlib

variable [linear_ordered_comm_ring R]

lemma dot_product_of_nonneg {v w : γ → R} (hv : 0 ≤ v) (hw : 0 ≤ w) : 0 ≤ dot_product v w :=
begin 
  simp only [dot_product], apply finset.sum_nonneg, intros x hx, 
  exact mul_nonneg (hv x) (hw x),
end 

lemma vec_mul_self_nonneg (v : γ → R) : 0 ≤ v * v :=
λ i, mul_self_nonneg (v i)

lemma dot_product_diagonal_mul_vec_eq (d v w : γ → R) :
dot_product ((diagonal d).mul_vec v) w = dot_product d (v * w) :=
begin 
  simp only [dot_product], congr, ext i, 
  rw [mul_vec_diagonal, pi.mul_apply, mul_assoc],
end 

lemma dot_product_self_nonneg (v : γ → R) : 0 ≤ dot_product v v := 
begin
  simp only [dot_product], apply finset.sum_nonneg, intros x hx, 
  exact mul_self_nonneg (v x),
end

lemma dot_product_self_eq_zero_iff (v : γ → R) : dot_product v v = 0 ↔ v = 0 :=
begin 
  have hsumz := finset.sum_eq_zero_iff_of_nonneg (λ x hx, mul_self_nonneg (v x)), split,
  { intros hdp, ext x,
    have hvx := (hsumz.1 hdp) x (finset.mem_univ x),
    exact (mul_self_eq_zero.1 hvx), },
  { intros hvz, erw hsumz, intros x hx, dsimp,
    erw [congr_fun hvz x], simp, }
end  

lemma dot_product_self_pos_of_nonzero (v : γ → R) (hvnz : v ≠ 0) : dot_product v v > 0 :=
begin
  have h1 := dot_product_self_nonneg v,
  have h2 := ne_comm.1 ((not_iff_not_of_iff (dot_product_self_eq_zero_iff v)).2 hvnz),
  exact (lt_of_le_of_ne h1 h2),
end 

lemma dot_product_transpose (v : γ → R) (K L : matrix μ γ R)
: dot_product v ((Kᵀ ⬝ L).mul_vec v) = dot_product (K.mul_vec v) (L.mul_vec v) :=
begin
  rw ←mul_vec_mul_vec, dsimp [mul_vec, dot_product], 
  have : ∑ i, (v i) * (∑ j, K j i * ∑ k, L j k * v k) = 
         ∑ i, (∑ j, (v i) * K j i * ∑ k, L j k * v k),
  { congr, ext i, rw [finset.mul_sum], congr, ext j, ring, },
  rw this,
  have : ∑ i j, v i * K j i * ∑ k, L j k * v k =
         ∑ i j k, v i * K j i * L j k * v k,
  { congr, ext i, congr, ext j, rw [finset.mul_sum], congr, ext k, ring, },
  rw this,
  have : ∑ i, (∑ j, K i j * v j) * ∑ k, L i k * v k = 
         ∑ i, (∑ j, K i j * v j * ∑ k, L i k * v k),
  { congr, ext i, rw [finset.sum_mul], },
  rw this,
  have : ∑ i j, K i j * v j * ∑ k, L i k * v k = 
         ∑ i j k, K i j * v j * L i k * v k,
  { congr, ext i, congr, ext j, rw [finset.mul_sum], congr, ext k, ring, },
  rw this,
  rw [finset.sum_comm],
  congr, ext i, congr, ext j, congr, ext k, ring,
end

end matrix 