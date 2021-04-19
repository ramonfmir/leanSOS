/-
  Results about matrices, PSD, etc.
-/
import data.real.basic
import data.matrix.basic
import linear_algebra.matrix
import linear_algebra.eigenspace

-- Check src/linear_algebra/quadratic_form

variables {γ : Type*} [fintype γ] 
variables {μ : Type*} [fintype μ]
variables {R : Type*}

open_locale big_operators

namespace matrix 

-- Properties of symmetric matrices. 

def symmetric (M : matrix γ γ R) : Prop :=
∀ i j, M i j = M j i

-- Properties of the dot product.

variable [linear_ordered_comm_ring R]

lemma dot_product_self_nonneg (v : γ → R) : 0 ≤ dot_product v v := 
begin
  simp [dot_product], apply finset.sum_nonneg, intros x hx, exact mul_self_nonneg (v x),
end

lemma dot_product_self_eq_zero_iff (v : γ → ℝ) : dot_product v v = 0 ↔ v = 0 :=
begin 
  have hsumz := finset.sum_eq_zero_iff_of_nonneg (λ x hx, mul_self_nonneg (v x)), split,
  { intros hdp, ext x,
    have hvx := (hsumz.1 hdp) x (finset.mem_univ x),
    exact (mul_self_eq_zero.1 hvx), },
  { intros hvz, erw hsumz, intros x hx, dsimp,
    erw [congr_fun hvz x], simp, }
end  

lemma dot_product_self_pos_of_nonzero (v : γ → ℝ) (hvnz : v ≠ 0) : dot_product v v > 0 :=
begin
  have h1 := dot_product_self_nonneg v,
  have h2 := ne_comm.1 ((not_iff_not_of_iff (dot_product_self_eq_zero_iff v)).2 hvnz),
  exact (lt_of_le_of_ne h1 h2),
end 

lemma dot_product_transpose (v : γ → R) (L : matrix μ γ R)
: dot_product v ((L.transpose.mul L).mul_vec v) = dot_product (L.mul_vec v) (L.mul_vec v) :=
begin
  rw ←mul_vec_mul_vec, dsimp [mul_vec, dot_product], 
  have : ∑ i, (v i) * (∑ j, L j i * ∑ k, L j k * v k) = 
         ∑ i, (∑ j, (v i) * L j i * ∑ k, L j k * v k),
  { congr, ext i, rw [finset.mul_sum], congr, ext j, ring, },
  rw this,
  have : ∑ i j, v i * L j i * ∑ k, L j k * v k =
         ∑ i j k, v i * L j i * L j k * v k,
  { congr, ext i, congr, ext j, rw [finset.mul_sum], congr, ext k, ring, },
  rw this,
  have : ∑ i, (∑ j, L i j * v j) * ∑ k, L i k * v k = 
         ∑ i, (∑ j, L i j * v j * ∑ k, L i k * v k),
  { congr, ext i, rw [finset.sum_mul], },
  rw this,
  have : ∑ i j, L i j * v j * ∑ k, L i k * v k = 
         ∑ i j k, L i j * v j * L i k * v k,
  { congr, ext i, congr, ext j, rw [finset.mul_sum], congr, ext k, ring, },
  rw this,
  rw [finset.sum_comm],
  congr, ext i, congr, ext j, congr, ext k, ring,
end

end matrix 

open matrix module.End

-- Equivalent conditions to positive semidefiniteness.

variable [linear_ordered_comm_ring R]

def cholesky_decomposition (M : matrix γ γ R) (h : symmetric M) : Prop :=
∃ L : matrix μ γ R, M = matrix.mul L.transpose L

def pos_semidef (M : matrix γ γ R) (h : symmetric M) : Prop :=
∀ (v : γ → R), dot_product v (mul_vec M v) ≥ 0

def nonneg_eigenvalues (M : matrix γ γ R) (h : symmetric M) : Prop :=
∀ r x, has_eigenvector (mul_vec_lin M) r x → r ≥ 0

theorem pos_semidef_of_cholesky_decomposition (M : matrix γ γ R) (h : symmetric M) 
: @cholesky_decomposition γ _ μ _ R _ M h → pos_semidef M h :=
begin 
  rintros ⟨L, hL⟩ v, rw hL, rw [dot_product_transpose],
  exact dot_product_self_nonneg _,
end 
