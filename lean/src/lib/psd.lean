/-
  Results about matrices, PSD, etc.
-/
import data.real.basic
import data.matrix.basic
import linear_algebra.matrix
import linear_algebra.eigenspace
import to_mathlib.matrix

variables {γ : Type*} [fintype γ] [decidable_eq γ]
variables {μ : Type*} [fintype μ] [decidable_eq μ]
variables {R : Type*} 

open_locale big_operators
open_locale matrix

open matrix module.End

-- Positive semidefiniteness.

variable [linear_ordered_comm_ring R]

def pos_semidef (M : matrix γ γ R) (h : symmetric M) : Prop :=
∀ (v : γ → R), 0 ≤ dot_product v (M.mul_vec v)

theorem pos_semidef_sum 
  (A B : matrix γ γ R) 
  (hAsymm : symmetric A) (hBsymm : symmetric B)
  (hApsd : pos_semidef A hAsymm) (hBpsd : pos_semidef B hBsymm)
: pos_semidef (A + B) (symmetric_sum hAsymm hBsymm) :=
begin
  intros v, rw [matrix.add_mul_vec, dot_product_add],
  exact add_nonneg (hApsd v) (hBpsd v),
end 

-- Cholesky.

def cholesky_decomposition (M : matrix γ γ R) (h : symmetric M) : Prop :=
∃ L : matrix μ γ R, M = Lᵀ ⬝ L

theorem pos_semidef_of_cholesky_decomposition (M : matrix γ γ R) (h : symmetric M) 
: @cholesky_decomposition γ _ _ μ _ _ R _ M h → pos_semidef M h :=
begin 
  rintros ⟨L, hL⟩ v, rw hL, rw [dot_product_transpose],
  exact dot_product_self_nonneg _,
end 

-- LDLT.

-- TODO: This is technically LTDL...
def LDLT_decomposition (M : matrix γ γ R) (h : symmetric M) : Prop :=
∃ (L : matrix γ γ R) (D : γ → R), M = Lᵀ ⬝ (diagonal D) ⬝ L ∧ 0 ≤ D 

theorem pos_semidef_of_LDLT_decomposition (M : matrix γ γ R) (h : symmetric M) 
: LDLT_decomposition M h → pos_semidef M h :=
begin
  rintros ⟨L, D, hLDLT, hD⟩ v, 
  rw [hLDLT, matrix.mul_assoc, dot_product_transpose], 
  rw [←mul_vec_mul_vec, dot_product_comm, dot_product_diagonal_mul_vec_eq],
  exact (dot_product_of_nonneg hD (vec_mul_self_nonneg _)),
end

-- Nonnegative eigenvalues.

def nonneg_eigenvalues (M : matrix γ γ R) (h : symmetric M) : Prop :=
∀ r, has_eigenvalue (mul_vec_lin M) r → r ≥ 0
