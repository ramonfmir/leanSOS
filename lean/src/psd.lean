import data.real.basic
import data.matrix.basic
import linear_algebra.matrix
import linear_algebra.eigenspace

-- Check src/linear_algebra/quadratic_form

variables {γ : Type*} [fintype γ]

namespace matrix 

def symmetric (M : matrix γ γ ℝ) : Prop :=
∀ i j, M i j = M j i

lemma dot_product_same_nonneg (v : γ → ℝ) : dot_product v v ≥ 0 := 
sorry

end matrix 

open matrix module.End

def pos_semidef (M : matrix γ γ ℝ) (h : symmetric M) : Prop :=
∀ (v : γ → ℝ), dot_product (mul_vec M v) v ≥ 0

def nonneg_eigenvalues (M : matrix γ γ ℝ) (h : symmetric M) : Prop :=
∀ r x, has_eigenvector (mul_vec_lin M) r x → r ≥ 0

lemma pos_semidef_iff_nonneg_eigenvalues : 
∀ (M : matrix γ γ ℝ) (h : symmetric M), pos_semidef M h ↔ nonneg_eigenvalues M h :=
begin
  intros M h, split,
  { rintros hpsd r x ⟨hxnez, hre⟩, by_contra hc, rw [mem_eigenspace_iff] at hre,
    replace hpsd := hpsd x,
    replace hre := congr_arg (λ y, dot_product y x) hre; simp at hre,
    suffices hsuff : r * dot_product x x < 0,
    { rw [←hre] at hsuff, exact ((not_le_of_lt hsuff) hpsd), },
    apply mul_neg_of_neg_of_pos,
    { sorry, },
    { sorry, }, },
  { intros hnne, sorry, },
end 

