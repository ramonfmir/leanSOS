import data.real.basic
import data.matrix.basic
import linear_algebra.matrix
import linear_algebra.eigenspace

-- Check src/linear_algebra/quadratic_form

variables {γ : Type*} [fintype γ]

namespace matrix 

def symmetric (M : matrix γ γ ℝ) : Prop :=
∀ i j, M i j = M j i

lemma dot_product_self_nonneg (v : γ → ℝ) : dot_product v v ≥ 0 := 
begin
  apply finset.sum_nonneg, intros x hx, exact mul_self_nonneg (v x),
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
  { rintros hpsd r x ⟨hxnz, hre⟩, by_contra hc, rw [mem_eigenspace_iff] at hre,
    replace hpsd := hpsd x,
    replace hre := congr_arg (λ y, dot_product y x) hre; simp at hre,
    replace hc := lt_of_not_ge hc,
    suffices hsuff : r * dot_product x x < 0,
    { rw [←hre] at hsuff, exact ((not_le_of_lt hsuff) hpsd), },
    apply mul_neg_of_neg_of_pos hc, rw [hre] at hpsd, exfalso,
    have hdp := dot_product_self_pos_of_nonzero x hxnz,
    have hc' := mul_neg_of_pos_of_neg hdp hc, rw [mul_comm] at hc',
    exact ((not_le_of_gt hc') hpsd), },
  { intros hnne, sorry, },
end 

