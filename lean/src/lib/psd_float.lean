import to_mathlib.matrix float.basic lib.psd 

-- We have A ∈ 𝒮(𝔽)ⁿˣⁿ. 

open matrix
open_locale matrix

variables (n : nat) (A : matrix (fin n) (fin n) float) (h : symmetric A)

theorem psd_of_ldlt 
  (L : matrix (fin n) (fin n) float)
  (hL : symmetric L)
  (D : fin n → float)
  (hD : 0 ≤ D)
  (hij : ∀ i j, i ≠ j → (Lᵀ ⬝ diagonal D ⬝ L) i j = A i j)
  (hii : ∀ i, 0 ≤ (A - (Lᵀ ⬝ diagonal D ⬝ L)) i i) 
: pos_semidef A h :=
begin 
  have hLDLTpsd := 
    pos_semidef_of_LDLT_decomposition (Lᵀ ⬝ diagonal D ⬝ L) (symmetric_LDLT L hL D) ⟨L, D, ⟨rfl, hD⟩⟩,
  have hDnn : (0 : fin n → float) ≤ (λ i, (A - Lᵀ ⬝ diagonal D ⬝ L) i i),
  { rw pi.le_def, intros i, exact hii i, },
  have hdA : (A - Lᵀ ⬝ diagonal D ⬝ L) = diagonal (λ i, (A - Lᵀ ⬝ diagonal D ⬝ L) i i),
  { ext i j, by_cases (i = j),
    { rw h, simp [diagonal], },
    { have hijij := (hij i j h).symm, rw ←sub_eq_zero at hijij, 
      rw [diagonal_apply_ne h, ←hijij], simp, }, },
  have hdApsd : pos_semidef (A - Lᵀ ⬝ diagonal D ⬝ L) sorry,
  { sorry, },
  have hA : A = Lᵀ ⬝ diagonal D ⬝ L + (A - Lᵀ ⬝ diagonal D ⬝ L),
  { simp, },
  sorry,
  --exact pos_semidef_sum 
end
