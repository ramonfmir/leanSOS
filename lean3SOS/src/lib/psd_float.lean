import to_mathlib.matrix float.basic float.div lib.psd 

-- We have A ∈ 𝒮(𝔽)ⁿˣⁿ. 

open matrix float
open_locale matrix big_operators

variables (n : nat) (A : matrix (fin n) (fin n) float) (h : symmetric A)

theorem psd_of_ldlt 
  (L : matrix (fin n) (fin n) float)
  (hL : symmetric L)
  (D : fin n → float)
  (hD : 0 ≤ D)
  (hij : ∀ i j, i ≠ j → (Lᵀ ⬝ diagonal D ⬝ L) i j = A i j)
  (hii : ∀ i, 0 ≤ (A - (Lᵀ ⬝ diagonal D ⬝ L)) i i) 
: pos_semidef A :=
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
  have hdAsymm : symmetric (A - Lᵀ ⬝ diagonal D ⬝ L),
  { rw hdA, exact symmetric_diagonal _, },
  have hdApsd : pos_semidef (A - Lᵀ ⬝ diagonal D ⬝ L),
  { rw hdA, exact pos_semidef_nonneg_diagonal hDnn, },
  have hA : A = Lᵀ ⬝ diagonal D ⬝ L + (A - Lᵀ ⬝ diagonal D ⬝ L),
  { simp, },
  rw hA, exact pos_semidef_sum hLDLTpsd hdApsd,
end

-- PLAN:
-- 1. Define diagonally dominant.
-- 2. Prove that diagonally dominant + nonnegative entries implies psd.
-- 3. This will show that dA' = A' - LᵀDL is psd where A' = A - cI.
-- 4. Now we have on the one hand that A' = LᵀDT + dA' is psd by sum of psds. 
-- 5. Similarly, A = A' + cI is psd by sum of psds. So last theorem not needed?

-- Lift eval to vectors and matrices.

def eval_vec (x : fin n → float) : fin n → ℚ := λ i, eval (x i) 

def eval_mat (M : matrix (fin n) (fin n) float) : matrix (fin n) (fin n) ℚ := λ i j, eval (M i j)

-- Norms.

def rat_norm (x : fin n → ℚ) : ℚ := ∑ i, abs (x i)

def rat_normalised (x : fin n → float) : fin n → ℚ := λ i, eval (x i) / (rat_norm n (eval_vec n x))

lemma eval_vec_eq_zero_iff (x : fin n → float) : eval_vec n x = 0 ↔ x = 0 :=
begin 
  sorry,
end 

lemma rat_norm_eq_zero_iff (x : fin n → ℚ) : rat_norm n x = 0 ↔ x = 0 :=
begin 
  sorry,
end 

lemma abs_nonneg_finsum (x : fin n → ℚ) (h : ∀ i, 0 ≤ x i) : abs (∑ i, x i) = ∑ i, x i :=
begin 
  apply finset.sum_induction x (λ r, abs r = r),
  { intros a b ha hb, 
    have hab : abs (a + b) = abs a + abs b,
    { rw abs_add_eq_add_abs_iff, left, split, 
      { exact abs_eq_self.1 ha, },
      { exact abs_eq_self.1 hb, }, },
    rw hab, congr, exact ha, exact hb, },
  { exact abs_zero, },
  { intros i hi, exact abs_eq_self.2 (h i), }
end  

lemma abs_rat_norm (x : fin n → ℚ) : abs (rat_norm n x) = rat_norm n x :=
begin 
  apply abs_nonneg_finsum, intros i, exact abs_nonneg (x i),
end 

-- TODO: Move (rat/order)
lemma rat.abs_div (p q : rat) : abs (p / q) = abs p / abs q :=
begin
  by_cases hpz : p = 0, { rw hpz, simp, }, 
  by_cases hqz : q = 0, { rw hqz, simp, },
  have hpc : 0 < p ∨ 0 > p, 
  { cases le_or_lt p 0, { right, exact lt_of_le_of_ne h hpz, }, { left, exact h, }, }, 
  have hqc : 0 < q ∨ 0 > q, 
  { cases le_or_lt q 0, { right, exact lt_of_le_of_ne h hqz, }, { left, exact h, }, }, 
  cases hpc with hp hp; cases hqc with hq hq,
  { rw [abs_of_pos hp, abs_of_pos hq, abs_of_pos (div_pos hp hq)], },
  { rw [abs_of_pos hp, abs_of_neg hq, abs_of_neg (div_neg_of_pos_of_neg hp hq), div_neg], },
  { rw [abs_of_neg hp, abs_of_pos hq, abs_of_neg (div_neg_of_neg_of_pos hp hq), neg_div], },
  { rw [abs_of_neg hp, abs_of_neg hq, abs_of_pos (div_pos_of_neg_of_neg hp hq), neg_div_neg_eq], },
end 

lemma normalised_norm_one (x : fin n → float) (hx : x ≠ 0) : rat_norm n (rat_normalised n x) = 1 :=
begin 
  unfold rat_norm, unfold rat_normalised,
  have hsum : ∑ i, abs ((x i).eval / rat_norm n (eval_vec n x)) = 
              ∑ i, abs ((x i).eval) / abs (rat_norm n (eval_vec n x)),
  { congr, ext i, rw rat.abs_div, },
  have hex := (not_iff_not_of_iff (eval_vec_eq_zero_iff n x)).mpr hx,
  have hrex := (not_iff_not_of_iff (rat_norm_eq_zero_iff n (eval_vec n x))).mpr hex,
  rw [hsum, ←finset.sum_div, abs_rat_norm, div_eq_one_iff_eq hrex],
  simp [rat_norm, eval_vec],
end 

-- PSD stuff.

-- First show that if eval M is psd then M is psd.

lemma pos_semidef_of_eval (M : matrix (fin n) (fin n) float) (h : pos_semidef (eval_mat n M))
: pos_semidef M := 
begin 
  intros v, have hv := h (eval_vec n v), sorry,
end 

def pos_semidef_unit (M : matrix (fin n) (fin n) float) : Prop :=
∀ (v : fin n → float), rat_norm n (eval_vec n v) = 1 → 0 ≤ dot_product v (M.mul_vec v)

lemma pos_semidef_of_unit (M : matrix (fin n) (fin n) float) (h : pos_semidef_unit n M)
: pos_semidef M :=
begin 
  intros v, sorry,
end 

-- lemma psd_of_nonneg_diagonally_dominant 
--   (hnonneg : ∀ i j, 0 ≤ A i j) 
--   (hdiagdom : ∀ i, A i i ≤ ∑ (j : fin n) (h : i ≠ j), A i j) 


-- With unit vectors.

