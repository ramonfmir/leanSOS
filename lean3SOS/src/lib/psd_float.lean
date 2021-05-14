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

lemma rat_norm_nonneg (x : fin n → ℚ) : 0 ≤ rat_norm n x :=
begin
  apply finset.sum_nonneg, intros i hi, exact abs_nonneg (x i),
end 

def rat_normalised (x : fin n → ℚ) : fin n → ℚ := λ i, (x i) / (rat_norm n x)

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

lemma normalised_norm_one (x : fin n → ℚ) (hx : x ≠ 0) : rat_norm n (rat_normalised n x) = 1 :=
begin 
  unfold rat_norm, unfold rat_normalised,
  have hsum : ∑ i, abs ((x i) / rat_norm n x) = 
              ∑ i, abs (x i) / abs (rat_norm n x),
  { congr, ext i, rw rat.abs_div, },
  --have hex := (not_iff_not_of_iff (eval_vec_eq_zero_iff n x)).mpr hx,
  have hrex := (not_iff_not_of_iff (rat_norm_eq_zero_iff n x)).mpr hx,
  rw [hsum, ←finset.sum_div, abs_rat_norm, div_eq_one_iff_eq hrex],
  simp [rat_norm, eval_vec],
end 

-- PSD stuff.

-- First show that if eval M is psd then M is psd.

lemma dot_product_eval (v w : fin n → float) 
: dot_product (eval_vec n v) (eval_vec n w) = eval (dot_product v w) :=
begin 
  sorry,
end 

lemma mul_vec_eval (M : matrix (fin n) (fin n) float) (v : fin n → float)
: (eval_mat n M).mul_vec (eval_vec n v) = eval_vec n (M.mul_vec v) :=
begin 
  sorry,
end 

lemma pos_semidef_of_eval (M : matrix (fin n) (fin n) float) (h : pos_semidef (eval_mat n M))
: pos_semidef M := 
begin 
  intros v, have hv := h (eval_vec n v), rw [mul_vec_eval, dot_product_eval] at hv,
  show eval _ ≤ _, rw [eval_zero], exact hv,
end 

lemma float_pos_semidef_eval (M : matrix (fin n) (fin n) float) (h : pos_semidef M) 
: ∀ (v : fin n → float), 0 ≤ dot_product (eval_vec n v) ((eval_mat n M).mul_vec (eval_vec n v)) :=
begin 
  intros v, rw [mul_vec_eval, dot_product_eval, ←eval_zero], exact (h v),
end

def pos_semidef_unit (M : matrix (fin n) (fin n) float) : Prop :=
∀ (v : fin n → ℚ), rat_norm n v = 1 → 0 ≤ dot_product v ((eval_mat n M).mul_vec v)

lemma pos_semidef_of_unit (M : matrix (fin n) (fin n) float) (h : pos_semidef_unit n M)
: pos_semidef M :=
begin 
  suffices hsuff : pos_semidef (eval_mat n M),
  { exact pos_semidef_of_eval n M hsuff, },
  intros v, 
  by_cases hvz : v = 0,
  { rw [hvz, dot_product_comm, dot_product_zero], },
  have hv := h (rat_normalised n v) (normalised_norm_one n v hvz),
  have hveq : dot_product (rat_normalised n v) ((eval_mat n M).mul_vec (rat_normalised n v))
    = (dot_product v ((eval_mat n M).mul_vec v)) / (rat_norm n v) ^ 2,
  { simp only [dot_product], rw [finset.sum_div], congr, ext i,
    simp only [rat_normalised, mul_vec, dot_product],
    have hsum : ∑ j, eval_mat n M i j * (v j / rat_norm n v) 
      = (∑ j, eval_mat n M i j * v j) / rat_norm n v,
    { rw [finset.sum_div], congr, ext j, rw [mul_div_assoc], },
    rw hsum, rw [div_mul_div, pow_two], },
  rw hveq at hv, clear hveq,
  have hrvz := (not_iff_not_of_iff (rat_norm_eq_zero_iff n v)).mpr hvz,
  have hrvpos := lt_of_le_of_ne (rat_norm_nonneg n v) (ne_comm.1 hrvz),
  have hrv2pos := mul_pos hrvpos hrvpos,
  rw [pow_two, le_div_iff hrv2pos, zero_mul] at hv,
  exact hv,
end 

-- TODO: Move
lemma finset_sum_neg {γ R : Type*} [fintype γ] [linear_ordered_ring R] {x : γ → R} 
  (h : ∑ i, x i < 0) : ∃ i, x i < 0 :=
begin 
  by_contra hc, 
  suffices hsuff : 0 ≤ ∑ i, x i, { exact (not_le_of_lt h) hsuff, },
  apply finset.sum_nonneg, intros i hi,
  rw not_exists at hc, replace hc := hc i,
  exact le_of_not_lt hc,
end 

#check finset.sum_eq_sum_diff_singleton_add

lemma psd_of_nonneg_diagonally_dominant 
  (hnonneg : ∀ i j, 0 ≤ A i j) 
  (hdiagdom : ∀ i, (∑ (j : fin n) in finset.univ \ {i}, A i j) ≤ A i i) 
: pos_semidef A :=
begin 
  apply pos_semidef_of_unit n A, intros v hvunit,
  simp only [dot_product], 
  
  apply finset.sum_nonneg, intros i hi,
  by_cases hvi : v i < 0,
  { suffices hsuff : (eval_mat n A).mul_vec v i < 0,
    { exact le_of_lt (mul_pos_of_neg_of_neg hvi hsuff), },
    simp only [mul_vec, dot_product], },
  { sorry, },

  
  -- by_contra hc, 
  -- obtain ⟨i, hci⟩ := finset_sum_neg (lt_of_not_ge hc), dsimp at hci,
  -- suffices hsuff : 0 ≤ v i * (eval_mat n A).mul_vec v i,
  -- { exact (not_le_of_lt hci) hsuff, },

  --simp only [mul_vec, dot_product] at hci, rw finset.mul_sum at hci,
  --obtain ⟨j, hcij⟩ := finset_sum_neg hci, dsimp at hcij,
end


-- With unit vectors.

