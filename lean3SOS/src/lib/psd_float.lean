import data.rat.order
import to_mathlib.matrix float.basic float.div lib.psd 

-- We have A ∈ 𝒮(𝔽)ⁿˣⁿ. 

open matrix float
open_locale matrix big_operators

variables (n : nat) (hn : 0 < n) (A : matrix (fin n) (fin n) float) (h : symmetric A)

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
  show eval _ ≤ _, rw [float.eval_zero], exact hv,
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

#check ite_mul

lemma symmetric_decomp 
  (B : matrix (fin n) (fin n) ℚ)
  (hB : symmetric B)
  (v : fin n → ℚ)
: dot_product v (B.mul_vec v) -- vᵀ * B * v = ∑ i ∑ j, B i j * vi * vj
= ∑ i, (B i i) * (v i) ^ 2 + 2 * ∑ i, ∑ j, (if i < j then (B i j) else 0) * (v i) * (v j) :=
begin
  simp only [mul_vec, dot_product],
  have h1 : ∑ i, ∑ j, (if i < j then (B i j) else 0) * (v i) * (v j)
    = ∑ j, ∑ i, (if j < i then (B i j) else 0) * (v i) * (v j),
  { congr, ext i, congr, ext j, split_ifs, 
    { rw hB i j, ring, },
    { ring, } },
  have h2 : ∑ i, ∑ j, (if i < j then (B i j) else 0) * (v i) * (v j)
    = ∑ i, ∑ j, (if j < i then (B i j) else 0) * (v i) * (v j),
  { rw h1, rw finset.sum_comm, },
  have h3 : 2 * ∑ i, ∑ j, (if i < j then (B i j) else 0) * (v i) * (v j)
    = (∑ i, ∑ j, (if i < j then (B i j) else 0) * (v i) * (v j))
    + (∑ i, ∑ j, (if j < i then (B i j) else 0) * (v i) * (v j)),
  { rw two_mul, congr' 1, },
  have h4 : (∑ i, ∑ j, (if i < j then (B i j) else 0) * (v i) * (v j))
    + (∑ i, ∑ j, (if j < i then (B i j) else 0) * (v i) * (v j))
    = ∑ i, ∑ j, (if i ≠ j then (B i j) else 0) * (v i) * (v j),
  { simp only [←finset.sum_add_distrib], congr, ext i, congr, ext j,
    by_cases hij : i < j,
    { rw if_pos hij, rw if_pos (ne_of_lt hij), rw if_neg (not_lt.2 $ le_of_lt hij), ring, },
    { replace hij := lt_or_eq_of_le (le_of_not_lt hij), cases hij,
      { rw if_pos hij, rw if_pos (ne_comm.1 $ ne_of_lt hij), 
        rw if_neg (not_lt.2 $ le_of_lt hij), ring, },
      { rw if_neg (not_not.2 hij.symm), rw if_neg (not_lt_iff_eq_or_lt.2 $ or.inl hij),
        rw if_neg (not_lt_iff_eq_or_lt.2 $ or.inl hij.symm), ring, }, }, },
  have h5 : ∑ i, (B i i) * (v i)^2
    = ∑ i, ∑ j, (if i = j then (B i j) else 0) * (v i) * (v j),
  { congr, ext i, simp only [ite_mul, zero_mul], rw finset.sum_ite_eq, 
    rw if_pos (finset.mem_univ i), rw pow_two, ring, },
  rw [h3, h4, h5], simp only [←finset.sum_add_distrib], congr, ext i,
  rw finset.mul_sum, congr, ext j, 
  by_cases hij : i = j,
  { rw if_pos hij, rw if_neg (not_not.2 hij), ring, },
  { rw if_pos hij, rw if_neg hij, ring, },
end

-- Idea : https://math.stackexchange.com/questions/87528/a-practical-way-to-check-if-a-matrix-is-positive-definite
lemma psd_of_nonneg_diagdom
  (B : matrix (fin n) (fin n) ℚ)
  (hB : symmetric B)
  (hnonneg : ∀ i j, 0 ≤ B i j) 
  (hdiagdom : ∀ i, (∑ j, if i ≠ j then B i j else 0) ≤ B i i) 
: pos_semidef B :=
begin 
  intros v,
  let R : fin n → ℚ := λ i, B i i - ∑ j, if i ≠ j then B i j else 0,
  let D : ℚ := ∑ i, (R i) * (v i) ^ 2,
  let O : ℚ := ∑ i, ∑ j, (if i < j then B i j else 0) * (v i + v j) ^ 2, 

  have hO : O = ∑ i, ∑ j, (if i < j then B i j else 0) * (v i) ^ 2
    + 2 * ∑ i, ∑ j, (if i < j then B i j else 0) * (v i) * (v j)
    + ∑ i, ∑ j, (if i < j then B i j else 0) * (v j) ^ 2,
  { simp only [finset.mul_sum, ←finset.sum_add_distrib, O], congr, ext i, congr, ext j,
    by_cases hij : i < j,
    { simp only [if_pos hij, pow_two], ring, },
    { simp only [if_neg hij], ring, }, },

  have h1 : (∑ i, ∑ j, (if i < j then B i j else 0) * (v j) ^ 2)
    = ∑ i, ∑ j, (if j < i then B i j else 0) * (v i) ^ 2,
  { rw finset.sum_comm, congr, ext i, congr, ext j, split_ifs,
    { rw (hB i j), },
    { refl, }, },

  have h2 : (∑ i, ∑ j, (if i < j then B i j else 0) * (v i) ^ 2) 
    + ∑ i, ∑ j, (if i < j then B i j else 0) * (v j) ^ 2
    = ∑ i, ∑ j, (if i ≠ j then B i j else 0) * (v i) ^ 2,
  { rw h1, simp only [←finset.sum_add_distrib], congr, ext i, congr, ext j,
    by_cases hij : i < j,
    { rw if_pos hij, rw if_pos (ne_of_lt hij), rw if_neg (not_lt.2 $ le_of_lt hij), ring, },
    { replace hij := lt_or_eq_of_le (le_of_not_lt hij), cases hij,
      { rw if_pos hij, rw if_pos (ne_comm.1 $ ne_of_lt hij), 
        rw if_neg (not_lt.2 $ le_of_lt hij), ring, },
      { rw if_neg (not_not.2 hij.symm), rw if_neg (not_lt_iff_eq_or_lt.2 $ or.inl hij),
        rw if_neg (not_lt_iff_eq_or_lt.2 $ or.inl hij.symm), ring, }, }, },

  have hO' : O = (∑ i, ∑ j, (if i ≠ j then B i j else 0) * (v i) ^ 2)
    + 2 * ∑ i, ∑ j, (if i < j then B i j else 0) * (v i) * (v j),
  { rw hO, rw add_assoc, rw add_comm ((2 : ℚ) * _), rw ←add_assoc, rw h2, },

  have h3 : D + (∑ i, ∑ j, (if i ≠ j then B i j else 0) * (v i) ^ 2)
    = ∑ i, (B i i) * (v i) ^ 2,
  { simp only [D, R, ←finset.sum_add_distrib], congr, ext i,
    simp only [sub_mul, finset.sum_mul], ring, },

  have heq : dot_product v (B.mul_vec v) = D + O,
  { rw hO', rw ←add_assoc, rw h3, rw symmetric_decomp n B hB v, },
  
  have hDnonneg : 0 ≤ D,
  { simp only [D], apply finset.sum_nonneg, intros i hi,
    apply mul_nonneg,
    { simp only [R], rw sub_nonneg, exact hdiagdom i, },
    { exact pow_two_nonneg (v i), }, },

  have hOnonneg : 0 ≤ O,
  { simp only [O], apply finset.sum_nonneg, intros i hi,
    apply finset.sum_nonneg, intros j hj, split_ifs,
    { exact mul_nonneg (hnonneg i j) (pow_two_nonneg _), },
    { simp, }, },

  rw heq, exact add_nonneg hDnonneg hOnonneg,
end


-- With unit vectors.

