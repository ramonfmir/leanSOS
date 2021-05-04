import .psd .float

variables {n m : nat}

def delta (A : matrix (fin n) (fin n) float) (R : matrix (fin m) (fin n) float) 
: matrix (fin n) (fin n) float :=
A - (matrix.mul R.transpose R)

open matrix module.End

-- prove that RtR is symmetric.
lemma RTR_symmetric 
  (R : matrix (fin m) (fin n) float) 
: symmetric (matrix.mul R.transpose R) :=
begin 
  intros i j, simp [matrix.mul, dot_product], congr, ext k, exact mul_comm _ _,
end 

-- prove that is psd.
lemma RTR_psd 
  (R : matrix (fin m) (fin n) float) 
: pos_semidef (matrix.mul R.transpose R) (RTR_symmetric R) :=
begin 
  intros v, rw [dot_product_transpose v _], exact dot_product_self_nonneg _,
end 

-- copy proof of psd -> positive eigens
lemma nonneg_eigenvalues_of_psd 
  (M : matrix (fin n) (fin n) float) 
  (h : symmetric M)
  (hpsd : pos_semidef M h)
: nonneg_eigenvalues M h :=
begin
  rintros r hre, by_contra hc, rw [has_eigenvalue, submodule.ne_bot_iff] at hre,
  obtain ⟨x, hre, hxnz⟩ := hre, rw [mem_eigenspace_iff] at hre,
  replace hpsd := hpsd x,
  replace hre := congr_arg (λ y, dot_product y x) hre; simp at hre,
  replace hc := lt_of_not_ge hc,
  rw [dot_product_comm] at hpsd,
  suffices hsuff : r * dot_product x x < 0,
  { rw [←hre] at hsuff, exact ((not_le_of_lt hsuff) (ge_iff_le.1 hpsd)), },
  apply mul_neg_of_neg_of_pos hc, rw [hre] at hpsd, exfalso,
  have hdp := dot_product_self_pos_of_nonzero x hxnz,
  have hc' := mul_neg_of_pos_of_neg hdp hc, rw [mul_comm] at hc',
  exact ((not_le_of_gt hc') hpsd),
end 

lemma pos_eigenvalue 
  (R : matrix (fin m) (fin n) float) 
  (a : float) 
  (h : has_eigenvalue (mul_vec_lin (matrix.mul R.transpose R)) a)
: a ≥ 0 := 
(nonneg_eigenvalues_of_psd (matrix.mul R.transpose R) (RTR_symmetric R) (RTR_psd R)) a h



-- argue about the difference between eigenvalues (seems hard).