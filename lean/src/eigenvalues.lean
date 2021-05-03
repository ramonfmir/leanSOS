import .psd .float

variables {n m : nat}

def delta (A : matrix (fin n) (fin n) float) (R : matrix (fin m) (fin n) float) 
: matrix (fin n) (fin n) float :=
A - (matrix.mul R.transpose R)

open matrix module.End

-- prove that RtR is symmetric.
-- prove that is psd.
-- copy proof of psd -> positive eigens

lemma pos_eigenvalue 
  (R : matrix (fin m) (fin n) float) 
  (a : float) 
  (h : has_eigenvalue (mul_vec_lin (matrix.mul R.transpose R)) a)
: a ≥ 0 := 
begin
  by_contra ha, apply h, ext x, rw [mem_eigenspace_iff],
  sorry,
end

-- argue about the difference between eigenvalues (seems hard).