/-
  Results about multivariate polynomials.
-/
import data.mv_polynomial.basic
import data.matrix.basic 
import .psd

open mv_polynomial matrix

variables {γ : Type*} [fintype γ]
variables {μ : Type*} [fintype μ]
variables {R : Type*} [linear_ordered_comm_ring R]

namespace poly

instance {σ R} [comm_semiring R] [has_le R] : has_le (mv_polynomial σ R) :=
{ le := λ p q, ∀ v, eval v p ≤ eval v q }

-- 1. eval of dot product is dot product of eval.
lemma eval_dot_product (p q : γ → mv_polynomial ℕ R) (e : ℕ → R) 
: eval e (dot_product p q) = dot_product (λ i, eval e (p i)) (λ i, eval e (q i)) :=
begin 
  simp [dot_product], rw [eval_sum], congr, ext i, rw [(eval e).map_mul],
end 

lemma eval_mul_vec (p : γ → mv_polynomial ℕ R) (M : matrix γ γ (mv_polynomial ℕ R)) 
  (e : ℕ → R) (i : γ)
: eval e (mul_vec M p i) = mul_vec (λ i j, eval e (M i j)) (λ i, eval e (p i)) i :=
begin 
  simp [mul_vec, dot_product], rw [eval_sum], congr, ext l, rw [(eval e).map_mul],
end 

-- 2. thus dot product same of poly is bigger than zero. 
lemma dot_product_self_nonneg (p : γ → mv_polynomial ℕ R)
: 0 ≤ dot_product p p := 
begin 
  intros e, rw [eval_dot_product p p e], simp [eval_C 0],
  exact matrix.dot_product_self_nonneg _,
end 

noncomputable def matrix.to_poly (Q : matrix γ γ R) : matrix γ γ (mv_polynomial ℕ R) :=
λ i j, C (Q i j)

-- 3. thus cholesky of polynomial means poly is nonneg. 
lemma nonneg_of_cholesky 
  (p : mv_polynomial ℕ R) 
  (ms : γ → mv_polynomial ℕ R)
  (Q : matrix γ γ R)
  (hQ : symmetric Q)
  (hp : p = dot_product ms (mul_vec (matrix.to_poly Q) ms))
  (hcholesky : @cholesky_decomposition γ _ μ _ R _ Q hQ)
: C 0 ≤ p := 
begin 
  intros e, rw [hp, eval_dot_product _ _ e],
  have : (λ i, (eval e) (mul_vec (λ i j, C (Q i j)) ms i)) = 
         λ i, mul_vec Q (λ i, eval e (ms i)) i,
  { funext i, rw eval_mul_vec ms _ e i, congr, ext l m, exact eval_C _, },
  simp [eval_C 0, matrix.to_poly], rw this, 
  obtain ⟨L, hL⟩ := hcholesky,
  rw hL,
  rw dot_product_transpose,
  exact matrix.dot_product_self_nonneg _,
end

end poly 
