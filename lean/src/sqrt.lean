import data.int.sqrt
import data.int.parity
import data.rat.sqrt
import .float

namespace float_raw

def sqrt (f : float_raw) : float_raw :=
if (even f.e) 
then ⟨int.sqrt f.m, f.e / 2⟩
else ⟨int.sqrt (f.m * 2), (f.e - 1) / 2⟩ 

end float_raw 

namespace float 

#check int.to_nat_mul
#check int.to_nat_of_nonneg
#check neg_lt_zero

#eval nat.sqrt (3 * 2 ^ (2 * 1))
#eval (nat.sqrt 3) * (2 ^ 1)

-- lemmas
lemma sqrt_useful_nat (n m : nat) : nat.sqrt (n * 2 ^ (2 * m)) = (nat.sqrt n) * 2 ^ m :=
begin 
  induction m with m h generalizing n,
  { simp, },
  { have h1 := h n,
    have h2 := h (2 * n), },
end 

lemma sqrt_useful (n : int) (m : nat) : int.sqrt (n * ↑(2 ^ (2 * m))) = (int.sqrt n) * 2 ^ m :=
begin 
  cases n,
  { simp only [int.sqrt], simp, sorry, },
  { simp only [int.sqrt], iterate 2 { rw int.to_nat_zero_of_neg, },
    { simp [nat.sqrt], },
    { exact int.neg_succ_lt_zero _, },
    { rw [int.neg_succ_mul_coe_nat, ←int.coe_nat_mul, neg_lt_zero, int.coe_nat_pos], simp, }, }
end 

lemma to_rat.sqrt {x y : float_raw} (h : to_rat x = to_rat y) 
: to_rat (float_raw.sqrt x) = to_rat (float_raw.sqrt y) :=
begin 
  simp [float_raw.sqrt, to_rat] at *, split_ifs,
  { obtain ⟨kx, hkx⟩ := h_1,
    obtain ⟨ky, hky⟩ := h_2,
    rw [hkx, hky],
    rw [int.mul_div_cancel_left kx (by norm_num : (2 : int) ≠ 0)],
    rw [int.mul_div_cancel_left ky (by norm_num : (2 : int) ≠ 0)],
    replace h := congr_arg rat.sqrt h,
    sorry, },
  { sorry, },
  { sorry, },
  { sorry, },
end

def sqrt (f : float) : float :=
quotient.lift (λ x, ⟦float_raw.sqrt x⟧) (λ a b h, quotient.sound $ begin sorry end)

end float 
