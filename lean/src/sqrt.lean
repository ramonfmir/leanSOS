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

-- lemmas
lemma to_rat.num_neg_exp (f : float_raw) (h : f.e < 0) : (to_rat f).num = f.m :=
begin 
  simp [to_rat], suffices hsuff : (f.m * 2 ^ f.e : ℚ) = rat.mk f.m (2 ^ int.to_nat (-f.e)),
  { rw hsuff, 
    -- num_div_eq_of_coprime if we assume x.m is odd?
    sorry, },
  sorry,
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
