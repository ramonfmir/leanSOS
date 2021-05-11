import float.basic 

-- Following https://isabelle.in.tum.de/website-Isabelle2013/dist/library/HOL/HOL-Library/Float.html

variable (prec : ℕ)

def round_up (x : ℚ) : 𝔽 := 
float.mk (⌈x * 2 ^ prec⌉) (-prec)

def round_down (x : ℚ) : 𝔽 := 
float.mk (⌊x * 2 ^ prec⌋) (-prec)

lemma round_up_zero : round_up prec 0 = 0 :=
by { apply quotient.sound, show to_rat _ = _, simp [to_rat], }

lemma round_down_zero : round_down prec 0 = 0 :=
by { apply quotient.sound, show to_rat _ = _, simp [to_rat], }

lemma round_up_diff_round_down (x : ℚ)
: round_up prec x - round_down prec x ≤ float.mk 1 (-prec) :=
begin 
  show float.eval _ ≤ _, 
  simp [float.eval_sub, round_up, round_down, float.eval_mk],
  suffices hsuff : ↑(⌈x * 2 ^ prec⌉ - ⌊x * 2 ^ prec⌋) * ((2 : ℚ) ^ prec)⁻¹ ≤ 1 * ((2 : ℚ) ^ prec)⁻¹,
  { push_cast at hsuff, rw [sub_mul, one_mul] at hsuff, exact hsuff, },
  have h : 0 < ((2 : ℚ) ^ prec)⁻¹,
  { norm_num, },
  rw [mul_le_mul_right h], show _ ≤ ↑(1 : ℤ), simp [coe],
  rw [sub_le_iff_le_add, add_comm],
  exact ceil_le_floor_add_one _,
end 
