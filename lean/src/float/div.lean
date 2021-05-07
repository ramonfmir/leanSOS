import float.basic
import float.round

open float

variable (prec : ℕ)

def divl (x y : 𝔽) : 𝔽 :=
round_down prec (eval x / eval y)

def divr (x y : 𝔽) : 𝔽 :=
round_up prec (eval x / eval y)

meta def div_rat' (x y : 𝔽) : ℚ :=
let x' := quot.unquot x, y' := quot.unquot y in 
if x'.e ≤ y'.e
then rat.mk (x'.m) (y'.m * 2 ^ int.to_nat (y'.e - x'.e))
else rat.mk (x'.m * 2 ^ int.to_nat (x'.e - y'.e)) (y'.m)

meta def divl' (x y : 𝔽) : 𝔽 :=
round_down prec (div_rat' x y)

meta def divr' (x y : 𝔽) : 𝔽 :=
round_up prec (div_rat' x y)

--instance : has_div 𝔽 := ⟨divl 10⟩ -- Fixed precision for now 
meta instance : has_div 𝔽 := ⟨divl' 10⟩ -- Fixed precision for now 


-- Lemmas.

lemma divl_bound (x y : 𝔽) 
: eval (divl prec x y) ≤ eval x / eval y :=
begin 
  simp [divl, round_down, eval_mk], 
  have h : 0 < ((2 : ℚ) ^ prec), { norm_num, },
  rw [mul_inv_le_iff h, mul_comm], exact floor_le _,
end 

lemma divr_bound (x y : 𝔽) 
: eval x / eval y ≤ eval (divr prec x y) :=
begin 
  simp [divr, round_up, eval_mk], 
  have h : 0 < ((2 : ℚ) ^ prec), { norm_num, },
  rw [←mul_le_mul_right h, mul_assoc, inv_mul_cancel (ne_of_gt h), mul_one],
  exact le_ceil _,
end 

lemma divl_diff_lb (x y : 𝔽) 
: 0 ≤ (eval x / eval y) - eval (divl prec x y) :=
sub_nonneg_of_le (divl_bound prec x y)

lemma divl_diff_ub (x y : 𝔽) 
: (eval x / eval y) - eval (divl prec x y) ≤ 2 ^ (-(prec : ℤ)) :=
begin 
  have h := divr_bound prec x y, 
  replace h := sub_le_sub_right h (eval (divl prec x y)),
  apply le_trans h, simp only [divr, divl],
  rw [←eval_sub],
  have h1 : 2 ^ (-(prec : ℤ)) = eval (float.mk 1 (-prec)),
  { simp [eval_mk], },
  rw h1, exact round_up_diff_round_down prec _,
end 

-- #eval divl 10 (mk 50 0) (mk 3 2)

-- Isabelle version:
-- lift_definition float_divr :: "nat => float => float => float" is
--   "λ(prec::nat) a b. round_up (prec + ⌊ log 2 ¦b¦ ⌋ - ⌊ log 2 ¦a¦ ⌋) (a / b)" by simp

-- TODO: Precision needs to change?
