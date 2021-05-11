import data.rat.basic 
import algebra.group_with_zero.power
import tactic.linarith

def reduce_float_raw'' : ℕ → ℕ
| 0 := 0
| m@(nat.succ _) := 
  if (m % 2 = 0) 
  then 
    have m / 2 < m, from nat.div_lt_self (nat.zero_lt_succ _) (by linarith), 
    reduce_float_raw'' (m / 2)
  else m

def reduce_float_raw_aux : ℕ × ℤ → ℕ × ℤ
| ⟨0, e⟩ := ⟨0, 1⟩
| ⟨m@(nat.succ _), e⟩ := 
  have prod.lex has_lt.lt (λ (a₁ a₂ : ℤ), a₁.sizeof < a₂.sizeof) (⟨m / 2, e + 1⟩ : ℕ × ℤ) ⟨m, e⟩, from 
  begin 
    have h : _x.succ / 2 < _x.succ, from nat.div_lt_self (nat.zero_lt_succ _) (by linarith), 
    rw prod.lex_def, left, dsimp, assumption,
  end,
  if (m % 2 = 0) 
  then 
    reduce_float_raw_aux ⟨m / 2, e + 1⟩
  else ⟨m, e⟩
using_well_founded { dec_tac := tactic.assumption }

lemma reduce_float_raw_aux_to_rat (m : ℕ) (e : ℤ) 
: (m : ℚ) * 2 ^ e = ((reduce_float_raw_aux ⟨m, e⟩).1 : ℚ) * 2 ^ ((reduce_float_raw_aux ⟨m, e⟩).2) :=
begin
  revert e,
  apply nat.strong_induction_on m, intros n ih, cases n,
  { simp [reduce_float_raw_aux], },
  { intros e, unfold reduce_float_raw_aux, 
    by_cases (n.succ % 2 = 0); split_ifs,
    { have hlt : n.succ / 2 < n.succ, from nat.div_lt_self (nat.zero_lt_succ _) (by linarith), 
      have ihm2 := ih (n.succ / 2) hlt (e + 1), rw ←ihm2, 
      have hn2 := nat.div_mul_cancel (nat.dvd_of_mod_eq_zero h), 
      have hn2e : (↑(n.succ) * 2 ^ e : ℚ) = ↑(n.succ / 2 * 2) * 2 ^ e, { rw hn2, }, 
      rw hn2e, push_cast, ring, congr,
      rw [fpow_add (by norm_num : (2 : ℚ) ≠ 0), mul_comm], congr, },
    { refl, } } 
end  
