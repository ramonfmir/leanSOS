/-
  SOS definition and the SOS tactic.
-/

import system.io
import data.real.basic
import data.mv_polynomial.basic

open mv_polynomial 

instance {σ R} [comm_semiring R] [has_le R] : has_le (mv_polynomial σ R) :=
{ le := λ p q, ∀ v, eval v p ≤ eval v q }

noncomputable def square_polys : list (mv_polynomial ℕ ℝ) → list (mv_polynomial ℕ ℝ) :=
λ l, list.map (λ q, q * q) l

noncomputable def sum_polys : list (mv_polynomial ℕ ℝ) → mv_polynomial ℕ ℝ :=
λ l, list.foldl (+) 0 l

def is_sos (p : mv_polynomial ℕ ℝ) : Prop :=
∃ l, p = sum_polys (square_polys l)

lemma nonneg_of_sos (p : mv_polynomial ℕ ℝ) : is_sos p → 0 ≤ p := 
begin 
  sorry,
end 

open tactic 

meta def execute (input : string) : tactic string :=
let path := "/Users/ramon/Documents/experiments/leanSOS/lean/scripts/client.py" in
unsafe_run_io $ io.cmd { 
  cmd := "python3.9", 
  args := [path, input] }

--set_option trace.eqn_compiler.elim_match true
set_option eqn_compiler.max_steps 10000

meta def parse_num : option nat → string 
| (some n) := to_string n
| _ := ""

meta def parse_sos : expr → string
| `(@has_le.le %%α %%inst %%e₁ %%e₂) := (parse_sos e₁) ++ "<=" ++ (parse_sos e₂)
| `(%%e₁ + %%e₂) :=  "(" ++ (parse_sos e₁) ++ "+" ++ (parse_sos e₂) ++ ")"
--| `(@has_sub.sub %%α %%inst %%e₁ %%e₂) := (parse_sos e₁) ++ "-" ++ (parse_sos e₂)
--| `(- %%e) := "-" ++ (parse_sos e)
| `(%%e₁ * %%e₂) := "(" ++ (parse_sos e₁) ++ "*" ++ (parse_sos e₂) ++ ")"
--| `(@has_pow.pow _ _ %%P %%e₁ %%e₂) := (parse_sos e₁) ++ "^" ++ (parse_sos e₂)
| `(mv_polynomial.C %%e) := (parse_num (expr.to_nat e))
| `(mv_polynomial.X %%e) := "x[" ++ (parse_num (expr.to_nat e)) ++ "]"
| e := ""

meta def sos_aux (input : expr) : tactic unit := do 
  m ← execute (parse_sos input),
  tactic.trace m

meta def sos : tactic unit := do 
  t ← target,
  sos_aux t
