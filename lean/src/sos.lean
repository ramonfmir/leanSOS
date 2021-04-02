import system.io
import data.mv_polynomial.basic

open tactic

meta def execute (input : string) : tactic string :=
let path := "/Users/ramon/Documents/experiments/leanSOS/lean/scripts/client.py" in
unsafe_run_io $ io.cmd { 
  cmd := "python3", 
  args := [path, input] }

set_option trace.eqn_compiler.elim_match true

meta def parse_sos : expr → string
| `(@has_le.le %%α %%inst %%e₁ %%e₂) := (parse_sos e₁) ++ "<=" ++ (parse_sos e₂)
| `(%%e₁ + %%e₂) :=  (parse_sos e₁) ++ "+" ++ (parse_sos e₂)
| `(@has_sub.sub %%α %%inst %%e₁ %%e₂) := (parse_sos e₁) ++ "-" ++ (parse_sos e₂)
| `(- %%e) := "-" ++ (parse_sos e)
| `(%%e₁ * %%e₂) := (parse_sos e₁) ++ "*" ++ (parse_sos e₂)
| `(@has_pow.pow _ _ %%P %%e₁ %%e₂) := (parse_sos e₁) ++ "^" ++ (parse_sos e₂)
--| `(mv_polynomial.C %%e) := (parse_sos e)
| e := to_string e

meta def sos_aux (input : expr) : tactic unit := do 
  m ← execute (parse_sos input),
  tactic.trace m

meta def sos : tactic unit := do 
  t ← target,
  sos_aux t
