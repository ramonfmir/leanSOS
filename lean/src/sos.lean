import system.io

open tactic

meta def execute (input : string) : tactic string :=
let path := "/Users/ramon/Documents/experiments/leanSOS/lean/scripts/client.py" in
unsafe_run_io $ io.cmd { 
  cmd := "python3", 
  args := [path, input] }

meta def parse_sos : expr → string
| `(%%e₁ + %%e₂) := "+"
| e@`(@has_sub.sub %%α %%inst %%e₁ %%e₂) := "-"
| `(- %%e) := "-"
| `(%%e₁ * %%e₂) := "*"
| e@`(@has_pow.pow _ _ %%P %%e₁ %%e₂) := "^"
| e := to_string e

meta def sos_aux (input : expr) : tactic unit := do 
  m ← execute (parse_sos input),
  tactic.trace m

meta def sos : tactic unit := do 
  t ← target,
  sos_aux t
