/-
  SOS definition and the SOS tactic.
-/

import system.io
import data.real.basic
import data.mv_polynomial.basic
import .poly

open mv_polynomial poly

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
open lean.parser interactive interactive.types (texpr)

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

noncomputable def p : mv_polynomial ℕ ℝ := (X 1) * (X 1)

noncomputable def ms : fin 1 → mv_polynomial ℕ ℝ := λ _, X 1

def Q : fin 1 → fin 1 → ℝ := λ _ _, 1

-- Quick and dirty tactic to prove that Q is symmetric.
meta def prove_symmetric : tactic unit := 
focus1 $ do 
  `(matrix.symmetric %%Q) ← target,
  [i, j] ← tactic.intro_lst [`i, `j],
  (_, _, _) ← simplify simp_lemmas.mk [] Q {fail_if_unchanged := ff},
  try tactic.reflexivity

lemma Qsymmetric : matrix.symmetric Q := 
by prove_symmetric

lemma Qsymmetric2 : matrix.symmetric (λ _ _, 3 : matrix (fin 1) (fin 1) ℝ) :=
by prove_symmetric 

-- Quick and dirty tactic to prove that p = xT * Q * x.
meta def prove_poly_eq : tactic unit := 
focus1 $ do 
  `(%%p = matrix.dot_product %%ms (matrix.mul_vec (matrix.to_poly %%Q) %%ms')) ← target,
  let l := [``matrix.dot_product, ``matrix.mul_vec, ``matrix.to_poly],
  lemmas ← l.mfoldl simp_lemmas.add_simp simp_lemmas.mk,
  (new_t, pr, _) ← target >>= simplify lemmas [``ms, ``Q, ``p],
  replace_target new_t pr,
  `[simp] 

lemma Qmsp : p = matrix.dot_product ms (matrix.mul_vec (matrix.to_poly Q) ms) :=
by prove_poly_eq

setup_tactic_parser
 
meta def prove_cholesky (pL : parse texpr) : tactic unit := 
focus1 $ do
  `(cholesky_decomposition %%Q %%hQ) ← target,
  tactic.use [pL],
  let l := [``matrix.mul, ``matrix.dot_product],
  lemmas ← l.mfoldl simp_lemmas.add_simp simp_lemmas.mk,
  (new_t, pr, _) ← target >>= simplify lemmas [``Q],
  replace_target new_t pr,
  `[simp]

lemma Qcholesky : cholesky_decomposition Q Qsymmetric :=
by prove_cholesky ``(λ _ _, 1)

meta def sos_aux (input : expr) : tactic unit := do 
  --m ← execute (parse_sos input),
  tactic.trace input,
  γ ← to_expr ``(fin 1),
  γi ← to_expr ``(fin.fintype 1),
  R ← to_expr ``(ℝ),
  Ri ← to_expr ``(real.linear_ordered_comm_ring),
  `(0 ≤ %%p) ← target,
  ms ← to_expr ``(λ _, X 1 : fin 1 → mv_polynomial ℕ ℝ),
  Q ← to_expr ``(λ _ _, 1 : matrix (fin 1) (fin 1) ℝ),
  x ← mk_mapp ``nonneg_of_cholesky [γ, γi, R, Ri, p, ms, Q],
  interactive.concat_tags $ tactic.apply x,
  prove_poly_eq, swap,
  prove_symmetric,
  prove_cholesky ``(λ _ _, 1)

meta def sos : tactic unit := do 
  t ← target,
  sos_aux t

set_option trace.app_builder true

example : 0 ≤ (p : mv_polynomial ℕ ℝ) := begin
  sos,
end 
