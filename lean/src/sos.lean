/-
  SOS definition and the SOS tactic.
-/

import system.io
import tactic.ring
import data.real.basic
import data.mv_polynomial.basic
import util.parser lib.poly float.basic

open mv_polynomial poly

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

-- Quick and dirty tactic to prove that Q is symmetric.
meta def prove_symmetric : tactic unit := 
do 
  `(matrix.symmetric %%Q) ← target,
  [i, j] ← tactic.intro_lst [`i, `j],
  (_, _, _) ← simplify simp_lemmas.mk [] Q {fail_if_unchanged := ff},
  `[fin_cases i; fin_cases j; 
    simp [matrix.map, list_to_vector, list_to_monomials, list_to_matrix, list_to_monomial, fin.sum_univ_succ];
    ring]

-- Quick and dirty tactic to prove that p = xT * Q * x.
meta def prove_poly_eq : tactic unit := 
focus1 $ do 
  `(%%p = matrix.dot_product %%ms (matrix.mul_vec (matrix.to_poly %%Q) %%ms')) ← target,
  let l := [``matrix.dot_product, ``matrix.mul_vec, ``matrix.to_poly],
  lemmas ← l.mfoldl simp_lemmas.add_simp simp_lemmas.mk,
  (new_t, pr, _) ← target >>= simplify lemmas [``ms, ``Q, ``p],
  replace_target new_t pr,
  `[simp [matrix.map, list_to_vector, list_to_monomials, list_to_matrix, list_to_monomial, fin.sum_univ_succ]; 
    ring]

setup_tactic_parser

-- Quick and dirty tactic to prove that Q = L^T * L
meta def prove_cholesky (pL : parse texpr) : tactic unit := 
do
  `(cholesky_decomposition %%Q %%hQ) ← target,
  tactic.use [pL],
  let l := [``matrix.mul, ``matrix.dot_product],
  lemmas ← l.mfoldl simp_lemmas.add_simp simp_lemmas.mk,
  (new_t, pr, _) ← target >>= simplify lemmas [``Q],
  replace_target new_t pr,
  `[simp [matrix.map, list_to_vector, list_to_monomials, list_to_matrix, list_to_monomial, fin.sum_univ_succ]; 
    ext i j; fin_cases i; fin_cases j; ring]

meta def sos_aux (input : expr) : tactic unit := do 
  `(%%q ≤ %%p) ← target,
  --m ← execute (parse_sos input),
  let f := "/Users/ramon/Documents/experiments/leanSOS/lean/scripts/temp.txt",
  buf ← unsafe_run_io (io.fs.read_file f),
  match (buf.to_string.split_on '\n') with 
    | sQdim::sQ::sms::sLdim::sL::_ := do {
        -- Parse strings.
        let n : ℕ := parse_dim sQdim,
        lms ← nat_list_of_lists_from_string sms,
        lQ ← rat_list_of_lists_from_string sQ,
        let m : ℕ := parse_dim sLdim,
        lL ← rat_list_of_lists_from_string sL,
        -- Some defaults.
        γ ← to_expr ``(fin %%n),
        γi ← to_expr ``(fin.fintype %%n),
        μ ← to_expr ``(fin %%m),
        μi ← to_expr ``(fin.fintype %%m),
        R ← to_expr ``(float),
        Ri ← to_expr ``(float.linear_ordered_comm_ring),
        -- Monomials and main matrix.
        ms ← monomials_from_list n lms,
        QZZ ← matrix_from_list n n lQ,
        LZZ ← matrix_from_list m n lL,
        Q ← to_expr ``(matrix.map %%QZZ float.mk),
        L ← to_expr ``(matrix.map %%LZZ float.mk),
        -- Apply the main theorem. 
        res ← mk_mapp ``nonneg_of_cholesky [γ, γi, μ, μi, R, Ri, p, ms, Q],
        interactive.concat_tags $ tactic.apply res
        -- Prove the three subgoals.
        --prove_poly_eq, swap,
        --prove_symmetric,
        --prove_cholesky ``(%%L)
        }
    | _ := tactic.trace "Error"
  end

meta def sos : tactic unit := do 
  t ← target,
  sos_aux t
