import system.io tactic
open io tactic list
open lean lean.parser tactic interactive


/-- Jason and Mario's parser code --/
meta def from_file {α : Type}
(f : string)
(p : lean.parser α) : lean.parser α :=
do
  buf ← unsafe_run_io (io.fs.read_file f),
  (a, s) ← with_input p buf.to_string,
  return a

meta def load_parser
{α : Type}
(p : lean.parser α) : lean.parser α :=
do
   t ← types.texpr,
   f ← of_tactic (do
      e <- to_expr t,
      s <- eval_expr string e,
      return s
   ),
   e <- from_file f p,
   return e

meta def tactic.interactive.load
(e : parse (load_parser types.texpr)) : tactic unit :=
interactive.exact e


meta def set_goal (goal : expr) : tactic unit :=
do
   v <- mk_meta_var goal,
   set_goals [v],
   return ()

/-- My custom structures/types --/

def Property (α : Type) : Type := α → Prop

structure Claim (α : Type) :=
(X : set α)
(P : Property α)

structure strategy (α : Type) :=
(Clm : Claim α)
(Props : list (Property α))

@[derive [fintype, has_reflect]]
inductive foo
| a
| b
| c
| d

def contra (α : Type)
(S : strategy foo ) : Prop :=
∀ x, ¬(S.Clm.P x) → (∃ i : fin (S.Props.length), (S.Props.nth_le i.1 i.2) x)

meta def silly_tactic : tactic unit :=
 do
 `[  intros n H,
     fin_cases n,
     simp at *,
     exfalso, assumption,
     use 0, simp, dsimp, refl,
     use 1, simp, dsimp, refl,
     use 2, simp, dsimp, refl]

--- path/to/input.txt file :
-- (strategy.mk
-- (Claim.mk {foo.a} (λ n, n = foo.a))
-- [(λ n, n=foo.b),
--  (λ n, n=foo.c),
--  (λ n, n=foo.d)])


@[user_command]
meta def main_app
(meta_info : decl_meta_info)
(_ : parse (tk "main_app")) : lean.parser unit :=
-- below is the code
do
   -- get contents of file as a pre-expression
   t <- from_file "/Users/ramon/Documents/experiments/leanSOS/lean/src/iotest.txt" types.texpr,
   -- now that we are done with the parser,
   -- everything else can be done in the tactic monad
   of_tactic (do
      e <- to_expr t,
      S <- eval_expr (strategy foo) e,
      let goal := `(contra foo %%e),
      let tac := `[silly_tactic],
      return ()
   )
.
main_app

