import data.real.basic

open lean.parser tactic interactive

meta def parse_parser {α} (p : lean.parser α) : lean.parser α :=
do t ← types.texpr,
  f ← ↑(to_expr t >>= eval_expr string),
  prod.fst <$> with_input p f

meta def tactic.interactive.parse (e : parse (parse_parser types.texpr)) : tactic unit :=
interactive.exact e

example : true :=
begin
  let foo := by parse "(0.55 : ℝ)",
-- foo : ℕ → Prop := λ (n : ℕ), n ≠ 0
end