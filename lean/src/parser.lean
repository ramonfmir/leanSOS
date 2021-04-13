import data.matrix.basic
import data.real.basic
import tactic.fin_cases

open lean.parser tactic interactive

meta def parse_parser {α} (p : lean.parser α) : lean.parser α :=
do t ← types.texpr,
  f ← ↑(to_expr t >>= eval_expr string),
  prod.fst <$> with_input p f

meta def tactic.interactive.parse (e : parse (parse_parser types.texpr)) : tactic unit :=
interactive.exact e

#check eval_expr

#print array

meta def parse_dimension : char → ℕ 
| '1' := 1
| '2' := 2
| '3' := 3
| '4' := 4
| _ := 0 -- and so on 

def list_to_vector (n : ℕ) (l : list ℚ) (hl : l.length = n) 
: fin n → ℚ := 
λ i, l.nth_le i.1 (hl.symm ▸ i.2)

def list_to_matrix (n : ℕ) (l : list (list ℚ)) 
(hl : l.length = n) (hl' : ∀ i : fin n, (l.nth_le i.1 (hl.symm ▸ i.2)).length = n)
: matrix (fin n) (fin n) ℚ := 
λ i j, (l.nth_le i.1 (hl.symm ▸ i.2)).nth_le j.1 ((hl' i).symm ▸ j.2)

def test_matrix : matrix (fin 2) (fin 2) ℚ :=
list_to_matrix 
  2 
  [[0.1, 0.2], [0.3, 0.4]]
  (by refl)
  (λ i, by fin_cases i; refl)


meta def list_from_string (st : string) : lean.parser expr := do
   (t, s) ← with_input types.texpr st,
   e <- to_expr t,
   n <- eval_expr' (list ℚ) e,
   ne ← to_expr ``(%%n),
   return ne

meta def tact (st : string) : tactic unit := do
  e ← run (list_from_string st),
  tactic.exact e
 
def a : list ℚ := by tact "[0.1, 0.2]"

