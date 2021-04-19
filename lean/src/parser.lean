import data.matrix.basic
import data.real.basic
import data.mv_polynomial.basic
import tactic.fin_cases

open lean.parser tactic interactive

-- Parsing strings.

private meta def parse_dim_aux : char → ℕ 
| '1' := 1
| '2' := 2
| '3' := 3
| '4' := 4
| _ := 0 -- and so on 

meta def parse_dim : string → ℕ := λ s, parse_dim_aux (string.head s)

private meta def nat_list_of_lists_from_string_aux (st : string) : lean.parser expr := do
  (t, s) ← with_input types.texpr st,
  e <- to_expr ``(%%t : list (list ℕ)),
  n <- eval_expr' (list (list ℕ)) e,
  return (reflect n)

meta def nat_list_of_lists_from_string (st : string) : tactic expr := do
  e ← run (nat_list_of_lists_from_string_aux st),
  return e

private meta def rat_list_of_lists_from_string_aux (st : string) : lean.parser expr := do
  (t, s) ← with_input types.texpr st,
  e <- to_expr ``(%%t : list (list ℚ)),
  n <- eval_expr' (list (list ℚ)) e,
  return (reflect n)

meta def rat_list_of_lists_from_string (st : string) : tactic expr := do
  e ← run (rat_list_of_lists_from_string_aux st),
  return e

-- Transforming lists (definitions).

@[reducible] noncomputable def list_to_monomial (l : list ℕ) : mv_polynomial ℕ ℚ :=
(l.map mv_polynomial.X).foldl (*) (mv_polynomial.C 1)

@[reducible] noncomputable def list_to_monomials (l : list (list ℕ)) : list (mv_polynomial ℕ ℚ) :=
l.map list_to_monomial

@[reducible] def list_to_vector {α} (n : ℕ) (l : list α) (hl : l.length = n) 
: fin n → α := 
λ i, l.nth_le i.1 (hl.symm ▸ i.2)

@[reducible] def list_to_matrix {α} (n m : ℕ) (l : list (list α)) 
(hl : l.length = n) (hl' : ∀ i : fin n, (l.nth_le i.1 (hl.symm ▸ i.2)).length = m)
: matrix (fin n) (fin m) α := 
λ i j, (l.nth_le i.1 (hl.symm ▸ i.2)).nth_le j.1 ((hl' i).symm ▸ j.2)

-- Transforming lists (tactics).

meta def monomials_from_list (d : ℕ) (l : expr) : tactic expr := do 
  e ← to_expr ``(list_to_vector %%d (list_to_monomials %%l) (by refl)),
  return e

meta def matrix_from_list (n m : ℕ) (l : expr) : tactic expr := do 
  e ← to_expr ``(list_to_matrix %%n %%m %%l (by refl) (λ i, by fin_cases i; refl)),
  return e

def test_matrix : matrix (fin 2) (fin 2) ℚ :=
by do { e ← (matrix_from_list 2 2 `([[0.1, 0.2], [0.3, 0.4]] : list (list ℚ)) ), tactic.exact e }

