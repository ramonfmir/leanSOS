import data.rat.basic
import data.matrix.basic
import tactic.linarith
import float.basic
import float.div

variables {k m n : nat}

open matrix

-- Copied from https://github.com/skbaek/cvx/blob/master/src/LDLT.lean

def get_diagonal (A : matrix (fin n) (fin n) rat) : matrix (fin n) (fin n) rat
| i j := if i = j then A i j else 0

def lower_triangle (A : matrix (fin n) (fin n) rat) : matrix (fin n) (fin n) rat 
| i j := if i = j then 1 else (if i > j then A i j else 0)

meta def write_col (A_jj' : rat) (j : nat) (v : fin j → rat) (h1 : j < n) 
: nat → matrix (fin n) (fin n) rat → matrix (fin n) (fin n) rat 
| k A := 
  if h2 : n ≤ k then A else 
  let j' : fin n := ⟨j, h1⟩ in
  let k' : fin n := ⟨k, lt_of_not_ge' h2⟩ in
  let A_kj : rat := A k' j' in
  let w : fin j → rat := λ l : fin j, A k' (fin.cast_le (le_of_lt h1) l) in
  let r : rat := (A_kj - matrix.dot_product w v) / A_jj' in
  let A' : matrix (fin n) (fin n) rat := λ a b, if (a = k') && (b = j') then r else A a b in
  write_col (k + 1) A'

meta def LDLT_aux : nat → matrix (fin n) (fin n) rat → matrix (fin n) (fin n) rat
| j A := 
  if h1 : n ≤ j then A else 
  let h2 : j < n := lt_of_not_ge' h1 in
  let j' : fin n := ⟨j, h2⟩ in
  let v : fin j → rat := (λ i, 
    let i' : fin n := ⟨i.val, lt_trans i.is_lt h2⟩ in
    (A j' i') * (A i' i')) in  
  let w : fin j → rat := λ l : fin j, A j' (fin.cast_le (le_of_lt h2) l) in
  let A_jj : rat := A j' j' in
  let A_jj' : rat := A_jj - (matrix.dot_product w v) in
  let A' : matrix (fin n) (fin n) rat := λ a b, if (a = j') && (b = j') then A_jj' else A a b in
  let A'' : matrix (fin n) (fin n) rat :=  write_col A_jj' j v h2 (j+1) A' in
  LDLT_aux (j + 1) A''

meta def LDLT (A : matrix (fin n) (fin n) rat) 
: (matrix (fin n) (fin n) rat) × (matrix (fin n) (fin n) rat) :=
let X := LDLT_aux 0 A in ⟨lower_triangle A, get_diagonal A⟩

-- New definition.

variables {R : Type*} [linear_ordered_ring R] [has_div R]

private meta def decompose_def_aux_2
: fin n → 
  fin n → 
  matrix (fin n) (fin n) R → 
  matrix (fin n) (fin n) R → 
  (fin n → R) →
  (matrix (fin n) (fin n) R)
| j i A L D := 
let S : fin i → R := 
  λ a, let a' := fin.cast_le i.2 a in (L j a') * (L i a') * (D a') in
let L' : matrix (fin n) (fin n) R := 
  λ a b, if (a = j) && (b = i) then ((A j i) - finset.univ.sum S) / (D i) else L a b in
if h : j.1 + 1 ≥ n
then L' 
else decompose_def_aux_2 ⟨j.val + 1, lt_of_not_ge' h⟩ i A L' D

private meta def decompose_def_aux
: fin n → 
  matrix (fin n) (fin n) R → 
  matrix (fin n) (fin n) R → 
  (fin n → R) →
  (matrix (fin n) (fin n) R) × (fin n → R)
| i A L D := 
let S : fin i → R := 
  λ a, let a' := fin.cast_le i.2 a in (L i a') * (L i a') * (D a') in 
let D' : fin n → R := 
  λ a, if (a = i) then (A i i) - finset.univ.sum S else D a in 
let L' : matrix (fin n) (fin n) R := 
  decompose_def_aux_2 i i A L D' in
if h : i.1 + 1 ≥ n
then ⟨L', D'⟩ 
else 
  let i' : fin n := ⟨i.val + 1, lt_of_not_ge' h⟩ in
  decompose_def_aux i' A L' D'

variables (n)

private meta def decompose_def (h : 0 < n) (A : matrix (fin n) (fin n) R)  
: (matrix (fin n) (fin n) R) × (fin n → R) :=
let D : fin n → R := λ x, 0 in 
let L : matrix (fin n) (fin n) R := λ x y, 0 in 
decompose_def_aux ⟨0, h⟩ A L D

meta def decompose (A : matrix (fin n) (fin n) R) : (matrix (fin n) (fin n) R) × (fin n → R) := do
by { by_cases (0 < n), { exact decompose_def n h A, }, { exact ⟨A, λ x, 0⟩, }, }
