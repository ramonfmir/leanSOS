import data.rat.basic
import data.matrix.basic
import tactic.linarith
import float.basic
import float.div

variables {k m n : nat}

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

-- Wee test

def M : matrix (fin 2) (fin 2) ℚ 
| ⟨0, _⟩ ⟨0, _⟩ := 1
| ⟨0, _⟩ ⟨1, _⟩ := 1/2
| ⟨1, _⟩ ⟨0, _⟩ := 1/2
| _      _      := 1 

#eval ((LDLT M).1 * (LDLT M).2 * (LDLT M).1.transpose) 1 1 -- 5/4 ==> Not good 

-- New definition.

variables {R : Type*} [linear_ordered_ring R] [has_div R]

meta def decompose_aux_2
: fin n → 
  fin n → 
  matrix (fin n) (fin n) R → 
  matrix (fin n) (fin n) R → 
  matrix (fin n) (fin n) R →
  (matrix (fin n) (fin n) R)
| j i A L D := 
let S : fin i → R := 
  λ a, let a' := fin.cast_le i.2 a in (L j a') * (L i a') * (D a' a') in
let L' : matrix (fin n) (fin n) R := 
  λ a b, if (a = j) && (b = i) then ((A j i) - finset.univ.sum S) / (D i i) else L a b in
if h : j.1 + 1 ≥ n
then L' 
else decompose_aux_2 ⟨j.val + 1, lt_of_not_ge' h⟩ i A L' D

meta def decompose_aux
: fin n → 
  matrix (fin n) (fin n) R → 
  matrix (fin n) (fin n) R → 
  matrix (fin n) (fin n) R →
  (matrix (fin n) (fin n) R) × (matrix (fin n) (fin n) R)
| i A L D := 
let S : fin i → R := 
  λ a, let a' := fin.cast_le i.2 a in (L i a') * (L i a') * (D a' a') in 
let D' : matrix (fin n) (fin n) R := 
  λ a b, if (a = i) && (b = i) then (A i i) - finset.univ.sum S else D a b in 
let L' : matrix (fin n) (fin n) R := 
  decompose_aux_2 i i A L D' in
if h : i.1 + 1 ≥ n
then ⟨L', D'⟩ 
else 
  let i' : fin n := ⟨i.val + 1, lt_of_not_ge' h⟩ in
  decompose_aux i' A L' D'

variables (n)

meta def decompose (h : 0 < n) (A : matrix (fin n) (fin n) R)  
: (matrix (fin n) (fin n) R) × (matrix (fin n) (fin n) R) :=
let D : matrix (fin n) (fin n) R := λ x y, 0 in 
let L : matrix (fin n) (fin n) R := λ x y, 0 in 
decompose_aux ⟨0, h⟩ A L D

-- TODO: Fix this. Make a tactic.
meta def decompose_2 (A : matrix (fin 2) (fin 2) R) 
: (matrix (fin 2) (fin 2) R) × (matrix (fin 2) (fin 2) R) :=
decompose 2 (by linarith : 0 < 2) A

#eval let LD := decompose_2 M in (LD.1 * LD.2 * LD.1.transpose) 0 0 -- 1
#eval let LD := decompose_2 M in (LD.1 * LD.2 * LD.1.transpose) 0 1 -- 1/2
#eval let LD := decompose_2 M in (LD.1 * LD.2 * LD.1.transpose) 1 0 -- 1/2
#eval let LD := decompose_2 M in (LD.1 * LD.2 * LD.1.transpose) 1 1 -- 1


-- More tests.
@[reducible] def N := 3

lemma hN : 0 < N := by { unfold N, linarith, }

def H : matrix (fin N) (fin N) rat 
--| ⟨i, _⟩ ⟨j, _⟩ := float.mk 1 0
| ⟨i, _⟩ ⟨j, _⟩ := 1

meta def decompose_N (A : matrix (fin N) (fin N) R) 
: (matrix (fin N) (fin N) R) × (matrix (fin N) (fin N) R) :=
decompose N hN A

--set_option timeout 1000000

#eval let LD := decompose_N H in (LD.1 * LD.2 * LD.1.transpose) 0 0

