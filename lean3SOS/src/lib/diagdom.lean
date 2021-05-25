/-
  Definition of diagonally dominant matrices and tactic.
-/

import data.matrix.basic 
import data.matrix.notation
import data.rat.basic 
import data.finset.basic

import tactic.fin_cases
import tactic.linarith

open_locale big_operators

def diagdom {n : ℕ} (A : matrix (fin n) (fin n) ℚ) : Prop :=
∀ i, (∑ j, if i ≠ j then A i j else 0) ≤ A i i

namespace diagdom 

open tactic
open interactive (parse)
open lean.parser (ident)

private meta def unfold_matrix : tactic unit :=
do 
  `(diagdom %%M) ← target,
  dunfold_target [name.from_string M.to_string] {}

meta def prove_diagdom : tactic unit :=
`[unfold_matrix, intros i, fin_cases i; simp [fin.sum_univ_succ]; linarith]

def I2 : matrix (fin 2) (fin 2) ℚ := 
![![1, 0], 
  ![0, 1]]

def I4 : matrix (fin 4) (fin 4) ℚ :=
![![1, 0, 0, 0], 
  ![0, 1, 0, 0], 
  ![0, 0, 1, 0], 
  ![0, 0, 0, 1]]

set_option profiler true

example : diagdom I2 := by prove_diagdom 

example : diagdom I4 := by prove_diagdom 

end diagdom
