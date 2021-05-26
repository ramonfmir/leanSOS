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
∀ i, (∑ j, if i ≠ j then abs (A i j) else 0) ≤ abs (A i i)

namespace diagdom 

open tactic
open interactive (parse)
open lean.parser (ident)

private meta def unfold_matrix : tactic unit :=
do 
  `(diagdom %%M) ← target,
  dunfold_target [name.from_string M.to_string] {}

meta def prove_diagdom : tactic unit :=
`[unfold_matrix, intros i, fin_cases i; simp only [fin.sum_univ_succ]; dec_trivial]

def I2 : matrix (fin 2) (fin 2) ℚ := 
![![1, 0], 
  ![0, 1]]

def I4 : matrix (fin 4) (fin 4) ℚ :=
![![1, 0, 0, 0], 
  ![0, 1, 0, 0], 
  ![0, 0, 1, 0], 
  ![0, 0, 0, 1]]

def A : matrix (fin 3) (fin 3) ℚ :=
![![ 3, -2,  1],
  ![ 1, -3,  2],
  ![-1,  2,  4]]

def F : matrix (fin 9) (fin 9) ℚ :=
![![1, 0.04, 0.05, 0.04, 0.02, 0.01, 0.02, 0.05, 0.03], 
  ![0.02, 1, 0.02, 0.02, 0.03, 0.02, 0.04, 0.04, 0.02], 
  ![0.04, 0.02, 1, 0.05, 0.05, 0.04, 0.03, 0.05, 0.03], 
  ![0.05, 0.04, 0.03, 1, 0.02, 0.05, 0.03, 0.02, 0.03], 
  ![0.03, 0.03, 0.05, 0.03, 1, 0.02, 0.04, 0.01, 0.03], 
  ![0.05, 0.04, 0.02, 0.01, 0.03, 1, 0.04, 0.05, 0.04], 
  ![0.03, 0.04, 0.04, 0.02, 0.02, 0.03, 1, 0.01, 0.01], 
  ![0.04, 0.03, 0.01, 0.02, 0.05, 0.02, 0.02, 1, 0.02], 
  ![0.05, 0.01, 0.03, 0.04, 0.04, 0.05, 0.03, 0.03, 1]]

set_option profiler true

set_option timeout 10000000

example : diagdom I2 := by prove_diagdom 

example : diagdom I4 := by prove_diagdom

example : diagdom A := by prove_diagdom

--example : diagdom F := by prove_diagdom

end diagdom
