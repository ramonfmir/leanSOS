import data.matrix.basic
import float.basic
import lib.ldlt
import data.nat.gcd

set_option profiler true

open matrix

-- Test 1: 2x2 rat

def M1 : matrix (fin 2) (fin 2) ℚ 
| ⟨0, _⟩ ⟨0, _⟩ := 1
| ⟨0, _⟩ ⟨1, _⟩ := 1/2
| ⟨1, _⟩ ⟨0, _⟩ := 1/2
| _      _      := 1 

#eval ((LDLT M1).1 * (LDLT M1).2 * (LDLT M1).1.transpose) 1 1 -- 5/4 ==> Not good 

#eval let LD := decompose 2 M1 in (LD.1 * diagonal LD.2 * LD.1.transpose) 0 0 -- 1
#eval let LD := decompose 2 M1 in (LD.1 * diagonal LD.2 * LD.1.transpose) 0 1 -- 1/2
#eval let LD := decompose 2 M1 in (LD.1 * diagonal LD.2 * LD.1.transpose) 1 0 -- 1/2
#eval let LD := decompose 2 M1 in (LD.1 * diagonal LD.2 * LD.1.transpose) 1 1 -- 1

-- Test 1: 2x2 float

def M2 : matrix (fin 2) (fin 2) 𝔽 
| ⟨0, _⟩ ⟨0, _⟩ := float.mk 1 0
| ⟨0, _⟩ ⟨1, _⟩ := float.mk 1 (-1)
| ⟨1, _⟩ ⟨0, _⟩ := float.mk 1 (-1)
| _      _      := float.mk 1 0

#eval let LD := decompose 2 M2 in (LD.1 * diagonal LD.2 * LD.1.transpose) 0 0 -- 1
#eval let LD := decompose 2 M2 in (LD.1 * diagonal LD.2 * LD.1.transpose) 0 1 -- 1/2
#eval let LD := decompose 2 M2 in (LD.1 * diagonal LD.2 * LD.1.transpose) 1 0 -- 1/2
#eval let LD := decompose 2 M2 in (LD.1 * diagonal LD.2 * LD.1.transpose) 1 1 -- 1

-- Test 3: 7x7 rat 

def H1 : matrix (fin 7) (fin 7) rat 
| ⟨i, _⟩ ⟨j, _⟩ := 1 / 2^(i + j)

#eval let LD := decompose 7 H1 in (LD.1 * diagonal LD.2 * LD.1.transpose) 0 0 -- 1

-- Test 4: 7x7 rat 

def H2 : matrix (fin 7) (fin 7) float 
| ⟨i, _⟩ ⟨j, _⟩ := float.mk 1 (i + j)

#eval let LD := decompose 7 H2 in (LD.1 * diagonal LD.2 * LD.1.transpose) 0 0 -- 1
