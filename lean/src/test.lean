/-
  Testing out the tactic.
-/

import data.real.basic
import data.mv_polynomial.basic
import .sos

open mv_polynomial

example : (C (0 : ℝ)) ≤ (X 5) * (X 1):= begin 
  sos, 
  sorry,
end 