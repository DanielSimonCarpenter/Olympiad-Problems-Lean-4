import MIL.Common
import Mathlib

variable (c d e: ℝ)

open Real

example (a n: ℕ): n*n+5*n+6≠a*a:= by
have h1: n*n+5*n+6=(n+2)*(n+3):= by
  ring
rw[h1]
refine Nat.ne_iff_lt_or_gt.mpr ?_
by_cases h2:a≥n+3
left
refine Nat.mul_lt_mul_of_lt_of_le' h2 h2 ?_
exact Nat.zero_lt_succ (n + 2)
right
have h4 : a ≤ n + 2:=by
  exact Nat.le_of_not_lt h2
refine Nat.mul_lt_mul_of_le_of_lt h4 ?_ ?_
exact Nat.gt_of_not_le h2
exact Nat.zero_lt_succ (n + 1)
