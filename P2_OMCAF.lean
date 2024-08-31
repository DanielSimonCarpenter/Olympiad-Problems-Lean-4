import MIL.Common
import Mathlib

variable (c d e: ℝ)

open Real
namespace tactic.ring_exp

def is_irrational (x : ℝ) : Prop := ¬ ∃ (q : ℚ), (q : ℝ) = x

theorem irrational_exponents (a : ℝ) (h : is_irrational a) : ¬ (∃ r1 r2 : ℚ, a^17 = r1 ∧ a^19 = r2) := by
  by_contra h1
  rcases h1 with ⟨r1, r2, h17, h19⟩
  have idk: (a^17)^9=a^153 :=by
    norm_num
  have idk2: (a^19)^8=a^152 :=by
    norm_num
  have h3 : ∃ r3 : ℚ, a^153 = r3:=by
    use r1^9
    rw[← idk]
    rw[h17]
    exact Eq.symm (Rat.cast_pow r1 9)

  have h4 : ∃ r4 : ℚ, a^152 = r4:=by
    use r2^8
    rw[← idk2]
    rw[h19]
    exact Eq.symm (Rat.cast_pow r2 8)
  rcases h3 with ⟨r3, h3⟩
  rcases h4 with ⟨r4, h4⟩
  have h5 : a = r3 / r4:=by
    rw[← h3, ← h4]
    rw [h3, h4, ←div_eq_mul_inv, ←pow_sub]
    norm_num
  exact h (rational_iff_rat.mp ⟨r3, r4, h5⟩),
