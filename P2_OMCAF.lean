import MIL.Common
import Mathlib

variable (c d e: ℝ)
variable {G : Type*} [Group G]
set_option maxRecDepth 2000000

def nonzero_reals_mul_group (x:ℝ):=
 x≠0
open Real

def is_irrational (x : ℝ) : Prop := ¬ ∃ (q : ℚ), (q : ℝ) = x

theorem irrational_exponents (a : ℝ) (h : is_irrational a) (nozero : a≠0): ¬ (∃ r1 r2 : ℚ, a^17 = r1 ∧ a^19 = r2) := by
  by_contra h1
  rcases h1 with ⟨r1, r2, h17, h19⟩
  have idk: (a^17)^9=a^153 :=by
    rw [← pow_mul]
  have idk2: (a^19)^8=a^152 :=by
    rw[← pow_mul]
  have h3 : ∃ r3 : ℚ, a^153 = r3:=by
    use r1^9
    rw[← idk, h17]
    exact Eq.symm (Rat.cast_pow r1 9)
  have h4 : ∃ r4 : ℚ, a^152 = r4:=by
    use r2^8
    rw[← idk2, h19]
    exact Eq.symm (Rat.cast_pow r2 8)
  rcases h3 with ⟨r3, h3⟩
  rcases h4 with ⟨r4, h4⟩
  have h5 : a = r3 / r4:=by
    rw[← h3, ← h4]
    have h: a^153 / a^152 = a^(153 - 152):=by
      rw[div_eq_mul_inv]
      refine Eq.symm (pow_sub₀ a ?ha ?hb)
      exact nozero
      linarith
    rw[h]
    simp
  have h6: ∃ x:ℚ, x=a:=by
    use r3/r4
    simp
    symm
    exact h5
  rcases h6 with ⟨r5, h7⟩
  have h_contradiction: ∃ (q : ℚ), q=a:=by
    use r5
  exact h h_contradiction
