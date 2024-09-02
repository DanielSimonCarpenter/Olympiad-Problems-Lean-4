import MIL.Common
import Mathlib

open Real
open Classical
open Set

namespace tactic.ring_exp
set_option maxRecDepth 2000000
set_option maxHeartbeats 2000000
set_option trace.split.failure true

structure irreducible (x: ℕ) : Prop :=
(not_unit : x>1)
(is_unit_or_is_unit' : ∀a b, x = a * b → a=1 ∨ b=1)

def prime : Set ℕ := { x | Nat.Prime x }

def consecutive_primes (p q : ℕ) : Prop :=
  Nat.Prime p ∧ Nat.Prime q ∧ p < q ∧ (∀ k : ℕ, p < k ∧ k < q → ¬ Nat.Prime k)

def consecutive_odd_primes (r s : ℕ) : Prop :=
  consecutive_primes r s ∧ ∃ k t : ℕ, r = 2 * k + 1 ∧ s = 2 * t + 1

theorem sum_of_consecutive_odd_primes (r s : ℕ) (hr : Nat.Prime r) (hs : Nat.Prime s)
  (h_consec : consecutive_odd_primes r s) : ∃ a b c, r + s = a * b * c ∧ 1 < a ∧ 1 < b ∧ 1 < c := by
  unfold consecutive_odd_primes at h_consec
  rcases h_consec with ⟨⟨hr, hs, hrs, hnone⟩, ⟨k, t, hr_eq, hs_eq⟩⟩
  have div: r + s = 2 * (k + t + 1):=by
    rw[hr_eq, hs_eq]
    ring
  have big:t>k:=by
    linarith [hrs, hr_eq, hs_eq]
  have n_bounds : r < t+k+1 ∧ t+k+1 < s :=by
    rw[hr_eq, hs_eq]
    rw[two_mul, two_mul]
    simp
    exact big
  have n_composite : ¬Nat.Prime (t+k+1):=by
    intro hn
    exact hnone (t + k + 1) n_bounds hn
  have bigger1:k>=1:=by
    refine Nat.one_le_iff_ne_zero.mpr ?_
    intro h
    have r1: r=1:=by
      rw[hr_eq, h]
    have notprime: ¬Nat.Prime (r):=by
      rw[r1]
      exact Nat.not_prime_one
    exact notprime hr
  have big1:t+k+1>=2:=by
    simp
    exact le_add_of_le_right bigger1
  have product: ∃ a b, (t+k+1)=a*b∧a>1∧ b>1:=by
    obtain ⟨a, ha1, ha2⟩ := Nat.exists_dvd_of_not_prime2 big1 n_composite
    use a, (t+k+1)/a
    rcases ha2 with ⟨h1, h2⟩
    refine (and_iff_right ?h.ha).mpr ?h.a
    exact Eq.symm (Nat.mul_div_cancel' ha1)
    refine ⟨?h.a.left, ?h.a.right⟩
    exact h1
    refine (Nat.lt_div_iff_mul_lt ha1 1).mpr ?h.a.right.a
    simp
    exact h2
  rcases product with ⟨h_prod, ha, hb, hc⟩
  use 2, h_prod, ha
  refine ⟨?h.left, ?h.right⟩
  have final: t+k+1=(r+s)/2:=by
    rw[hr_eq, hs_eq]
    refine Eq.symm (Nat.div_eq_of_eq_mul_right ?H1 ?H2)
    trivial
    ring
  rw[mul_assoc, ← hb, final]
  refine Eq.symm (Nat.two_mul_div_two_of_even ?h.left.a)
  use k+t+1
  rw[← two_mul]
  exact div
  exact if_false_right.mp hc
