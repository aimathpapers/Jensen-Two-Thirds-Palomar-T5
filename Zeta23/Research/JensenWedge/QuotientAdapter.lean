import Mathlib

/-!
# Four quotient equations recover six coefficients

This module formalizes the elementary adapter used by the two-Jacobi branch.
After taking logarithms, equality of four consecutive quotient invariants is
equality of four consecutive second differences.  Two normalizations then
recover all six coefficient logarithms.  No asymptotic or special-function
input occurs here.
-/

namespace Zeta23.Research.JensenWedge

/-- The second forward difference at an arbitrary natural index. -/
def secondDiff (a : ℕ → ℝ) (k : ℕ) : ℝ :=
  a (k + 2) - 2 * a (k + 1) + a k

/-- Four equal quotient coordinates together with the two initial
normalizations recover coefficient coordinates `0,...,5`. -/
theorem fourQuotients_twoNormalizations_sixCoefficients
    (a b : ℕ → ℝ)
    (h0 : a 0 = b 0) (h1 : a 1 = b 1)
    (hq : ∀ k ≤ 3, secondDiff a k = secondDiff b k) :
    ∀ j : Fin 6, a j = b j := by
  have h2 : a 2 = b 2 := by
    have h := hq 0 (by norm_num)
    simp only [secondDiff] at h
    norm_num at h
    linarith
  have h3 : a 3 = b 3 := by
    have h := hq 1 (by norm_num)
    simp only [secondDiff] at h
    norm_num at h
    linarith
  have h4 : a 4 = b 4 := by
    have h := hq 2 (by norm_num)
    simp only [secondDiff] at h
    norm_num at h
    linarith
  have h5 : a 5 = b 5 := by
    have h := hq 3 (by norm_num)
    simp only [secondDiff] at h
    norm_num at h
    linarith
  intro j
  fin_cases j <;> assumption

/-- Pointwise equality of the six logarithmic coefficient coordinates gives
pointwise equality after exponentiation. -/
theorem exp_sixCoefficients_of_log_sixCoefficients
    (a b : ℕ → ℝ) (h : ∀ j : Fin 6, a j = b j) :
    ∀ j : Fin 6, Real.exp (a j) = Real.exp (b j) := by
  intro j
  rw [h j]

end Zeta23.Research.JensenWedge
