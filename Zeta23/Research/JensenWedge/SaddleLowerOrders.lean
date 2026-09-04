import Zeta23.Research.JensenWedge.SaddleOrderSixAlgebra

/-!
# Exact lower-order reduced saddle functions

The order-six recurrence already stores the exact numerator tables for
orders two through five.  This module turns those tables into the reduced
rational functions used by the signed lower-derivative estimates.  Lean
checks their values at the limiting point `(r,sigma)=(0,0)` and proves
uniform whole-bidisc norm bounds from the same coefficientwise majorant used
at order six.

The central values `1,-1,2,-6` are before the affine change `N=2M-2`.
They become the manuscript constants `2,-2,4,-12` after the chain and
normalization factors are inserted.  No identification with an actual
derivative of `G0` is asserted in this algebra-only module.
-/

namespace Zeta23.Research.JensenWedge

open Complex

noncomputable section

def h2Numerator (r sigma : ℂ) : ℂ :=
  evalBivariateTerms h2Terms r sigma

def h3Numerator (r sigma : ℂ) : ℂ :=
  evalBivariateTerms h3Terms r sigma

def h4Numerator (r sigma : ℂ) : ℂ :=
  evalBivariateTerms h4Terms r sigma

def h5Numerator (r sigma : ℂ) : ℂ :=
  evalBivariateTerms h5Terms r sigma

def h2ReducedDenominator (r sigma : ℂ) : ℂ :=
  (4 + 4 * r - 3 * sigma) ^ 4

def h3ReducedDenominator (r sigma : ℂ) : ℂ :=
  (4 + 4 * r - 3 * sigma) ^ 6

def h4ReducedDenominator (r sigma : ℂ) : ℂ :=
  (4 + 4 * r - 3 * sigma) ^ 8

def h5ReducedDenominator (r sigma : ℂ) : ℂ :=
  (4 + 4 * r - 3 * sigma) ^ 10

def saddleH2 (r sigma : ℂ) : ℂ :=
  h2Numerator r sigma / h2ReducedDenominator r sigma

def saddleH3 (r sigma : ℂ) : ℂ :=
  h3Numerator r sigma / h3ReducedDenominator r sigma

def saddleH4 (r sigma : ℂ) : ℂ :=
  h4Numerator r sigma / h4ReducedDenominator r sigma

def saddleH5 (r sigma : ℂ) : ℂ :=
  h5Numerator r sigma / h5ReducedDenominator r sigma

theorem saddleH2_zero_zero : saddleH2 0 0 = 1 := by
  norm_num [saddleH2, h2Numerator, h2ReducedDenominator,
    evalBivariateTerms, h2Terms, BivariateTerm.eval]

theorem saddleH3_zero_zero : saddleH3 0 0 = -1 := by
  norm_num [saddleH3, h3Numerator, h3ReducedDenominator,
    evalBivariateTerms, h3Terms, BivariateTerm.eval]

theorem saddleH4_zero_zero : saddleH4 0 0 = 2 := by
  norm_num [saddleH4, h4Numerator, h4ReducedDenominator,
    evalBivariateTerms, h4Terms, BivariateTerm.eval]

theorem saddleH5_zero_zero : saddleH5 0 0 = -6 := by
  norm_num [saddleH5, h5Numerator, h5ReducedDenominator,
    evalBivariateTerms, h5Terms, BivariateTerm.eval]

def h2NumeratorMajorant : ℝ :=
  bivariateTermsMajorant h2Terms (7 / 50)

def h3NumeratorMajorant : ℝ :=
  bivariateTermsMajorant h3Terms (7 / 50)

def h4NumeratorMajorant : ℝ :=
  bivariateTermsMajorant h4Terms (7 / 50)

def h5NumeratorMajorant : ℝ :=
  bivariateTermsMajorant h5Terms (7 / 50)

theorem h2NumeratorMajorant_exact :
    h2NumeratorMajorant =
      (20530955113 : ℝ) / 39062500 := by
  norm_num [h2NumeratorMajorant, bivariateTermsMajorant, h2Terms,
    BivariateTerm.majorant]

theorem h3NumeratorMajorant_exact :
    h3NumeratorMajorant =
      (170660199148573 : ℝ) / 12207031250 := by
  norm_num [h3NumeratorMajorant, bivariateTermsMajorant, h3Terms,
    BivariateTerm.majorant]

theorem h4NumeratorMajorant_exact :
    h4NumeratorMajorant =
      (1083873490718801961 : ℝ) / 1525878906250 := by
  norm_num [h4NumeratorMajorant, bivariateTermsMajorant, h4Terms,
    BivariateTerm.majorant]

theorem h5NumeratorMajorant_exact :
    h5NumeratorMajorant =
      (126829035840942491148441 : ℝ) / 2384185791015625 := by
  norm_num [h5NumeratorMajorant, bivariateTermsMajorant, h5Terms,
    BivariateTerm.majorant]

private theorem lowerReducedDenominator_norm_lower
    {r sigma : ℂ} (hr : ‖r‖ ≤ 7 / 50) (hsigma : ‖sigma‖ ≤ 7 / 50)
    (q : ℕ) :
    ((151 : ℝ) / 50) ^ q ≤ ‖(4 + 4 * r - 3 * sigma) ^ q‖ := by
  rw [norm_pow]
  exact pow_le_pow_left₀ (by norm_num)
    (saddle_reduced_denominator_norm_lower hr hsigma) q

private theorem lowerReducedDenominator_ne_zero
    {r sigma : ℂ} (hr : ‖r‖ ≤ 7 / 50) (hsigma : ‖sigma‖ ≤ 7 / 50)
    (q : ℕ) :
    (4 + 4 * r - 3 * sigma) ^ q ≠ 0 := by
  have hlower := lowerReducedDenominator_norm_lower hr hsigma q
  intro hzero
  rw [hzero, norm_zero] at hlower
  have hpositive : 0 < ((151 : ℝ) / 50) ^ q := by positivity
  linarith

theorem h2Numerator_norm_le
    {r sigma : ℂ} (hr : ‖r‖ ≤ 7 / 50) (hsigma : ‖sigma‖ ≤ 7 / 50) :
    ‖h2Numerator r sigma‖ ≤ h2NumeratorMajorant := by
  exact norm_evalBivariateTerms_le_majorant h2Terms (by norm_num) hr hsigma

theorem h3Numerator_norm_le
    {r sigma : ℂ} (hr : ‖r‖ ≤ 7 / 50) (hsigma : ‖sigma‖ ≤ 7 / 50) :
    ‖h3Numerator r sigma‖ ≤ h3NumeratorMajorant := by
  exact norm_evalBivariateTerms_le_majorant h3Terms (by norm_num) hr hsigma

theorem h4Numerator_norm_le
    {r sigma : ℂ} (hr : ‖r‖ ≤ 7 / 50) (hsigma : ‖sigma‖ ≤ 7 / 50) :
    ‖h4Numerator r sigma‖ ≤ h4NumeratorMajorant := by
  exact norm_evalBivariateTerms_le_majorant h4Terms (by norm_num) hr hsigma

theorem h5Numerator_norm_le
    {r sigma : ℂ} (hr : ‖r‖ ≤ 7 / 50) (hsigma : ‖sigma‖ ≤ 7 / 50) :
    ‖h5Numerator r sigma‖ ≤ h5NumeratorMajorant := by
  exact norm_evalBivariateTerms_le_majorant h5Terms (by norm_num) hr hsigma

private theorem norm_div_lt_of_majorant
    {z d : ℂ} {A B C : ℝ}
    (hz : ‖z‖ ≤ A) (hB : 0 < B) (hd : B ≤ ‖d‖)
    (hAC : A / B < C) :
    ‖z / d‖ < C := by
  rw [norm_div]
  have hA : 0 ≤ A := (norm_nonneg z).trans hz
  exact (div_le_div₀ hA hz hB hd).trans_lt hAC

theorem saddleH2_norm_lt_seven
    {r sigma : ℂ} (hr : ‖r‖ ≤ 7 / 50) (hsigma : ‖sigma‖ ≤ 7 / 50) :
    ‖saddleH2 r sigma‖ < 7 := by
  apply norm_div_lt_of_majorant (h2Numerator_norm_le hr hsigma)
      (B := ((151 : ℝ) / 50) ^ 4)
  · positivity
  · exact lowerReducedDenominator_norm_lower hr hsigma 4
  · rw [h2NumeratorMajorant_exact]
    norm_num

theorem saddleH3_norm_lt_nineteen
    {r sigma : ℂ} (hr : ‖r‖ ≤ 7 / 50) (hsigma : ‖sigma‖ ≤ 7 / 50) :
    ‖saddleH3 r sigma‖ < 19 := by
  apply norm_div_lt_of_majorant (h3Numerator_norm_le hr hsigma)
      (B := ((151 : ℝ) / 50) ^ 6)
  · positivity
  · exact lowerReducedDenominator_norm_lower hr hsigma 6
  · rw [h3NumeratorMajorant_exact]
    norm_num

theorem saddleH4_norm_lt_oneHundredThree
    {r sigma : ℂ} (hr : ‖r‖ ≤ 7 / 50) (hsigma : ‖sigma‖ ≤ 7 / 50) :
    ‖saddleH4 r sigma‖ < 103 := by
  apply norm_div_lt_of_majorant (h4Numerator_norm_le hr hsigma)
      (B := ((151 : ℝ) / 50) ^ 8)
  · positivity
  · exact lowerReducedDenominator_norm_lower hr hsigma 8
  · rw [h4NumeratorMajorant_exact]
    norm_num

theorem saddleH5_norm_lt_eightHundredFortyThree
    {r sigma : ℂ} (hr : ‖r‖ ≤ 7 / 50) (hsigma : ‖sigma‖ ≤ 7 / 50) :
    ‖saddleH5 r sigma‖ < 843 := by
  apply norm_div_lt_of_majorant (h5Numerator_norm_le hr hsigma)
      (B := ((151 : ℝ) / 50) ^ 10)
  · positivity
  · exact lowerReducedDenominator_norm_lower hr hsigma 10
  · rw [h5NumeratorMajorant_exact]
    norm_num

end

end Zeta23.Research.JensenWedge
