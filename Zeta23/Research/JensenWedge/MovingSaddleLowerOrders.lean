import Zeta23.Research.JensenWedge.SaddleLowerOrderLimits
import Zeta23.Research.JensenWedge.MovingSaddleSixth
import Zeta23.Research.JensenWedge.CoefficientAssembly

/-!
# Lower derivatives on the concrete moving saddle

This module evaluates the exact reduced functions `H2,...,H5` on the
contraction-selected saddle branch.  Two explicit scalar rate inequalities
put the reduced coordinates in the tiny bidisc, after which the limiting
constants are kernel consequences of `SaddleLowerOrderLimits`.

As at order six, identification with actual iterated derivatives of the
displayed `G0` is isolated in a named record.  The downstream
`MovingSaddleDerivativeIdentification` module constructs the record in Lean;
the independent SymPy and Mathematica calculations remain corroboration.
-/

namespace Zeta23.Research.JensenWedge

open Complex

noncomputable section

def manuscriptSaddleMainTwo (N : ℂ) : ℂ :=
  saddleH2 (manuscriptSaddleR N) (manuscriptSaddleSigma N) /
    (N * quantitativeSaddleBranch N)

def manuscriptSaddleMainThree (N : ℂ) : ℂ :=
  saddleH3 (manuscriptSaddleR N) (manuscriptSaddleSigma N) /
    (N ^ 2 * quantitativeSaddleBranch N)

def manuscriptSaddleMainFour (N : ℂ) : ℂ :=
  saddleH4 (manuscriptSaddleR N) (manuscriptSaddleSigma N) /
    (N ^ 3 * quantitativeSaddleBranch N)

def manuscriptSaddleMainFive (N : ℂ) : ℂ :=
  saddleH5 (manuscriptSaddleR N) (manuscriptSaddleSigma N) /
    (N ^ 4 * quantitativeSaddleBranch N)

/-- Explicit symbolic-identification seam for the lower derivative tower.
It has exactly the four equalities independently checked by both CAS paths. -/
structure ManuscriptG0LowerIdentification (N : ℂ) : Prop where
  orderTwo : iteratedDeriv 2 manuscriptSaddleG0 N = manuscriptSaddleMainTwo N
  orderThree : iteratedDeriv 3 manuscriptSaddleG0 N = manuscriptSaddleMainThree N
  orderFour : iteratedDeriv 4 manuscriptSaddleG0 N = manuscriptSaddleMainFour N
  orderFive : iteratedDeriv 5 manuscriptSaddleG0 N = manuscriptSaddleMainFive N

/-- The two scalar rate estimates put the moving saddle in any declared
reduced-coordinate box.  The previously used `10^-7` and the final Step-4
`10^-14` boxes are specializations of this statement. -/
theorem manuscriptSaddle_scaled_coordinates_in_box_of_rates
    {N : ℂ} (hN : N ∈ leanSaddleSector) {rho : ℝ}
    (hrRate : 2 / Real.log ‖N‖ ≤ rho)
    (hsigmaRate : 2 * Real.log ‖N‖ / ‖N‖ ≤ rho) :
    ‖manuscriptSaddleR N‖ ≤ rho ∧
      ‖manuscriptSaddleSigma N‖ ≤ rho := by
  have hinput := leanSaddleSector_quantitative hN
  have hNpos : 0 < ‖N‖ := norm_pos_iff.mpr hinput.parameter_ne_zero
  have hlogRadial : leanSaddleCutoff < Real.log ‖N‖ :=
    (Real.lt_log_iff_exp_lt hNpos).2 hN.1
  have hlogpos : 0 < Real.log ‖N‖ :=
    (by norm_num [leanSaddleCutoff] : (0 : ℝ) < leanSaddleCutoff).trans hlogRadial
  have hLne : quantitativeSaddleBranch N ≠ 0 :=
    (quantitativeSaddleBranch_scaled_bounds hinput).1
  have hLpos : 0 < ‖quantitativeSaddleBranch N‖ := norm_pos_iff.mpr hLne
  have hLlower := quantitativeSaddleBranch_norm_lower_half_realLog hN
  have hrRaw : 1 / ‖quantitativeSaddleBranch N‖ ≤
      2 / Real.log ‖N‖ := by
    calc
      1 / ‖quantitativeSaddleBranch N‖ ≤
          1 / (Real.log ‖N‖ / 2) := by
        exact one_div_le_one_div_of_le (by positivity) hLlower
      _ = 2 / Real.log ‖N‖ := by field_simp
  have hLupper := quantitativeSaddleBranch_norm_le_two_log_norm hN
  constructor
  · unfold manuscriptSaddleR
    rw [norm_div, norm_one]
    exact hrRaw.trans hrRate
  · unfold manuscriptSaddleSigma
    rw [norm_div]
    exact (div_le_div_of_nonneg_right hLupper hNpos.le).trans hsigmaRate

/-- Two scalar rates imply the strong reduced-coordinate box. -/
theorem manuscriptSaddle_scaled_coordinates_in_lowerLimitBox
    {N : ℂ} (hN : N ∈ leanSaddleSector)
    (hrRate : 2 / Real.log ‖N‖ ≤ saddleLowerLimitRadius)
    (hsigmaRate : 2 * Real.log ‖N‖ / ‖N‖ ≤ saddleLowerLimitRadius) :
    ‖manuscriptSaddleR N‖ ≤ saddleLowerLimitRadius ∧
      ‖manuscriptSaddleSigma N‖ ≤ saddleLowerLimitRadius := by
  exact manuscriptSaddle_scaled_coordinates_in_box_of_rates hN hrRate hsigmaRate

/-- Final reduced-value bounds used by the effective interval certificate. -/
theorem manuscriptSaddle_lower_reduced_limits_final
    {N : ℂ} (hN : N ∈ leanSaddleSector)
    (hrRate : 2 / Real.log ‖N‖ ≤ saddleFinalLimitRadius)
    (hsigmaRate : 2 * Real.log ‖N‖ / ‖N‖ ≤ saddleFinalLimitRadius) :
    ‖saddleH2 (manuscriptSaddleR N) (manuscriptSaddleSigma N) - 1‖ <
        saddleFinalLimitError ∧
    ‖saddleH3 (manuscriptSaddleR N) (manuscriptSaddleSigma N) + 1‖ <
        saddleFinalLimitError ∧
    ‖saddleH4 (manuscriptSaddleR N) (manuscriptSaddleSigma N) - 2‖ <
        saddleFinalLimitError ∧
    ‖saddleH5 (manuscriptSaddleR N) (manuscriptSaddleSigma N) + 6‖ <
        saddleFinalLimitError := by
  rcases manuscriptSaddle_scaled_coordinates_in_box_of_rates hN hrRate hsigmaRate with
    ⟨hr, hsigma⟩
  exact ⟨saddleH2_sub_one_norm_lt_final hr hsigma,
    saddleH3_add_one_norm_lt_final hr hsigma,
    saddleH4_sub_two_norm_lt_final hr hsigma,
    saddleH5_add_six_norm_lt_final hr hsigma⟩

theorem manuscriptSaddle_lower_reduced_limits
    {N : ℂ} (hN : N ∈ leanSaddleSector)
    (hrRate : 2 / Real.log ‖N‖ ≤ saddleLowerLimitRadius)
    (hsigmaRate : 2 * Real.log ‖N‖ / ‖N‖ ≤ saddleLowerLimitRadius) :
    ‖saddleH2 (manuscriptSaddleR N) (manuscriptSaddleSigma N) - 1‖ <
        saddleLowerLimitError ∧
    ‖saddleH3 (manuscriptSaddleR N) (manuscriptSaddleSigma N) + 1‖ <
        saddleLowerLimitError ∧
    ‖saddleH4 (manuscriptSaddleR N) (manuscriptSaddleSigma N) - 2‖ <
        saddleLowerLimitError ∧
    ‖saddleH5 (manuscriptSaddleR N) (manuscriptSaddleSigma N) + 6‖ <
        saddleLowerLimitError := by
  rcases manuscriptSaddle_scaled_coordinates_in_lowerLimitBox hN hrRate hsigmaRate with
    ⟨hr, hsigma⟩
  exact ⟨saddleH2_sub_one_norm_lt hr hsigma,
    saddleH3_add_one_norm_lt hr hsigma,
    saddleH4_sub_two_norm_lt hr hsigma,
    saddleH5_add_six_norm_lt hr hsigma⟩

private theorem saddleParameter_mul_mainTwo
    {N : ℂ} (hN : N ∈ leanSaddleSector) :
    N * quantitativeSaddleBranch N * manuscriptSaddleMainTwo N =
      saddleH2 (manuscriptSaddleR N) (manuscriptSaddleSigma N) := by
  have hNne := (leanSaddleSector_quantitative hN).parameter_ne_zero
  have hLne := (quantitativeSaddleBranch_scaled_bounds
    (leanSaddleSector_quantitative hN)).1
  unfold manuscriptSaddleMainTwo
  field_simp [hNne, hLne]

private theorem saddleParameter_mul_mainThree
    {N : ℂ} (hN : N ∈ leanSaddleSector) :
    N ^ 2 * quantitativeSaddleBranch N * manuscriptSaddleMainThree N =
      saddleH3 (manuscriptSaddleR N) (manuscriptSaddleSigma N) := by
  have hNne := (leanSaddleSector_quantitative hN).parameter_ne_zero
  have hLne := (quantitativeSaddleBranch_scaled_bounds
    (leanSaddleSector_quantitative hN)).1
  unfold manuscriptSaddleMainThree
  field_simp [hNne, hLne]

private theorem saddleParameter_mul_mainFour
    {N : ℂ} (hN : N ∈ leanSaddleSector) :
    N ^ 3 * quantitativeSaddleBranch N * manuscriptSaddleMainFour N =
      saddleH4 (manuscriptSaddleR N) (manuscriptSaddleSigma N) := by
  have hNne := (leanSaddleSector_quantitative hN).parameter_ne_zero
  have hLne := (quantitativeSaddleBranch_scaled_bounds
    (leanSaddleSector_quantitative hN)).1
  unfold manuscriptSaddleMainFour
  field_simp [hNne, hLne]

private theorem saddleParameter_mul_mainFive
    {N : ℂ} (hN : N ∈ leanSaddleSector) :
    N ^ 4 * quantitativeSaddleBranch N * manuscriptSaddleMainFive N =
      saddleH5 (manuscriptSaddleR N) (manuscriptSaddleSigma N) := by
  have hNne := (leanSaddleSector_quantitative hN).parameter_ne_zero
  have hLne := (quantitativeSaddleBranch_scaled_bounds
    (leanSaddleSector_quantitative hN)).1
  unfold manuscriptSaddleMainFive
  field_simp [hNne, hLne]

/-- Kernel-checked normalized lower-derivative estimates after supplying the
named symbolic identification. -/
theorem iteratedDeriv_manuscriptSaddleG0_lower_normalized_limits
    {N : ℂ} (hN : N ∈ leanSaddleSector)
    (hrRate : 2 / Real.log ‖N‖ ≤ saddleLowerLimitRadius)
    (hsigmaRate : 2 * Real.log ‖N‖ / ‖N‖ ≤ saddleLowerLimitRadius)
    (I : ManuscriptG0LowerIdentification N) :
    ‖N * quantitativeSaddleBranch N * iteratedDeriv 2 manuscriptSaddleG0 N - 1‖ <
        saddleLowerLimitError ∧
    ‖N ^ 2 * quantitativeSaddleBranch N * iteratedDeriv 3 manuscriptSaddleG0 N + 1‖ <
        saddleLowerLimitError ∧
    ‖N ^ 3 * quantitativeSaddleBranch N * iteratedDeriv 4 manuscriptSaddleG0 N - 2‖ <
        saddleLowerLimitError ∧
    ‖N ^ 4 * quantitativeSaddleBranch N * iteratedDeriv 5 manuscriptSaddleG0 N + 6‖ <
        saddleLowerLimitError := by
  rcases manuscriptSaddle_lower_reduced_limits hN hrRate hsigmaRate with
    ⟨h2, h3, h4, h5⟩
  rw [I.orderTwo, I.orderThree, I.orderFour, I.orderFive,
    saddleParameter_mul_mainTwo hN, saddleParameter_mul_mainThree hN,
    saddleParameter_mul_mainFour hN, saddleParameter_mul_mainFive hN]
  exact ⟨h2, h3, h4, h5⟩

end

end Zeta23.Research.JensenWedge
