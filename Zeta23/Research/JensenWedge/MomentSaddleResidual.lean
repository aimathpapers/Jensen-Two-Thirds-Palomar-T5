import Zeta23.Research.JensenWedge.MovingSaddleSixth

/-!
# Moment-variable saddle bound and residual insertion

The saddle main is first differentiated in `N` and then pulled back through
`N=2M-2`.  At order six the affine chain contributes the exact factor
`2^6=64`.  This module proves the corresponding reduced value is uniformly
bounded on the manuscript's inner Cauchy disc and inserts that value into the
concrete outer-box sixth-residual inequality.

As in `MovingSaddleSixth`, the result is intentionally phrased for the exact
reduced value.  Calling it the actual derivative of `G₀(2M-2)` still requires
the named CAS identification certificate.
-/

noncomputable section

namespace Zeta23.Research.JensenWedge

open Complex Metric

/-- The order-six reduced saddle value after the affine change `N=2M-2`.
The multiplier is exactly `2^6`. -/
def manuscriptMomentSaddleMainSix (M : ℂ) : ℂ :=
  64 * manuscriptSaddleMainSix (coefficientMellinParameter M)

/-- Every point in the inner residual disc maps to the already constructed
outer saddle sector under `N=2M-2`. -/
theorem coefficientMellinParameter_mem_leanSaddleSector_of_innerDisc
    {n : ℕ} (hnLarge : Real.exp (leanSaddleCutoff + 2) < (n : ℝ))
    {z : ℂ} (hzNorm : ‖z‖ ≤ manuscriptInteriorCauchyRadius (n : ℝ)) :
    coefficientMellinParameter ((n : ℂ) + z) ∈ leanSaddleSector := by
  have hnpos : (0 : ℝ) < n :=
    (Real.exp_pos _).trans hnLarge
  have hzOuter : (n : ℂ) + z ∈
      Metric.closedBall ((n : ℝ) : ℂ) (manuscriptCauchyRadius (n : ℝ)) := by
    rw [Metric.mem_closedBall, dist_eq_norm]
    have hdiff : (n : ℂ) + z - ((n : ℝ) : ℂ) = z := by
      push_cast
      ring
    rw [hdiff]
    unfold manuscriptInteriorCauchyRadius at hzNorm
    unfold manuscriptCauchyRadius
    nlinarith
  have hM := manuscriptCauchy_closedBall_subset_sector hnLarge hzOuter
  exact leanTwoShiftAdmissible_base (leanCoefficientSector_admissible hM.2)

/-- On the inner disc, the shifted Mellin parameter has norm at least the
positive integer center. -/
theorem coefficientMellinParameter_norm_ge_center_of_innerDisc
    {n : ℕ} (hnLarge : Real.exp (leanSaddleCutoff + 2) < (n : ℝ))
    {z : ℂ} (hzNorm : ‖z‖ ≤ manuscriptInteriorCauchyRadius (n : ℝ)) :
    (n : ℝ) ≤ ‖coefficientMellinParameter ((n : ℂ) + z)‖ := by
  have hzOuter : (n : ℂ) + z ∈
      Metric.closedBall ((n : ℝ) : ℂ) (manuscriptCauchyRadius (n : ℝ)) := by
    rw [Metric.mem_closedBall, dist_eq_norm]
    have hdiff : (n : ℂ) + z - ((n : ℝ) : ℂ) = z := by
      push_cast
      ring
    rw [hdiff]
    unfold manuscriptInteriorCauchyRadius at hzNorm
    unfold manuscriptCauchyRadius
    have hnpos : (0 : ℝ) < n := (Real.exp_pos _).trans hnLarge
    nlinarith
  exact (manuscriptCauchy_shifted_norm_bounds hnLarge hzOuter).1

/-- Uniform sixth-saddle bound in the moment variable, including the exact
affine-chain factor and comparison to the real integer center. -/
theorem manuscriptMomentSaddleMainSix_norm_le_on_innerDisc
    {n : ℕ} (hnLarge : Real.exp (leanSaddleCutoff + 2) < (n : ℝ))
    {z : ℂ} (hzNorm : ‖z‖ ≤ manuscriptInteriorCauchyRadius (n : ℝ)) :
    ‖manuscriptMomentSaddleMainSix ((n : ℂ) + z)‖ ≤
      1280000 / ((n : ℝ) ^ 5 * Real.log (n : ℝ)) := by
  let N : ℂ := coefficientMellinParameter ((n : ℂ) + z)
  have hnpos : (0 : ℝ) < n := (Real.exp_pos _).trans hnLarge
  have hnLargeOne : (1 : ℝ) < n := by
    have hcutpos : 0 < leanSaddleCutoff + 2 := by
      norm_num [leanSaddleCutoff]
    have hone := Real.one_lt_exp_iff.mpr hcutpos
    exact hone.trans hnLarge
  have hlogn : 0 < Real.log (n : ℝ) := Real.log_pos hnLargeOne
  have hNsector : N ∈ leanSaddleSector :=
    coefficientMellinParameter_mem_leanSaddleSector_of_innerDisc hnLarge hzNorm
  have hNlower : (n : ℝ) ≤ ‖N‖ :=
    coefficientMellinParameter_norm_ge_center_of_innerDisc hnLarge hzNorm
  have hNpos : 0 < ‖N‖ := hnpos.trans_le hNlower
  have hlogLower : Real.log (n : ℝ) ≤ Real.log ‖N‖ :=
    Real.log_le_log hnpos hNlower
  have hpowLower : (n : ℝ) ^ 5 ≤ ‖N‖ ^ 5 :=
    pow_le_pow_left₀ hnpos.le hNlower 5
  have hdenomLower :
      (n : ℝ) ^ 5 * Real.log (n : ℝ) ≤
        ‖N‖ ^ 5 * Real.log ‖N‖ := by
    exact mul_le_mul hpowLower hlogLower
      (Real.log_pos hnLargeOne).le (pow_nonneg (norm_nonneg N) 5)
  have hbase := manuscriptSaddleMainSix_norm_le hNsector
  have hdenomCenterPos : 0 < (n : ℝ) ^ 5 * Real.log (n : ℝ) :=
    mul_pos (pow_pos hnpos 5) hlogn
  have hquotient :
      20000 / (‖N‖ ^ 5 * Real.log ‖N‖) ≤
        20000 / ((n : ℝ) ^ 5 * Real.log (n : ℝ)) := by
    exact div_le_div_of_nonneg_left (by norm_num) hdenomCenterPos hdenomLower
  unfold manuscriptMomentSaddleMainSix
  rw [norm_mul]
  norm_num only [Complex.norm_ofNat]
  calc
    64 * ‖manuscriptSaddleMainSix N‖ ≤
        64 * (20000 / (‖N‖ ^ 5 * Real.log ‖N‖)) := by
      gcongr
    _ ≤ 64 * (20000 / ((n : ℝ) ^ 5 * Real.log (n : ℝ))) := by
      gcongr
    _ = 1280000 / ((n : ℝ) ^ 5 * Real.log (n : ℝ)) := by ring

/-- The full concrete sixth residual with the reduced moving-saddle value
inserted.  No free `mainSix` or `Hmain` variable remains. -/
theorem manuscriptSixthResidual_outerBox_reducedSaddle_norm_le
    {y : BranchPoint} (hy : InOuterParameterBox y)
    {n : ℕ} (hn : 8 ≤ n)
    (hnLarge : Real.exp (leanSaddleCutoff + 2) < (n : ℝ))
    {e : ℝ} (he : 0 < e) (he12 : e ≤ 1 / 12)
    {z : ℂ}
    (hzNorm : ‖z‖ ≤ manuscriptInteriorCauchyRadius (n : ℝ))
    (hzRe : -(n : ℝ) / 2 ≤ z.re) :
    ‖manuscriptSixthResidualValue
        (manuscriptXiSixthLogDecomposition
          (manuscriptMomentSaddleMainSix ((n : ℂ) + z)) ((n : ℂ) + z)) n
        (residualParameterA y n e)
        (residualParameterB y n e)
        (residualParameterC y n)
        (residualParameterD y n e) z‖ ≤
      (1280000 / ((n : ℝ) ^ 5 * Real.log (n : ℝ)) +
          Nat.factorial 6 *
            ((3 / 2 : ℝ) * manuscriptCauchyEpsilon (n : ℝ)) /
              manuscriptInteriorCauchyRadius (n : ℝ) ^ 6) +
        120 * (6 * n * e) / (((n / 4 - 1 : ℕ) : ℝ) ^ 6) +
        120 * ((5 / 12 : ℝ) * n * e + 1 / 2) /
          (((n / 4 - 1 : ℕ) : ℝ) ^ 6) +
        24 / (((n / 4 - 1 : ℕ) : ℝ) ^ 5) := by
  exact manuscriptSixthResidual_outerBox_norm_le hy hn hnLarge he he12
    hzNorm hzRe
      (manuscriptMomentSaddleMainSix_norm_le_on_innerDisc hnLarge hzNorm)

/-- Sharpened concrete residual with the separate distant-`A` floor anchor.
This is the form from which the final `1/(n^5 log n)` rate is derived. -/
theorem manuscriptSixthResidual_outerBox_farA_norm_le
    {y : BranchPoint} (hy : InOuterParameterBox y)
    {n : ℕ} (hn : 8 ≤ n)
    (hnLarge : Real.exp (leanSaddleCutoff + 2) < (n : ℝ))
    {e : ℝ} (he : 0 < e) (he12 : e ≤ 1 / 12)
    {z : ℂ}
    (hzNorm : ‖z‖ ≤ manuscriptInteriorCauchyRadius (n : ℝ))
    (hzRe : -(n : ℝ) / 2 ≤ z.re) :
    ‖manuscriptSixthResidualValue
        (manuscriptXiSixthLogDecomposition
          (manuscriptMomentSaddleMainSix ((n : ℂ) + z)) ((n : ℂ) + z)) n
        (residualParameterA y n e)
        (residualParameterB y n e)
        (residualParameterC y n)
        (residualParameterD y n e) z‖ ≤
      (1280000 / ((n : ℝ) ^ 5 * Real.log (n : ℝ)) +
          Nat.factorial 6 *
            ((3 / 2 : ℝ) * manuscriptCauchyEpsilon (n : ℝ)) /
              manuscriptInteriorCauchyRadius (n : ℝ) ^ 6) +
        120 * (6 * n * e) / (((n / 4 - 1 : ℕ) : ℝ) ^ 6) +
        120 * ((5 / 12 : ℝ) * n * e + 1 / 2) /
          (((n / 4 - 1 : ℕ) : ℝ) ^ 6) +
        24 / (((⌊(n : ℝ) / e⌋₊ - 1 : ℕ) : ℝ) ^ 5) := by
  let C := residualParameterCertificate_of_outerBox hy hn he he12 hzRe
  have hA := residualParameterA_floor_anchor_of_outerBox hy hn he he12 hzRe
  have hzCenter : (n : ℂ) + z ∈
      Metric.closedBall ((n : ℝ) : ℂ)
        (manuscriptInteriorCauchyRadius (n : ℝ)) := by
    rw [Metric.mem_closedBall, dist_eq_norm]
    convert hzNorm using 1 <;> push_cast <;> ring
  have hmain := manuscriptMomentSaddleMainSix_norm_le_on_innerDisc
    hnLarge hzNorm
  have hSix := manuscriptXiSixthLogDecomposition_norm_le
    hnLarge hzCenter hmain
  have hbase := manuscriptSixthResidualValue_norm_le_separateA
    C.anchor_two hA.1 hSix C.B_right C.C_right C.D_right C.half_right hA.2
  apply hbase.trans
  gcongr
  · exact C.BC_distance
  · exact C.Dhalf_distance

end Zeta23.Research.JensenWedge
