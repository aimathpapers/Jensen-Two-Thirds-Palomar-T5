import Zeta23.Research.JensenWedge.LeadingGaussianTruncation

/-!
# Relative normalization of the leading Gaussian

The final central estimate is relative to the exact whole-line Gaussian.
This module proves that the Gaussian main term is large enough to divide by
and that the signed cubic correction is already of relative order `1 / |K|`.
The lower bound retains the complex square root and exponential exactly; no
choice of an informal asymptotic branch is used.
-/

namespace Zeta23.Research.JensenWedge

open Complex Filter MeasureTheory Set

noncomputable section

/-- The exact complex Gaussian main term dominates the natural
`|K|^(-1/2)` scale. -/
theorem norm_integral_leadingGaussian_lower
    {K : ℂ} (hK : 0 < K.re) :
    ‖K‖ ^ (-(1 / 2 : ℝ)) ≤ ‖∫ r : ℝ, leadingGaussian K r‖ := by
  have hKne : K ≠ 0 := by
    intro hzero
    rw [hzero] at hK
    simpa using hK
  have hKnorm : 0 < ‖K‖ := norm_pos_iff.mpr hKne
  have hbase :
      1 / ‖K‖ ≤ ‖((2 * Real.pi : ℂ) / K)‖ := by
    have hnum : ‖(2 * Real.pi : ℂ)‖ = 2 * Real.pi := by
      rw [norm_mul]
      norm_num [norm_real, abs_of_pos Real.pi_pos]
    rw [norm_div, hnum]
    exact (div_le_div_iff₀ hKnorm hKnorm).2 (by
      nlinarith [Real.pi_gt_three])
  have hsqrt :
      ‖K‖ ^ (-(1 / 2 : ℝ)) ≤
        ‖((2 * Real.pi : ℂ) / K)‖ ^ (1 / 2 : ℝ) := by
    have hinvpos : 0 < 1 / ‖K‖ := one_div_pos.mpr hKnorm
    have hrpow := Real.rpow_le_rpow hinvpos.le hbase
      (by norm_num : (0 : ℝ) ≤ 1 / 2)
    calc
      ‖K‖ ^ (-(1 / 2 : ℝ)) = (‖K‖ ^ (1 / 2 : ℝ))⁻¹ := by
        rw [Real.rpow_neg hKnorm.le]
      _ = (1 / ‖K‖) ^ (1 / 2 : ℝ) := by
        rw [Real.div_rpow zero_le_one hKnorm.le, Real.one_rpow]
        simp only [one_div]
      _ ≤ _ := hrpow
  have hexpRe : 0 ≤ (1 / (2 * K)).re := by
    rw [one_div, Complex.inv_re]
    apply div_nonneg
    · have htwo : (2 * K).re = 2 * K.re := by norm_num
      rw [htwo]
      linarith
    · exact Complex.normSq_nonneg _
  rw [integral_leadingGaussian hK, norm_mul,
    show (1 / 2 : ℂ) = ((1 / 2 : ℝ) : ℂ) by norm_num,
    Complex.norm_cpow_real, Complex.norm_exp]
  calc
    ‖K‖ ^ (-(1 / 2 : ℝ)) ≤
        ‖((2 * Real.pi : ℂ) / K)‖ ^ (1 / 2 : ℝ) := hsqrt
    _ ≤ ‖((2 * Real.pi : ℂ) / K)‖ ^ (1 / 2 : ℝ) *
          Real.exp (1 / (2 * K)).re := by
      have hone : 1 ≤ Real.exp (1 / (2 * K)).re := by
        simpa only [Real.exp_zero] using Real.exp_monotone hexpRe
      exact le_mul_of_one_le_right (Real.rpow_nonneg (norm_nonneg _) _) hone

/-- A coefficient of size at most `|K|` turns the exact signed cubic moment
into a relative correction of size at most `4 / |K|`. -/
theorem norm_leadingCubicCorrection_le
    {K c : ℂ} (hK : 0 < K.re) (hKone : 1 ≤ ‖K‖)
    (hc : ‖c‖ ≤ ‖K‖) :
    ‖c * (3 / K ^ 2 + 1 / K ^ 3)‖ ≤ 4 / ‖K‖ := by
  have hKne : K ≠ 0 := by
    intro hzero
    rw [hzero] at hK
    simpa using hK
  have hKpos : 0 < ‖K‖ := norm_pos_iff.mpr hKne
  rw [norm_mul]
  calc
    ‖c‖ * ‖3 / K ^ 2 + 1 / K ^ 3‖ ≤
        ‖K‖ * (‖3 / K ^ 2‖ + ‖1 / K ^ 3‖) := by
      exact mul_le_mul hc (norm_add_le _ _) (norm_nonneg _) (norm_nonneg _)
    _ = ‖K‖ * (3 / ‖K‖ ^ 2 + 1 / ‖K‖ ^ 3) := by
      rw [norm_div, norm_div, norm_pow, norm_pow]
      norm_num
    _ ≤ 4 / ‖K‖ := by
      field_simp [hKpos.ne']
      nlinarith [sq_nonneg (‖K‖ - 1)]

/-- Whole-line signed cubic approximation, now stated as an explicit
relative error from the exact Gaussian main term. -/
theorem integral_leadingCubicGaussianApproximation_relative_error_le
    {K c : ℂ} (hK : 0 < K.re) (hKone : 1 ≤ ‖K‖)
    (hc : ‖c‖ ≤ ‖K‖) :
    ‖(∫ r : ℝ, leadingCubicGaussianApproximation K c r) -
        ∫ r : ℝ, leadingGaussian K r‖ ≤
      (4 / ‖K‖) * ‖∫ r : ℝ, leadingGaussian K r‖ := by
  rw [integral_leadingCubicGaussianApproximation hK]
  have hcorr := norm_leadingCubicCorrection_le hK hKone hc
  calc
    ‖(∫ r : ℝ, leadingGaussian K r) *
          (1 + c * (3 / K ^ 2 + 1 / K ^ 3)) -
        ∫ r : ℝ, leadingGaussian K r‖ =
        ‖∫ r : ℝ, leadingGaussian K r‖ *
          ‖c * (3 / K ^ 2 + 1 / K ^ 3)‖ := by
      rw [← norm_mul]
      congr 1
      ring
    _ ≤ ‖∫ r : ℝ, leadingGaussian K r‖ * (4 / ‖K‖) := by
      gcongr
    _ = (4 / ‖K‖) * ‖∫ r : ℝ, leadingGaussian K r‖ := by ring

/-- Main-term lower bound specialized to the selected saddle branch. -/
theorem quantitativeSaddleBranch_norm_integral_leadingGaussian_lower
    {s : ℂ} (hs : s ∈ leanSaddleSector) :
    ‖leadingCurvature s (quantitativeSaddleBranch s)‖ ^ (-(1 / 2 : ℝ)) ≤
      ‖∫ r : ℝ,
        leadingGaussian (leadingCurvature s (quantitativeSaddleBranch s)) r‖ :=
  norm_integral_leadingGaussian_lower
    (quantitativeSaddleBranch_curvature_re_pos hs)

/-- Relative cubic correction specialized to the selected saddle branch. -/
theorem quantitativeSaddleBranch_cubicGaussian_relative_error_le
    {s : ℂ} (hs : s ∈ leanSaddleSector) :
    let L := quantitativeSaddleBranch s
    let K := leadingCurvature s L
    ‖(∫ r : ℝ,
          leadingCubicGaussianApproximation K (leadingCubicCoefficient s L) r) -
        ∫ r : ℝ, leadingGaussian K r‖ ≤
      (4 / ‖K‖) * ‖∫ r : ℝ, leadingGaussian K r‖ := by
  dsimp only
  apply integral_leadingCubicGaussianApproximation_relative_error_le
  · exact quantitativeSaddleBranch_curvature_re_pos hs
  · linarith [quantitativeSaddleBranch_curvature_norm_ge_fourThousand hs]
  · exact quantitativeSaddleBranch_cubicCoefficient_norm_le hs

end

end Zeta23.Research.JensenWedge
