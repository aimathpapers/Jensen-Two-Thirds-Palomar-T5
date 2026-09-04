import Zeta23.Research.JensenWedge.LeadingGaussianRelative
import Mathlib.Analysis.Complex.ExponentialBounds

/-!
# Fixed absolute Gaussian moments on the curvature scale

The Gamma-form moment theorem is exact but not yet in the `|K|` scale used by
the relative saddle estimate.  This module performs that finite arithmetic
for orders four, six, eight, and ten.  The constants are intentionally coarse
powers of two: this makes every inequality kernel-transparent and leaves no
floating-point evaluation in the proof.
-/

namespace Zeta23.Research.JensenWedge

open Complex MeasureTheory

noncomputable section

theorem gamma_five_halves_le_two : Real.Gamma (5 / 2 : ℝ) ≤ 2 := by
  have hsqrt : Real.sqrt Real.pi ≤ 2 := by
    rw [Real.sqrt_le_iff]
    exact ⟨by norm_num, by nlinarith [Real.pi_le_four]⟩
  have hg := Real.Gamma_nat_add_half 2
  norm_num at hg
  rw [hg]
  linarith

theorem gamma_seven_halves_le_four : Real.Gamma (7 / 2 : ℝ) ≤ 4 := by
  have hsqrt : Real.sqrt Real.pi ≤ 2 := by
    rw [Real.sqrt_le_iff]
    exact ⟨by norm_num, by nlinarith [Real.pi_le_four]⟩
  have hg := Real.Gamma_nat_add_half 3
  norm_num at hg
  rw [hg]
  linarith

theorem gamma_nine_halves_le_fourteen : Real.Gamma (9 / 2 : ℝ) ≤ 14 := by
  have hsqrt : Real.sqrt Real.pi ≤ 2 := by
    rw [Real.sqrt_le_iff]
    exact ⟨by norm_num, by nlinarith [Real.pi_le_four]⟩
  have hg := Real.Gamma_nat_add_half 4
  norm_num at hg
  rw [hg]
  linarith

theorem gamma_eleven_halves_le_sixty : Real.Gamma (11 / 2 : ℝ) ≤ 60 := by
  have hsqrt : Real.sqrt Real.pi ≤ 2 := by
    rw [Real.sqrt_le_iff]
    exact ⟨by norm_num, by nlinarith [Real.pi_le_four]⟩
  have hg := Real.Gamma_nat_add_half 5
  norm_num at hg
  rw [hg]
  linarith

/-- Convert the Gamma-form absolute moment to a coarse `|K|` power whenever
`1 < Re K` and `|K| <= 2 Re K`. -/
theorem integral_norm_pow_mul_leadingGaussian_le_scaled
    {K : ℂ} (hK : 1 < K.re) (hcomp : ‖K‖ ≤ 2 * K.re)
    (n : ℕ) (p G P : ℝ)
    (hp : p = (n + 1 : ℝ) / 2) (hp0 : 0 ≤ p)
    (hGamma : Real.Gamma p ≤ G)
    (hEight : (8 : ℝ) ^ p ≤ P) :
    (∫ r : ℝ, ‖(r : ℂ) ^ n * leadingGaussian K r‖) ≤
      3 * G * P * ‖K‖ ^ (-p) := by
  have hKre : 0 < K.re := by linarith
  have hKnorm : 0 < ‖K‖ := by
    exact norm_pos_iff.mpr (by
      intro hzero
      rw [hzero] at hK
      norm_num at hK)
  have hexp : Real.exp (1 / K.re) ≤ 3 := by
    calc
      Real.exp (1 / K.re) ≤ Real.exp 1 := by
        exact Real.exp_monotone (by
          rw [div_le_one hKre]
          exact hK.le)
      _ ≤ 3 := Real.exp_one_lt_three.le
  have hbase : ‖K‖ / 8 ≤ K.re / 4 := by linarith
  have hbasePos : 0 < ‖K‖ / 8 := div_pos hKnorm (by norm_num)
  have hpow : (K.re / 4) ^ (-p) ≤ (‖K‖ / 8) ^ (-p) :=
    Real.rpow_le_rpow_of_nonpos hbasePos hbase (neg_nonpos.mpr hp0)
  have hscale : (‖K‖ / 8) ^ (-p) =
      (8 : ℝ) ^ p * ‖K‖ ^ (-p) := by
    rw [Real.div_rpow hKnorm.le (by norm_num : (0 : ℝ) ≤ 8),
      Real.rpow_neg hKnorm.le, Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 8)]
    field_simp [Real.rpow_pos_of_pos hKnorm p,
      Real.rpow_pos_of_pos (by norm_num : (0 : ℝ) < 8) p]
  have hbaseScale : (K.re / 4) ^ (-p) ≤
      P * ‖K‖ ^ (-p) := by
    calc
      (K.re / 4) ^ (-p) ≤ (‖K‖ / 8) ^ (-p) := hpow
      _ = (8 : ℝ) ^ p * ‖K‖ ^ (-p) := hscale
      _ ≤ P * ‖K‖ ^ (-p) := by gcongr
  have hP0 : 0 ≤ P :=
    (Real.rpow_pos_of_pos (by norm_num : (0 : ℝ) < 8) p).le.trans hEight
  have hraw := integral_norm_pow_mul_leadingGaussian_le hKre n
  have hexponent : (-(n + 1 : ℝ) / 2) = -p := by rw [hp]; ring
  rw [hexponent, ← hp] at hraw
  calc
    (∫ r : ℝ, ‖(r : ℂ) ^ n * leadingGaussian K r‖) ≤
        Real.exp (1 / K.re) *
          (2 * ((K.re / 4) ^ (-p) * (1 / 2) * Real.Gamma p)) := hraw
    _ = Real.exp (1 / K.re) * ((K.re / 4) ^ (-p) * Real.Gamma p) := by ring
    _ ≤ 3 * ((K.re / 4) ^ (-p) * Real.Gamma p) := by gcongr
    _ ≤ 3 * (P * ‖K‖ ^ (-p) * Real.Gamma p) := by gcongr
    _ ≤ 3 * (P * ‖K‖ ^ (-p) * G) := by gcongr
    _ = 3 * G * P * ‖K‖ ^ (-p) := by ring

theorem quantitativeSaddleBranch_fourthGaussianMoment_le
    {s : ℂ} (hs : s ∈ leanSaddleSector) :
    let K := leadingCurvature s (quantitativeSaddleBranch s)
    (∫ r : ℝ, ‖(r : ℂ) ^ 4 * leadingGaussian K r‖) ≤
      4096 * ‖K‖ ^ (-(5 / 2 : ℝ)) := by
  dsimp only
  let K := leadingCurvature s (quantitativeSaddleBranch s)
  have hstrong := quantitativeSaddleBranch_curvature_strong_bounds hs
  have h8 : (8 : ℝ) ^ (5 / 2 : ℝ) ≤ 512 := by
    calc
      (8 : ℝ) ^ (5 / 2 : ℝ) ≤ 8 ^ (3 : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num)
      _ = 512 := by norm_num [Real.rpow_natCast]
  have h := integral_norm_pow_mul_leadingGaussian_le_scaled
    hstrong.1 hstrong.2 4 (5 / 2) 2 512
    (by norm_num) (by norm_num) gamma_five_halves_le_two h8
  change (∫ r : ℝ, ‖(r : ℂ) ^ 4 * leadingGaussian K r‖) ≤
    4096 * ‖K‖ ^ (-(5 / 2 : ℝ))
  calc
    (∫ r : ℝ, ‖(r : ℂ) ^ 4 * leadingGaussian K r‖) ≤
        3 * 2 * 512 * ‖K‖ ^ (-(5 / 2 : ℝ)) := h
    _ ≤ 4096 * ‖K‖ ^ (-(5 / 2 : ℝ)) := by
      gcongr <;> norm_num

theorem quantitativeSaddleBranch_sixthGaussianMoment_le
    {s : ℂ} (hs : s ∈ leanSaddleSector) :
    let K := leadingCurvature s (quantitativeSaddleBranch s)
    (∫ r : ℝ, ‖(r : ℂ) ^ 6 * leadingGaussian K r‖) ≤
      65536 * ‖K‖ ^ (-(7 / 2 : ℝ)) := by
  dsimp only
  let K := leadingCurvature s (quantitativeSaddleBranch s)
  have hstrong := quantitativeSaddleBranch_curvature_strong_bounds hs
  have h8 : (8 : ℝ) ^ (7 / 2 : ℝ) ≤ 4096 := by
    calc
      (8 : ℝ) ^ (7 / 2 : ℝ) ≤ 8 ^ (4 : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num)
      _ = 4096 := by norm_num [Real.rpow_natCast]
  have h := integral_norm_pow_mul_leadingGaussian_le_scaled
    hstrong.1 hstrong.2 6 (7 / 2) 4 4096
    (by norm_num) (by norm_num) gamma_seven_halves_le_four h8
  change (∫ r : ℝ, ‖(r : ℂ) ^ 6 * leadingGaussian K r‖) ≤
    65536 * ‖K‖ ^ (-(7 / 2 : ℝ))
  calc
    (∫ r : ℝ, ‖(r : ℂ) ^ 6 * leadingGaussian K r‖) ≤
        3 * 4 * 4096 * ‖K‖ ^ (-(7 / 2 : ℝ)) := h
    _ ≤ 65536 * ‖K‖ ^ (-(7 / 2 : ℝ)) := by
      gcongr <;> norm_num

theorem quantitativeSaddleBranch_eighthGaussianMoment_le
    {s : ℂ} (hs : s ∈ leanSaddleSector) :
    let K := leadingCurvature s (quantitativeSaddleBranch s)
    (∫ r : ℝ, ‖(r : ℂ) ^ 8 * leadingGaussian K r‖) ≤
      2097152 * ‖K‖ ^ (-(9 / 2 : ℝ)) := by
  dsimp only
  let K := leadingCurvature s (quantitativeSaddleBranch s)
  have hstrong := quantitativeSaddleBranch_curvature_strong_bounds hs
  have h8 : (8 : ℝ) ^ (9 / 2 : ℝ) ≤ 32768 := by
    calc
      (8 : ℝ) ^ (9 / 2 : ℝ) ≤ 8 ^ (5 : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num)
      _ = 32768 := by norm_num [Real.rpow_natCast]
  have h := integral_norm_pow_mul_leadingGaussian_le_scaled
    hstrong.1 hstrong.2 8 (9 / 2) 14 32768
    (by norm_num) (by norm_num) gamma_nine_halves_le_fourteen h8
  change (∫ r : ℝ, ‖(r : ℂ) ^ 8 * leadingGaussian K r‖) ≤
    2097152 * ‖K‖ ^ (-(9 / 2 : ℝ))
  calc
    (∫ r : ℝ, ‖(r : ℂ) ^ 8 * leadingGaussian K r‖) ≤
        3 * 14 * 32768 * ‖K‖ ^ (-(9 / 2 : ℝ)) := h
    _ ≤ 2097152 * ‖K‖ ^ (-(9 / 2 : ℝ)) := by
      gcongr <;> norm_num

theorem quantitativeSaddleBranch_tenthGaussianMoment_le
    {s : ℂ} (hs : s ∈ leanSaddleSector) :
    let K := leadingCurvature s (quantitativeSaddleBranch s)
    (∫ r : ℝ, ‖(r : ℂ) ^ 10 * leadingGaussian K r‖) ≤
      67108864 * ‖K‖ ^ (-(11 / 2 : ℝ)) := by
  dsimp only
  let K := leadingCurvature s (quantitativeSaddleBranch s)
  have hstrong := quantitativeSaddleBranch_curvature_strong_bounds hs
  have h8 : (8 : ℝ) ^ (11 / 2 : ℝ) ≤ 262144 := by
    calc
      (8 : ℝ) ^ (11 / 2 : ℝ) ≤ 8 ^ (6 : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num)
      _ = 262144 := by norm_num [Real.rpow_natCast]
  have h := integral_norm_pow_mul_leadingGaussian_le_scaled
    hstrong.1 hstrong.2 10 (11 / 2) 60 262144
    (by norm_num) (by norm_num) gamma_eleven_halves_le_sixty h8
  change (∫ r : ℝ, ‖(r : ℂ) ^ 10 * leadingGaussian K r‖) ≤
    67108864 * ‖K‖ ^ (-(11 / 2 : ℝ))
  calc
    (∫ r : ℝ, ‖(r : ℂ) ^ 10 * leadingGaussian K r‖) ≤
        3 * 60 * 262144 * ‖K‖ ^ (-(11 / 2 : ℝ)) := h
    _ ≤ 67108864 * ‖K‖ ^ (-(11 / 2 : ℝ)) := by
      gcongr <;> norm_num

end

end Zeta23.Research.JensenWedge
