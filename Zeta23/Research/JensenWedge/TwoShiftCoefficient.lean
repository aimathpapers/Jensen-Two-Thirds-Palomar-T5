import Zeta23.Research.JensenWedge.ThetaMomentAssembly

/-!
# Two-shift coefficient error assembly

This module converts the complete T3--T4 theta-moment estimate into a
pointwise relative error, proves its main term is nonzero, and checks the
exact cancellation algebra for the `s` and `s+2` moments.  The remaining
analytic input is isolated precisely as the relative comparison of the two
saddle main terms; it is not assumed by any theorem that claims a concrete
bound.
-/

namespace Zeta23.Research.JensenWedge

open Complex

noncomputable section

def twoShiftRelativeError
    (coefficient saddleScale lowerError upperError ratioError : ℂ) : ℂ :=
  (coefficient * lowerError - saddleScale ^ 2 *
    (ratioError + upperError + ratioError * upperError)) /
      (coefficient - saddleScale ^ 2)

theorem twoShiftRelativeError_exact
    {coefficient amplitude saddleScale lowerError upperError ratioError : ℂ}
    (hdenom : coefficient - saddleScale ^ 2 ≠ 0) :
    coefficient * (amplitude * (1 + lowerError)) -
        amplitude * saddleScale ^ 2 * (1 + ratioError) * (1 + upperError) =
      (amplitude * (coefficient - saddleScale ^ 2)) *
        (1 + twoShiftRelativeError coefficient saddleScale
          lowerError upperError ratioError) := by
  unfold twoShiftRelativeError
  field_simp
  ring

theorem twoShiftAssembly_of_errors
    {scale coefficient amplitude saddleScale lowerMoment upperMoment
      lowerError upperError ratioError : ℂ}
    (hdenom : coefficient - saddleScale ^ 2 ≠ 0)
    (hlower : lowerMoment = amplitude * (1 + lowerError))
    (hupper : upperMoment =
      amplitude * saddleScale ^ 2 * (1 + ratioError) * (1 + upperError)) :
    scale * (coefficient * lowerMoment - upperMoment) =
      (scale * amplitude * (coefficient - saddleScale ^ 2)) *
        (1 + twoShiftRelativeError coefficient saddleScale
          lowerError upperError ratioError) := by
  rw [hlower, hupper]
  rw [twoShiftRelativeError_exact hdenom]
  ring

theorem holomorphicRelativeError_factorization
    {actual main : ℂ → ℂ} {z : ℂ} (hmain : main z ≠ 0) :
    actual z = main z * (1 + holomorphicRelativeError actual main z) := by
  unfold holomorphicRelativeError
  field_simp
  ring

theorem holomorphicRelativeError_norm_le_of_sub_le
    {actual main : ℂ → ℂ} {z : ℂ} {epsilon : ℝ}
    (hmain : main z ≠ 0)
    (hsub : ‖actual z - main z‖ ≤ epsilon * ‖main z‖) :
    ‖holomorphicRelativeError actual main z‖ ≤ epsilon := by
  have hnorm : 0 < ‖main z‖ := norm_pos_iff.mpr hmain
  have hid : holomorphicRelativeError actual main z =
      (actual z - main z) / main z := by
    unfold holomorphicRelativeError
    field_simp
  rw [hid, norm_div, div_le_iff₀ hnorm]
  exact hsub

def saddleMomentMain (s : ℂ) : ℂ :=
  let L := quantitativeSaddleBranch s
  let K := leadingCurvature s L
  leadingIntegrand s L * ∫ r : ℝ, leadingGaussian K r

def fullThetaMomentRelativeError (s : ℂ) : ℂ :=
  holomorphicRelativeError fullThetaMoment saddleMomentMain s

def fullThetaMomentErrorCoefficient : ℝ :=
  71000004 + 2 * (2 * 20 ^ 15 * (Nat.factorial 15 : ℝ))

theorem saddleMomentMain_ne_zero
    {s : ℂ} (hs : s ∈ leanSaddleSector) : saddleMomentMain s ≠ 0 := by
  let L : ℂ := quantitativeSaddleBranch s
  let K : ℂ := leadingCurvature s L
  let M : ℂ := ∫ r : ℝ, leadingGaussian K r
  have hKne : K ≠ 0 := by
    have hKre : 0 < K.re := quantitativeSaddleBranch_curvature_re_pos hs
    intro hzero
    rw [hzero] at hKre
    simp at hKre
  have hKnorm : 0 < ‖K‖ := norm_pos_iff.mpr hKne
  have hlower : ‖K‖ ^ (-(1 / 2 : ℝ)) ≤ ‖M‖ := by
    exact quantitativeSaddleBranch_norm_integral_leadingGaussian_lower hs
  have hMnorm : 0 < ‖M‖ :=
    lt_of_lt_of_le (Real.rpow_pos_of_pos hKnorm _) hlower
  have hMne : M ≠ 0 := norm_pos_iff.mp hMnorm
  have hlead : leadingIntegrand s L ≠ 0 := by
    rw [leadingIntegrand_eq_exp_logIntegrand]
    exact exp_ne_zero _
  exact mul_ne_zero hlead hMne

theorem fullThetaMoment_factorization
    {s : ℂ} (hs : s ∈ leanSaddleSector) :
    fullThetaMoment s = saddleMomentMain s *
      (1 + fullThetaMomentRelativeError s) := by
  exact holomorphicRelativeError_factorization
    (saddleMomentMain_ne_zero hs)

theorem fullThetaMomentRelativeError_norm_le
    {s : ℂ} (hs : s ∈ leanSaddleSector) :
    ‖fullThetaMomentRelativeError s‖ ≤
      fullThetaMomentErrorCoefficient /
        ‖leadingCurvature s (quantitativeSaddleBranch s)‖ := by
  apply holomorphicRelativeError_norm_le_of_sub_le
    (saddleMomentMain_ne_zero hs)
  simpa only [saddleMomentMain, fullThetaMomentErrorCoefficient] using
    quantitativeSaddleBranch_fullThetaMoment_relative_error_le hs

theorem twoShiftRelativeError_norm_le
    {coefficient saddleScale lowerError upperError ratioError : ℂ}
    {epsilonLower epsilonUpper epsilonRatio denominatorFloor : ℝ}
    (hlower : ‖lowerError‖ ≤ epsilonLower)
    (hupper : ‖upperError‖ ≤ epsilonUpper)
    (hratio : ‖ratioError‖ ≤ epsilonRatio)
    (hfloor : denominatorFloor ≤ ‖coefficient - saddleScale ^ 2‖)
    (hfloor_pos : 0 < denominatorFloor) :
    ‖twoShiftRelativeError coefficient saddleScale
        lowerError upperError ratioError‖ ≤
      (‖coefficient‖ * epsilonLower + ‖saddleScale‖ ^ 2 *
        (epsilonRatio + epsilonUpper + epsilonRatio * epsilonUpper)) /
          denominatorFloor := by
  have heL : 0 ≤ epsilonLower := le_trans (norm_nonneg _) hlower
  have heU : 0 ≤ epsilonUpper := le_trans (norm_nonneg _) hupper
  have heR : 0 ≤ epsilonRatio := le_trans (norm_nonneg _) hratio
  have hdenom_pos : 0 < ‖coefficient - saddleScale ^ 2‖ :=
    lt_of_lt_of_le hfloor_pos hfloor
  unfold twoShiftRelativeError
  rw [norm_div]
  apply (div_le_div_iff₀ hdenom_pos hfloor_pos).2
  have hnum :
      ‖coefficient * lowerError - saddleScale ^ 2 *
          (ratioError + upperError + ratioError * upperError)‖ ≤
        ‖coefficient‖ * epsilonLower + ‖saddleScale‖ ^ 2 *
          (epsilonRatio + epsilonUpper + epsilonRatio * epsilonUpper) := by
    calc
      _ ≤ ‖coefficient * lowerError‖ +
          ‖saddleScale ^ 2 *
            (ratioError + upperError + ratioError * upperError)‖ := norm_sub_le _ _
      _ = ‖coefficient‖ * ‖lowerError‖ + ‖saddleScale‖ ^ 2 *
          ‖ratioError + upperError + ratioError * upperError‖ := by
            rw [norm_mul, norm_mul, norm_pow]
      _ ≤ ‖coefficient‖ * epsilonLower + ‖saddleScale‖ ^ 2 *
          (‖ratioError‖ + ‖upperError‖ + ‖ratioError‖ * ‖upperError‖) := by
            gcongr
            exact le_trans (norm_add_le _ _)
              (add_le_add (norm_add_le _ _) (by rw [norm_mul]))
      _ ≤ ‖coefficient‖ * epsilonLower + ‖saddleScale‖ ^ 2 *
          (epsilonRatio + epsilonUpper + epsilonRatio * epsilonUpper) := by
            gcongr
  calc
    ‖coefficient * lowerError - saddleScale ^ 2 *
        (ratioError + upperError + ratioError * upperError)‖ * denominatorFloor
      ≤ (‖coefficient‖ * epsilonLower + ‖saddleScale‖ ^ 2 *
          (epsilonRatio + epsilonUpper + epsilonRatio * epsilonUpper)) *
          denominatorFloor := mul_le_mul_of_nonneg_right hnum hfloor_pos.le
    _ ≤ (‖coefficient‖ * epsilonLower + ‖saddleScale‖ ^ 2 *
          (epsilonRatio + epsilonUpper + epsilonRatio * epsilonUpper)) *
          ‖coefficient - saddleScale ^ 2‖ := by
            gcongr

theorem fullThetaTwoShiftAssembly
    {s scale coefficient saddleScale ratioError : ℂ}
    (hs : s ∈ leanSaddleSector)
    (hs2 : s + 2 ∈ leanSaddleSector)
    (hdenom : coefficient - saddleScale ^ 2 ≠ 0)
    (hratio : saddleMomentMain (s + 2) =
      saddleMomentMain s * saddleScale ^ 2 * (1 + ratioError)) :
    scale * (coefficient * fullThetaMoment s - fullThetaMoment (s + 2)) =
      (scale * saddleMomentMain s * (coefficient - saddleScale ^ 2)) *
        (1 + twoShiftRelativeError coefficient saddleScale
          (fullThetaMomentRelativeError s)
          (fullThetaMomentRelativeError (s + 2)) ratioError) := by
  apply twoShiftAssembly_of_errors hdenom
  · exact fullThetaMoment_factorization hs
  · rw [fullThetaMoment_factorization hs2, hratio]

theorem fullThetaTwoShiftRelativeError_norm_le
    {s coefficient saddleScale ratioError : ℂ}
    {epsilonRatio denominatorFloor : ℝ}
    (hs : s ∈ leanSaddleSector)
    (hs2 : s + 2 ∈ leanSaddleSector)
    (hratio : ‖ratioError‖ ≤ epsilonRatio)
    (hfloor : denominatorFloor ≤ ‖coefficient - saddleScale ^ 2‖)
    (hfloor_pos : 0 < denominatorFloor) :
    ‖twoShiftRelativeError coefficient saddleScale
        (fullThetaMomentRelativeError s)
        (fullThetaMomentRelativeError (s + 2)) ratioError‖ ≤
      (‖coefficient‖ *
          (fullThetaMomentErrorCoefficient /
            ‖leadingCurvature s (quantitativeSaddleBranch s)‖) +
        ‖saddleScale‖ ^ 2 *
          (epsilonRatio +
            fullThetaMomentErrorCoefficient /
              ‖leadingCurvature (s + 2) (quantitativeSaddleBranch (s + 2))‖ +
            epsilonRatio *
              (fullThetaMomentErrorCoefficient /
                ‖leadingCurvature (s + 2)
                  (quantitativeSaddleBranch (s + 2))‖))) /
        denominatorFloor := by
  exact twoShiftRelativeError_norm_le
    (fullThetaMomentRelativeError_norm_le hs)
    (fullThetaMomentRelativeError_norm_le hs2)
    hratio hfloor hfloor_pos

end

end Zeta23.Research.JensenWedge
