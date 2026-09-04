import Zeta23.Research.JensenWedge.HigherThetaIntegral

/-!
# Curvature scale of higher-theta suppression

This module compares the theta-mode exponential parameter directly with the
selected saddle curvature, propagates the comparison from the saddle to the
central-window boundary, and absorbs the resulting exponential into an
explicit inverse-square curvature factor.
-/

namespace Zeta23.Research.JensenWedge

open Complex MeasureTheory Set

noncomputable section

theorem quantitativeSaddleBranch_modeParameter_at_saddle_ge_curvature_div_four
    {s : ℂ} (hs : s ∈ leanSaddleSector) :
    ‖leadingCurvature s (quantitativeSaddleBranch s)‖ / 4 ≤
      Real.pi * (exp (quantitativeSaddleBranch s)).re := by
  let L : ℂ := quantitativeSaddleBranch s
  let K : ℂ := leadingCurvature s L
  let B : ℂ := s / L
  let a : ℂ := 1 + 1 / L - (3 / 4) * (L / s)
  let A : ℝ := Real.pi * Real.exp L.re
  have hinput := leanSaddleSector_quantitative hs
  have hbounds := quantitativeSaddleBranch_scaled_bounds hinput
  have hLne : L ≠ 0 := hbounds.1
  have hsne : s ≠ 0 := hinput.parameter_ne_zero
  have hroot : sectorialSaddleEquation s L = 0 := by
    simpa only [L] using (quantitativeSaddleBranch_spec hinput).2.1
  have hmap : s = L * ((Real.pi : ℂ) * exp L + 3 / 4) := by
    unfold sectorialSaddleEquation saddleParameterMap at hroot
    exact (eq_of_sub_eq_zero hroot).symm
  have hB : B = (Real.pi : ℂ) * exp L + 3 / 4 := by
    simp only [B]
    rw [hmap]
    field_simp [hLne]
  have haNorm : ‖a‖ ≤ 5 / 4 := by
    calc
      ‖a‖ ≤ ‖1 + 1 / L‖ + ‖(3 / 4 : ℂ) * (L / s)‖ := norm_sub_le _ _
      _ ≤ (‖(1 : ℂ)‖ + ‖1 / L‖) + ‖(3 / 4 : ℂ) * (L / s)‖ := by
        gcongr
        exact norm_add_le _ _
      _ = 1 + ‖1 / L‖ + (3 / 4 : ℝ) * ‖L / s‖ := by
        rw [norm_mul]
        norm_num
      _ ≤ 1 + 7 / 50 + (3 / 4 : ℝ) * (7 / 50) := by
        gcongr
        · exact hbounds.2.1
        · exact hbounds.2.2
      _ ≤ 5 / 4 := by norm_num
  have hKfactor : K = B * a := by
    simpa only [K, B, a] using leadingCurvature_factor hsne hLne
  have hKleB : ‖K‖ ≤ (5 / 4 : ℝ) * ‖B‖ := by
    rw [hKfactor, norm_mul]
    nlinarith [mul_nonneg (norm_nonneg B) (sub_nonneg.mpr haNorm)]
  have hAim : |L.im| < 1 / 20 := by
    simpa only [L] using quantitativeSaddleBranch_im_abs_lt hs
  have hcos : 99 / 100 < Real.cos L.im := by
    calc
      99 / 100 < 1 - L.im ^ 2 / 2 := by
        nlinarith [sq_abs L.im, abs_nonneg L.im]
      _ ≤ Real.cos L.im := Real.one_sub_sq_div_two_le_cos
  have hApos : 0 < A := mul_pos Real.pi_pos (Real.exp_pos _)
  have hBre : B.re = A * Real.cos L.im + 3 / 4 := by
    rw [hB]
    simp only [add_re, mul_re, ofReal_re, ofReal_im, zero_mul, sub_zero,
      Complex.exp_re, A]
    norm_num
    ring
  have hBim : B.im = A * Real.sin L.im := by
    rw [hB]
    simp only [add_im, mul_im, ofReal_re, ofReal_im, zero_mul, add_zero,
      Complex.exp_im, A]
    norm_num
    ring
  have hBrePos : 0 < B.re := by
    rw [hBre]
    have hcosPos : 0 < Real.cos L.im := by linarith
    nlinarith [mul_pos hApos hcosPos]
  have hBimLe : |B.im| ≤ B.re := by
    rw [hBim, abs_mul, abs_of_pos hApos, hBre]
    have hsin : |Real.sin L.im| ≤ |L.im| := Real.abs_sin_le_abs
    have hleft : A * |Real.sin L.im| < A / 20 := by
      calc
        A * |Real.sin L.im| ≤ A * |L.im| :=
          mul_le_mul_of_nonneg_left hsin hApos.le
        _ < A * (1 / 20) := mul_lt_mul_of_pos_left hAim hApos
        _ = A / 20 := by ring
    have hAcos : A * (99 / 100) < A * Real.cos L.im :=
      mul_lt_mul_of_pos_left hcos hApos
    linarith
  have hBnorm : ‖B‖ ≤ 2 * B.re := by
    calc
      ‖B‖ ≤ |B.re| + |B.im| := Complex.norm_le_abs_re_add_abs_im B
      _ = B.re + |B.im| := by rw [abs_of_pos hBrePos]
      _ ≤ 2 * B.re := by linarith
  have hKBre : 2 * ‖K‖ ≤ 5 * B.re := by
    nlinarith [hKleB, hBnorm, norm_nonneg B]
  have hKge : 4000 ≤ ‖K‖ := by
    simpa only [L, K] using quantitativeSaddleBranch_curvature_norm_ge_fourThousand hs
  have hq : Real.pi * (exp L).re = B.re - 3 / 4 := by
    rw [hB]
    simp only [add_re, mul_re, ofReal_re, ofReal_im, zero_mul, sub_zero]
    norm_num
  have hfinal : ‖K‖ / 4 ≤ B.re - 3 / 4 := by nlinarith
  rw [← hq] at hfinal
  simpa only [L, K] using hfinal

theorem quantitativeSaddleBranch_modeParameter_beyond_leftBoundary_ge_curvature_div_five
    {s : ℂ} (hs : s ∈ leanSaddleSector) {x : ℝ}
    (hx : (quantitativeSaddleBranch s).re -
      leadingCentralRadius
        (leadingCurvature s (quantitativeSaddleBranch s)) ≤ x) :
    ‖leadingCurvature s (quantitativeSaddleBranch s)‖ / 5 ≤
      Real.pi * (exp (x + (quantitativeSaddleBranch s).im * I)).re := by
  let L : ℂ := quantitativeSaddleBranch s
  let K : ℂ := leadingCurvature s L
  let ρ : ℝ := leadingCentralRadius K
  have hρpos : 0 < ρ := by
    simpa only [L, K, ρ] using quantitativeSaddleBranch_centralRadius_pos hs
  have hρle : ρ ≤ 1 / 10 := by
    simpa only [L, K, ρ] using
      quantitativeSaddleBranch_centralRadius_le_tenth hs
  have hqL : ‖K‖ / 4 ≤ Real.pi * (exp L).re := by
    simpa only [L, K] using
      quantitativeSaddleBranch_modeParameter_at_saddle_ge_curvature_div_four hs
  have hexpNeg : 9 / 10 ≤ Real.exp (-ρ) := by
    calc
      9 / 10 ≤ 1 + (-ρ) := by linarith
      _ ≤ Real.exp (-ρ) := by
        simpa [add_comm] using Real.add_one_le_exp (-ρ)
  have hcos : 0 < Real.cos L.im := by
    have hb : |L.im| < 1 / 20 := by
      simpa only [L] using quantitativeSaddleBranch_im_abs_lt hs
    have : 99 / 100 < Real.cos L.im := by
      calc
        99 / 100 < 1 - L.im ^ 2 / 2 := by
          nlinarith [sq_abs L.im, abs_nonneg L.im]
        _ ≤ Real.cos L.im := Real.one_sub_sq_div_two_le_cos
    linarith
  have hqEq (y : ℝ) :
      Real.pi * (exp (y + L.im * I)).re =
        (Real.pi * (exp L).re) * Real.exp (y - L.re) := by
    simp only [Complex.exp_re, add_re, ofReal_re, mul_re, ofReal_im,
      I_re, I_im, mul_zero, sub_zero, add_zero, add_im,
      mul_im, mul_one, zero_add, Real.exp_sub]
    field_simp [ne_of_gt (Real.exp_pos L.re)]
  have hexpMono : Real.exp (-ρ) ≤ Real.exp (x - L.re) := by
    apply Real.exp_monotone
    simpa only [L, K, ρ] using (by linarith : -ρ ≤ x - L.re)
  rw [show Real.pi * (exp (x + L.im * I)).re =
      (Real.pi * (exp L).re) * Real.exp (x - L.re) by exact hqEq x]
  have hqNonneg : 0 ≤ Real.pi * (exp L).re := by
    rw [Complex.exp_re]
    positivity
  calc
    ‖K‖ / 5 ≤ (‖K‖ / 4) * (9 / 10 : ℝ) := by
      have hKnonneg := norm_nonneg K
      nlinarith
    _ ≤ (Real.pi * (exp L).re) * Real.exp (-ρ) := by gcongr
    _ ≤ (Real.pi * (exp L).re) * Real.exp (x - L.re) := by gcongr

theorem two_exp_modeFactor_le_curvature_sq_inv
    {K q : ℝ} (hK : 4000 ≤ K) (hq : K / 5 ≤ q) :
    2 * Real.exp (-3 * q) ≤ 1 / K ^ 2 := by
  have hKpos : 0 < K := lt_of_lt_of_le (by norm_num) hK
  have hqpos : 0 < q := by nlinarith
  have hxpos : 0 ≤ 3 * q := by positivity
  have hseries := Real.pow_div_factorial_le_exp (3 * q) hxpos 3
  norm_num [Nat.factorial] at hseries
  have hpoly : 2 * K ^ 2 ≤ (3 * q) ^ 3 / 6 := by
    have hmul := mul_nonneg (sub_nonneg.mpr hq) (sq_nonneg K)
    nlinarith [sq_nonneg q, sq_nonneg K]
  have hexpLower : 2 * K ^ 2 ≤ Real.exp (3 * q) := hpoly.trans hseries
  rw [show -3 * q = -(3 * q) by ring, Real.exp_neg]
  have hexpPos : 0 < Real.exp (3 * q) := Real.exp_pos _
  have hKsqPos : 0 < K ^ 2 := sq_pos_of_pos hKpos
  change 2 / Real.exp (3 * q) ≤ 1 / K ^ 2
  apply (div_le_iff₀ hexpPos).2
  calc
    (2 : ℝ) = (1 / K ^ 2) * (2 * K ^ 2) := by field_simp
    _ ≤ (1 / K ^ 2) * Real.exp (3 * q) := by gcongr

end

end Zeta23.Research.JensenWedge
