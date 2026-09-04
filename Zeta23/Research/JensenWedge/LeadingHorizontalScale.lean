import Zeta23.Research.JensenWedge.LeadingHorizontalRelative

/-!
# Inverse-curvature scale of the horizontal tails

This module reduces the exact exponential coefficient of the noncentral
horizontal integrals to an explicit multiple of `|K|^-1`.  It first proves
directly from the saddle equation that the curvature norm dominates the real
part of the selected branch.  No asymptotic notation or floating-point
certificate is used.
-/

namespace Zeta23.Research.JensenWedge

open Complex Set

noncomputable section

theorem quantitativeSaddleBranch_re_lt_curvature_norm
    {s : ℂ} (hs : s ∈ leanSaddleSector) :
    (quantitativeSaddleBranch s).re <
      ‖leadingCurvature s (quantitativeSaddleBranch s)‖ := by
  let L : ℂ := quantitativeSaddleBranch s
  let K : ℂ := leadingCurvature s L
  have hLre : 1000 < L.re := by
    simpa only [L] using quantitativeSaddleBranch_re_gt hs
  have hLne : L ≠ 0 := by
    intro hzero
    rw [hzero] at hLre
    norm_num at hLre
  have hroot : sectorialSaddleEquation s L = 0 := by
    simpa only [L] using
      (quantitativeSaddleBranch_spec
        (leanSaddleSector_quantitative hs)).2.1
  have hD2 := leadingLogD2_at_saddle hLne hroot
  have hKformula : K = s / L ^ 2 + (Real.pi : ℂ) * exp L := by
    calc
      K = -(-K) := by ring
      _ = -leadingLogD2 s L := by rw [hD2]
      _ = s / L ^ 2 + (Real.pi : ℂ) * exp L := by
        unfold leadingLogD2
        ring
  have hrat : 0 < (s / L ^ 2).re := by
    have hx : 1 ≤ (quantitativeSaddleBranch s + (0 : ℝ)).re := by
      norm_num
      simpa only [L] using hLre.le.trans' (by norm_num)
    have h := quantitativeSaddleBranch_horizontal_rational_re_pos hs hx
    norm_num at h
    simpa only [L] using h
  have hb : |L.im| < 1 / 20 := by
    simpa only [L] using quantitativeSaddleBranch_im_abs_lt hs
  have hcos : 99 / 100 < Real.cos L.im := by
    calc
      99 / 100 < 1 - L.im ^ 2 / 2 := by
        nlinarith [sq_abs L.im, abs_nonneg L.im]
      _ ≤ Real.cos L.im := Real.one_sub_sq_div_two_le_cos
  have hpiCos : 1 < Real.pi * Real.cos L.im := by
    nlinarith [Real.pi_gt_three,
      mul_lt_mul_of_pos_left hcos Real.pi_pos]
  have hexpPart : Real.exp L.re <
      (((Real.pi : ℂ) * exp L).re) := by
    simp only [mul_re, ofReal_re, Complex.exp_re, ofReal_im, zero_mul,
      sub_zero]
    calc
      Real.exp L.re = 1 * Real.exp L.re := by ring
      _ < (Real.pi * Real.cos L.im) * Real.exp L.re :=
        mul_lt_mul_of_pos_right hpiCos (Real.exp_pos _)
      _ = Real.pi * (Real.exp L.re * Real.cos L.im) := by ring
  have hKre : Real.exp L.re < K.re := by
    rw [hKformula, add_re]
    linarith
  have hlinear : L.re + 1 ≤ Real.exp L.re := Real.add_one_le_exp L.re
  have hnorm : K.re ≤ ‖K‖ := Complex.re_le_norm K
  have hfinal : L.re < ‖K‖ := by linarith
  simpa only [L, K] using hfinal

theorem leadingCentralRadius_square_scale
    {K : ℂ} (hK : 0 < ‖K‖) :
    ‖K‖ * leadingCentralRadius K ^ 2 = ‖K‖ ^ (1 / 5 : ℝ) := by
  unfold leadingCentralRadius
  calc
    ‖K‖ * (‖K‖ ^ (-(2 / 5 : ℝ))) ^ 2 =
        ‖K‖ ^ (1 : ℝ) * ‖K‖ ^ ((-(2 / 5 : ℝ)) * 2) := by
      rw [Real.rpow_one, ← Real.rpow_mul_natCast hK.le]
      norm_num
    _ = ‖K‖ ^ ((1 : ℝ) + (-(2 / 5 : ℝ)) * 2) := by
      rw [Real.rpow_add hK]
    _ = ‖K‖ ^ (1 / 5 : ℝ) := by norm_num

theorem pow_fifteen_mul_exp_neg_div_twenty_le (x : ℝ) (hx : 0 ≤ x) :
    x ^ 15 * Real.exp (-x / 20) ≤
      20 ^ 15 * (Nat.factorial 15 : ℝ) := by
  let y : ℝ := x / 20
  have hy : 0 ≤ y := by dsimp [y]; positivity
  have hpoly := Real.pow_div_factorial_le_exp (x := y) hy 15
  have hsmall : y ^ 15 / (Nat.factorial 15 : ℝ) * Real.exp (-y) ≤ 1 := by
    calc
      y ^ 15 / (Nat.factorial 15 : ℝ) * Real.exp (-y) ≤
          Real.exp y * Real.exp (-y) :=
        mul_le_mul_of_nonneg_right hpoly (Real.exp_pos _).le
      _ = 1 := by rw [← Real.exp_add]; norm_num
  have hybound : y ^ 15 * Real.exp (-y) ≤ (Nat.factorial 15 : ℝ) := by
    calc
      y ^ 15 * Real.exp (-y) =
          (Nat.factorial 15 : ℝ) *
            (y ^ 15 / (Nat.factorial 15 : ℝ) * Real.exp (-y)) := by
        norm_num [Nat.factorial]
        ring
      _ ≤ (Nat.factorial 15 : ℝ) * 1 := by gcongr
      _ = (Nat.factorial 15 : ℝ) := by ring
  calc
    x ^ 15 * Real.exp (-x / 20) =
        20 ^ 15 * (y ^ 15 * Real.exp (-y)) := by
      dsimp only [y]
      norm_num
      ring
    _ ≤ 20 ^ 15 * (Nat.factorial 15 : ℝ) := by gcongr

theorem quantitativeSaddleBranch_horizontal_tail_coefficient_le
    {s : ℂ} (hs : s ∈ leanSaddleSector) :
    let L := quantitativeSaddleBranch s
    let K := leadingCurvature s L
    let ρ := leadingCentralRadius K
    ((L.re + 20 / (‖K‖ * ρ)) *
        Real.exp (- (‖K‖ * ρ ^ 2 / 20)) * ‖K‖ ^ (1 / 2 : ℝ)) ≤
      (2 * 20 ^ 15 * (Nat.factorial 15 : ℝ)) / ‖K‖ := by
  dsimp only
  let L : ℂ := quantitativeSaddleBranch s
  let K : ℂ := leadingCurvature s L
  let Kabs : ℝ := ‖K‖
  let ρ : ℝ := leadingCentralRadius K
  let x : ℝ := Kabs ^ (1 / 5 : ℝ)
  have hKge : 4000 ≤ Kabs := by
    simpa only [L, K, Kabs] using
      quantitativeSaddleBranch_curvature_norm_ge_fourThousand hs
  have hKpos : 0 < Kabs := lt_of_lt_of_le (by norm_num) hKge
  have hLlt : L.re < Kabs := by
    simpa only [L, K, Kabs] using
      quantitativeSaddleBranch_re_lt_curvature_norm hs
  have hKrho : 125 ≤ Kabs * ρ := by
    simpa only [L, K, Kabs, ρ] using
      quantitativeSaddleBranch_curvature_mul_centralRadius_ge hs
  have hq : 20 / (Kabs * ρ) ≤ 1 := by
    apply (div_le_one (by linarith)).2
    linarith
  have hsum : L.re + 20 / (Kabs * ρ) ≤ 2 * Kabs := by
    nlinarith
  have hhalf : Kabs ^ (1 / 2 : ℝ) ≤ Kabs := by
    calc
      Kabs ^ (1 / 2 : ℝ) ≤ Kabs ^ (1 : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le (by linarith) (by norm_num)
      _ = Kabs := Real.rpow_one _
  have hrho2 : Kabs * ρ ^ 2 = x := by
    simpa only [Kabs, ρ, x] using leadingCentralRadius_square_scale hKpos
  have hx : 0 ≤ x := Real.rpow_nonneg hKpos.le _
  have hxpow : x ^ 15 = Kabs ^ 3 := by
    dsimp only [x]
    rw [← Real.rpow_mul_natCast hKpos.le]
    norm_num [Real.rpow_natCast]
  have hdecay : Kabs ^ 3 * Real.exp (-x / 20) ≤
      20 ^ 15 * (Nat.factorial 15 : ℝ) := by
    rw [← hxpow]
    exact pow_fifteen_mul_exp_neg_div_twenty_le x hx
  have hcoef :
      (L.re + 20 / (Kabs * ρ)) * Real.exp (-(Kabs * ρ ^ 2 / 20)) *
          Kabs ^ (1 / 2 : ℝ) ≤
        2 * Kabs ^ 2 * Real.exp (-x / 20) := by
    rw [hrho2]
    calc
      (L.re + 20 / (Kabs * ρ)) * Real.exp (-(x / 20)) *
          Kabs ^ (1 / 2 : ℝ) ≤
        (2 * Kabs) * Real.exp (-(x / 20)) * Kabs := by gcongr
      _ = 2 * Kabs ^ 2 * Real.exp (-x / 20) := by ring
  apply (le_div_iff₀ hKpos).2
  calc
    ((L.re + 20 / (Kabs * ρ)) * Real.exp (-(Kabs * ρ ^ 2 / 20)) *
        Kabs ^ (1 / 2 : ℝ)) * Kabs ≤
      (2 * Kabs ^ 2 * Real.exp (-x / 20)) * Kabs := by gcongr
    _ = 2 * (Kabs ^ 3 * Real.exp (-x / 20)) := by ring
    _ ≤ 2 * (20 ^ 15 * (Nat.factorial 15 : ℝ)) := by gcongr
    _ = (2 * 20 ^ 15 * (Nat.factorial 15 : ℝ)) := by ring

/-- Both noncentral horizontal pieces are an explicit inverse-curvature
multiple of the exact complex Gaussian main term. -/
theorem quantitativeSaddleBranch_horizontal_tail_relative_inverse_curvature
    {s : ℂ} (hs : s ∈ leanSaddleSector) :
    let L := quantitativeSaddleBranch s
    let K := leadingCurvature s L
    let ρ := leadingCentralRadius K
    let M := ∫ r : ℝ, leadingGaussian K r
    (∫ r : ℝ in Icc (1 - L.re) (-ρ), ‖leadingIntegrand s (L + r)‖) +
        (∫ r : ℝ in Ioi ρ, ‖leadingIntegrand s (L + r)‖) ≤
      ((2 * 20 ^ 15 * (Nat.factorial 15 : ℝ)) / ‖K‖) *
        ‖leadingIntegrand s L * M‖ := by
  dsimp only
  let L : ℂ := quantitativeSaddleBranch s
  let K : ℂ := leadingCurvature s L
  let ρ : ℝ := leadingCentralRadius K
  let M : ℂ := ∫ r : ℝ, leadingGaussian K r
  have hrelative :=
    quantitativeSaddleBranch_horizontal_tail_relative_bound hs
  have hcoefficient :=
    quantitativeSaddleBranch_horizontal_tail_coefficient_le hs
  calc
    (∫ r : ℝ in Icc (1 - L.re) (-ρ), ‖leadingIntegrand s (L + r)‖) +
        (∫ r : ℝ in Ioi ρ, ‖leadingIntegrand s (L + r)‖) ≤
      ((L.re + 20 / (‖K‖ * ρ)) *
          Real.exp (- (‖K‖ * ρ ^ 2 / 20)) * ‖K‖ ^ (1 / 2 : ℝ)) *
        ‖leadingIntegrand s L * M‖ := by
          simpa only [L, K, ρ, M] using hrelative
    _ ≤ ((2 * 20 ^ 15 * (Nat.factorial 15 : ℝ)) / ‖K‖) *
        ‖leadingIntegrand s L * M‖ := by
      apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
      simpa only [L, K, ρ] using hcoefficient

end

end Zeta23.Research.JensenWedge
