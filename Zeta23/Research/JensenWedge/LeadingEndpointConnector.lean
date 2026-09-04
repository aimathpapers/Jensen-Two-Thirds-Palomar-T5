import Zeta23.Research.JensenWedge.LeadingHorizontalScale

/-!
# Endpoint connector on the Gaussian main scale

The legal contour begins at real part one, so its finite vertical connector
must be estimated rather than discarded.  This module proves an explicit
phase gap between that connector and the selected saddle and reduces the
connector to an inverse-curvature multiple of the exact Gaussian main.
-/

namespace Zeta23.Research.JensenWedge

open Complex MeasureTheory Set

noncomputable section

theorem quantitativeSaddleBranch_re_gt_eightHundredThousand
    {s : ℂ} (hs : s ∈ leanSaddleSector) :
    800000 < (quantitativeSaddleBranch s).re := by
  have hq : s ∈ quantitativeSaddleDomain := leanSaddleSector_quantitative hs
  have hdist := quantitativeSaddleBranch_dist_center_le hq
  have hdiff : |(quantitativeSaddleBranch s - saddleComparisonCenter s).re| ≤
      dist (quantitativeSaddleBranch s) (saddleComparisonCenter s) := by
    calc
      |(quantitativeSaddleBranch s - saddleComparisonCenter s).re| ≤
          ‖quantitativeSaddleBranch s - saddleComparisonCenter s‖ :=
        Complex.abs_re_le_norm _
      _ = dist (quantitativeSaddleBranch s) (saddleComparisonCenter s) := by
        rw [dist_eq]
  have hcenter := saddleComparisonCenter_re_gt hs
  simp only [sub_re] at hdiff
  have hlower := neg_le_of_abs_le hdiff
  nlinarith

theorem quantitativeSaddleBranch_curvature_norm_le_parameter_norm
    {s : ℂ} (hs : s ∈ leanSaddleSector) :
    ‖leadingCurvature s (quantitativeSaddleBranch s)‖ ≤ ‖s‖ := by
  let L : ℂ := quantitativeSaddleBranch s
  let a : ℂ := 1 + 1 / L - (3 / 4) * (L / s)
  have hinput := leanSaddleSector_quantitative hs
  have hbounds := quantitativeSaddleBranch_scaled_bounds hinput
  have hLne : L ≠ 0 := hbounds.1
  have hsne : s ≠ 0 := hinput.parameter_ne_zero
  have haDiff : a - 1 = 1 / L - (3 / 4) * (L / s) := by
    simp only [a]
    ring
  have haNorm : ‖a - 1‖ ≤ 1 / 4 := by
    rw [haDiff]
    calc
      ‖(1 : ℂ) / L - (3 / 4) * (L / s)‖ ≤
          ‖(1 : ℂ) / L‖ + ‖(3 / 4 : ℂ) * (L / s)‖ := norm_sub_le _ _
      _ = ‖(1 : ℂ) / L‖ + (3 / 4 : ℝ) * ‖L / s‖ := by
        rw [norm_mul]
        norm_num
      _ ≤ 7 / 50 + (3 / 4 : ℝ) * (7 / 50) := by
        gcongr
        · exact hbounds.2.1
        · exact hbounds.2.2
      _ ≤ 1 / 4 := by norm_num
  have ha : ‖a‖ ≤ 5 / 4 := by
    have htri : ‖a‖ ≤ ‖a - 1‖ + ‖(1 : ℂ)‖ := by
      calc
        ‖a‖ = ‖(a - 1) + 1‖ := by ring_nf
        _ ≤ ‖a - 1‖ + ‖(1 : ℂ)‖ := norm_add_le _ _
    norm_num at htri ⊢
    linarith
  have hinv : ‖(1 : ℂ) / L‖ ≤ 7 / 50 := by
    simpa only [L] using hbounds.2.1
  rw [leadingCurvature_factor hsne hLne, norm_mul]
  calc
    ‖s / L‖ * ‖a‖ ≤ (‖s‖ * (7 / 50)) * (5 / 4) := by
      gcongr
      calc
        ‖s / L‖ = ‖s‖ * ‖(1 : ℂ) / L‖ := by
          rw [norm_div, norm_div]
          norm_num
          field_simp [norm_ne_zero_iff.mpr hLne]
        _ ≤ ‖s‖ * (7 / 50) := by gcongr
    _ ≤ ‖s‖ := by nlinarith [norm_nonneg s]

theorem quantitativeSaddleBranch_log_re_gt_ten
    {s : ℂ} (hs : s ∈ leanSaddleSector) :
    10 < (log (quantitativeSaddleBranch s)).re := by
  let L : ℂ := quantitativeSaddleBranch s
  have hLre : 800000 < L.re := by
    simpa only [L] using
      quantitativeSaddleBranch_re_gt_eightHundredThousand hs
  have hLnorm : 800000 < ‖L‖ :=
    hLre.trans_le ((le_abs_self L.re).trans (Complex.abs_re_le_norm L))
  have hexp10 : Real.exp 10 < 800000 := by
    calc
      Real.exp 10 = Real.exp 1 ^ 10 := by
        simpa using Real.exp_nat_mul 1 10
      _ < 3 ^ 10 :=
        pow_lt_pow_left₀ Real.exp_one_lt_three (Real.exp_nonneg _) (by norm_num)
      _ < 800000 := by norm_num
  rw [Complex.log_re]
  exact (Real.lt_log_iff_exp_lt (lt_trans (by norm_num) hLnorm)).2
    (hexp10.trans hLnorm)

theorem quantitativeSaddleBranch_phase_re_gt_eight_parameter_norm
    {s : ℂ} (hs : s ∈ leanSaddleSector) :
    8 * ‖s‖ <
      (leadingLogIntegrand s (quantitativeSaddleBranch s)).re := by
  let L : ℂ := quantitativeSaddleBranch s
  have hinput := leanSaddleSector_quantitative hs
  have hLre : 800000 < L.re := by
    simpa only [L] using
      quantitativeSaddleBranch_re_gt_eightHundredThousand hs
  have hLne : L ≠ 0 := by
    intro hzero
    rw [hzero] at hLre
    norm_num at hLre
  have hroot : sectorialSaddleEquation s L = 0 := by
    simpa only [L] using (quantitativeSaddleBranch_spec hinput).2.1
  have hformula := leadingLogIntegrand_at_saddle hLne hroot
  have hcomp := leanSaddleSector_parameter_component_bounds hs
  have hspos : 0 < ‖s‖ := norm_pos_iff.mpr hinput.parameter_ne_zero
  have hsre : 0 < s.re := by nlinarith
  have hlogre : 10 < (log L).re := by
    simpa only [L] using quantitativeSaddleBranch_log_re_gt_ten hs
  have hfirst : (99 / 100 : ℝ) * ‖s‖ * 10 < s.re * (log L).re := by
    calc
      (99 / 100 : ℝ) * ‖s‖ * 10 < s.re * 10 :=
        mul_lt_mul_of_pos_right hcomp.1 (by norm_num)
      _ < s.re * (log L).re :=
        mul_lt_mul_of_pos_left hlogre hsre
  have hcross : s.im * (log L).im ≤ ‖s‖ / 25 := by
    have hlogIm : |(log L).im| ≤ Real.pi := by
      rw [Complex.log_im]
      exact Complex.abs_arg_le_pi L
    calc
      s.im * (log L).im ≤ |s.im * (log L).im| := le_abs_self _
      _ = |s.im| * |(log L).im| := abs_mul _ _
      _ ≤ (‖s‖ / 100) * Real.pi := by
        exact mul_le_mul hcomp.2.le hlogIm
          (abs_nonneg _) (by positivity)
      _ ≤ (‖s‖ / 100) * 4 := by gcongr; exact Real.pi_le_four
      _ = ‖s‖ / 25 := by ring
  have hmul : 9 * ‖s‖ < (s * log L).re := by
    rw [mul_re]
    nlinarith
  have hratioNorm : ‖s / L‖ ≤ ‖s‖ := by
    have hinv : ‖(1 : ℂ) / L‖ ≤ 7 / 50 := by
      simpa only [L] using
        (quantitativeSaddleBranch_scaled_bounds hinput).2.1
    calc
      ‖s / L‖ = ‖s‖ * ‖(1 : ℂ) / L‖ := by
        rw [norm_div, norm_div]
        norm_num
        field_simp [norm_ne_zero_iff.mpr hLne]
      _ ≤ ‖s‖ * (7 / 50) := by gcongr
      _ ≤ ‖s‖ := by nlinarith
  have hratioRe : (s / L).re ≤ ‖s‖ :=
    (Complex.re_le_norm _).trans hratioNorm
  rw [hformula, add_re, sub_re, add_re]
  norm_num
  nlinarith

theorem leadingConnectorPoint_phase_re_le
    (s : ℂ) {y : ℝ} (hy : |y| ≤ 1 / 20) :
    (leadingLogIntegrand s (1 + y * I)).re ≤ 5 * ‖s‖ + 1 := by
  let u : ℂ := 1 + y * I
  have hlog : ‖log u‖ ≤ 5 := by
    have h := norm_log_horizontal_le (X := 1) (y := y) (by norm_num) hy
    norm_num at h
    simpa only [u] using h
  have hslog : (s * log u).re ≤ 5 * ‖s‖ := by
    calc
      (s * log u).re ≤ ‖s * log u‖ := Complex.re_le_norm _
      _ = ‖s‖ * ‖log u‖ := norm_mul _ _
      _ ≤ ‖s‖ * 5 := by gcongr
      _ = 5 * ‖s‖ := by ring
  have hcos : 0 < Real.cos y := by
    calc
      0 < 1 - y ^ 2 / 2 := by
        have hsquare :=
          (sq_le_sq₀ (abs_nonneg y) (by norm_num : (0 : ℝ) ≤ 1 / 20)).2 hy
        rw [sq_abs] at hsquare
        nlinarith
      _ ≤ Real.cos y := Real.one_sub_sq_div_two_le_cos
  have hexpRe : 0 < (((Real.pi : ℂ) * exp u).re) := by
    simp only [u, mul_re, ofReal_re, Complex.exp_re, ofReal_im, zero_mul,
      sub_zero, add_re, one_re, mul_re, I_re, I_im, mul_zero, zero_mul,
      add_zero, add_im, one_im, mul_im]
    norm_num
    exact mul_pos Real.pi_pos (mul_pos (Real.exp_pos _) hcos)
  have hlinear : (u / 4).re = 1 / 4 := by
    norm_num [u, Complex.div_re]
  change (leadingLogIntegrand s u).re ≤ 5 * ‖s‖ + 1
  unfold leadingLogIntegrand
  rw [sub_re, add_re, hlinear]
  nlinarith

theorem quantitativeSaddleBranch_leftSegment_norm_le
    {s : ℂ} (hs : s ∈ leanSaddleSector) :
    ‖leadingLeftSegment s (quantitativeSaddleBranch s).im‖ ≤
      Real.exp (6 * ‖s‖) := by
  let b : ℝ := (quantitativeSaddleBranch s).im
  have hb : |b| ≤ 1 / 20 :=
    (quantitativeSaddleBranch_im_abs_lt hs).le
  have hsone : 1 ≤ ‖s‖ := by
    have hcut : 1 < Real.exp leanSaddleCutoff := by
      rw [← Real.exp_zero]
      exact Real.exp_lt_exp.mpr (by norm_num [leanSaddleCutoff])
    exact (hcut.trans hs.1).le
  unfold leadingLeftSegment
  rw [norm_mul, norm_I, one_mul]
  calc
    ‖∫ y : ℝ in 0..b, leadingIntegrand s (1 + y * I)‖ ≤
        Real.exp (5 * ‖s‖ + 1) * |b - 0| := by
      apply intervalIntegral.norm_integral_le_of_norm_le_const
      intro y hy
      have hyabs : |y| ≤ |b| := by
        simpa using abs_sub_left_of_mem_uIcc (uIoc_subset_uIcc hy)
      rw [leadingIntegrand_eq_exp_logIntegrand, Complex.norm_exp]
      exact Real.exp_le_exp.mpr
        (leadingConnectorPoint_phase_re_le s (hyabs.trans hb))
    _ ≤ Real.exp (5 * ‖s‖ + 1) * 1 := by
      rw [sub_zero]
      gcongr
      exact hb.trans (by norm_num)
    _ ≤ Real.exp (6 * ‖s‖) := by
      rw [mul_one]
      exact Real.exp_le_exp.mpr (by linarith)

theorem quantitativeSaddleBranch_curvature_threeHalves_le_exp_two_parameterNorm
    {s : ℂ} (hs : s ∈ leanSaddleSector) :
    ‖leadingCurvature s (quantitativeSaddleBranch s)‖ ^ (3 / 2 : ℝ) ≤
      Real.exp (2 * ‖s‖) := by
  let Kabs : ℝ :=
    ‖leadingCurvature s (quantitativeSaddleBranch s)‖
  let S : ℝ := ‖s‖
  have hKge : 4000 ≤ Kabs := by
    simpa only [Kabs] using
      quantitativeSaddleBranch_curvature_norm_ge_fourThousand hs
  have hKone : 1 ≤ Kabs := by linarith
  have hKS : Kabs ≤ S := by
    simpa only [Kabs, S] using
      quantitativeSaddleBranch_curvature_norm_le_parameter_norm hs
  have hSnonneg : 0 ≤ S := norm_nonneg s
  have hSexp : S ≤ Real.exp S := by
    linarith [Real.add_one_le_exp S]
  calc
    Kabs ^ (3 / 2 : ℝ) ≤ Kabs ^ (2 : ℝ) :=
      Real.rpow_le_rpow_of_exponent_le hKone (by norm_num)
    _ = Kabs ^ 2 := Real.rpow_natCast Kabs 2
    _ ≤ S ^ 2 := by
      nlinarith [mul_nonneg (sub_nonneg.mpr hKS)
        (by linarith : 0 ≤ S + Kabs)]
    _ ≤ (Real.exp S) ^ 2 := by nlinarith [Real.exp_nonneg S]
    _ = Real.exp (2 * S) := by
      symm
      simpa using Real.exp_nat_mul S 2

/-- The finite endpoint connector is itself inverse-curvature relative to
the exact Gaussian main term. -/
theorem quantitativeSaddleBranch_leftSegment_relative_inverse_curvature
    {s : ℂ} (hs : s ∈ leanSaddleSector) :
    let L := quantitativeSaddleBranch s
    let K := leadingCurvature s L
    let M := ∫ r : ℝ, leadingGaussian K r
    ‖leadingLeftSegment s L.im‖ ≤
      (1 / ‖K‖) * ‖leadingIntegrand s L * M‖ := by
  dsimp only
  let L : ℂ := quantitativeSaddleBranch s
  let K : ℂ := leadingCurvature s L
  let M : ℂ := ∫ r : ℝ, leadingGaussian K r
  let g : ℂ := leadingIntegrand s L
  let C : ℂ := leadingLeftSegment s L.im
  let Kabs : ℝ := ‖K‖
  let S : ℝ := ‖s‖
  have hKge : 4000 ≤ Kabs := by
    simpa only [L, K, Kabs] using
      quantitativeSaddleBranch_curvature_norm_ge_fourThousand hs
  have hKpos : 0 < Kabs := lt_of_lt_of_le (by norm_num) hKge
  have hC : ‖C‖ ≤ Real.exp (6 * S) := by
    simpa only [L, C, S] using
      quantitativeSaddleBranch_leftSegment_norm_le hs
  have hKpow : Kabs ^ (3 / 2 : ℝ) ≤ Real.exp (2 * S) := by
    simpa only [L, K, Kabs, S] using
      quantitativeSaddleBranch_curvature_threeHalves_le_exp_two_parameterNorm hs
  have hphase : 8 * S < (leadingLogIntegrand s L).re := by
    simpa only [L, S] using
      quantitativeSaddleBranch_phase_re_gt_eight_parameter_norm hs
  have hgnorm : ‖g‖ = Real.exp (leadingLogIntegrand s L).re := by
    simp only [g, leadingIntegrand_eq_exp_logIntegrand, Complex.norm_exp]
  have hgap : ‖C‖ * Kabs ^ (3 / 2 : ℝ) ≤ ‖g‖ := by
    calc
      ‖C‖ * Kabs ^ (3 / 2 : ℝ) ≤
          Real.exp (6 * S) * Kabs ^ (3 / 2 : ℝ) := by gcongr
      _ ≤ Real.exp (6 * S) * Real.exp (2 * S) := by gcongr
      _ = Real.exp (8 * S) := by rw [← Real.exp_add]; congr 1; ring
      _ ≤ ‖g‖ := by
        rw [hgnorm]
        exact (Real.exp_lt_exp.mpr hphase).le
  have hqpos : 0 < Kabs ^ (1 / 2 : ℝ) :=
    Real.rpow_pos_of_pos hKpos _
  have hpowSplit : Kabs ^ (3 / 2 : ℝ) =
      Kabs * Kabs ^ (1 / 2 : ℝ) := by
    calc
      Kabs ^ (3 / 2 : ℝ) = Kabs ^ ((1 : ℝ) + (1 / 2 : ℝ)) := by
        norm_num
      _ = Kabs ^ (1 : ℝ) * Kabs ^ (1 / 2 : ℝ) := by
        rw [Real.rpow_add hKpos]
      _ = Kabs * Kabs ^ (1 / 2 : ℝ) := by rw [Real.rpow_one]
  have hCKdiv : ‖C‖ * Kabs ≤
      ‖g‖ / Kabs ^ (1 / 2 : ℝ) := by
    apply (le_div_iff₀ hqpos).2
    calc
      ‖C‖ * Kabs * Kabs ^ (1 / 2 : ℝ) =
          ‖C‖ * (Kabs * Kabs ^ (1 / 2 : ℝ)) := by ring
      _ = ‖C‖ * Kabs ^ (3 / 2 : ℝ) := by rw [hpowSplit]
      _ ≤ ‖g‖ := hgap
  have hCK : ‖C‖ * Kabs ≤
      ‖g‖ * Kabs ^ (-(1 / 2 : ℝ)) := by
    calc
      ‖C‖ * Kabs ≤ ‖g‖ / Kabs ^ (1 / 2 : ℝ) := hCKdiv
      _ = ‖g‖ * Kabs ^ (-(1 / 2 : ℝ)) := by
        rw [Real.rpow_neg hKpos.le]
        simp only [div_eq_mul_inv]
  have hM : Kabs ^ (-(1 / 2 : ℝ)) ≤ ‖M‖ := by
    simpa only [L, K, Kabs, M] using
      quantitativeSaddleBranch_norm_integral_leadingGaussian_lower hs
  have hCKmain : ‖C‖ * Kabs ≤ ‖g * M‖ := by
    calc
      ‖C‖ * Kabs ≤ ‖g‖ * Kabs ^ (-(1 / 2 : ℝ)) := hCK
      _ ≤ ‖g‖ * ‖M‖ := by gcongr
      _ = ‖g * M‖ := (norm_mul g M).symm
  have hdiv : ‖C‖ ≤ ‖g * M‖ / Kabs :=
    (le_div_iff₀ hKpos).2 hCKmain
  have hfinal : ‖C‖ ≤ (1 / Kabs) * ‖g * M‖ := by
    calc
      ‖C‖ ≤ ‖g * M‖ / Kabs := hdiv
      _ = (1 / Kabs) * ‖g * M‖ := by ring
  simpa only [L, K, M, g, C, Kabs] using hfinal

end

end Zeta23.Research.JensenWedge
