import Zeta23.Research.JensenWedge.SaddleMainDifferential

namespace Zeta23.Research.JensenWedge

open Complex Filter Function MeasureTheory Set Topology

noncomputable section

/-!
# Uniform two-shift ratio for the exact saddle main

This module derives rational norm bounds directly from the T2 branch boxes,
integrates the exact logarithmic derivative from `SaddleMainDifferential`, and
constructs the two-shift relative error on a fixed inner sector.  The final
result is the concrete estimate

`Main(s+2) = Main(s) * L_s^2 * (1 + rho(s))`,
`|rho(s)| <= 52 / |s|`.

The deliberately large inherited cutoff is used only to keep the certificate
arithmetic simple; no asymptotic premise or numerical sample is imported.
-/

theorem branchDeriv_mul_parameterNorm_le
    {s : ℂ} (hs : s ∈ leanSaddleSector) :
    ‖quantitativeSaddleBranch s /
        sectorialSaddleCurvature s (quantitativeSaddleBranch s)‖ * ‖s‖ ≤
      16 / 9 := by
  let L : ℂ := quantitativeSaddleBranch s
  let a : ℂ := 1 + 1 / L - (3 / 4) * (L / s)
  have hinput := leanSaddleSector_quantitative hs
  have hbounds := quantitativeSaddleBranch_scaled_bounds hinput
  have hsne : s ≠ 0 := hinput.parameter_ne_zero
  have hLne : L ≠ 0 := hbounds.1
  have ha : 9 / 16 ≤ ‖a‖ := by
    exact saddle_scaled_factor_norm_lower hbounds.2.1 hbounds.2.2
  have hscaled : sectorialSaddleCurvature s L = s * L * a := by
    exact sectorialSaddleCurvature_scaled hsne hLne rfl rfl
  rw [show quantitativeSaddleBranch s = L by rfl, hscaled, norm_div,
    norm_mul, norm_mul]
  have hspos : 0 < ‖s‖ := norm_pos_iff.mpr hsne
  have hLpos : 0 < ‖L‖ := norm_pos_iff.mpr hLne
  have hapos : 0 < ‖a‖ := lt_of_lt_of_le (by norm_num) ha
  rw [div_mul_eq_mul_div, mul_div_assoc]
  field_simp
  nlinarith

theorem branchDeriv_div_branch_mul_parameterNorm_le
    {s : ℂ} (hs : s ∈ leanSaddleSector) :
    ‖(quantitativeSaddleBranch s /
          sectorialSaddleCurvature s (quantitativeSaddleBranch s)) /
        quantitativeSaddleBranch s‖ * ‖s‖ ≤ 56 / 225 := by
  let L : ℂ := quantitativeSaddleBranch s
  let dL : ℂ := L / sectorialSaddleCurvature s L
  have hbounds := quantitativeSaddleBranch_scaled_bounds
    (leanSaddleSector_quantitative hs)
  have hmain : ‖dL‖ * ‖s‖ ≤ 16 / 9 := by
    simpa only [L, dL] using branchDeriv_mul_parameterNorm_le hs
  have hr : ‖L⁻¹‖ ≤ 7 / 50 := by
    simpa only [one_div] using hbounds.2.1
  change ‖dL / L‖ * ‖s‖ ≤ 56 / 225
  rw [div_eq_mul_inv, norm_mul]
  calc
    ‖dL‖ * ‖L⁻¹‖ * ‖s‖ = (‖dL‖ * ‖s‖) * ‖L⁻¹‖ := by ring
    _ ≤ (16 / 9 : ℝ) * (7 / 50) := by gcongr
    _ = 56 / 225 := by norm_num

def saddleScaledFactorAlong (s : ℂ) : ℂ :=
  let L := quantitativeSaddleBranch s
  1 + 1 / L - (3 / 4) * (L / s)

def saddleScaledFactorAlongD1 (s : ℂ) : ℂ :=
  let L := quantitativeSaddleBranch s
  let dL := L / sectorialSaddleCurvature s L
  (-dL) / L ^ 2 - (3 / 4) * (dL / s - L / s ^ 2)

theorem saddleCurvatureAlongD1_div_eq
    {s : ℂ} (hs : s ∈ leanSaddleSector) :
    saddleCurvatureAlongD1 s / saddleCurvatureAlong s =
      1 / s -
        (quantitativeSaddleBranch s /
            sectorialSaddleCurvature s (quantitativeSaddleBranch s)) /
          quantitativeSaddleBranch s +
        saddleScaledFactorAlongD1 s / saddleScaledFactorAlong s := by
  let L : ℂ := quantitativeSaddleBranch s
  let dL : ℂ := L / sectorialSaddleCurvature s L
  let a : ℂ := 1 + 1 / L - (3 / 4) * (L / s)
  have hinput := leanSaddleSector_quantitative hs
  have hbounds := quantitativeSaddleBranch_scaled_bounds hinput
  have hsne : s ≠ 0 := hinput.parameter_ne_zero
  have hLne : L ≠ 0 := hbounds.1
  have hane : a ≠ 0 :=
    saddle_scaled_factor_ne_zero hbounds.2.1 hbounds.2.2
  have hKfactor : saddleCurvatureAlong s = (s / L) * a := by
    rw [saddleCurvatureAlong_eq hs, leadingCurvature_factor hsne hLne]
  have hD1 : saddleCurvatureAlongD1 s =
      (1 / L - s * dL / L ^ 2) * a +
        (s / L) * ((-dL) / L ^ 2 -
          (3 / 4) * (dL / s - L / s ^ 2)) := by
    simp only [saddleCurvatureAlongD1]
    change (L⁻¹ + (L ^ 2)⁻¹) +
          s * (-dL / L ^ 2 - 2 * dL / L ^ 3) = _
    dsimp [a]
    field_simp [hsne, hLne]
    ring
  change saddleCurvatureAlongD1 s / saddleCurvatureAlong s =
    1 / s - dL / L +
      ((-dL) / L ^ 2 - (3 / 4) * (dL / s - L / s ^ 2)) / a
  rw [hD1, hKfactor]
  field_simp [hsne, hLne, hane]

theorem leanSaddleSector_parameterNorm_gt_one
    {s : ℂ} (hs : s ∈ leanSaddleSector) : 1 < ‖s‖ := by
  have hradial : Real.exp leanSaddleCutoff < ‖s‖ := hs.1
  have hcut : 1 < Real.exp leanSaddleCutoff := by
    rw [← Real.exp_zero]
    exact Real.exp_lt_exp.mpr (by norm_num [leanSaddleCutoff])
  exact hcut.trans hradial

theorem leanSaddleSector_parameterNorm_ge_fiveHundredBillion
    {s : ℂ} (hs : s ∈ leanSaddleSector) :
    (500000000000 : ℝ) ≤ ‖s‖ := by
  have hquad := Real.pow_div_factorial_le_exp leanSaddleCutoff
    (show (0 : ℝ) ≤ leanSaddleCutoff by norm_num [leanSaddleCutoff]) 2
  have hcut : (500000000000 : ℝ) ≤ Real.exp leanSaddleCutoff := by
    norm_num [leanSaddleCutoff] at hquad
    exact hquad
  exact hcut.trans hs.1.le

theorem saddleScaledFactorAlong_norm_lower
    {s : ℂ} (hs : s ∈ leanSaddleSector) :
    9 / 16 ≤ ‖saddleScaledFactorAlong s‖ := by
  have hbounds := quantitativeSaddleBranch_scaled_bounds
    (leanSaddleSector_quantitative hs)
  exact saddle_scaled_factor_norm_lower hbounds.2.1 hbounds.2.2

theorem saddleScaledFactorAlongD1_mul_parameterNorm_le
    {s : ℂ} (hs : s ∈ leanSaddleSector) :
    ‖saddleScaledFactorAlongD1 s‖ * ‖s‖ ≤ 3 / 2 := by
  let L : ℂ := quantitativeSaddleBranch s
  let dL : ℂ := L / sectorialSaddleCurvature s L
  have hbounds := quantitativeSaddleBranch_scaled_bounds
    (leanSaddleSector_quantitative hs)
  have hdLmain : ‖dL‖ * ‖s‖ ≤ 16 / 9 := by
    simpa only [L, dL] using branchDeriv_mul_parameterNorm_le hs
  have hsone : 1 ≤ ‖s‖ :=
    (leanSaddleSector_parameterNorm_gt_one hs).le
  have hdL : ‖dL‖ ≤ 16 / 9 := by
    calc
      ‖dL‖ = ‖dL‖ * 1 := by ring
      _ ≤ ‖dL‖ * ‖s‖ := by gcongr
      _ ≤ 16 / 9 := hdLmain
  have hr : ‖L⁻¹‖ ≤ 7 / 50 := by
    simpa only [one_div] using hbounds.2.1
  have hsigma : ‖L / s‖ ≤ 7 / 50 := hbounds.2.2
  have hfirst : ‖(-dL) / L ^ 2‖ * ‖s‖ ≤ 784 / 22500 := by
    rw [norm_div, norm_neg, norm_pow]
    have hmul : ‖dL‖ * ‖s‖ * ‖L⁻¹‖ ^ 2 ≤
        (16 / 9 : ℝ) * (7 / 50) ^ 2 := by gcongr
    rw [norm_inv] at hr
    calc
      ‖dL‖ / ‖L‖ ^ 2 * ‖s‖ =
          (‖dL‖ * ‖s‖) * ‖L⁻¹‖ ^ 2 := by
        rw [norm_inv]
        field_simp [hbounds.1]
      _ ≤ (16 / 9 : ℝ) * (7 / 50) ^ 2 := hmul
      _ = 784 / 22500 := by norm_num
  have hsecondInside : ‖dL / s - L / s ^ 2‖ * ‖s‖ ≤
      16 / 9 + 7 / 50 := by
    calc
      ‖dL / s - L / s ^ 2‖ * ‖s‖ ≤
          (‖dL / s‖ + ‖L / s ^ 2‖) * ‖s‖ := by
        gcongr
        exact norm_sub_le _ _
      _ = ‖dL‖ + ‖L / s‖ := by
        have hsne := (leanSaddleSector_quantitative hs).parameter_ne_zero
        simp only [norm_div, norm_pow]
        field_simp [norm_ne_zero_iff.mpr hsne]
      _ ≤ 16 / 9 + 7 / 50 := add_le_add hdL hsigma
  have hsecond :
      ‖(3 / 4 : ℂ) * (dL / s - L / s ^ 2)‖ * ‖s‖ ≤
        (3 / 4 : ℝ) * (16 / 9 + 7 / 50) := by
    rw [norm_mul]
    norm_num
    nlinarith
  change ‖(-dL) / L ^ 2 -
      (3 / 4) * (dL / s - L / s ^ 2)‖ * ‖s‖ ≤ 3 / 2
  calc
    ‖(-dL) / L ^ 2 - (3 / 4) * (dL / s - L / s ^ 2)‖ * ‖s‖ ≤
        (‖(-dL) / L ^ 2‖ +
          ‖(3 / 4 : ℂ) * (dL / s - L / s ^ 2)‖) * ‖s‖ := by
      gcongr
      exact norm_sub_le _ _
    _ = ‖(-dL) / L ^ 2‖ * ‖s‖ +
        ‖(3 / 4 : ℂ) * (dL / s - L / s ^ 2)‖ * ‖s‖ := by ring
    _ ≤ 784 / 22500 + (3 / 4 : ℝ) * (16 / 9 + 7 / 50) :=
      add_le_add hfirst hsecond
    _ ≤ 3 / 2 := by norm_num

theorem saddleScaledFactorAlong_logDeriv_mul_parameterNorm_le
    {s : ℂ} (hs : s ∈ leanSaddleSector) :
    ‖saddleScaledFactorAlongD1 s / saddleScaledFactorAlong s‖ * ‖s‖ ≤
      8 / 3 := by
  have hnum := saddleScaledFactorAlongD1_mul_parameterNorm_le hs
  have hden := saddleScaledFactorAlong_norm_lower hs
  have hdenpos : 0 < ‖saddleScaledFactorAlong s‖ :=
    lt_of_lt_of_le (by norm_num) hden
  rw [norm_div]
  rw [div_mul_eq_mul_div]
  apply (div_le_iff₀ hdenpos).mpr
  nlinarith

theorem saddleCurvatureAlong_logDeriv_mul_parameterNorm_le
    {s : ℂ} (hs : s ∈ leanSaddleSector) :
    ‖saddleCurvatureAlongD1 s / saddleCurvatureAlong s‖ * ‖s‖ ≤ 4 := by
  have hsne := (leanSaddleSector_quantitative hs).parameter_ne_zero
  have hbranch := branchDeriv_div_branch_mul_parameterNorm_le hs
  have hfactor := saddleScaledFactorAlong_logDeriv_mul_parameterNorm_le hs
  rw [saddleCurvatureAlongD1_div_eq hs]
  calc
    ‖1 / s -
          (quantitativeSaddleBranch s /
              sectorialSaddleCurvature s (quantitativeSaddleBranch s)) /
            quantitativeSaddleBranch s +
          saddleScaledFactorAlongD1 s / saddleScaledFactorAlong s‖ * ‖s‖ ≤
        (‖1 / s‖ +
            ‖(quantitativeSaddleBranch s /
                sectorialSaddleCurvature s (quantitativeSaddleBranch s)) /
              quantitativeSaddleBranch s‖ +
            ‖saddleScaledFactorAlongD1 s / saddleScaledFactorAlong s‖) * ‖s‖ := by
      gcongr
      calc
        ‖1 / s -
              (quantitativeSaddleBranch s /
                  sectorialSaddleCurvature s (quantitativeSaddleBranch s)) /
                quantitativeSaddleBranch s +
              saddleScaledFactorAlongD1 s / saddleScaledFactorAlong s‖ ≤
            ‖1 / s -
                (quantitativeSaddleBranch s /
                    sectorialSaddleCurvature s (quantitativeSaddleBranch s)) /
                  quantitativeSaddleBranch s‖ +
              ‖saddleScaledFactorAlongD1 s / saddleScaledFactorAlong s‖ :=
          norm_add_le _ _
        _ ≤ ‖1 / s‖ +
              ‖(quantitativeSaddleBranch s /
                  sectorialSaddleCurvature s (quantitativeSaddleBranch s)) /
                quantitativeSaddleBranch s‖ +
              ‖saddleScaledFactorAlongD1 s / saddleScaledFactorAlong s‖ := by
          linarith [norm_sub_le (1 / s)
            ((quantitativeSaddleBranch s /
                sectorialSaddleCurvature s (quantitativeSaddleBranch s)) /
              quantitativeSaddleBranch s)]
    _ = ‖1 / s‖ * ‖s‖ +
          ‖(quantitativeSaddleBranch s /
              sectorialSaddleCurvature s (quantitativeSaddleBranch s)) /
            quantitativeSaddleBranch s‖ * ‖s‖ +
          ‖saddleScaledFactorAlongD1 s / saddleScaledFactorAlong s‖ * ‖s‖ := by
      ring
    _ = 1 +
          ‖(quantitativeSaddleBranch s /
              sectorialSaddleCurvature s (quantitativeSaddleBranch s)) /
            quantitativeSaddleBranch s‖ * ‖s‖ +
          ‖saddleScaledFactorAlongD1 s / saddleScaledFactorAlong s‖ * ‖s‖ := by
      rw [norm_div, norm_one]
      field_simp [norm_ne_zero_iff.mpr hsne]
    _ ≤ 1 + 56 / 225 + 8 / 3 := by gcongr
    _ ≤ 4 := by norm_num

theorem saddleMomentLogMainD1_sub_log_mul_parameterNorm_le
    {s : ℂ} (hs : s ∈ leanSaddleSector) :
    ‖saddleMomentLogMainD1 s - log (quantitativeSaddleBranch s)‖ * ‖s‖ ≤
      6 := by
  let K : ℂ := saddleCurvatureAlong s
  let dK : ℂ := saddleCurvatureAlongD1 s
  let dL : ℂ := quantitativeSaddleBranch s /
    sectorialSaddleCurvature s (quantitativeSaddleBranch s)
  have hdL : ‖dL‖ * ‖s‖ ≤ 16 / 9 := by
    simpa only [dL] using branchDeriv_mul_parameterNorm_le hs
  have hq : ‖dK / K‖ * ‖s‖ ≤ 4 := by
    simpa only [dK, K] using
      saddleCurvatureAlong_logDeriv_mul_parameterNorm_le hs
  have hKre : 1 < K.re := by
    change 1 < (saddleCurvatureAlong s).re
    rw [saddleCurvatureAlong_eq hs]
    exact (quantitativeSaddleBranch_curvature_strong_bounds hs).1
  have hKnorm : 1 ≤ ‖K‖ := by
    exact hKre.le.trans (Complex.re_le_norm K)
  have hqK : ‖dK / K ^ 2‖ * ‖s‖ ≤ 4 := by
    have hfactor : dK / K ^ 2 = (dK / K) / K := by ring
    rw [hfactor, norm_div]
    have hKpos : 0 < ‖K‖ := lt_of_lt_of_le zero_lt_one hKnorm
    rw [div_mul_eq_mul_div]
    apply (div_le_iff₀ hKpos).mpr
    nlinarith
  simp only [saddleMomentLogMainD1, saddleLeadingLogD1]
  calc
    ‖(log (quantitativeSaddleBranch s) + dL - dK / (2 * K) -
          dK / (2 * K ^ 2)) - log (quantitativeSaddleBranch s)‖ * ‖s‖ ≤
        (‖dL‖ + (1 / 2 : ℝ) * ‖dK / K‖ +
          (1 / 2 : ℝ) * ‖dK / K ^ 2‖) * ‖s‖ := by
      gcongr
      calc
        ‖(log (quantitativeSaddleBranch s) + dL - dK / (2 * K) -
            dK / (2 * K ^ 2)) - log (quantitativeSaddleBranch s)‖ =
            ‖dL - dK / (2 * K) - dK / (2 * K ^ 2)‖ := by ring_nf
        _ ≤ ‖dL‖ + ‖dK / (2 * K)‖ + ‖dK / (2 * K ^ 2)‖ := by
          calc
            ‖dL - dK / (2 * K) - dK / (2 * K ^ 2)‖ ≤
                ‖dL - dK / (2 * K)‖ + ‖dK / (2 * K ^ 2)‖ :=
              norm_sub_le _ _
            _ ≤ ‖dL‖ + ‖dK / (2 * K)‖ +
                ‖dK / (2 * K ^ 2)‖ := by
              linarith [norm_sub_le dL (dK / (2 * K))]
        _ = ‖dL‖ + (1 / 2 : ℝ) * ‖dK / K‖ +
            (1 / 2 : ℝ) * ‖dK / K ^ 2‖ := by
          rw [show dK / (2 * K) = (1 / 2 : ℂ) * (dK / K) by ring,
            show dK / (2 * K ^ 2) = (1 / 2 : ℂ) * (dK / K ^ 2) by ring,
            norm_mul, norm_mul]
          norm_num
    _ = ‖dL‖ * ‖s‖ + (1 / 2 : ℝ) * (‖dK / K‖ * ‖s‖) +
        (1 / 2 : ℝ) * (‖dK / K ^ 2‖ * ‖s‖) := by ring
    _ ≤ 16 / 9 + (1 / 2 : ℝ) * 4 + (1 / 2 : ℝ) * 4 := by gcongr
    _ ≤ 6 := by norm_num

def saddleBranchLog (s : ℂ) : ℂ :=
  log (quantitativeSaddleBranch s)

def saddleBranchLogD1 (s : ℂ) : ℂ :=
  (quantitativeSaddleBranch s /
      sectorialSaddleCurvature s (quantitativeSaddleBranch s)) /
    quantitativeSaddleBranch s

theorem hasDerivAt_saddleBranchLog
    {s : ℂ} (hs : s ∈ leanSaddleSector) :
    HasDerivAt saddleBranchLog (saddleBranchLogD1 s) s := by
  let L : ℂ := quantitativeSaddleBranch s
  let dL : ℂ := L / sectorialSaddleCurvature s L
  have hL : HasDerivAt quantitativeSaddleBranch dL s :=
    hasDerivAt_quantitativeSaddleBranch hs
  have hLre : 0 < L.re := by
    linarith [quantitativeSaddleBranch_re_gt hs]
  have hlog := (Complex.hasDerivAt_log
    (Complex.mem_slitPlane_iff.mpr (Or.inl hLre))).comp s hL
  apply hlog.congr_deriv
  simp only [saddleBranchLogD1, L, dL]
  ring

theorem saddleBranchLogD1_mul_parameterNorm_le
    {s : ℂ} (hs : s ∈ leanSaddleSector) :
    ‖saddleBranchLogD1 s‖ * ‖s‖ ≤ 56 / 225 := by
  exact branchDeriv_div_branch_mul_parameterNorm_le hs

theorem norm_sub_le_mul_of_hasDerivAt_le
    {f f' : ℝ → ℂ} {a b C : ℝ} (hab : a ≤ b)
    (hderiv : ∀ x ∈ Icc a b, HasDerivAt f (f' x) x)
    (hbound : ∀ x ∈ Icc a b, ‖f' x‖ ≤ C) :
    ‖f b - f a‖ ≤ C * (b - a) := by
  have hcont : ContinuousOn f (Icc a b) := by
    intro x hx
    exact (hderiv x hx).continuousAt.continuousWithinAt
  have hdiff : DifferentiableOn ℝ f (Ioo a b) := by
    intro x hx
    exact (hderiv x ⟨hx.1.le, hx.2.le⟩).differentiableAt.differentiableWithinAt
  have hae : ∀ᵐ x, x ∈ Ioo a b → ‖deriv f x‖ ≤ C := by
    filter_upwards with x
    intro hx
    rw [(hderiv x ⟨hx.1.le, hx.2.le⟩).deriv]
    exact hbound x ⟨hx.1.le, hx.2.le⟩
  have h := norm_sub_le_integral_of_norm_deriv_le_of_le hab hcont hdiff hae
    (intervalIntegrable_const : IntervalIntegrable (fun _ : ℝ => C) volume a b)
  simpa [intervalIntegral.integral_const, hab, mul_comm] using h

def leanTwoShiftAdmissible (s : ℂ) : Prop :=
  ∀ t ∈ Icc (0 : ℝ) 1,
    s + 2 * (t : ℂ) ∈ leanSaddleSector ∧
      ‖s‖ ≤ 2 * ‖s + 2 * (t : ℂ)‖

theorem leanTwoShiftAdmissible_base
    {s : ℂ} (hs : leanTwoShiftAdmissible s) : s ∈ leanSaddleSector := by
  simpa using (hs 0 (by constructor <;> norm_num)).1

theorem saddleBranchLog_segment_bound
    {s : ℂ} (hs : leanTwoShiftAdmissible s)
    {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    ‖saddleBranchLog (s + 2 * (t : ℂ)) - saddleBranchLog s‖ * ‖s‖ ≤ 1 := by
  let p : ℝ → ℂ := fun u => s + 2 * (u : ℂ)
  let f : ℝ → ℂ := fun u => saddleBranchLog (p u)
  let f' : ℝ → ℂ := fun u => 2 * saddleBranchLogD1 (p u)
  have hderiv : ∀ u ∈ Icc (0 : ℝ) t, HasDerivAt f (f' u) u := by
    intro u hu
    have hut : u ∈ Icc (0 : ℝ) 1 := ⟨hu.1, hu.2.trans ht.2⟩
    have hpu := (hs u hut).1
    have hmapC : HasDerivAt (fun z : ℂ => s + 2 * z) 2 (u : ℂ) := by
      simpa using ((hasDerivAt_id (u : ℂ)).const_mul (2 : ℂ)).const_add s
    have hcomp := (hasDerivAt_saddleBranchLog hpu).comp (u : ℂ) hmapC
    have hreal := hcomp.comp_ofReal
    apply hreal.congr_deriv
    simp only [f', p]
    ring
  have hbound : ∀ u ∈ Icc (0 : ℝ) t, ‖f' u‖ ≤ 1 / ‖s‖ := by
    intro u hu
    have hut : u ∈ Icc (0 : ℝ) 1 := ⟨hu.1, hu.2.trans ht.2⟩
    have hpu := (hs u hut).1
    have hnormCompare := (hs u hut).2
    have hpoint := saddleBranchLogD1_mul_parameterNorm_le hpu
    have hspos : 0 < ‖s‖ :=
      norm_pos_iff.mpr (leanSaddleSector_quantitative
        (leanTwoShiftAdmissible_base hs)).parameter_ne_zero
    apply (le_div_iff₀ hspos).mpr
    simp only [f', p, norm_mul]
    norm_num
    calc
      2 * ‖saddleBranchLogD1 (s + 2 * (u : ℂ))‖ * ‖s‖ ≤
          2 * ‖saddleBranchLogD1 (s + 2 * (u : ℂ))‖ *
            (2 * ‖s + 2 * (u : ℂ)‖) := by gcongr
      _ = 4 * (‖saddleBranchLogD1 (s + 2 * (u : ℂ))‖ *
          ‖s + 2 * (u : ℂ)‖) := by ring
      _ ≤ 4 * (56 / 225 : ℝ) := by gcongr
      _ ≤ 1 := by norm_num
  have hdiff := norm_sub_le_mul_of_hasDerivAt_le ht.1 hderiv hbound
  have hscaled : ‖f t - f 0‖ * ‖s‖ ≤ 1 := by
    calc
    ‖f t - f 0‖ * ‖s‖ ≤ (1 / ‖s‖ * (t - 0)) * ‖s‖ := by gcongr
    _ = t := by
      have hsne : ‖s‖ ≠ 0 := ne_of_gt (norm_pos_iff.mpr
        (leanSaddleSector_quantitative
          (leanTwoShiftAdmissible_base hs)).parameter_ne_zero)
      field_simp
      ring
    _ ≤ 1 := ht.2
  simpa [f, p] using hscaled

def saddleMainTwoShiftLogError (s : ℂ) : ℂ :=
  saddleMomentLogMain (s + 2) - saddleMomentLogMain s - 2 * saddleBranchLog s

theorem saddleMainTwoShiftLogError_mul_parameterNorm_le
    {s : ℂ} (hs : leanTwoShiftAdmissible s) :
    ‖saddleMainTwoShiftLogError s‖ * ‖s‖ ≤ 26 := by
  let p : ℝ → ℂ := fun u => s + 2 * (u : ℂ)
  let f : ℝ → ℂ := fun u =>
    saddleMomentLogMain (p u) - 2 * (u : ℂ) * saddleBranchLog s
  let f' : ℝ → ℂ := fun u =>
    2 * (saddleMomentLogMainD1 (p u) - saddleBranchLog s)
  have hderiv : ∀ u ∈ Icc (0 : ℝ) 1, HasDerivAt f (f' u) u := by
    intro u hu
    have hpu := (hs u hu).1
    have hmapC : HasDerivAt (fun z : ℂ => s + 2 * z) 2 (u : ℂ) := by
      simpa using ((hasDerivAt_id (u : ℂ)).const_mul (2 : ℂ)).const_add s
    have hmainC := (hasDerivAt_saddleMomentLogMain hpu).comp (u : ℂ) hmapC
    have hmain := hmainC.comp_ofReal
    have hlinear : HasDerivAt
        (fun v : ℝ => 2 * (v : ℂ) * saddleBranchLog s)
        (2 * saddleBranchLog s) u := by
      have hreal : HasDerivAt (fun v : ℝ => (v : ℂ)) 1 u :=
        Complex.ofRealCLM.hasDerivAt
      have hraw := hreal.const_mul (2 * saddleBranchLog s)
      have hfun :
          (fun v : ℝ => 2 * (v : ℂ) * saddleBranchLog s) =ᶠ[nhds u]
            (fun v : ℝ => (2 * saddleBranchLog s) * (v : ℂ)) := by
        filter_upwards with v
        ring
      have htarget := hraw.congr_of_eventuallyEq hfun
      apply htarget.congr_deriv
      ring
    have hraw := hmain.sub hlinear
    apply hraw.congr_deriv
    simp only [f', p]
    ring
  have hbound : ∀ u ∈ Icc (0 : ℝ) 1, ‖f' u‖ ≤ 26 / ‖s‖ := by
    intro u hu
    have hpu := (hs u hu).1
    have hnormCompare := (hs u hu).2
    have hlocal := saddleMomentLogMainD1_sub_log_mul_parameterNorm_le hpu
    have hlog := saddleBranchLog_segment_bound hs hu
    have hsum :
        ‖saddleMomentLogMainD1 (p u) - saddleBranchLog s‖ * ‖s‖ ≤ 13 := by
      calc
        ‖saddleMomentLogMainD1 (p u) - saddleBranchLog s‖ * ‖s‖ ≤
            (‖saddleMomentLogMainD1 (p u) - saddleBranchLog (p u)‖ +
              ‖saddleBranchLog (p u) - saddleBranchLog s‖) * ‖s‖ := by
          gcongr
          have hdecomp : saddleMomentLogMainD1 (p u) - saddleBranchLog s =
              (saddleMomentLogMainD1 (p u) - saddleBranchLog (p u)) +
                (saddleBranchLog (p u) - saddleBranchLog s) := by ring
          rw [hdecomp]
          exact norm_add_le _ _
        _ = ‖saddleMomentLogMainD1 (p u) - saddleBranchLog (p u)‖ * ‖s‖ +
            ‖saddleBranchLog (p u) - saddleBranchLog s‖ * ‖s‖ := by ring
        _ ≤ 12 + 1 := by
          apply add_le_add
          · calc
              ‖saddleMomentLogMainD1 (p u) - saddleBranchLog (p u)‖ * ‖s‖ ≤
                  ‖saddleMomentLogMainD1 (p u) - saddleBranchLog (p u)‖ *
                    (2 * ‖p u‖) := by gcongr
              _ = 2 * (‖saddleMomentLogMainD1 (p u) - saddleBranchLog (p u)‖ *
                    ‖p u‖) := by ring
              _ ≤ 2 * 6 := by
                gcongr
                simpa only [saddleBranchLog] using hlocal
              _ = 12 := by norm_num
          · simpa only [p] using hlog
        _ = 13 := by norm_num
    have hspos : 0 < ‖s‖ :=
      norm_pos_iff.mpr (leanSaddleSector_quantitative
        (leanTwoShiftAdmissible_base hs)).parameter_ne_zero
    apply (le_div_iff₀ hspos).mpr
    simp only [f', norm_mul]
    norm_num
    nlinarith
  have hdiff := norm_sub_le_mul_of_hasDerivAt_le (by norm_num) hderiv hbound
  have hscaled : ‖f 1 - f 0‖ * ‖s‖ ≤ 26 := by
    calc
      ‖f 1 - f 0‖ * ‖s‖ ≤ (26 / ‖s‖ * (1 - 0)) * ‖s‖ := by gcongr
      _ = 26 := by
        have hsne : ‖s‖ ≠ 0 := ne_of_gt (norm_pos_iff.mpr
          (leanSaddleSector_quantitative
            (leanTwoShiftAdmissible_base hs)).parameter_ne_zero)
        field_simp
        ring
  change ‖saddleMomentLogMain (s + 2) - saddleMomentLogMain s -
      2 * saddleBranchLog s‖ * ‖s‖ ≤ 26
  simp only [f, p, ofReal_one, ofReal_zero, mul_one, mul_zero, add_zero,
    zero_mul, sub_zero] at hscaled
  have hshape : saddleMomentLogMain (s + 2) - 2 * saddleBranchLog s -
      saddleMomentLogMain s =
        saddleMomentLogMain (s + 2) - saddleMomentLogMain s -
          2 * saddleBranchLog s := by ring
  rw [hshape] at hscaled
  exact hscaled

def saddleMainTwoShiftRelativeError (s : ℂ) : ℂ :=
  exp (saddleMainTwoShiftLogError s) - 1

theorem saddleMomentMain_twoShift_factorization
    {s : ℂ} (hs : leanTwoShiftAdmissible s) :
    saddleMomentMain (s + 2) =
      saddleMomentMain s * quantitativeSaddleBranch s ^ 2 *
        (1 + saddleMainTwoShiftRelativeError s) := by
  have hs0 : s ∈ leanSaddleSector := leanTwoShiftAdmissible_base hs
  have hs1 : s + 2 ∈ leanSaddleSector := by
    simpa using (hs 1 (by constructor <;> norm_num)).1
  have hLne := (quantitativeSaddleBranch_scaled_bounds
    (leanSaddleSector_quantitative hs0)).1
  rw [saddleMomentMain_eq_exp_logMain hs1,
    saddleMomentMain_eq_exp_logMain hs0]
  have hlogSquare : exp (2 * saddleBranchLog s) =
      quantitativeSaddleBranch s ^ 2 := by
    unfold saddleBranchLog
    rw [show 2 * log (quantitativeSaddleBranch s) =
        log (quantitativeSaddleBranch s) +
      log (quantitativeSaddleBranch s) by ring,
      exp_add, Complex.exp_log hLne]
    ring
  have hlogDecomp : saddleMomentLogMain (s + 2) =
      saddleMomentLogMain s + 2 * saddleBranchLog s +
        saddleMainTwoShiftLogError s := by
    unfold saddleMainTwoShiftLogError
    ring
  rw [hlogDecomp, exp_add, exp_add, hlogSquare]
  unfold saddleMainTwoShiftRelativeError
  ring

theorem saddleMainTwoShiftRelativeError_mul_parameterNorm_le
    {s : ℂ} (hs : leanTwoShiftAdmissible s) :
    ‖saddleMainTwoShiftRelativeError s‖ * ‖s‖ ≤ 52 := by
  have hlog := saddleMainTwoShiftLogError_mul_parameterNorm_le hs
  have hs0 : s ∈ leanSaddleSector := leanTwoShiftAdmissible_base hs
  have hnormLarge :=
    leanSaddleSector_parameterNorm_ge_fiveHundredBillion hs0
  have hspos : 0 < ‖s‖ := lt_of_lt_of_le (by norm_num) hnormLarge
  have hlogSmall : ‖saddleMainTwoShiftLogError s‖ ≤ 1 := by
    have hdiv : ‖saddleMainTwoShiftLogError s‖ ≤ 26 / ‖s‖ :=
      (le_div_iff₀ hspos).mpr hlog
    calc
      ‖saddleMainTwoShiftLogError s‖ ≤ 26 / ‖s‖ := hdiv
      _ ≤ 1 := by
        apply (div_le_one hspos).mpr
        linarith
  have hexp := Complex.norm_exp_sub_one_le hlogSmall
  unfold saddleMainTwoShiftRelativeError
  calc
    ‖exp (saddleMainTwoShiftLogError s) - 1‖ * ‖s‖ ≤
        (2 * ‖saddleMainTwoShiftLogError s‖) * ‖s‖ := by gcongr
    _ = 2 * (‖saddleMainTwoShiftLogError s‖ * ‖s‖) := by ring
    _ ≤ 2 * 26 := by gcongr
    _ = 52 := by norm_num

def leanCoefficientSector : Set ℂ :=
  {s | Real.exp (leanSaddleCutoff + 1) < ‖s‖ ∧ |s.arg| < saddleOuterAngle}

theorem leanCoefficientSector_admissible
    {s : ℂ} (hs : s ∈ leanCoefficientSector) :
    leanTwoShiftAdmissible s := by
  intro t ht
  let w : ℂ := (2 * (t : ℂ)) / s
  let z : ℂ := 1 + w
  let p : ℂ := s + 2 * (t : ℂ)
  have hsCut : Real.exp leanSaddleCutoff < ‖s‖ := by
    apply lt_trans _ hs.1
    rw [Real.exp_add]
    have hpos := Real.exp_pos leanSaddleCutoff
    nlinarith [Real.exp_one_gt_two]
  have hsOuter : s ∈ leanSaddleSector :=
    ⟨hsCut, hs.2.trans saddleOuterAngle_lt_proofAngle⟩
  have hsne : s ≠ 0 := (leanSaddleSector_quantitative hsOuter).parameter_ne_zero
  have hsHuge := leanSaddleSector_parameterNorm_ge_fiveHundredBillion hsOuter
  have htAbs : |t| ≤ 1 := by
    rw [abs_of_nonneg ht.1]
    exact ht.2
  have hwNorm : ‖w‖ ≤ 1 / 1000 := by
    simp only [w, norm_div, norm_mul, norm_ofNat, norm_real, Real.norm_eq_abs]
    have hspos : 0 < ‖s‖ := lt_of_lt_of_le (by norm_num) hsHuge
    apply (div_le_iff₀ hspos).mpr
    calc
      2 * |t| ≤ 2 * 1 := by gcongr
      _ ≤ (1 / 1000 : ℝ) * ‖s‖ := by nlinarith
  have hzRe : 0 < z.re := by
    have hwRe := (Complex.abs_re_le_norm w).trans hwNorm
    simp only [z, add_re, one_re]
    nlinarith [neg_le_of_abs_le hwRe]
  have hzNormLower : 999 / 1000 ≤ ‖z‖ := by
    have htri : (1 : ℝ) ≤ ‖z‖ + ‖w‖ := by
      calc
        (1 : ℝ) = ‖(1 : ℂ)‖ := by norm_num
        _ = ‖z - w‖ := by simp only [z]; ring_nf
        _ ≤ ‖z‖ + ‖w‖ := norm_sub_le _ _
    linarith
  have hzNe : z ≠ 0 := norm_pos_iff.mp (lt_of_lt_of_le (by norm_num) hzNormLower)
  have hzArg : |z.arg| < saddleOuterAngle := by
    have hargRange : |z.arg| ≤ Real.pi / 2 :=
      Complex.abs_arg_le_pi_div_two_iff.mpr hzRe.le
    have hzIm : |z.im| ≤ 1 / 1000 := by
      have := (Complex.abs_im_le_norm w).trans hwNorm
      simpa only [z, add_im, one_im, zero_add] using this
    have hsin : |Real.sin z.arg| ≤ 1 / 999 := by
      rw [Complex.sin_arg, abs_div, abs_of_nonneg (norm_nonneg z)]
      apply (div_le_iff₀ (norm_pos_iff.mpr hzNe)).mpr
      nlinarith
    have hjordan : 2 / Real.pi * |z.arg| ≤ |Real.sin z.arg| :=
      Real.mul_abs_le_abs_sin hargRange
    have hpiPos : 0 < Real.pi := Real.pi_pos
    calc
      |z.arg| = (Real.pi / 2) * (2 / Real.pi * |z.arg|) := by
        field_simp [Real.pi_ne_zero]
      _ ≤ (Real.pi / 2) * |Real.sin z.arg| := by gcongr
      _ ≤ (Real.pi / 2) * (1 / 999) := by gcongr
      _ < 1 / 400 := by
        rw [div_mul_div_comm]
        nlinarith [Real.pi_lt_four]
      _ < saddleOuterAngle := by norm_num [saddleOuterAngle]
  have hpFactor : p = s * z := by
    simp only [p, z, w]
    field_simp [hsne]
  have hpArg : |p.arg| < saddleProofAngle := by
    have hsumAbs : |s.arg + z.arg| < saddleProofAngle := by
      calc
        |s.arg + z.arg| ≤ |s.arg| + |z.arg| := abs_add_le _ _
        _ < saddleOuterAngle + saddleOuterAngle := add_lt_add hs.2 hzArg
        _ = saddleProofAngle := by norm_num [saddleOuterAngle, saddleProofAngle]
    have hsumRange : s.arg + z.arg ∈ Ioc (-Real.pi) Real.pi := by
      have hsmall : |s.arg + z.arg| < Real.pi :=
        hsumAbs.trans (saddleProofAngle_lt_pi_div_two.trans
          (half_lt_self Real.pi_pos))
      rw [abs_lt] at hsmall
      exact ⟨hsmall.1, hsmall.2.le⟩
    rw [hpFactor, Complex.arg_mul hsne hzNe hsumRange]
    exact hsumAbs
  have hshiftNorm : ‖(2 : ℂ) * (t : ℂ)‖ ≤ 2 := by
    rw [norm_mul]
    norm_num
    exact htAbs
  have htri : ‖s‖ ≤ ‖p‖ + 2 := by
    calc
      ‖s‖ = ‖p - 2 * (t : ℂ)‖ := by simp only [p]; congr 1; ring
      _ ≤ ‖p‖ + ‖2 * (t : ℂ)‖ := norm_sub_le _ _
      _ ≤ ‖p‖ + 2 := by gcongr
  have hnormCompare : ‖s‖ ≤ 2 * ‖p‖ := by
    nlinarith
  have hpRadial : Real.exp leanSaddleCutoff < ‖p‖ := by
    have hsDouble : 2 * Real.exp leanSaddleCutoff < ‖s‖ := by
      apply lt_trans _ hs.1
      rw [Real.exp_add]
      have hpos := Real.exp_pos leanSaddleCutoff
      nlinarith [Real.exp_one_gt_two]
    have hcutLarge : 2 < Real.exp leanSaddleCutoff := by
      exact Real.exp_one_gt_two.trans (Real.exp_lt_exp.mpr
        (by norm_num [leanSaddleCutoff]))
    nlinarith
  change p ∈ leanSaddleSector ∧ ‖s‖ ≤ 2 * ‖p‖
  exact ⟨⟨hpRadial, hpArg⟩, hnormCompare⟩

theorem saddleMomentMain_fixedSector_twoShift_factorization
    {s : ℂ} (hs : s ∈ leanCoefficientSector) :
    saddleMomentMain (s + 2) =
      saddleMomentMain s * quantitativeSaddleBranch s ^ 2 *
        (1 + saddleMainTwoShiftRelativeError s) :=
  saddleMomentMain_twoShift_factorization
    (leanCoefficientSector_admissible hs)

theorem saddleMainTwoShiftRelativeError_fixedSector
    {s : ℂ} (hs : s ∈ leanCoefficientSector) :
    ‖saddleMainTwoShiftRelativeError s‖ ≤ 52 / ‖s‖ := by
  have hprod := saddleMainTwoShiftRelativeError_mul_parameterNorm_le
    (leanCoefficientSector_admissible hs)
  have hspos : 0 < ‖s‖ := by
    have hsOuter := leanTwoShiftAdmissible_base
      (leanCoefficientSector_admissible hs)
    exact norm_pos_iff.mpr (leanSaddleSector_quantitative hsOuter).parameter_ne_zero
  exact (le_div_iff₀ hspos).mpr hprod

end

end Zeta23.Research.JensenWedge
