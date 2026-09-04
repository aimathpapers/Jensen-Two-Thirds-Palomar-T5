import Zeta23.Research.JensenWedge.HigherThetaContour

/-!
# Complete theta moment and the low endpoint interval

The contour theorems begin at the branch-safe point `u = 1`.  This module
keeps the omitted real interval `(0,1]` separate, proves a uniform absolute
bound there, and only then joins it to the all-mode bottom ray.  The result
is the full moment on `(0,infinity)` with an explicit inverse-curvature
relative error.  No full-line contour crossing the principal-log cut is
introduced.
-/

namespace Zeta23.Research.JensenWedge

open Complex Filter Function MeasureTheory Set Topology

noncomputable section

theorem fullThetaContourIntegrand_low_norm_le_six
    {s : ℂ} (hs : s ∈ leanSaddleSector) {u : ℝ}
    (hu0 : 0 < u) (hu1 : u ≤ 1) :
    ‖fullThetaContourIntegrand s u‖ ≤ 6 := by
  have hsre : 0 < s.re := by
    have hcomp := leanSaddleSector_parameter_component_bounds hs
    have hspos : 0 < ‖s‖ := norm_pos_iff.mpr
      (leanSaddleSector_quantitative hs).parameter_ne_zero
    nlinarith
  have hlog : Real.log u ≤ 0 := Real.log_nonpos hu0.le hu1
  have hq : 1 ≤ Real.pi * (exp (u : ℂ)).re := by
    simp only [Complex.exp_re, ofReal_re, ofReal_im, Real.cos_zero, mul_one]
    calc
      (1 : ℝ) ≤ 3 * 1 := by norm_num
      _ ≤ Real.pi * Real.exp u := by
        gcongr
        · exact Real.pi_gt_three.le
        · exact Real.one_le_exp hu0.le
  have hhigh := higherThetaMode_tsum_norm_le (s := s) (u := (u : ℂ)) hq
  have hhalf := exp_neg_three_mul_le_half hq
  have hhighLead : ‖∑' n : ℕ, higherThetaMode n s (u : ℂ)‖ ≤
      ‖leadingIntegrand s (u : ℂ)‖ := by
    calc
      ‖∑' n : ℕ, higherThetaMode n s (u : ℂ)‖ ≤
          2 * ‖leadingIntegrand s (u : ℂ)‖ *
            Real.exp (-3 * (Real.pi * (exp (u : ℂ)).re)) := hhigh
      _ = ‖leadingIntegrand s (u : ℂ)‖ *
          (2 * Real.exp (-3 * (Real.pi * (exp (u : ℂ)).re))) := by ring
      _ ≤ ‖leadingIntegrand s (u : ℂ)‖ * 1 := by
        gcongr
        linarith
      _ = ‖leadingIntegrand s (u : ℂ)‖ := by ring
  have hlead : ‖leadingIntegrand s (u : ℂ)‖ ≤ 3 := by
    rw [leadingIntegrand_eq_exp_logIntegrand, Complex.norm_exp]
    calc
      Real.exp (leadingLogIntegrand s (u : ℂ)).re ≤ Real.exp 1 := by
        apply Real.exp_le_exp.mpr
        have hphase : (leadingLogIntegrand s (u : ℂ)).re =
            s.re * Real.log u + u / 4 - Real.pi * Real.exp u := by
          unfold leadingLogIntegrand
          rw [sub_re, add_re, mul_re, Complex.log_ofReal_re, Complex.log_im,
            Complex.arg_ofReal_of_nonneg hu0.le]
          norm_num [Complex.div_re, Complex.exp_re]
        rw [hphase]
        have hslog : s.re * Real.log u ≤ 0 :=
          mul_nonpos_of_nonneg_of_nonpos hsre.le hlog
        nlinarith [Real.pi_pos, Real.exp_pos u]
      _ ≤ 3 := Real.exp_one_lt_three.le
  unfold fullThetaContourIntegrand
  calc
    ‖leadingIntegrand s (u : ℂ) +
        ∑' n : ℕ, higherThetaMode n s (u : ℂ)‖ ≤
        ‖leadingIntegrand s (u : ℂ)‖ +
          ‖∑' n : ℕ, higherThetaMode n s (u : ℂ)‖ := norm_add_le _ _
    _ ≤ 2 * ‖leadingIntegrand s (u : ℂ)‖ := by linarith
    _ ≤ 6 := by linarith

theorem aestronglyMeasurable_fullThetaContourIntegrand_low
    (s : ℂ) :
    AEStronglyMeasurable (fun u : ℝ => fullThetaContourIntegrand s u)
      (volume.restrict (Ioc 0 1)) := by
  have hlead : AEStronglyMeasurable (fun u : ℝ => leadingIntegrand s u)
      (volume.restrict (Ioc 0 1)) := by
    exact (leadingIntegrand_differentiableOn_domain s).continuousOn.comp'
      (by fun_prop) (by
        intro u hu
        simp only [leadingLogDomain, mem_setOf_eq, ofReal_re]
        exact hu.1) |>.aestronglyMeasurable measurableSet_Ioc
  have hmode (n : ℕ) : AEStronglyMeasurable
      (fun u : ℝ => higherThetaMode n s u)
      (volume.restrict (Ioc 0 1)) := by
    exact (higherThetaMode_differentiableOn_domain n s).continuousOn.comp'
      (by fun_prop) (by
        intro u hu
        simp only [leadingLogDomain, mem_setOf_eq, ofReal_re]
        exact hu.1) |>.aestronglyMeasurable measurableSet_Ioc
  unfold fullThetaContourIntegrand
  exact hlead.add (AEStronglyMeasurable.tsum hmode)

theorem integrableOn_fullThetaContourIntegrand_low
    {s : ℂ} (hs : s ∈ leanSaddleSector) :
    IntegrableOn (fun u : ℝ => fullThetaContourIntegrand s u) (Ioc 0 1) := by
  have hconst : IntegrableOn (fun _ : ℝ => (6 : ℝ)) (Ioc 0 1) :=
    integrableOn_const (ne_of_lt measure_Ioc_lt_top)
  apply Integrable.mono' hconst
    (aestronglyMeasurable_fullThetaContourIntegrand_low s)
  filter_upwards [ae_restrict_mem measurableSet_Ioc] with u hu
  simpa only [Real.norm_eq_abs, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 6)] using
    fullThetaContourIntegrand_low_norm_le_six hs hu.1 hu.2

def fullThetaLowInterval (s : ℂ) : ℂ :=
  ∫ u : ℝ in Ioc 0 1, fullThetaContourIntegrand s u

theorem quantitativeSaddleBranch_fullThetaLowInterval_norm_le_six
    {s : ℂ} (hs : s ∈ leanSaddleSector) :
    ‖fullThetaLowInterval s‖ ≤ 6 := by
  unfold fullThetaLowInterval
  calc
    ‖∫ u : ℝ in Ioc 0 1, fullThetaContourIntegrand s u‖ ≤
        6 * (volume.real (Ioc (0 : ℝ) 1)) := by
      apply norm_setIntegral_le_of_norm_le_const measure_Ioc_lt_top
      intro u hu
      exact fullThetaContourIntegrand_low_norm_le_six hs hu.1 hu.2
    _ = 6 := by
      rw [Real.volume_real_Ioc]
      norm_num

theorem quantitativeSaddleBranch_fullThetaLowInterval_norm_le_exp
    {s : ℂ} (hs : s ∈ leanSaddleSector) :
    ‖fullThetaLowInterval s‖ ≤ Real.exp (6 * ‖s‖) := by
  have hsone : 1 ≤ ‖s‖ := by
    have hcut : 1 < Real.exp leanSaddleCutoff := by
      rw [← Real.exp_zero]
      exact Real.exp_lt_exp.mpr (by norm_num [leanSaddleCutoff])
    exact (hcut.trans hs.1).le
  calc
    ‖fullThetaLowInterval s‖ ≤ 6 :=
      quantitativeSaddleBranch_fullThetaLowInterval_norm_le_six hs
    _ ≤ 1 + 6 * ‖s‖ := by linarith
    _ ≤ Real.exp (6 * ‖s‖) := by
      simpa [add_comm] using Real.add_one_le_exp (6 * ‖s‖)

theorem quantitativeSaddleBranch_fullThetaLowInterval_relative_inverse_curvature
    {s : ℂ} (hs : s ∈ leanSaddleSector) :
    let L := quantitativeSaddleBranch s
    let K := leadingCurvature s L
    let M := ∫ r : ℝ, leadingGaussian K r
    ‖fullThetaLowInterval s‖ ≤
      (1 / ‖K‖) * ‖leadingIntegrand s L * M‖ := by
  exact quantitativeSaddleBranch_connector_relative_inverse_curvature_of_norm_le
    hs (quantitativeSaddleBranch_fullThetaLowInterval_norm_le_exp hs)

def fullThetaMoment (s : ℂ) : ℂ :=
  ∫ u : ℝ in Ioi 0, fullThetaContourIntegrand s u

theorem integrableOn_fullThetaContourIntegrand_bottom (s : ℂ) :
    IntegrableOn (fun u : ℝ => fullThetaContourIntegrand s u) (Ioi 1) := by
  unfold fullThetaContourIntegrand
  have hlead : IntegrableOn (fun u : ℝ => leadingIntegrand s u) (Ioi 1) :=
    integrableOn_leadingBottomRay s
  have hhigh : IntegrableOn
      (fun u : ℝ => ∑' n : ℕ, higherThetaMode n s u) (Ioi 1) := by
    simpa using integrableOn_higherThetaHorizontalSum s
      (b := 0) (by norm_num)
  exact hlead.add hhigh

theorem fullThetaMoment_eq_low_add_bottom
    {s : ℂ} (hs : s ∈ leanSaddleSector) :
    fullThetaMoment s =
      fullThetaLowInterval s + fullThetaBottomRay s := by
  let f : ℝ → ℂ := fun u => fullThetaContourIntegrand s u
  have hlow : IntegrableOn f (Ioc 0 1) := by
    simpa only [f] using integrableOn_fullThetaContourIntegrand_low hs
  have hbottom : IntegrableOn f (Ioi 1) := by
    simpa only [f] using integrableOn_fullThetaContourIntegrand_bottom s
  have hsplit := setIntegral_union Ioc_disjoint_Ioi_same
    measurableSet_Ioi hlow hbottom
  rw [Ioc_union_Ioi_eq_Ioi (by norm_num : (0 : ℝ) ≤ 1)] at hsplit
  simpa only [fullThetaMoment, fullThetaLowInterval,
    fullThetaBottomRay, f] using hsplit

/-- The complete theta moment on `(0, infinity)` has the exact leading
Gaussian main term with an explicit inverse-curvature relative error. -/
theorem quantitativeSaddleBranch_fullThetaMoment_relative_error_le
    {s : ℂ} (hs : s ∈ leanSaddleSector) :
    let L := quantitativeSaddleBranch s
    let K := leadingCurvature s L
    let M := ∫ r : ℝ, leadingGaussian K r
    ‖fullThetaMoment s - leadingIntegrand s L * M‖ ≤
      ((71000004 + 2 * (2 * 20 ^ 15 * (Nat.factorial 15 : ℝ))) / ‖K‖) *
        ‖leadingIntegrand s L * M‖ := by
  dsimp only
  let L : ℂ := quantitativeSaddleBranch s
  let K : ℂ := leadingCurvature s L
  let M : ℂ := ∫ r : ℝ, leadingGaussian K r
  let G : ℂ := leadingIntegrand s L * M
  let T : ℝ := 2 * 20 ^ 15 * (Nat.factorial 15 : ℝ)
  have hsplit : fullThetaMoment s =
      fullThetaLowInterval s + fullThetaBottomRay s :=
    fullThetaMoment_eq_low_add_bottom hs
  have hlow : ‖fullThetaLowInterval s‖ ≤
      (1 / ‖K‖) * ‖G‖ := by
    simpa only [L, K, M, G] using
      quantitativeSaddleBranch_fullThetaLowInterval_relative_inverse_curvature hs
  have hbottom : ‖fullThetaBottomRay s - G‖ ≤
      ((71000003 + 2 * T) / ‖K‖) * ‖G‖ := by
    simpa only [L, K, M, G, T] using
      quantitativeSaddleBranch_fullThetaBottomRay_relative_error_le hs
  rw [hsplit]
  have halgebra : fullThetaLowInterval s + fullThetaBottomRay s - G =
      fullThetaLowInterval s + (fullThetaBottomRay s - G) := by ring
  rw [halgebra]
  calc
    ‖fullThetaLowInterval s + (fullThetaBottomRay s - G)‖ ≤
        ‖fullThetaLowInterval s‖ + ‖fullThetaBottomRay s - G‖ :=
      norm_add_le _ _
    _ ≤ (1 / ‖K‖) * ‖G‖ +
        ((71000003 + 2 * T) / ‖K‖) * ‖G‖ := by gcongr
    _ = ((71000004 + 2 * T) / ‖K‖) * ‖G‖ := by ring
    _ = _ := by simp only [L, K, M, G, T]

end

end Zeta23.Research.JensenWedge
