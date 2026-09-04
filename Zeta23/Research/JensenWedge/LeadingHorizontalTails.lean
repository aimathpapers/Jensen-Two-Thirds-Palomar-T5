import Zeta23.Research.JensenWedge.LeadingHorizontalBoundary

/-!
# Noncentral horizontal-ray tails

This module turns strict concavity and the two central-window boundary signs
into pointwise exponential envelopes.  It then integrates those envelopes on
the finite left interval and infinite right interval, retaining explicit
constants for later normalization by the Gaussian main term.
-/

namespace Zeta23.Research.JensenWedge

open Complex MeasureTheory Set

noncomputable section

theorem concaveOn_right_tangent_bound
    {S : Set ℝ} {f : ℝ → ℝ} {x y d : ℝ}
    (hc : ConcaveOn ℝ S f) (hx : x ∈ S) (hy : y ∈ S)
    (hxy : x ≤ y) (hd : HasDerivAt f d x) :
    f y - f x ≤ d * (y - x) := by
  rcases hxy.eq_or_lt with rfl | hlt
  · simp
  · have hs := hc.slope_le_of_hasDerivAt hx hy hlt hd
    rw [slope_def_field] at hs
    have hpos : 0 < y - x := sub_pos.mpr hlt
    exact (div_le_iff₀ hpos).mp hs

theorem concaveOn_left_tangent_bound
    {S : Set ℝ} {f : ℝ → ℝ} {x y d : ℝ}
    (hc : ConcaveOn ℝ S f) (hx : x ∈ S) (hy : y ∈ S)
    (hxy : x ≤ y) (hd : HasDerivAt f d y) :
    f x - f y ≤ d * (x - y) := by
  rcases hxy.eq_or_lt with rfl | hlt
  · simp
  · have hs := hc.le_slope_of_hasDerivAt hx hy hlt hd
    rw [slope_def_field] at hs
    have hpos : 0 < y - x := sub_pos.mpr hlt
    have hmul := (le_div_iff₀ hpos).mp hs
    nlinarith

theorem quantitativeSaddleBranch_horizontal_phase_tail_envelopes
    {s : ℂ} (hs : s ∈ leanSaddleSector) :
    let L := quantitativeSaddleBranch s
    let K := leadingCurvature s L
    let ρ := leadingCentralRadius K
    (∀ r, 1 - L.re ≤ r → r ≤ -ρ →
      leadingHorizontalRealLog s L r - leadingHorizontalRealLog s L 0 ≤
        -(‖K‖ * ρ ^ 2 / 20) + (r + ρ)) ∧
    (∀ r, ρ ≤ r →
      leadingHorizontalRealLog s L r - leadingHorizontalRealLog s L 0 ≤
        -(‖K‖ * ρ ^ 2 / 20) - (‖K‖ * ρ / 20) * (r - ρ)) := by
  dsimp only
  let L : ℂ := quantitativeSaddleBranch s
  let K : ℂ := leadingCurvature s L
  let ρ : ℝ := leadingCentralRadius K
  let f : ℝ → ℝ := leadingHorizontalRealLog s L
  let S : Set ℝ := Ici (1 - L.re)
  have hLre : 1000 < L.re := by
    simpa only [L] using quantitativeSaddleBranch_re_gt hs
  have hρpos : 0 < ρ := by
    simpa only [L, K, ρ] using quantitativeSaddleBranch_centralRadius_pos hs
  have hρle : ρ ≤ 1 / 10 := by
    simpa only [L, K, ρ] using
      quantitativeSaddleBranch_centralRadius_le_tenth hs
  have hleftMem : -ρ ∈ S := by
    simp only [S, mem_Ici]
    linarith
  have hrightMem : ρ ∈ S := by
    simp only [S, mem_Ici]
    linarith
  have hconc : ConcaveOn ℝ S f := by
    exact (by simpa only [L, S, f] using
      (quantitativeSaddleBranch_horizontal_strictConcaveOn hs).concaveOn)
  have hsigns := quantitativeSaddleBranch_horizontal_boundary_derivative_signs hs
  have hleftSign : 1 < deriv f (-ρ) := by
    simpa only [L, K, ρ, f] using hsigns.1
  have hrightSign : deriv f ρ < -(‖K‖ * ρ / 20) := by
    simpa only [L, K, ρ, f] using hsigns.2
  have hgap := quantitativeSaddleBranch_horizontal_boundary_phase_gaps hs
  have hrightGap : f ρ - f 0 ≤ -(‖K‖ * ρ ^ 2 / 20) := by
    simpa [f, L, K, leadingHorizontalRealLog, leadingHorizontalLog] using hgap.1
  have hleftGap : f (-ρ) - f 0 ≤ -(‖K‖ * ρ ^ 2 / 20) := by
    simpa [f, L, K, leadingHorizontalRealLog, leadingHorizontalLog,
      sub_eq_add_neg] using hgap.2
  constructor
  · intro r hray hrrho
    have hrMem : r ∈ S := hray
    have hdiff : DifferentiableAt ℝ f (-ρ) := by
      apply (hasDerivAt_leadingHorizontalRealLog
        (s := s) (L := L) (r := -ρ) ?_).differentiableAt
      simp only [add_re, ofReal_re]
      linarith
    have htangent :=
      concaveOn_left_tangent_bound hconc hrMem hleftMem hrrho hdiff.hasDerivAt
    have hneg : r - -ρ ≤ 0 := by linarith
    have hscale : deriv f (-ρ) * (r - -ρ) ≤ r + ρ := by
      nlinarith
    change f r - f 0 ≤ _
    nlinarith
  · intro r hrrho
    have hrMem : r ∈ S := by
      simp only [S, mem_Ici]
      linarith
    have hdiff : DifferentiableAt ℝ f ρ := by
      apply (hasDerivAt_leadingHorizontalRealLog
        (s := s) (L := L) (r := ρ) ?_).differentiableAt
      simp only [add_re, ofReal_re]
      linarith
    have htangent :=
      concaveOn_right_tangent_bound hconc hrightMem hrMem hrrho hdiff.hasDerivAt
    have hnonneg : 0 ≤ r - ρ := sub_nonneg.mpr hrrho
    have hscale : deriv f ρ * (r - ρ) ≤
        -(‖K‖ * ρ / 20) * (r - ρ) :=
      mul_le_mul_of_nonneg_right hrightSign.le hnonneg
    change f r - f 0 ≤ _
    nlinarith

theorem norm_leadingIntegrand_horizontal_eq_exp
    (s L : ℂ) (r : ℝ) :
    ‖leadingIntegrand s (L + r)‖ =
      Real.exp (leadingHorizontalRealLog s L r) := by
  rw [leadingIntegrand_eq_exp_logIntegrand, Complex.norm_exp]
  rfl

theorem quantitativeSaddleBranch_horizontal_norm_tail_envelopes
    {s : ℂ} (hs : s ∈ leanSaddleSector) :
    let L := quantitativeSaddleBranch s
    let K := leadingCurvature s L
    let ρ := leadingCentralRadius K
    (∀ r, 1 - L.re ≤ r → r ≤ -ρ →
      ‖leadingIntegrand s (L + r)‖ ≤
        ‖leadingIntegrand s L‖ * Real.exp (-(‖K‖ * ρ ^ 2 / 20))) ∧
    (∀ r, ρ ≤ r →
      ‖leadingIntegrand s (L + r)‖ ≤
        ‖leadingIntegrand s L‖ * Real.exp (-(‖K‖ * ρ ^ 2 / 20)) *
          Real.exp (-(‖K‖ * ρ / 20) * (r - ρ))) := by
  dsimp only
  let L : ℂ := quantitativeSaddleBranch s
  let K : ℂ := leadingCurvature s L
  let ρ : ℝ := leadingCentralRadius K
  let f : ℝ → ℝ := leadingHorizontalRealLog s L
  have hphase := quantitativeSaddleBranch_horizontal_phase_tail_envelopes hs
  constructor
  · intro r hray hrrho
    have hp := hphase.1 r hray hrrho
    have hshift : r + ρ ≤ 0 := by linarith
    have hnorm0 : ‖leadingIntegrand s L‖ = Real.exp (f 0) := by
      have h := norm_leadingIntegrand_horizontal_eq_exp s L 0
      norm_num at h
      simpa only [f] using h
    rw [norm_leadingIntegrand_horizontal_eq_exp, hnorm0]
    rw [← Real.exp_add]
    apply Real.exp_le_exp.mpr
    change f r ≤ f 0 + -(‖K‖ * ρ ^ 2 / 20)
    linarith
  · intro r hrrho
    have hp := hphase.2 r hrrho
    have hnorm0 : ‖leadingIntegrand s L‖ = Real.exp (f 0) := by
      have h := norm_leadingIntegrand_horizontal_eq_exp s L 0
      norm_num at h
      simpa only [f] using h
    rw [norm_leadingIntegrand_horizontal_eq_exp, hnorm0]
    rw [← Real.exp_add, ← Real.exp_add]
    apply Real.exp_le_exp.mpr
    change f r ≤ f 0 + -(‖K‖ * ρ ^ 2 / 20) +
      -(‖K‖ * ρ / 20) * (r - ρ)
    linarith

theorem integral_exp_neg_mul_sub_Ioi
    {a ρ : ℝ} (ha : 0 < a) :
    (∫ r : ℝ in Ioi ρ, Real.exp (-a * (r - ρ))) = 1 / a := by
  have hformula := integral_exp_mul_Ioi (a := -a) (by linarith) ρ
  have hfun : (fun r : ℝ => Real.exp (-a * (r - ρ))) =
      fun r : ℝ => Real.exp (a * ρ) * Real.exp ((-a) * r) := by
    funext r
    rw [← Real.exp_add]
    congr 1
    ring
  rw [hfun, MeasureTheory.integral_const_mul, hformula]
  rw [show -Real.exp (-a * ρ) / -a = Real.exp (-a * ρ) / a by ring]
  rw [← mul_div_assoc, ← Real.exp_add]
  simp

theorem quantitativeSaddleBranch_horizontal_tail_integral_bounds
    {s : ℂ} (hs : s ∈ leanSaddleSector) :
    let L := quantitativeSaddleBranch s
    let K := leadingCurvature s L
    let ρ := leadingCentralRadius K
    (∫ r : ℝ in Icc (1 - L.re) (-ρ), ‖leadingIntegrand s (L + r)‖) ≤
        L.re * ‖leadingIntegrand s L‖ *
          Real.exp (-(‖K‖ * ρ ^ 2 / 20)) ∧
    (∫ r : ℝ in Ioi ρ, ‖leadingIntegrand s (L + r)‖) ≤
        ‖leadingIntegrand s L‖ *
          Real.exp (-(‖K‖ * ρ ^ 2 / 20)) * (20 / (‖K‖ * ρ)) := by
  dsimp only
  let L : ℂ := quantitativeSaddleBranch s
  let K : ℂ := leadingCurvature s L
  let ρ : ℝ := leadingCentralRadius K
  let C : ℝ := ‖leadingIntegrand s L‖ *
    Real.exp (-(‖K‖ * ρ ^ 2 / 20))
  let a : ℝ := ‖K‖ * ρ / 20
  have hLre : 1000 < L.re := by
    simpa only [L] using quantitativeSaddleBranch_re_gt hs
  have hρpos : 0 < ρ := by
    simpa only [L, K, ρ] using quantitativeSaddleBranch_centralRadius_pos hs
  have hρle : ρ ≤ 1 / 10 := by
    simpa only [L, K, ρ] using
      quantitativeSaddleBranch_centralRadius_le_tenth hs
  have hKpos : 0 < ‖K‖ := by
    have hKge : 4000 ≤ ‖K‖ := by
      simpa only [L, K] using
        quantitativeSaddleBranch_curvature_norm_ge_fourThousand hs
    linarith
  have ha : 0 < a := by dsimp [a]; positivity
  have henv := quantitativeSaddleBranch_horizontal_norm_tail_envelopes hs
  constructor
  · let A : Set ℝ := Icc (1 - L.re) (-ρ)
    have hpoint : ∀ r ∈ A, ‖leadingIntegrand s (L + r)‖ ≤ C := by
      intro r hr
      exact henv.1 r hr.1 hr.2
    have hfinite : volume A < ⊤ := measure_Icc_lt_top
    have hbound := norm_setIntegral_le_of_norm_le_const
      (μ := volume) (f := fun r : ℝ => ‖leadingIntegrand s (L + r)‖)
      hfinite (fun r hr => by simpa [Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _)] using hpoint r hr)
    have hintegralNonneg : 0 ≤
        ∫ r : ℝ in A, ‖leadingIntegrand s (L + r)‖ :=
      integral_nonneg_of_ae (Filter.Eventually.of_forall fun _ => norm_nonneg _)
    have hmeasure : volume.real A = L.re - ρ - 1 := by
      change (volume A).toReal = L.re - ρ - 1
      dsimp [A]
      rw [Real.volume_Icc, ENNReal.toReal_ofReal (by linarith)]
      ring
    have hlength : L.re - ρ - 1 ≤ L.re := by linarith
    have hlocal :
        (∫ r : ℝ in A, ‖leadingIntegrand s (L + r)‖) ≤ L.re * C := by
      calc
        (∫ r : ℝ in A, ‖leadingIntegrand s (L + r)‖) ≤
            ‖∫ r : ℝ in A, ‖leadingIntegrand s (L + r)‖‖ := by
          simpa [Real.norm_eq_abs, abs_of_nonneg hintegralNonneg]
        _ ≤ C * volume.real A := hbound
        _ = C * (L.re - ρ - 1) := by rw [hmeasure]
        _ ≤ C * L.re := by
          exact mul_le_mul_of_nonneg_left hlength (by positivity)
        _ = L.re * C := by ring
    simpa [A, L, K, ρ, C, mul_assoc] using hlocal
  · let g : ℝ → ℝ := fun r => C * Real.exp (-a * (r - ρ))
    have hgint : IntegrableOn g (Ioi ρ) := by
      have hbase : IntegrableOn (fun r : ℝ => Real.exp (-a * (r - ρ))) (Ioi ρ) := by
        have hrewrite : (fun r : ℝ => Real.exp (-a * (r - ρ))) =
            fun r : ℝ => Real.exp (a * ρ) * Real.exp ((-a) * r) := by
          funext r
          rw [← Real.exp_add]
          congr 1
          ring
        rw [hrewrite]
        exact (integrableOn_exp_mul_Ioi (a := -a) (by linarith) ρ).const_mul _
      exact hbase.const_mul C
    have htargetMeas : AEStronglyMeasurable
        (fun r : ℝ => ‖leadingIntegrand s (L + r)‖) (volume.restrict (Ioi ρ)) := by
      have hcont : ContinuousOn
          (fun r : ℝ => leadingIntegrand s (L + r)) (Ioi ρ) := by
        exact (leadingIntegrand_differentiableOn_domain s).continuousOn.comp'
          (by fun_prop) (by
            intro r hr
            have hr' : ρ < r := hr
            simp only [leadingLogDomain, mem_setOf_eq, add_re, ofReal_re]
            linarith)
      exact hcont.norm.aestronglyMeasurable measurableSet_Ioi
    have htarget : IntegrableOn
        (fun r : ℝ => ‖leadingIntegrand s (L + r)‖) (Ioi ρ) := by
      apply Integrable.mono' hgint htargetMeas
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with r hr
      have hp := henv.2 r hr.le
      simpa [L, K, ρ, C, a, g, Real.norm_eq_abs,
        abs_of_nonneg (norm_nonneg _)] using hp
    have hmono := setIntegral_mono_on htarget hgint measurableSet_Ioi (fun r hr => by
      have hp := henv.2 r hr.le
      simpa only [L, K, ρ, C, a, g] using hp)
    have hgintegral : (∫ r : ℝ in Ioi ρ, g r) = C * (1 / a) := by
      simp only [g]
      rw [MeasureTheory.integral_const_mul, integral_exp_neg_mul_sub_Ioi ha]
    rw [hgintegral] at hmono
    have hlocal :
        (∫ r : ℝ in Ioi ρ, ‖leadingIntegrand s (L + r)‖) ≤
          C * (20 / (‖K‖ * ρ)) := by
      calc
        (∫ r : ℝ in Ioi ρ, ‖leadingIntegrand s (L + r)‖) ≤
            C * (1 / a) := hmono
        _ = C * (20 / (‖K‖ * ρ)) := by
          dsimp [a]
          field_simp
    simpa [L, K, ρ, C, mul_assoc] using hlocal

end

end Zeta23.Research.JensenWedge
