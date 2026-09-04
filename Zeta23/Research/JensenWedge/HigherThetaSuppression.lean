import Zeta23.Research.JensenWedge.HigherThetaScale

/-!
# Quantitative suppression of the complete higher theta tail

This module centers the legal shifted ray at the quantitative saddle, splits
it into the left tail, central window, and right tail, and controls the entire
infinite sum of modes `k >= 2`.  The central window uses the inverse-square
curvature suppression of each pointwise higher-mode sum; the noncentral
pieces are dominated by the already-integrable leading mode.  The result is
an explicit inverse-curvature estimate relative to the exact complex
Gaussian main term, followed by the full all-mode top-ray theorem.
-/

namespace Zeta23.Research.JensenWedge

open Complex MeasureTheory Set

noncomputable section

theorem quantitativeSaddleBranch_central_leading_norm_integral_le_two_amplitude
    {s : ℂ} (hs : s ∈ leanSaddleSector) :
    let L := quantitativeSaddleBranch s
    let K := leadingCurvature s L
    let ρ := leadingCentralRadius K
    (∫ r : ℝ in Icc (-ρ) ρ, ‖leadingIntegrand s (L + r)‖) ≤
      2 * ‖leadingIntegrand s L‖ := by
  dsimp only
  let L : ℂ := quantitativeSaddleBranch s
  let K : ℂ := leadingCurvature s L
  let ρ : ℝ := leadingCentralRadius K
  let g : ℂ := leadingIntegrand s L
  have hLre : 1000 < L.re := by
    simpa only [L] using quantitativeSaddleBranch_re_gt hs
  have hρpos : 0 < ρ := by
    simpa only [L, K, ρ] using quantitativeSaddleBranch_centralRadius_pos hs
  have hρle : ρ ≤ 1 / 10 := by
    simpa only [L, K, ρ] using
      quantitativeSaddleBranch_centralRadius_le_tenth hs
  have hcentral : ‖K‖ * ρ ^ 3 ≤ 1 / 2 := by
    simpa only [L, K, ρ] using
      quantitativeSaddleBranch_curvature_mul_centralRadius_cube_le_half hs
  have hKre : 0 < K.re := by
    simpa only [L, K] using quantitativeSaddleBranch_curvature_re_pos hs
  have hpoint : ∀ r ∈ Icc (-ρ) ρ,
      ‖leadingIntegrand s (L + r)‖ ≤ 9 * ‖g‖ := by
    intro r hr
    have hrabs : |r| ≤ ρ := by rw [abs_le]; exact hr
    have hrTenth : |r| ≤ 1 / 10 := hrabs.trans hρle
    have hrcentral : ‖K‖ * |r| ^ 3 ≤ 1 / 2 := by
      exact (mul_le_mul_of_nonneg_left
        (pow_le_pow_left₀ (abs_nonneg r) hrabs 3) (norm_nonneg K)).trans hcentral
    have hpert := quantitativeSaddleBranch_localPerturbation_norm_le hs hrTenth
    have hpertOne :
        ‖leadingLocalPerturbation s L r‖ ≤ 1 := by
      simpa only [L, K] using hpert.trans (by nlinarith : 2 * ‖K‖ * |r| ^ 3 ≤ 1)
    have hgauss : ‖leadingGaussian K r‖ ≤ 3 := by
      rw [norm_leadingGaussian]
      calc
        Real.exp (r - K.re * r ^ 2 / 2) ≤ Real.exp |r| := by
          apply Real.exp_monotone
          have hquad : 0 ≤ K.re * r ^ 2 / 2 := by positivity
          linarith [le_abs_self r]
        _ ≤ Real.exp 1 := by
          apply Real.exp_monotone
          linarith
        _ ≤ 3 := Real.exp_one_lt_three.le
    have hpertExp : ‖exp (leadingLocalPerturbation s L r)‖ ≤ 3 := by
      rw [Complex.norm_exp]
      calc
        Real.exp (leadingLocalPerturbation s L r).re ≤
            Real.exp ‖leadingLocalPerturbation s L r‖ := by
          exact Real.exp_monotone (Complex.re_le_norm _)
        _ ≤ Real.exp 1 := Real.exp_monotone hpertOne
        _ ≤ 3 := Real.exp_one_lt_three.le
    rw [quantitativeSaddleBranch_localFactorization hs hrTenth, norm_mul,
      norm_mul]
    dsimp only [g]
    calc
      ‖leadingIntegrand s L‖ * ‖leadingGaussian K r‖ *
          ‖exp (leadingLocalPerturbation s L r)‖ ≤
          ‖leadingIntegrand s L‖ * 3 * 3 := by gcongr
      _ = 9 * ‖leadingIntegrand s L‖ := by ring
  have hcontinuous : ContinuousOn
      (fun r : ℝ => ‖leadingIntegrand s (L + r)‖) (Icc (-ρ) ρ) := by
    apply ContinuousOn.norm
    exact (leadingIntegrand_differentiableOn_domain s).continuousOn.comp'
      (by fun_prop) (by
        intro r hr
        change 0 < (L + (r : ℂ)).re
        simp only [add_re, ofReal_re]
        linarith [hr.1])
  have hInt : IntegrableOn
      (fun r : ℝ => ‖leadingIntegrand s (L + r)‖) (Icc (-ρ) ρ) :=
    hcontinuous.integrableOn_Icc
  have hConst : IntegrableOn (fun _ : ℝ => 9 * ‖g‖) (Icc (-ρ) ρ) :=
    integrableOn_const (ne_of_lt measure_Icc_lt_top)
  calc
    (∫ r : ℝ in Icc (-ρ) ρ, ‖leadingIntegrand s (L + r)‖) ≤
        ∫ _r : ℝ in Icc (-ρ) ρ, 9 * ‖g‖ := by
      apply integral_mono_ae hInt hConst
      filter_upwards [ae_restrict_mem measurableSet_Icc] with r hr
      exact hpoint r hr
    _ = (2 * ρ) * (9 * ‖g‖) := by
      rw [setIntegral_const]
      change (volume (Icc (-ρ) ρ)).toReal * (9 * ‖g‖) = _
      rw [Real.volume_Icc, ENNReal.toReal_ofReal (by linarith)]
      ring
    _ ≤ 2 * ‖g‖ := by
      nlinarith [norm_nonneg g,
        mul_nonneg (sub_nonneg.mpr hρle) (norm_nonneg g)]
    _ = _ := by simp only [L, g]

theorem quantitativeSaddleBranch_central_higherThetaSum_norm_le_curvature_sq_inv_mul_leading
    {s : ℂ} (hs : s ∈ leanSaddleSector) {r : ℝ}
    (hr : r ∈ Icc
      (-leadingCentralRadius
        (leadingCurvature s (quantitativeSaddleBranch s)))
      (leadingCentralRadius
        (leadingCurvature s (quantitativeSaddleBranch s)))) :
    let L := quantitativeSaddleBranch s
    let K := leadingCurvature s L
    ‖∑' n : ℕ, higherThetaMode n s (L + r)‖ ≤
      (1 / ‖K‖ ^ 2) * ‖leadingIntegrand s (L + r)‖ := by
  dsimp only
  let L : ℂ := quantitativeSaddleBranch s
  let K : ℂ := leadingCurvature s L
  let ρ : ℝ := leadingCentralRadius K
  let q : ℝ := Real.pi * (exp (L + r)).re
  have hK : 4000 ≤ ‖K‖ := by
    simpa only [L, K] using
      quantitativeSaddleBranch_curvature_norm_ge_fourThousand hs
  have hx : L.re - ρ ≤ L.re + r := by
    have hr' : r ∈ Icc (-ρ) ρ := by
      simpa only [L, K, ρ] using hr
    linarith [hr'.1]
  have hqScale :=
    quantitativeSaddleBranch_modeParameter_beyond_leftBoundary_ge_curvature_div_five
      hs hx
  have hu : ((L.re + r : ℝ) : ℂ) + L.im * I = L + r := by
    apply Complex.ext <;> simp
  rw [hu] at hqScale
  have hqScale' : ‖K‖ / 5 ≤ q := by
    simpa only [L, K, q] using hqScale
  have hqOne : 1 ≤ q := by nlinarith
  have hsum := higherThetaMode_tsum_norm_le (s := s) (u := L + r) hqOne
  have hfactor : 2 * Real.exp (-3 * q) ≤ 1 / ‖K‖ ^ 2 :=
    two_exp_modeFactor_le_curvature_sq_inv hK hqScale'
  calc
    ‖∑' n : ℕ, higherThetaMode n s (L + r)‖ ≤
        2 * ‖leadingIntegrand s (L + r)‖ * Real.exp (-3 * q) := by
      simpa only [q] using hsum
    _ = (2 * Real.exp (-3 * q)) * ‖leadingIntegrand s (L + r)‖ := by ring
    _ ≤ (1 / ‖K‖ ^ 2) * ‖leadingIntegrand s (L + r)‖ := by gcongr

theorem integrableOn_quantitativeSaddleBranch_centeredHigherThetaRay
    {s : ℂ} (hs : s ∈ leanSaddleSector) :
    let L := quantitativeSaddleBranch s
    IntegrableOn (fun r : ℝ => ∑' n : ℕ, higherThetaMode n s (L + r))
      (Ioi (1 - L.re)) := by
  dsimp only
  let L : ℂ := quantitativeSaddleBranch s
  let top : ℝ → ℂ := fun x =>
    ∑' n : ℕ, higherThetaMode n s (x + L.im * I)
  let F : ℝ → ℂ := fun x => (Ioi (1 : ℝ)).indicator top x
  have hb : |L.im| ≤ 1 / 20 := by
    simpa only [L] using (quantitativeSaddleBranch_im_abs_lt hs).le
  have htop : IntegrableOn top (Ioi 1) := by
    simpa only [L, top] using
      integrableOn_higherThetaHorizontalSum s hb
  have hF : Integrable F := by
    exact (integrable_indicator_iff measurableSet_Ioi).2 htop
  have hshift : Integrable (fun r : ℝ => F (r + L.re)) :=
    hF.comp_add_right L.re
  have heq : (fun r : ℝ => F (r + L.re)) =
      fun r : ℝ => (Ioi (1 - L.re)).indicator
        (fun r : ℝ => ∑' n : ℕ, higherThetaMode n s (L + r)) r := by
    funext r
    by_cases hr : r ∈ Ioi (1 - L.re)
    · have hr' : r + L.re ∈ Ioi (1 : ℝ) := by
        simp only [mem_Ioi] at hr ⊢
        linarith
      simp only [F, top, indicator_of_mem hr, indicator_of_mem hr']
      congr 1
      funext n
      congr 1
      apply Complex.ext <;> simp <;> ring
    · have hr' : r + L.re ∉ Ioi (1 : ℝ) := by
        simp only [mem_Ioi] at hr ⊢
        linarith
      simp [F, hr, hr']
  rw [heq] at hshift
  exact (integrable_indicator_iff measurableSet_Ioi).1 hshift

theorem quantitativeSaddleBranch_central_higherTheta_norm_integral_le
    {s : ℂ} (hs : s ∈ leanSaddleSector) :
    let L := quantitativeSaddleBranch s
    let K := leadingCurvature s L
    let ρ := leadingCentralRadius K
    (∫ r : ℝ in Icc (-ρ) ρ,
      ‖∑' n : ℕ, higherThetaMode n s (L + r)‖) ≤
      (2 / ‖K‖ ^ 2) * ‖leadingIntegrand s L‖ := by
  dsimp only
  let L : ℂ := quantitativeSaddleBranch s
  let K : ℂ := leadingCurvature s L
  let ρ : ℝ := leadingCentralRadius K
  let f : ℝ → ℂ := fun r =>
    ∑' n : ℕ, higherThetaMode n s (L + r)
  let g : ℝ → ℂ := fun r => leadingIntegrand s (L + r)
  have hLre : 1000 < L.re := by
    simpa only [L] using quantitativeSaddleBranch_re_gt hs
  have hρpos : 0 < ρ := by
    simpa only [L, K, ρ] using
      quantitativeSaddleBranch_centralRadius_pos hs
  have hρle : ρ ≤ 1 / 10 := by
    simpa only [L, K, ρ] using
      quantitativeSaddleBranch_centralRadius_le_tenth hs
  have hsubset : Icc (-ρ) ρ ⊆ Ioi (1 - L.re) := by
    intro r hr
    simp only [mem_Icc] at hr
    simp only [mem_Ioi]
    linarith
  have hf : IntegrableOn f (Icc (-ρ) ρ) := by
    apply (integrableOn_quantitativeSaddleBranch_centeredHigherThetaRay hs).mono_set
    simpa only [L, K, ρ, f] using hsubset
  have hg : IntegrableOn g (Icc (-ρ) ρ) := by
    apply (integrableOn_quantitativeSaddleBranch_centeredRay hs).mono_set
    simpa only [L, K, ρ, g] using hsubset
  have hKnonneg : 0 ≤ 1 / ‖K‖ ^ 2 := by positivity
  calc
    (∫ r : ℝ in Icc (-ρ) ρ, ‖f r‖) ≤
        ∫ r : ℝ in Icc (-ρ) ρ, (1 / ‖K‖ ^ 2) * ‖g r‖ := by
      apply integral_mono_ae hf.norm (hg.norm.const_mul _)
      filter_upwards [ae_restrict_mem measurableSet_Icc] with r hr
      simpa only [L, K, ρ, f, g] using
        quantitativeSaddleBranch_central_higherThetaSum_norm_le_curvature_sq_inv_mul_leading hs hr
    _ = (1 / ‖K‖ ^ 2) *
        (∫ r : ℝ in Icc (-ρ) ρ, ‖g r‖) := by
      rw [integral_const_mul]
    _ ≤ (1 / ‖K‖ ^ 2) * (2 * ‖leadingIntegrand s L‖) := by
      gcongr
      simpa only [L, K, ρ, g] using
        quantitativeSaddleBranch_central_leading_norm_integral_le_two_amplitude hs
    _ = (2 / ‖K‖ ^ 2) * ‖leadingIntegrand s L‖ := by ring
    _ = _ := by simp only [L, K]

theorem quantitativeSaddleBranch_central_higherTheta_norm_integral_relative_le
    {s : ℂ} (hs : s ∈ leanSaddleSector) :
    let L := quantitativeSaddleBranch s
    let K := leadingCurvature s L
    let ρ := leadingCentralRadius K
    let M := ∫ r : ℝ, leadingGaussian K r
    (∫ r : ℝ in Icc (-ρ) ρ,
      ‖∑' n : ℕ, higherThetaMode n s (L + r)‖) ≤
      (1 / ‖K‖) * ‖leadingIntegrand s L * M‖ := by
  dsimp only
  let L : ℂ := quantitativeSaddleBranch s
  let K : ℂ := leadingCurvature s L
  let ρ : ℝ := leadingCentralRadius K
  let M : ℂ := ∫ r : ℝ, leadingGaussian K r
  let G : ℂ := leadingIntegrand s L * M
  have hK : 4000 ≤ ‖K‖ := by
    simpa only [L, K] using
      quantitativeSaddleBranch_curvature_norm_ge_fourThousand hs
  have hKpos : 0 < ‖K‖ := by linarith
  have hamp : ‖leadingIntegrand s L‖ ≤
      ‖K‖ ^ (1 / 2 : ℝ) * ‖G‖ := by
    simpa only [L, K, M, G] using
      quantitativeSaddleBranch_amplitude_le_gaussianMain_scale hs
  have hcoef : (2 / ‖K‖ ^ 2) * ‖K‖ ^ (1 / 2 : ℝ) ≤ 1 / ‖K‖ := by
    have hsqrt : Real.sqrt ‖K‖ ≤ ‖K‖ / 2 := by
      rw [Real.sqrt_le_iff]
      constructor
      · positivity
      · nlinarith [sq_nonneg (‖K‖ - 2)]
    rw [← Real.sqrt_eq_rpow]
    calc
      (2 / ‖K‖ ^ 2) * √‖K‖ ≤
          (2 / ‖K‖ ^ 2) * (‖K‖ / 2) := by gcongr
      _ = 1 / ‖K‖ := by field_simp
  calc
    (∫ r : ℝ in Icc (-ρ) ρ,
        ‖∑' n : ℕ, higherThetaMode n s (L + r)‖) ≤
        (2 / ‖K‖ ^ 2) * ‖leadingIntegrand s L‖ := by
      simpa only [L, K, ρ] using
        quantitativeSaddleBranch_central_higherTheta_norm_integral_le hs
    _ ≤ (2 / ‖K‖ ^ 2) *
        (‖K‖ ^ (1 / 2 : ℝ) * ‖G‖) := by gcongr
    _ = ((2 / ‖K‖ ^ 2) * ‖K‖ ^ (1 / 2 : ℝ)) * ‖G‖ := by ring
    _ ≤ (1 / ‖K‖) * ‖G‖ := by gcongr
    _ = _ := by simp only [L, K, M, G]

theorem higherThetaTopRay_eq_centered
    (s L : ℂ) :
    higherThetaTopRay s L.im =
      ∫ r : ℝ in Ioi (1 - L.re),
        ∑' n : ℕ, higherThetaMode n s (L + r) := by
  let top : ℝ → ℂ := fun x =>
    ∑' n : ℕ, higherThetaMode n s (x + L.im * I)
  let F : ℝ → ℂ := fun x => (Ioi (1 : ℝ)).indicator top x
  have hshift := integral_add_right_eq_self (μ := volume) F L.re
  unfold higherThetaTopRay
  rw [← MeasureTheory.integral_indicator measurableSet_Ioi]
  change (∫ x : ℝ, F x) = _
  calc
    (∫ x : ℝ, F x) = ∫ r : ℝ, F (r + L.re) := hshift.symm
    _ = ∫ r : ℝ,
        (Ioi (1 - L.re)).indicator
          (fun r : ℝ => ∑' n : ℕ, higherThetaMode n s (L + r)) r := by
      apply integral_congr_ae
      filter_upwards with r
      by_cases hr : r ∈ Ioi (1 - L.re)
      · have hr' : r + L.re ∈ Ioi (1 : ℝ) := by
          simp only [mem_Ioi] at hr ⊢
          linarith
        simp only [F, top, indicator_of_mem hr, indicator_of_mem hr']
        congr 1
        funext n
        congr 1
        apply Complex.ext <;> simp <;> ring
      · have hr' : r + L.re ∉ Ioi (1 : ℝ) := by
          simp only [mem_Ioi] at hr ⊢
          linarith
        simp [F, hr, hr']
    _ = ∫ r : ℝ in Ioi (1 - L.re),
        ∑' n : ℕ, higherThetaMode n s (L + r) :=
      MeasureTheory.integral_indicator measurableSet_Ioi

theorem quantitativeSaddleBranch_centeredHigherThetaRay_integral_split
    {s : ℂ} (hs : s ∈ leanSaddleSector) :
    let L := quantitativeSaddleBranch s
    let K := leadingCurvature s L
    let ρ := leadingCentralRadius K
    (∫ r : ℝ in Ioi (1 - L.re),
      ∑' n : ℕ, higherThetaMode n s (L + r)) =
      (∫ r : ℝ in Icc (1 - L.re) (-ρ),
        ∑' n : ℕ, higherThetaMode n s (L + r)) +
      (∫ r : ℝ in Icc (-ρ) ρ,
        ∑' n : ℕ, higherThetaMode n s (L + r)) +
      (∫ r : ℝ in Ioi ρ,
        ∑' n : ℕ, higherThetaMode n s (L + r)) := by
  dsimp only
  let L : ℂ := quantitativeSaddleBranch s
  let K : ℂ := leadingCurvature s L
  let ρ : ℝ := leadingCentralRadius K
  let a : ℝ := 1 - L.re
  let f : ℝ → ℂ := fun r =>
    ∑' n : ℕ, higherThetaMode n s (L + r)
  have hLre : 1000 < L.re := by
    simpa only [L] using quantitativeSaddleBranch_re_gt hs
  have hρpos : 0 < ρ := by
    simpa only [L, K, ρ] using
      quantitativeSaddleBranch_centralRadius_pos hs
  have hρle : ρ ≤ 1 / 10 := by
    simpa only [L, K, ρ] using
      quantitativeSaddleBranch_centralRadius_le_tenth hs
  have haNeg : a ≤ -ρ := by dsimp [a]; linarith
  have hnegPos : -ρ ≤ ρ := by linarith
  have haRho : a ≤ ρ := haNeg.trans hnegPos
  have hfull : IntegrableOn f (Ioi a) := by
    simpa only [L, a, f] using
      integrableOn_quantitativeSaddleBranch_centeredHigherThetaRay hs
  have hA : IntegrableOn f (Ioc a (-ρ)) :=
    hfull.mono_set (fun r hr => hr.1)
  have hB : IntegrableOn f (Ioc (-ρ) ρ) :=
    hfull.mono_set (fun r hr => haNeg.trans_lt hr.1)
  have hAB : IntegrableOn f (Ioc a ρ) :=
    hfull.mono_set (fun r hr => hr.1)
  have hC : IntegrableOn f (Ioi ρ) :=
    hfull.mono_set (Ioi_subset_Ioi haRho)
  have hsplitAB := setIntegral_union
    (Ioc_disjoint_Ioc_of_le (a := a) (d := ρ) (le_refl (-ρ)))
    measurableSet_Ioc hA hB
  rw [Ioc_union_Ioc_eq_Ioc haNeg hnegPos] at hsplitAB
  have hsplitC := setIntegral_union Ioc_disjoint_Ioi_same
    measurableSet_Ioi hAB hC
  rw [Ioc_union_Ioi_eq_Ioi haRho] at hsplitC
  have hAclosed : (∫ r : ℝ in Ioc a (-ρ), f r) =
      ∫ r : ℝ in Icc a (-ρ), f r :=
    setIntegral_congr_set Ioc_ae_eq_Icc
  have hBclosed : (∫ r : ℝ in Ioc (-ρ) ρ, f r) =
      ∫ r : ℝ in Icc (-ρ) ρ, f r :=
    setIntegral_congr_set Ioc_ae_eq_Icc
  calc
    (∫ r : ℝ in Ioi a, f r) =
        (∫ r : ℝ in Ioc a ρ, f r) +
          ∫ r : ℝ in Ioi ρ, f r := hsplitC
    _ = ((∫ r : ℝ in Ioc a (-ρ), f r) +
          ∫ r : ℝ in Ioc (-ρ) ρ, f r) +
          ∫ r : ℝ in Ioi ρ, f r := by rw [hsplitAB]
    _ = (∫ r : ℝ in Icc a (-ρ), f r) +
        (∫ r : ℝ in Icc (-ρ) ρ, f r) +
        (∫ r : ℝ in Ioi ρ, f r) := by rw [hAclosed, hBclosed]
    _ = _ := by simp only [L, K, ρ, a, f]

theorem quantitativeSaddleBranch_higherThetaTopRay_relative_le
    {s : ℂ} (hs : s ∈ leanSaddleSector) :
    let L := quantitativeSaddleBranch s
    let K := leadingCurvature s L
    let M := ∫ r : ℝ, leadingGaussian K r
    ‖higherThetaTopRay s L.im‖ ≤
      ((1 + 2 * 20 ^ 15 * (Nat.factorial 15 : ℝ)) / ‖K‖) *
        ‖leadingIntegrand s L * M‖ := by
  dsimp only
  let L : ℂ := quantitativeSaddleBranch s
  let K : ℂ := leadingCurvature s L
  let ρ : ℝ := leadingCentralRadius K
  let f : ℝ → ℂ := fun r =>
    ∑' n : ℕ, higherThetaMode n s (L + r)
  let g : ℝ → ℂ := fun r => leadingIntegrand s (L + r)
  let A : ℂ := ∫ r : ℝ in Icc (1 - L.re) (-ρ), f r
  let B : ℂ := ∫ r : ℝ in Icc (-ρ) ρ, f r
  let C : ℂ := ∫ r : ℝ in Ioi ρ, f r
  let M : ℂ := ∫ r : ℝ, leadingGaussian K r
  let G : ℂ := leadingIntegrand s L * M
  let T : ℝ := 2 * 20 ^ 15 * (Nat.factorial 15 : ℝ)
  have hLre : 1000 < L.re := by
    simpa only [L] using quantitativeSaddleBranch_re_gt hs
  have hρpos : 0 < ρ := by
    simpa only [L, K, ρ] using
      quantitativeSaddleBranch_centralRadius_pos hs
  have hρle : ρ ≤ 1 / 10 := by
    simpa only [L, K, ρ] using
      quantitativeSaddleBranch_centralRadius_le_tenth hs
  have hb : |L.im| ≤ 1 / 20 := by
    simpa only [L] using (quantitativeSaddleBranch_im_abs_lt hs).le
  have hsplit : higherThetaTopRay s L.im = A + B + C := by
    rw [higherThetaTopRay_eq_centered]
    simpa only [L, K, ρ, f, A, B, C] using
      quantitativeSaddleBranch_centeredHigherThetaRay_integral_split hs
  have hfullF : IntegrableOn f (Ioi (1 - L.re)) := by
    simpa only [L, f] using
      integrableOn_quantitativeSaddleBranch_centeredHigherThetaRay hs
  have hfullG : IntegrableOn g (Ioi (1 - L.re)) := by
    simpa only [L, g] using
      integrableOn_quantitativeSaddleBranch_centeredRay hs
  have hrightSub : Ioi ρ ⊆ Ioi (1 - L.re) := by
    intro r hr
    simp only [mem_Ioi] at hr ⊢
    linarith
  have hfA : IntegrableOn f (Icc (1 - L.re) (-ρ)) := by
    have hIoc : IntegrableOn f (Ioc (1 - L.re) (-ρ)) := by
      apply hfullF.mono_set
      intro r hr
      exact hr.1
    exact hIoc.congr_set_ae Ioc_ae_eq_Icc.symm
  have hgA : IntegrableOn g (Icc (1 - L.re) (-ρ)) := by
    have hIoc : IntegrableOn g (Ioc (1 - L.re) (-ρ)) := by
      apply hfullG.mono_set
      intro r hr
      exact hr.1
    exact hIoc.congr_set_ae Ioc_ae_eq_Icc.symm
  have hfC : IntegrableOn f (Ioi ρ) := hfullF.mono_set hrightSub
  have hgC : IntegrableOn g (Ioi ρ) := hfullG.mono_set hrightSub
  have hpoint (r : ℝ) (hr : 1 - L.re ≤ r) : ‖f r‖ ≤ ‖g r‖ := by
    have hx : 1 ≤ L.re + r := by linarith
    have h := higherThetaHorizontalSum_norm_le_leading
      (s := s) hb hx
    have hu : ((L.re + r : ℝ) : ℂ) + L.im * I = L + r := by
      apply Complex.ext <;> simp
    rw [hu] at h
    simpa only [f, g] using h
  have htailNorms :
      (∫ r : ℝ in Icc (1 - L.re) (-ρ), ‖f r‖) +
          (∫ r : ℝ in Ioi ρ, ‖f r‖) ≤
        (∫ r : ℝ in Icc (1 - L.re) (-ρ), ‖g r‖) +
          (∫ r : ℝ in Ioi ρ, ‖g r‖) := by
    apply add_le_add
    · apply integral_mono_ae hfA.norm hgA.norm
      filter_upwards [ae_restrict_mem measurableSet_Icc] with r hr
      exact hpoint r hr.1
    · apply integral_mono_ae hfC.norm hgC.norm
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with r hr
      exact hpoint r ((by linarith : 1 - L.re ≤ ρ).trans hr.le)
  have htails :
      (∫ r : ℝ in Icc (1 - L.re) (-ρ), ‖g r‖) +
          (∫ r : ℝ in Ioi ρ, ‖g r‖) ≤
        (T / ‖K‖) * ‖G‖ := by
    simpa only [L, K, ρ, g, M, G, T] using
      quantitativeSaddleBranch_horizontal_tail_relative_inverse_curvature hs
  have hcentralNorm : ‖B‖ ≤ (1 / ‖K‖) * ‖G‖ := by
    calc
      ‖B‖ ≤ ∫ r : ℝ in Icc (-ρ) ρ, ‖f r‖ := by
        dsimp only [B]
        exact norm_integral_le_integral_norm f
      _ ≤ (1 / ‖K‖) * ‖G‖ := by
        simpa only [L, K, ρ, f, M, G] using
          quantitativeSaddleBranch_central_higherTheta_norm_integral_relative_le hs
  have hnormA : ‖A‖ ≤
      ∫ r : ℝ in Icc (1 - L.re) (-ρ), ‖f r‖ := by
    dsimp only [A]
    exact norm_integral_le_integral_norm f
  have hnormC : ‖C‖ ≤ ∫ r : ℝ in Ioi ρ, ‖f r‖ := by
    dsimp only [C]
    exact norm_integral_le_integral_norm f
  rw [hsplit]
  calc
    ‖A + B + C‖ ≤ ‖A‖ + ‖B‖ + ‖C‖ := by
      calc
        ‖A + B + C‖ ≤ ‖A + B‖ + ‖C‖ := norm_add_le _ _
        _ ≤ (‖A‖ + ‖B‖) + ‖C‖ :=
          add_le_add (norm_add_le _ _) (le_refl _)
    _ ≤ (∫ r : ℝ in Icc (1 - L.re) (-ρ), ‖f r‖) +
          ((1 / ‖K‖) * ‖G‖) +
          (∫ r : ℝ in Ioi ρ, ‖f r‖) := by gcongr
    _ = ((1 / ‖K‖) * ‖G‖) +
          ((∫ r : ℝ in Icc (1 - L.re) (-ρ), ‖f r‖) +
            ∫ r : ℝ in Ioi ρ, ‖f r‖) := by ring
    _ ≤ ((1 / ‖K‖) * ‖G‖) +
          ((∫ r : ℝ in Icc (1 - L.re) (-ρ), ‖g r‖) +
            ∫ r : ℝ in Ioi ρ, ‖g r‖) := by gcongr
    _ ≤ ((1 / ‖K‖) * ‖G‖) + (T / ‖K‖) * ‖G‖ := by gcongr
    _ = ((1 + T) / ‖K‖) * ‖G‖ := by ring
    _ = _ := by simp only [L, K, M, G, T]

/-- The complete infinite theta sum on the legal shifted ray has the exact
complex Gaussian leading-mode main term with an explicit relative error. -/
theorem quantitativeSaddleBranch_fullThetaTopRay_relative_error_le
    {s : ℂ} (hs : s ∈ leanSaddleSector) :
    let L := quantitativeSaddleBranch s
    let K := leadingCurvature s L
    let M := ∫ r : ℝ, leadingGaussian K r
    ‖fullThetaTopRay s L.im - leadingIntegrand s L * M‖ ≤
      ((71000001 + 2 * (2 * 20 ^ 15 * (Nat.factorial 15 : ℝ))) / ‖K‖) *
        ‖leadingIntegrand s L * M‖ := by
  dsimp only
  let L : ℂ := quantitativeSaddleBranch s
  let K : ℂ := leadingCurvature s L
  let M : ℂ := ∫ r : ℝ, leadingGaussian K r
  let G : ℂ := leadingIntegrand s L * M
  let T : ℝ := 2 * 20 ^ 15 * (Nat.factorial 15 : ℝ)
  have hb : |L.im| ≤ 1 / 20 := by
    simpa only [L] using (quantitativeSaddleBranch_im_abs_lt hs).le
  have hfull : fullThetaTopRay s L.im =
      leadingTopRay s L.im + higherThetaTopRay s L.im :=
    fullThetaTopRay_eq_leading_add_higher s hb
  have hlead : ‖leadingTopRay s L.im - G‖ ≤
      ((71000000 + T) / ‖K‖) * ‖G‖ := by
    simpa only [L, K, M, G, T] using
      quantitativeSaddleBranch_leadingTopRay_relative_error_le hs
  have hhigh : ‖higherThetaTopRay s L.im‖ ≤
      ((1 + T) / ‖K‖) * ‖G‖ := by
    simpa only [L, K, M, G, T] using
      quantitativeSaddleBranch_higherThetaTopRay_relative_le hs
  rw [hfull]
  have halgebra :
      leadingTopRay s L.im + higherThetaTopRay s L.im - G =
        (leadingTopRay s L.im - G) + higherThetaTopRay s L.im := by ring
  rw [halgebra]
  calc
    ‖(leadingTopRay s L.im - G) + higherThetaTopRay s L.im‖ ≤
        ‖leadingTopRay s L.im - G‖ + ‖higherThetaTopRay s L.im‖ :=
      norm_add_le _ _
    _ ≤ ((71000000 + T) / ‖K‖) * ‖G‖ +
        ((1 + T) / ‖K‖) * ‖G‖ := by gcongr
    _ = ((71000001 + 2 * T) / ‖K‖) * ‖G‖ := by ring
    _ = _ := by simp only [L, K, M, G, T]

end

end Zeta23.Research.JensenWedge
