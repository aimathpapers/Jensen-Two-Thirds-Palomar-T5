import Zeta23.Research.JensenWedge.HigherThetaSuppression

/-!
# Legal all-mode contour deformation

Every higher theta mode is deformed through its own finite branch-safe
rectangle.  Absolute geometric majorants justify the infinite horizontal
and connector sums, after which the modewise identities assemble to the
complete higher-mode and full-theta infinite rectangles.  The finite
left connector is normalized by the exact Gaussian main term, yielding the
original-ray T4 estimate on `(1, infinity)`.
-/

namespace Zeta23.Research.JensenWedge

open Complex Filter Function MeasureTheory Set Topology

noncomputable section

theorem higherThetaMode_differentiableOn_domain
    (n : ℕ) (s : ℂ) :
    DifferentiableOn ℂ (higherThetaMode n s) leadingLogDomain := by
  unfold higherThetaMode higherThetaComplexFactor
  apply (leadingIntegrand_differentiableOn_domain s).mul
  fun_prop

def higherThetaModeBottomSegment (n : ℕ) (s : ℂ) (X : ℝ) : ℂ :=
  ∫ x : ℝ in 1..X, higherThetaMode n s x

def higherThetaModeTopSegment
    (n : ℕ) (s : ℂ) (b X : ℝ) : ℂ :=
  ∫ x : ℝ in 1..X, higherThetaMode n s (x + b * I)

def higherThetaModeRightSegment
    (n : ℕ) (s : ℂ) (b X : ℝ) : ℂ :=
  I * ∫ y : ℝ in 0..b, higherThetaMode n s (X + y * I)

def higherThetaModeLeftSegment
    (n : ℕ) (s : ℂ) (b : ℝ) : ℂ :=
  I * ∫ y : ℝ in 0..b, higherThetaMode n s (1 + y * I)

theorem higherThetaMode_finite_rectangle_identity
    (n : ℕ) (s : ℂ) {b X : ℝ} (hX : 1 ≤ X) :
    higherThetaModeBottomSegment n s X -
        higherThetaModeTopSegment n s b X +
        higherThetaModeRightSegment n s b X -
        higherThetaModeLeftSegment n s b = 0 := by
  have hdiff : DifferentiableOn ℂ (higherThetaMode n s)
      (Set.uIcc ((1 : ℂ).re) (X + b * I : ℂ).re ×ℂ
        Set.uIcc ((1 : ℂ).im) (X + b * I : ℂ).im) :=
    (higherThetaMode_differentiableOn_domain n s).mono
      (leadingRectangle_subset_domain hX)
  have hboundary := Complex.integral_boundary_rect_eq_zero_of_differentiableOn
    (higherThetaMode n s) (1 : ℂ) (X + b * I) hdiff
  simpa [higherThetaModeBottomSegment, higherThetaModeTopSegment,
    higherThetaModeRightSegment, higherThetaModeLeftSegment,
    smul_eq_mul] using hboundary

theorem higherThetaModeBottomSegment_eq_top_sub_right_add_left
    (n : ℕ) (s : ℂ) {b X : ℝ} (hX : 1 ≤ X) :
    higherThetaModeBottomSegment n s X =
      higherThetaModeTopSegment n s b X -
      higherThetaModeRightSegment n s b X +
      higherThetaModeLeftSegment n s b := by
  have h := higherThetaMode_finite_rectangle_identity n s (b := b) hX
  linear_combination h

theorem norm_higherThetaMode_right_le_exp_neg
    (n : ℕ) (s : ℂ) {X y : ℝ}
    (hX : 2 * (5 * ‖s‖ + 1) + 2 ≤ X)
    (hy : |y| ≤ 1 / 20) :
    ‖higherThetaMode n s (X + y * I)‖ ≤ Real.exp (-X) := by
  have hXone : 1 ≤ X := by
    have hsnonneg : 0 ≤ ‖s‖ := norm_nonneg s
    linarith
  have hmode := higherThetaMode_horizontal_geometric_bound
    (s := s) hy n hXone
  have hlead := norm_leadingIntegrand_right_le_exp_neg s hX hy
  have hfactor : (Real.exp (-3)) ^ (n + 1) ≤ 1 := by
    have hbase : Real.exp (-3) ≤ 1 := by
      rw [Real.exp_le_one_iff]
      norm_num
    exact pow_le_one₀ (Real.exp_nonneg _) hbase
  calc
    ‖higherThetaMode n s (X + y * I)‖ ≤
        (Real.exp (-3)) ^ (n + 1) *
          ‖leadingIntegrand s (X + y * I)‖ := hmode
    _ ≤ 1 * ‖leadingIntegrand s (X + y * I)‖ := by gcongr
    _ ≤ Real.exp (-X) := by simpa using hlead

theorem norm_higherThetaModeRightSegment_le
    (n : ℕ) (s : ℂ) {b X : ℝ} (hb : |b| ≤ 1 / 20)
    (hX : 2 * (5 * ‖s‖ + 1) + 2 ≤ X) :
    ‖higherThetaModeRightSegment n s b X‖ ≤
      Real.exp (-X) * |b| := by
  unfold higherThetaModeRightSegment
  rw [norm_mul, norm_I, one_mul]
  calc
    ‖∫ y : ℝ in 0..b, higherThetaMode n s (X + y * I)‖ ≤
        Real.exp (-X) * |b - 0| :=
      intervalIntegral.norm_integral_le_of_norm_le_const
        (C := Real.exp (-X)) (fun y hy => by
          have hyabs : |y| ≤ |b| := by
            simpa using abs_sub_left_of_mem_uIcc (uIoc_subset_uIcc hy)
          exact norm_higherThetaMode_right_le_exp_neg n s hX
            (hyabs.trans hb))
    _ = Real.exp (-X) * |b| := by rw [sub_zero]

theorem tendsto_higherThetaModeRightSegment_zero
    (n : ℕ) (s : ℂ) {b : ℝ} (hb : |b| ≤ 1 / 20) :
    Tendsto (fun X : ℝ => higherThetaModeRightSegment n s b X)
      atTop (𝓝 0) := by
  rw [tendsto_zero_iff_norm_tendsto_zero]
  have hbound : ∀ᶠ X : ℝ in atTop,
      ‖higherThetaModeRightSegment n s b X‖ ≤
        Real.exp (-X) * |b| := by
    filter_upwards [eventually_ge_atTop
      (2 * (5 * ‖s‖ + 1) + 2)] with X hX
    exact norm_higherThetaModeRightSegment_le n s hb hX
  have hexp : Tendsto (fun X : ℝ => Real.exp (-X)) atTop (𝓝 0) :=
    Real.tendsto_exp_atBot.comp tendsto_neg_atTop_atBot
  have hupper : Tendsto (fun X : ℝ => Real.exp (-X) * |b|)
      atTop (𝓝 0) := by
    simpa using hexp.mul_const |b|
  exact squeeze_zero' (Eventually.of_forall fun X => norm_nonneg _) hbound hupper

def higherThetaModeBottomRay (n : ℕ) (s : ℂ) : ℂ :=
  ∫ x : ℝ in Ioi 1, higherThetaMode n s x

def higherThetaModeTopRay (n : ℕ) (s : ℂ) (b : ℝ) : ℂ :=
  ∫ x : ℝ in Ioi 1, higherThetaMode n s (x + b * I)

theorem tendsto_higherThetaModeBottomSegment_ray
    (n : ℕ) (s : ℂ) :
    Tendsto (higherThetaModeBottomSegment n s) atTop
      (𝓝 (higherThetaModeBottomRay n s)) := by
  change Tendsto (fun X : ℝ =>
    ∫ x : ℝ in 1..X, higherThetaMode n s x) atTop
      (𝓝 (∫ x : ℝ in Ioi 1, higherThetaMode n s x))
  have hint := integrableOn_higherThetaHorizontalMode n s
    (b := 0) (by norm_num)
  exact intervalIntegral_tendsto_integral_Ioi 1
    (by simpa using hint) tendsto_id

theorem tendsto_higherThetaModeTopSegment_ray
    (n : ℕ) (s : ℂ) {b : ℝ} (hb : |b| ≤ 1 / 20) :
    Tendsto (higherThetaModeTopSegment n s b) atTop
      (𝓝 (higherThetaModeTopRay n s b)) := by
  change Tendsto (fun X : ℝ =>
    ∫ x : ℝ in 1..X, higherThetaMode n s (x + b * I)) atTop
      (𝓝 (∫ x : ℝ in Ioi 1, higherThetaMode n s (x + b * I)))
  exact intervalIntegral_tendsto_integral_Ioi 1
    (integrableOn_higherThetaHorizontalMode n s hb) tendsto_id

theorem higherThetaMode_infinite_rectangle_identity
    (n : ℕ) (s : ℂ) {b : ℝ} (hb : |b| ≤ 1 / 20) :
    higherThetaModeBottomRay n s =
      higherThetaModeTopRay n s b +
        higherThetaModeLeftSegment n s b := by
  have hfinite : ∀ᶠ X : ℝ in atTop,
      higherThetaModeBottomSegment n s X =
        higherThetaModeTopSegment n s b X -
          higherThetaModeRightSegment n s b X +
            higherThetaModeLeftSegment n s b := by
    filter_upwards [eventually_ge_atTop (1 : ℝ)] with X hX
    exact higherThetaModeBottomSegment_eq_top_sub_right_add_left
      n s hX
  have hbottom := tendsto_higherThetaModeBottomSegment_ray n s
  have htop := tendsto_higherThetaModeTopSegment_ray n s hb
  have hright := tendsto_higherThetaModeRightSegment_zero n s hb
  have hrhs : Tendsto
      (fun X : ℝ => higherThetaModeTopSegment n s b X -
        higherThetaModeRightSegment n s b X +
          higherThetaModeLeftSegment n s b) atTop
      (𝓝 (higherThetaModeTopRay n s b - 0 +
        higherThetaModeLeftSegment n s b)) :=
    (htop.sub hright).add_const _
  have hreverse : ∀ᶠ X : ℝ in atTop,
      higherThetaModeTopSegment n s b X -
          higherThetaModeRightSegment n s b X +
            higherThetaModeLeftSegment n s b =
        higherThetaModeBottomSegment n s X :=
    hfinite.mono (fun _ h => h.symm)
  have heq := tendsto_nhds_unique hbottom (hrhs.congr' hreverse)
  simpa using heq

theorem continuous_higherThetaMode_connector
    (n : ℕ) (s : ℂ) :
    Continuous (fun y : ℝ => higherThetaMode n s (1 + y * I)) := by
  rw [← continuousOn_univ]
  exact (higherThetaMode_differentiableOn_domain n s).continuousOn.comp
    (by fun_prop) (by
      intro y hy
      norm_num [leadingLogDomain])

theorem higherThetaMode_connector_geometric_bound
    (n : ℕ) (s : ℂ) {y : ℝ} (hy : |y| ≤ 1 / 20) :
    ‖higherThetaMode n s (1 + y * I)‖ ≤
      (Real.exp (-3)) ^ (n + 1) * Real.exp (5 * ‖s‖ + 1) := by
  have hmode := higherThetaMode_horizontal_geometric_bound
    (s := s) hy n (by norm_num : (1 : ℝ) ≤ 1)
  have hlead : ‖leadingIntegrand s (1 + y * I)‖ ≤
      Real.exp (5 * ‖s‖ + 1) := by
    rw [leadingIntegrand_eq_exp_logIntegrand, Complex.norm_exp]
    exact Real.exp_le_exp.mpr (leadingConnectorPoint_phase_re_le s hy)
  exact hmode.trans (mul_le_mul_of_nonneg_left hlead (by positivity))

theorem hasSum_intervalIntegral_higherThetaMode_connector
    (s : ℂ) {b : ℝ} (hb : |b| ≤ 1 / 20) :
    HasSum
      (fun n : ℕ => ∫ y : ℝ in 0..b,
        higherThetaMode n s (1 + y * I))
      (∫ y : ℝ in 0..b,
        ∑' n : ℕ, higherThetaMode n s (1 + y * I)) := by
  let c : ℕ → ℝ := fun n => (Real.exp (-3)) ^ (n + 1)
  let C : ℝ := Real.exp (5 * ‖s‖ + 1)
  apply intervalIntegral.hasSum_integral_of_dominated_convergence
    (fun n _y => c n * C)
  · intro n
    exact (continuous_higherThetaMode_connector n s).aestronglyMeasurable
  · intro n
    filter_upwards with y hy
    have hyabs : |y| ≤ |b| := by
      simpa using abs_sub_left_of_mem_uIcc (uIoc_subset_uIcc hy)
    simpa only [c, C] using
      higherThetaMode_connector_geometric_bound n s (hyabs.trans hb)
  · filter_upwards with y hy
    have hr0 : 0 ≤ Real.exp (-3) := Real.exp_nonneg _
    have hr1 : Real.exp (-3) < 1 := by
      rw [Real.exp_lt_one_iff]
      norm_num
    exact ((summable_nat_add_iff 1).mpr
      (summable_geometric_of_lt_one hr0 hr1)).mul_right C
  · exact (continuous_const : Continuous
      (fun _ : ℝ => ∑' n : ℕ, c n * C)).intervalIntegrable 0 b
  · filter_upwards with y hy
    have hyabs : |y| ≤ |b| := by
      simpa using abs_sub_left_of_mem_uIcc (uIoc_subset_uIcc hy)
    have him : |((1 : ℂ) + y * I).im| ≤ 1 / 20 := by
      simpa using hyabs.trans hb
    have hq := thetaStrip_modeParameter_ge_one
      (u := (1 : ℂ) + y * I) (by norm_num) him
    exact (summable_higherThetaMode
      (lt_of_lt_of_le zero_lt_one hq)).hasSum

def higherThetaLeftSegment (s : ℂ) (b : ℝ) : ℂ :=
  I * ∫ y : ℝ in 0..b,
    ∑' n : ℕ, higherThetaMode n s (1 + y * I)

theorem higherThetaLeftSegment_eq_tsum_modeSegments
    (s : ℂ) {b : ℝ} (hb : |b| ≤ 1 / 20) :
    higherThetaLeftSegment s b =
      ∑' n : ℕ, higherThetaModeLeftSegment n s b := by
  unfold higherThetaLeftSegment higherThetaModeLeftSegment
  rw [tsum_mul_left]
  congr 1
  exact (hasSum_intervalIntegral_higherThetaMode_connector s hb).tsum_eq.symm

theorem summable_higherThetaModeTopRay
    (s : ℂ) {b : ℝ} (hb : |b| ≤ 1 / 20) :
    Summable (fun n : ℕ => higherThetaModeTopRay n s b) := by
  rw [← summable_norm_iff]
  apply Summable.of_nonneg_of_le
  · intro n
    exact norm_nonneg _
  · intro n
    exact norm_integral_le_integral_norm _
  · simpa only [higherThetaModeTopRay] using
      summable_integral_norm_higherThetaHorizontalMode s hb

theorem summable_higherThetaModeBottomRay (s : ℂ) :
    Summable (fun n : ℕ => higherThetaModeBottomRay n s) := by
  simpa [higherThetaModeBottomRay, higherThetaModeTopRay] using
    summable_higherThetaModeTopRay s (b := 0) (by norm_num)

theorem summable_higherThetaModeLeftSegment
    (s : ℂ) {b : ℝ} (hb : |b| ≤ 1 / 20) :
    Summable (fun n : ℕ => higherThetaModeLeftSegment n s b) := by
  have hsum :=
    (hasSum_intervalIntegral_higherThetaMode_connector s hb).summable
  simpa only [higherThetaModeLeftSegment] using hsum.mul_left I

theorem higherThetaTopRay_eq_tsum_modeTopRays
    (s : ℂ) {b : ℝ} (hb : |b| ≤ 1 / 20) :
    higherThetaTopRay s b =
      ∑' n : ℕ, higherThetaModeTopRay n s b := by
  simpa only [higherThetaModeTopRay] using
    higherThetaTopRay_eq_tsum_modeIntegrals s hb

theorem higherThetaBottomRay_eq_tsum_modeBottomRays (s : ℂ) :
    higherThetaTopRay s 0 =
      ∑' n : ℕ, higherThetaModeBottomRay n s := by
  simpa [higherThetaModeBottomRay, higherThetaModeTopRay] using
    higherThetaTopRay_eq_tsum_modeTopRays s (b := 0) (by norm_num)

theorem higherTheta_infinite_rectangle_identity
    (s : ℂ) {b : ℝ} (hb : |b| ≤ 1 / 20) :
    higherThetaTopRay s 0 =
      higherThetaTopRay s b + higherThetaLeftSegment s b := by
  have hbottom := summable_higherThetaModeBottomRay s
  have htop := summable_higherThetaModeTopRay s hb
  have hleft := summable_higherThetaModeLeftSegment s hb
  calc
    higherThetaTopRay s 0 =
        ∑' n : ℕ, higherThetaModeBottomRay n s :=
      higherThetaBottomRay_eq_tsum_modeBottomRays s
    _ = ∑' n : ℕ, (higherThetaModeTopRay n s b +
        higherThetaModeLeftSegment n s b) := by
      apply tsum_congr
      intro n
      exact higherThetaMode_infinite_rectangle_identity n s hb
    _ = (∑' n : ℕ, higherThetaModeTopRay n s b) +
        ∑' n : ℕ, higherThetaModeLeftSegment n s b :=
      htop.tsum_add hleft
    _ = higherThetaTopRay s b + higherThetaLeftSegment s b := by
      rw [← higherThetaTopRay_eq_tsum_modeTopRays s hb,
        ← higherThetaLeftSegment_eq_tsum_modeSegments s hb]

def fullThetaBottomRay (s : ℂ) : ℂ :=
  ∫ x : ℝ in Ioi 1, fullThetaContourIntegrand s x

def fullThetaLeftSegment (s : ℂ) (b : ℝ) : ℂ :=
  leadingLeftSegment s b + higherThetaLeftSegment s b

theorem fullThetaBottomRay_eq_topRay_zero (s : ℂ) :
    fullThetaBottomRay s = fullThetaTopRay s 0 := by
  unfold fullThetaBottomRay fullThetaTopRay
  apply integral_congr_ae
  filter_upwards with x
  congr 2
  apply Complex.ext <;> simp

theorem fullTheta_infinite_rectangle_identity
    (s : ℂ) {b : ℝ} (hb : |b| ≤ 1 / 20) :
    fullThetaBottomRay s =
      fullThetaTopRay s b + fullThetaLeftSegment s b := by
  have hlead : leadingBottomRay s =
      leadingTopRay s b + leadingLeftSegment s b :=
    leading_infinite_rectangle_identity s hb
  have hhigh : higherThetaTopRay s 0 =
      higherThetaTopRay s b + higherThetaLeftSegment s b :=
    higherTheta_infinite_rectangle_identity s hb
  rw [fullThetaBottomRay_eq_topRay_zero,
    fullThetaTopRay_eq_leading_add_higher s (b := 0) (by norm_num),
    fullThetaTopRay_eq_leading_add_higher s hb]
  have hzero : leadingTopRay s 0 = leadingBottomRay s := by
    unfold leadingTopRay leadingBottomRay
    apply integral_congr_ae
    filter_upwards with x
    congr 2
    apply Complex.ext <;> simp
  rw [hzero, hlead, hhigh]
  unfold fullThetaLeftSegment
  ring

theorem quantitativeSaddleBranch_higherThetaLeftSegment_norm_le
    {s : ℂ} (hs : s ∈ leanSaddleSector) :
    ‖higherThetaLeftSegment s (quantitativeSaddleBranch s).im‖ ≤
      Real.exp (6 * ‖s‖) := by
  let b : ℝ := (quantitativeSaddleBranch s).im
  have hb : |b| ≤ 1 / 20 :=
    (quantitativeSaddleBranch_im_abs_lt hs).le
  have hsone : 1 ≤ ‖s‖ := by
    have hcut : 1 < Real.exp leanSaddleCutoff := by
      rw [← Real.exp_zero]
      exact Real.exp_lt_exp.mpr (by norm_num [leanSaddleCutoff])
    exact (hcut.trans hs.1).le
  unfold higherThetaLeftSegment
  rw [norm_mul, norm_I, one_mul]
  calc
    ‖∫ y : ℝ in 0..b,
        ∑' n : ℕ, higherThetaMode n s (1 + y * I)‖ ≤
        Real.exp (5 * ‖s‖ + 1) * |b - 0| := by
      apply intervalIntegral.norm_integral_le_of_norm_le_const
      intro y hy
      have hyabs : |y| ≤ |b| := by
        simpa using abs_sub_left_of_mem_uIcc (uIoc_subset_uIcc hy)
      have hsum := higherThetaHorizontalSum_norm_le_leading
        (s := s) (x := 1) (hyabs.trans hb) (by norm_num)
      have hlead : ‖leadingIntegrand s (1 + y * I)‖ ≤
          Real.exp (5 * ‖s‖ + 1) := by
        rw [leadingIntegrand_eq_exp_logIntegrand, Complex.norm_exp]
        exact Real.exp_le_exp.mpr
          (leadingConnectorPoint_phase_re_le s (hyabs.trans hb))
      exact hsum.trans hlead
    _ ≤ Real.exp (5 * ‖s‖ + 1) * 1 := by
      rw [sub_zero]
      gcongr
      exact hb.trans (by norm_num)
    _ ≤ Real.exp (6 * ‖s‖) := by
      rw [mul_one]
      exact Real.exp_le_exp.mpr (by linarith)

theorem quantitativeSaddleBranch_connector_relative_inverse_curvature_of_norm_le
    {s C : ℂ} (hs : s ∈ leanSaddleSector)
    (hC : ‖C‖ ≤ Real.exp (6 * ‖s‖)) :
    let L := quantitativeSaddleBranch s
    let K := leadingCurvature s L
    let M := ∫ r : ℝ, leadingGaussian K r
    ‖C‖ ≤ (1 / ‖K‖) * ‖leadingIntegrand s L * M‖ := by
  dsimp only
  let L : ℂ := quantitativeSaddleBranch s
  let K : ℂ := leadingCurvature s L
  let M : ℂ := ∫ r : ℝ, leadingGaussian K r
  let g : ℂ := leadingIntegrand s L
  let Kabs : ℝ := ‖K‖
  let S : ℝ := ‖s‖
  have hKge : 4000 ≤ Kabs := by
    simpa only [L, K, Kabs] using
      quantitativeSaddleBranch_curvature_norm_ge_fourThousand hs
  have hKpos : 0 < Kabs := lt_of_lt_of_le (by norm_num) hKge
  have hC' : ‖C‖ ≤ Real.exp (6 * S) := by
    simpa only [S] using hC
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
  have hCKdiv : ‖C‖ * Kabs ≤ ‖g‖ / Kabs ^ (1 / 2 : ℝ) := by
    apply (le_div_iff₀ hqpos).2
    calc
      ‖C‖ * Kabs * Kabs ^ (1 / 2 : ℝ) =
          ‖C‖ * (Kabs * Kabs ^ (1 / 2 : ℝ)) := by ring
      _ = ‖C‖ * Kabs ^ (3 / 2 : ℝ) := by rw [hpowSplit]
      _ ≤ ‖g‖ := hgap
  have hCK : ‖C‖ * Kabs ≤ ‖g‖ * Kabs ^ (-(1 / 2 : ℝ)) := by
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
  simpa only [L, K, M, g, Kabs] using hfinal

theorem quantitativeSaddleBranch_higherThetaLeftSegment_relative_inverse_curvature
    {s : ℂ} (hs : s ∈ leanSaddleSector) :
    let L := quantitativeSaddleBranch s
    let K := leadingCurvature s L
    let M := ∫ r : ℝ, leadingGaussian K r
    ‖higherThetaLeftSegment s L.im‖ ≤
      (1 / ‖K‖) * ‖leadingIntegrand s L * M‖ := by
  exact quantitativeSaddleBranch_connector_relative_inverse_curvature_of_norm_le
    hs (quantitativeSaddleBranch_higherThetaLeftSegment_norm_le hs)

theorem quantitativeSaddleBranch_fullThetaLeftSegment_relative_inverse_curvature
    {s : ℂ} (hs : s ∈ leanSaddleSector) :
    let L := quantitativeSaddleBranch s
    let K := leadingCurvature s L
    let M := ∫ r : ℝ, leadingGaussian K r
    ‖fullThetaLeftSegment s L.im‖ ≤
      (2 / ‖K‖) * ‖leadingIntegrand s L * M‖ := by
  dsimp only
  let L : ℂ := quantitativeSaddleBranch s
  let K : ℂ := leadingCurvature s L
  let M : ℂ := ∫ r : ℝ, leadingGaussian K r
  let G : ℂ := leadingIntegrand s L * M
  have hlead : ‖leadingLeftSegment s L.im‖ ≤
      (1 / ‖K‖) * ‖G‖ := by
    simpa only [L, K, M, G] using
      quantitativeSaddleBranch_leftSegment_relative_inverse_curvature hs
  have hhigh : ‖higherThetaLeftSegment s L.im‖ ≤
      (1 / ‖K‖) * ‖G‖ := by
    simpa only [L, K, M, G] using
      quantitativeSaddleBranch_higherThetaLeftSegment_relative_inverse_curvature hs
  unfold fullThetaLeftSegment
  calc
    ‖leadingLeftSegment s L.im + higherThetaLeftSegment s L.im‖ ≤
        ‖leadingLeftSegment s L.im‖ +
          ‖higherThetaLeftSegment s L.im‖ := norm_add_le _ _
    _ ≤ (1 / ‖K‖) * ‖G‖ + (1 / ‖K‖) * ‖G‖ := by gcongr
    _ = (2 / ‖K‖) * ‖G‖ := by ring
    _ = _ := by simp only [L, K, M, G]

/-- The original all-mode Mellin ray has the exact leading complex Gaussian
main term with an explicit inverse-curvature relative error. -/
theorem quantitativeSaddleBranch_fullThetaBottomRay_relative_error_le
    {s : ℂ} (hs : s ∈ leanSaddleSector) :
    let L := quantitativeSaddleBranch s
    let K := leadingCurvature s L
    let M := ∫ r : ℝ, leadingGaussian K r
    ‖fullThetaBottomRay s - leadingIntegrand s L * M‖ ≤
      ((71000003 + 2 * (2 * 20 ^ 15 * (Nat.factorial 15 : ℝ))) / ‖K‖) *
        ‖leadingIntegrand s L * M‖ := by
  dsimp only
  let L : ℂ := quantitativeSaddleBranch s
  let K : ℂ := leadingCurvature s L
  let M : ℂ := ∫ r : ℝ, leadingGaussian K r
  let G : ℂ := leadingIntegrand s L * M
  let T : ℝ := 2 * 20 ^ 15 * (Nat.factorial 15 : ℝ)
  have hb : |L.im| ≤ 1 / 20 := by
    simpa only [L] using (quantitativeSaddleBranch_im_abs_lt hs).le
  have hrectangle : fullThetaBottomRay s =
      fullThetaTopRay s L.im + fullThetaLeftSegment s L.im :=
    fullTheta_infinite_rectangle_identity s hb
  have htop : ‖fullThetaTopRay s L.im - G‖ ≤
      ((71000001 + 2 * T) / ‖K‖) * ‖G‖ := by
    simpa only [L, K, M, G, T] using
      quantitativeSaddleBranch_fullThetaTopRay_relative_error_le hs
  have hconnector : ‖fullThetaLeftSegment s L.im‖ ≤
      (2 / ‖K‖) * ‖G‖ := by
    simpa only [L, K, M, G] using
      quantitativeSaddleBranch_fullThetaLeftSegment_relative_inverse_curvature hs
  rw [hrectangle]
  have halgebra :
      fullThetaTopRay s L.im + fullThetaLeftSegment s L.im - G =
        (fullThetaTopRay s L.im - G) +
          fullThetaLeftSegment s L.im := by ring
  rw [halgebra]
  calc
    ‖(fullThetaTopRay s L.im - G) +
        fullThetaLeftSegment s L.im‖ ≤
        ‖fullThetaTopRay s L.im - G‖ +
          ‖fullThetaLeftSegment s L.im‖ := norm_add_le _ _
    _ ≤ ((71000001 + 2 * T) / ‖K‖) * ‖G‖ +
        (2 / ‖K‖) * ‖G‖ := by gcongr
    _ = ((71000003 + 2 * T) / ‖K‖) * ‖G‖ := by ring
    _ = _ := by simp only [L, K, M, G, T]

end

end Zeta23.Research.JensenWedge
