import Zeta23.Research.JensenWedge.HigherThetaModes

/-!
# Infinite higher-mode contour integrals

This module proves measurability and integrability for every higher theta
mode on the legal horizontal ray, dominates their integral norms by a fixed
geometric series, and justifies exchanging the infinite sum with the contour
integral.  It then decomposes the full theta ray exactly into its leading and
higher-mode parts.
-/

namespace Zeta23.Research.JensenWedge

open Complex Filter Function MeasureTheory Set Topology

noncomputable section

theorem continuousOn_higherThetaHorizontalMode
    (n : ℕ) (s : ℂ) (b : ℝ) :
    ContinuousOn (fun x : ℝ => higherThetaMode n s (x + b * I)) (Ici 1) := by
  unfold higherThetaMode higherThetaComplexFactor
  apply (continuousOn_leadingHorizontalRay s b).mul
  fun_prop

theorem aestronglyMeasurable_higherThetaHorizontalMode
    (n : ℕ) (s : ℂ) (b : ℝ) :
    AEStronglyMeasurable
      (fun x : ℝ => higherThetaMode n s (x + b * I))
      (volume.restrict (Ioi 1)) := by
  exact (continuousOn_higherThetaHorizontalMode n s b).mono
    Ioi_subset_Ici_self |>.aestronglyMeasurable measurableSet_Ioi

theorem aestronglyMeasurable_higherThetaHorizontalSum
    (s : ℂ) (b : ℝ) :
    AEStronglyMeasurable
      (fun x : ℝ => ∑' n : ℕ, higherThetaMode n s (x + b * I))
      (volume.restrict (Ioi 1)) :=
  AEStronglyMeasurable.tsum fun n =>
    aestronglyMeasurable_higherThetaHorizontalMode n s b

theorem higherThetaMode_horizontal_geometric_bound
    {s : ℂ} {b : ℝ} (hb : |b| ≤ 1 / 20) (n : ℕ)
    {x : ℝ} (hx : 1 ≤ x) :
    ‖higherThetaMode n s (x + b * I)‖ ≤
      (Real.exp (-3)) ^ (n + 1) *
        ‖leadingIntegrand s (x + b * I)‖ := by
  let u : ℂ := x + b * I
  let q : ℝ := Real.pi * (exp u).re
  have huRe : u.re = x := by simp only [u, add_re, ofReal_re, mul_re,
    ofReal_im, I_re, I_im, mul_zero, zero_mul, sub_zero, add_zero]
  have huIm : u.im = b := by simp [u]
  have hq : 1 ≤ q := by
    apply thetaStrip_modeParameter_ge_one
    · simpa only [huRe] using hx
    · simpa only [huIm] using hb
  have hscalar := higherThetaScalarFactor_le_geometric
    (zero_le_one.trans hq) n
  have hbase : Real.exp (-3 * q) ≤ Real.exp (-3) := by
    apply Real.exp_monotone
    nlinarith
  have hpow : (Real.exp (-3 * q)) ^ (n + 1) ≤
      (Real.exp (-3)) ^ (n + 1) := by gcongr
  calc
    ‖higherThetaMode n s u‖ =
        ‖leadingIntegrand s u‖ * higherThetaScalarFactor q n := by
      rw [higherThetaMode, norm_mul, higherThetaComplexFactor_norm]
    _ ≤ ‖leadingIntegrand s u‖ * (Real.exp (-3 * q)) ^ (n + 1) := by
      gcongr
    _ ≤ ‖leadingIntegrand s u‖ * (Real.exp (-3)) ^ (n + 1) := by
      gcongr
    _ = (Real.exp (-3)) ^ (n + 1) *
        ‖leadingIntegrand s (x + b * I)‖ := by simp only [u]; ring

theorem integrableOn_higherThetaHorizontalMode
    (n : ℕ) (s : ℂ) {b : ℝ} (hb : |b| ≤ 1 / 20) :
    IntegrableOn (fun x : ℝ => higherThetaMode n s (x + b * I))
      (Ioi 1) := by
  let c : ℝ := (Real.exp (-3)) ^ (n + 1)
  have hlead := integrableOn_leadingHorizontalRay s hb
  have hmajor : IntegrableOn
      (fun x : ℝ => c * ‖leadingIntegrand s (x + b * I)‖) (Ioi 1) :=
    hlead.norm.const_mul c
  apply Integrable.mono' hmajor
    (aestronglyMeasurable_higherThetaHorizontalMode n s b)
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
  simpa only [c, Real.norm_eq_abs, abs_of_nonneg (by positivity : 0 ≤ c),
    norm_mul, norm_norm] using
      higherThetaMode_horizontal_geometric_bound hb n hx.le

theorem integral_norm_higherThetaHorizontalMode_le
    (n : ℕ) (s : ℂ) {b : ℝ} (hb : |b| ≤ 1 / 20) :
    (∫ x : ℝ in Ioi 1, ‖higherThetaMode n s (x + b * I)‖) ≤
      (Real.exp (-3)) ^ (n + 1) *
        ∫ x : ℝ in Ioi 1, ‖leadingIntegrand s (x + b * I)‖ := by
  let c : ℝ := (Real.exp (-3)) ^ (n + 1)
  have hmode := integrableOn_higherThetaHorizontalMode n s hb
  have hlead := integrableOn_leadingHorizontalRay s hb
  calc
    (∫ x : ℝ in Ioi 1, ‖higherThetaMode n s (x + b * I)‖) ≤
        ∫ x : ℝ in Ioi 1, c * ‖leadingIntegrand s (x + b * I)‖ := by
      apply integral_mono_ae hmode.norm (hlead.norm.const_mul c)
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
      exact higherThetaMode_horizontal_geometric_bound hb n hx.le
    _ = c * ∫ x : ℝ in Ioi 1, ‖leadingIntegrand s (x + b * I)‖ := by
      rw [integral_const_mul]
    _ = _ := by simp only [c]

theorem summable_integral_norm_higherThetaHorizontalMode
    (s : ℂ) {b : ℝ} (hb : |b| ≤ 1 / 20) :
    Summable (fun n : ℕ =>
      ∫ x : ℝ in Ioi 1, ‖higherThetaMode n s (x + b * I)‖) := by
  let A : ℝ := ∫ x : ℝ in Ioi 1, ‖leadingIntegrand s (x + b * I)‖
  have hr0 : 0 ≤ Real.exp (-3) := (Real.exp_pos _).le
  have hr1 : Real.exp (-3) < 1 := by rw [Real.exp_lt_one_iff]; norm_num
  have hgeo : Summable (fun n : ℕ => (Real.exp (-3)) ^ (n + 1) * A) :=
    ((summable_nat_add_iff 1).mpr (summable_geometric_of_lt_one hr0 hr1)).mul_right A
  apply Summable.of_nonneg_of_le
  · intro n
    exact integral_nonneg_of_ae (Filter.Eventually.of_forall fun _ => norm_nonneg _)
  · intro n
    simpa only [A] using integral_norm_higherThetaHorizontalMode_le n s hb
  · exact hgeo

theorem integral_tsum_higherThetaHorizontalMode
    (s : ℂ) {b : ℝ} (hb : |b| ≤ 1 / 20) :
    (∫ x : ℝ in Ioi 1,
      ∑' n : ℕ, higherThetaMode n s (x + b * I)) =
      ∑' n : ℕ, ∫ x : ℝ in Ioi 1,
        higherThetaMode n s (x + b * I) := by
  symm
  apply integral_tsum_of_summable_integral_norm
  · intro n
    exact integrableOn_higherThetaHorizontalMode n s hb
  · exact summable_integral_norm_higherThetaHorizontalMode s hb

def higherThetaTopRay (s : ℂ) (b : ℝ) : ℂ :=
  ∫ x : ℝ in Ioi 1, ∑' n : ℕ, higherThetaMode n s (x + b * I)

def fullThetaTopRay (s : ℂ) (b : ℝ) : ℂ :=
  ∫ x : ℝ in Ioi 1, fullThetaContourIntegrand s (x + b * I)

theorem higherThetaHorizontalSum_norm_le_leading
    {s : ℂ} {b : ℝ} (hb : |b| ≤ 1 / 20)
    {x : ℝ} (hx : 1 ≤ x) :
    ‖∑' n : ℕ, higherThetaMode n s (x + b * I)‖ ≤
      ‖leadingIntegrand s (x + b * I)‖ := by
  let u : ℂ := x + b * I
  have huRe : u.re = x := by simp [u]
  have huIm : u.im = b := by simp [u]
  have hq : 1 ≤ Real.pi * (exp u).re := by
    apply thetaStrip_modeParameter_ge_one
    · simpa only [huRe] using hx
    · simpa only [huIm] using hb
  have hhalf := exp_neg_three_mul_le_half hq
  calc
    ‖∑' n : ℕ, higherThetaMode n s (x + b * I)‖ ≤
        2 * ‖leadingIntegrand s u‖ *
          Real.exp (-3 * (Real.pi * (exp u).re)) :=
      higherThetaMode_tsum_norm_le hq
    _ = ‖leadingIntegrand s u‖ *
        (2 * Real.exp (-3 * (Real.pi * (exp u).re))) := by ring
    _ ≤ ‖leadingIntegrand s u‖ * 1 := by
      gcongr
      linarith
    _ = ‖leadingIntegrand s (x + b * I)‖ := by simp only [u, mul_one]

theorem integrableOn_higherThetaHorizontalSum
    (s : ℂ) {b : ℝ} (hb : |b| ≤ 1 / 20) :
    IntegrableOn
      (fun x : ℝ => ∑' n : ℕ, higherThetaMode n s (x + b * I))
      (Ioi 1) := by
  have hlead := integrableOn_leadingHorizontalRay s hb
  apply Integrable.mono' hlead.norm
    (aestronglyMeasurable_higherThetaHorizontalSum s b)
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
  simpa only [norm_norm] using
    higherThetaHorizontalSum_norm_le_leading hb hx.le

theorem fullThetaTopRay_eq_leading_add_higher
    (s : ℂ) {b : ℝ} (hb : |b| ≤ 1 / 20) :
    fullThetaTopRay s b = leadingTopRay s b + higherThetaTopRay s b := by
  unfold fullThetaTopRay leadingTopRay higherThetaTopRay
    fullThetaContourIntegrand
  exact integral_add (integrableOn_leadingHorizontalRay s hb)
    (integrableOn_higherThetaHorizontalSum s hb)

theorem higherThetaTopRay_eq_tsum_modeIntegrals
    (s : ℂ) {b : ℝ} (hb : |b| ≤ 1 / 20) :
    higherThetaTopRay s b =
      ∑' n : ℕ, ∫ x : ℝ in Ioi 1,
        higherThetaMode n s (x + b * I) := by
  unfold higherThetaTopRay
  exact integral_tsum_higherThetaHorizontalMode s hb

end

end Zeta23.Research.JensenWedge
