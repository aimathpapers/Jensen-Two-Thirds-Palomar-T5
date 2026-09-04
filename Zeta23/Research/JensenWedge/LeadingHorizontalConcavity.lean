import Zeta23.Research.JensenWedge.LeadingLocalExpansion
import Mathlib.Analysis.Convex.Deriv

/-!
# Horizontal-ray concavity for the leading saddle

This module begins the noncentral part of T3.  It converts the angular sector
into explicit real/imaginary component bounds, proves positivity of the
rational and exponential pieces of the horizontal curvature for every point
with real part at least one, and concludes strict concavity of the real phase
on the legal translated ray.

The selected contour is parametrized by `L + r`, with `r` real.  No vertical
`L + I * r` surrogate occurs in these statements.
-/

namespace Zeta23.Research.JensenWedge

open Complex Filter Set Topology

noncomputable section

/-- The fixed sector makes the real component of the parameter at least
ninety-nine percent of its norm, while the imaginary component is below one
hundredth of the norm. -/
theorem leanSaddleSector_parameter_component_bounds
    {s : ℂ} (hs : s ∈ leanSaddleSector) :
    (99 / 100 : ℝ) * ‖s‖ < s.re ∧ |s.im| < ‖s‖ / 100 := by
  have harg : |s.arg| < 1 / 100 := hs.2
  have hcos : 99 / 100 < Real.cos s.arg := by
    calc
      99 / 100 < 1 - s.arg ^ 2 / 2 := by
        nlinarith [sq_abs s.arg, abs_nonneg s.arg]
      _ ≤ Real.cos s.arg := Real.one_sub_sq_div_two_le_cos
  have hnorm : 0 < ‖s‖ := norm_pos_iff.mpr
    (leanSaddleSector_quantitative hs).parameter_ne_zero
  constructor
  · rw [← Complex.norm_mul_cos_arg]
    simpa [mul_comm] using mul_lt_mul_of_pos_left hcos hnorm
  · rw [← Complex.norm_mul_sin_arg, abs_mul, abs_of_pos hnorm]
    calc
      ‖s‖ * |Real.sin s.arg| ≤ ‖s‖ * |s.arg| :=
        mul_le_mul_of_nonneg_left Real.abs_sin_le_abs hnorm.le
      _ < ‖s‖ * (1 / 100) := mul_lt_mul_of_pos_left harg hnorm
      _ = ‖s‖ / 100 := by ring

/-- A convenient quotient form of the component bound. -/
theorem leanSaddleSector_parameter_im_abs_lt_re_div_ninetyNine
    {s : ℂ} (hs : s ∈ leanSaddleSector) :
    |s.im| < s.re / 99 := by
  have h := leanSaddleSector_parameter_component_bounds hs
  nlinarith [norm_nonneg s]

/-- The rational part `Re(s/u^2)` is positive everywhere on the selected
horizontal ray to the right of real part one. -/
theorem quantitativeSaddleBranch_horizontal_rational_re_pos
    {s : ℂ} (hs : s ∈ leanSaddleSector) {r : ℝ}
    (hx : 1 ≤ (quantitativeSaddleBranch s + r).re) :
    0 < (s / (quantitativeSaddleBranch s + r) ^ 2).re := by
  let L : ℂ := quantitativeSaddleBranch s
  let x : ℝ := (L + r).re
  let b : ℝ := L.im
  let u : ℂ := L + r
  have hsim : |s.im| < s.re / 99 :=
    leanSaddleSector_parameter_im_abs_lt_re_div_ninetyNine hs
  have hsre : 0 < s.re := by
    have h := leanSaddleSector_parameter_component_bounds hs
    have hnorm : 0 < ‖s‖ := norm_pos_iff.mpr
      (leanSaddleSector_quantitative hs).parameter_ne_zero
    nlinarith
  have hx1 : 1 ≤ x := by simpa only [L, x] using hx
  have hbsmall : |b| < 1 / 20 := by
    simpa only [L, b] using quantitativeSaddleBranch_im_abs_lt hs
  have hb2 : b ^ 2 < 1 / 400 := by
    have hsquare :=
      (sq_lt_sq₀ (abs_nonneg b) (by norm_num : (0 : ℝ) ≤ 1 / 20)).2 hbsmall
    rw [sq_abs] at hsquare
    norm_num at hsquare ⊢
    exact hsquare
  have hcross : |2 * s.im * x * b| < s.re * x ^ 2 / 990 := by
    have hxpos : 0 < x := lt_of_lt_of_le zero_lt_one hx1
    have habsX : |x| = x := abs_of_pos hxpos
    calc
      |2 * s.im * x * b| = 2 * |s.im| * x * |b| := by
        rw [abs_mul, abs_mul, abs_mul,
          abs_of_pos (by norm_num : (0 : ℝ) < 2), habsX]
      _ < 2 * (s.re / 99) * x * (1 / 20) := by
        gcongr
      _ ≤ s.re * x ^ 2 / 990 := by
        have hxx : x ≤ x ^ 2 := by nlinarith
        have := mul_le_mul_of_nonneg_left hxx hsre.le
        nlinarith
  have hnum : 0 < s.re * (x ^ 2 - b ^ 2) + 2 * s.im * x * b := by
    have hneg := neg_le_of_abs_le hcross.le
    have hbterm : s.re * b ^ 2 < s.re / 400 :=
      (mul_lt_mul_of_pos_left hb2 hsre).trans_eq (by ring)
    have hxx : 1 ≤ x ^ 2 := by nlinarith
    have hxterm : s.re ≤ s.re * x ^ 2 := by
      simpa using mul_le_mul_of_nonneg_left hxx hsre.le
    nlinarith
  have huRe : u.re = x := rfl
  have huIm : u.im = b := by simp [u, b]
  have hune : u ≠ 0 := by
    intro hzero
    have : u.re = 0 := by rw [hzero]; norm_num
    linarith
  change 0 < (s / u ^ 2).re
  rw [Complex.div_re, ← add_div]
  have hden : 0 < Complex.normSq (u ^ 2) :=
    Complex.normSq_pos.mpr (pow_ne_zero 2 hune)
  apply div_pos _ hden
  rw [pow_two]
  simp only [mul_re, mul_im, huRe, huIm]
  nlinarith

/-- The exponential part of the horizontal curvature has positive real
part on the same ray. -/
theorem quantitativeSaddleBranch_horizontal_exponential_re_pos
    {s : ℂ} (hs : s ∈ leanSaddleSector) {r : ℝ} :
    0 < (((Real.pi : ℂ) *
      exp (quantitativeSaddleBranch s + r)).re) := by
  let L : ℂ := quantitativeSaddleBranch s
  have hb : |L.im| < 1 / 20 := by
    simpa only [L] using quantitativeSaddleBranch_im_abs_lt hs
  have hcos : 0 < Real.cos L.im := by
    calc
      0 < 1 - L.im ^ 2 / 2 := by
        have hsquare :=
          (sq_lt_sq₀ (abs_nonneg L.im) (by norm_num : (0 : ℝ) ≤ 1 / 20)).2 hb
        rw [sq_abs] at hsquare
        nlinarith
      _ ≤ Real.cos L.im := Real.one_sub_sq_div_two_le_cos
  change 0 < (((Real.pi : ℂ) * exp (L + r)).re)
  simp only [mul_re, ofReal_re, Complex.exp_re, ofReal_im, zero_mul,
    sub_zero, add_re, ofReal_re, add_im, ofReal_im, add_zero]
  exact mul_pos Real.pi_pos (mul_pos (Real.exp_pos _) hcos)

/-- The exact second derivative of the logarithmic integrand is negative in
the horizontal direction throughout the legal ray. -/
theorem quantitativeSaddleBranch_horizontalLogD2_re_neg
    {s : ℂ} (hs : s ∈ leanSaddleSector) {r : ℝ}
    (hx : 1 ≤ (quantitativeSaddleBranch s + r).re) :
    (leadingLogD2 s (quantitativeSaddleBranch s + r)).re < 0 := by
  let L : ℂ := quantitativeSaddleBranch s
  have hrat := quantitativeSaddleBranch_horizontal_rational_re_pos hs hx
  have hexp :=
    quantitativeSaddleBranch_horizontal_exponential_re_pos (s := s) hs (r := r)
  have hneg : (-s / (L + r) ^ 2).re = -(s / (L + r) ^ 2).re := by
    rw [neg_div, neg_re]
  unfold leadingLogD2
  change (-s / (L + r) ^ 2).re -
      ((Real.pi : ℂ) * exp (L + r)).re < 0
  rw [hneg]
  simpa only [L] using (show
    -(s / (L + r) ^ 2).re - ((Real.pi : ℂ) * exp (L + r)).re < 0 by
      linarith)

/-- Real part of the logarithmic integrand on the selected horizontal
coordinate. -/
def leadingHorizontalRealLog (s L : ℂ) (r : ℝ) : ℝ :=
  (leadingHorizontalLog s L r).re

def leadingHorizontalRealD1 (s L : ℂ) (r : ℝ) : ℝ :=
  (leadingHorizontalD1 s L r).re

def leadingHorizontalRealD2 (s L : ℂ) (r : ℝ) : ℝ :=
  (leadingHorizontalD2 s L r).re

theorem hasDerivAt_leadingHorizontalRealLog
    {s L : ℂ} {r : ℝ} (hr : 0 < (L + r).re) :
    HasDerivAt (leadingHorizontalRealLog s L)
      (leadingHorizontalRealD1 s L r) r := by
  convert Complex.reCLM.hasFDerivAt.comp_hasDerivAt r
    (hasDerivAt_leadingHorizontalLog hr) using 1 <;>
    rfl

theorem hasDerivAt_leadingHorizontalRealD1
    {s L : ℂ} {r : ℝ} (hr : 0 < (L + r).re) :
    HasDerivAt (leadingHorizontalRealD1 s L)
      (leadingHorizontalRealD2 s L r) r := by
  convert Complex.reCLM.hasFDerivAt.comp_hasDerivAt r
    (hasDerivAt_leadingHorizontalD1 hr) using 1 <;>
    rfl

/-- The second real derivative is exactly the real part of the named complex
differential tower. -/
theorem leadingHorizontalRealLog_iteratedDeriv_two
    {s L : ℂ} {r : ℝ} (hr : 0 < (L + r).re) :
    deriv^[2] (leadingHorizontalRealLog s L) r =
      leadingHorizontalRealD2 s L r := by
  have hnear : ∀ᶠ y : ℝ in 𝓝 r, 0 < (L + y).re := by
    have hrlower : -L.re < r := by
      simp only [add_re, ofReal_re] at hr
      linarith
    filter_upwards [Ioi_mem_nhds hrlower] with y hy
    change -L.re < y at hy
    simp only [add_re, ofReal_re]
    linarith
  have hderiv : deriv (leadingHorizontalRealLog s L) =ᶠ[𝓝 r]
      leadingHorizontalRealD1 s L := hnear.mono fun _ hy =>
    (hasDerivAt_leadingHorizontalRealLog hy).deriv
  change deriv (deriv (leadingHorizontalRealLog s L)) r = _
  rw [Filter.EventuallyEq.deriv_eq hderiv]
  exact (hasDerivAt_leadingHorizontalRealD1 hr).deriv

/-- The real logarithmic phase is strictly concave on the entire translated
horizontal ray beginning at real part one. -/
theorem quantitativeSaddleBranch_horizontal_strictConcaveOn
    {s : ℂ} (hs : s ∈ leanSaddleSector) :
    StrictConcaveOn ℝ (Ici (1 - (quantitativeSaddleBranch s).re))
      (leadingHorizontalRealLog s (quantitativeSaddleBranch s)) := by
  let L : ℂ := quantitativeSaddleBranch s
  change StrictConcaveOn ℝ (Ici (1 - L.re)) (leadingHorizontalRealLog s L)
  apply strictConcaveOn_of_deriv2_neg (convex_Ici (1 - L.re))
  · intro r hr
    have hrmem : 1 - L.re ≤ r := hr
    exact (hasDerivAt_leadingHorizontalRealLog (by
      simp only [add_re, ofReal_re]
      linarith)).continuousAt.continuousWithinAt
  · intro r hr
    have hr' : 1 - L.re < r := by
      simpa only [interior_Ici, mem_Ioi] using hr
    rw [leadingHorizontalRealLog_iteratedDeriv_two (by
      simp only [add_re, ofReal_re]
      linarith)]
    simpa only [leadingHorizontalRealD2, leadingHorizontalD2] using
      quantitativeSaddleBranch_horizontalLogD2_re_neg hs (by
        simp only [add_re, ofReal_re]
        linarith)

end

end Zeta23.Research.JensenWedge
