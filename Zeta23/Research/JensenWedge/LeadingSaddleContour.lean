import Zeta23.Research.JensenWedge.SectorialSaddle
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.SpecialFunctions.Gaussian.FourierTransform

/-!
# Leading-mode saddle contour

This module begins the concrete T3 formalization.  It keeps separate the
published phase (before the `dt = exp u du` Jacobian), the full logarithmic
integrand, and the integrand itself.  The separation is important: the
published saddle makes the derivative of the full logarithmic integrand equal
to `1`, not `0`.

The first section kernel-checks the exact phase algebra, the horizontal
direction, derivatives through order four, the saddle value and curvature,
and the full complex Gaussian comparison.  The legal rectangle deformation
and its quantitative estimates are added in later sections of this module.
-/

namespace Zeta23.Research.JensenWedge

open Complex Filter Function MeasureTheory Set Topology

noncomputable section

/-! ## Exact phase and contour coordinates -/

/-- The published first-mode phase before the logarithmic Jacobian is
included. -/
def leadingPhase (s u : ℂ) : ℂ :=
  s * log u - (3 / 4) * u - (Real.pi : ℂ) * exp u

/-- The first-mode integrand after `t = exp u`, with the Jacobian displayed
as its own factor. -/
def leadingIntegrand (s u : ℂ) : ℂ :=
  exp u * exp (leadingPhase s u)

/-- The logarithm of the full first-mode integrand. -/
def leadingLogIntegrand (s u : ℂ) : ℂ :=
  s * log u + u / 4 - (Real.pi : ℂ) * exp u

theorem leadingIntegrand_eq_exp_logIntegrand (s u : ℂ) :
    leadingIntegrand s u = exp (leadingLogIntegrand s u) := by
  unfold leadingIntegrand leadingPhase leadingLogIntegrand
  rw [← exp_add]
  congr 1
  ring

/-- The actual contour is a horizontal ray through `L`, parametrized by a
real displacement. -/
def leadingHorizontalPoint (L : ℂ) (r : ℝ) : ℂ := L + r

/-- The endpoint connector at real part one. -/
def leadingConnectorPoint (y : ℝ) : ℂ := 1 + y * I

/-- The open right half-plane, a fixed domain avoiding the principal-log
cut. -/
def leadingLogDomain : Set ℂ := {u | 0 < u.re}

theorem leadingHorizontalPoint_re (L : ℂ) (r : ℝ) :
    (leadingHorizontalPoint L r).re = L.re + r := by
  simp [leadingHorizontalPoint]

theorem leadingHorizontalPoint_im (L : ℂ) (r : ℝ) :
    (leadingHorizontalPoint L r).im = L.im := by
  simp [leadingHorizontalPoint]

/-- The top side at height `Im L` is exactly the horizontal saddle
coordinate, never the vertical coordinate `L + i r`. -/
theorem leadingTopPoint_eq_horizontal (L : ℂ) (r : ℝ) :
    ((L.re + r : ℝ) : ℂ) + L.im * I = leadingHorizontalPoint L r := by
  apply Complex.ext <;> simp [leadingHorizontalPoint]

theorem leadingConnectorPoint_re (y : ℝ) :
    (leadingConnectorPoint y).re = 1 := by
  simp [leadingConnectorPoint]

theorem leadingConnectorPoint_mem_domain (y : ℝ) :
    leadingConnectorPoint y ∈ leadingLogDomain := by
  norm_num [leadingLogDomain, leadingConnectorPoint]

theorem leadingHorizontalPoint_mem_domain
    {L : ℂ} {r : ℝ} (hr : 1 ≤ L.re + r) :
    leadingHorizontalPoint L r ∈ leadingLogDomain := by
  simp only [leadingLogDomain, mem_setOf_eq, leadingHorizontalPoint_re]
  linarith

/-! ## Concrete branch geometry needed by the contour -/

theorem leanSaddleSector_log_re_gt
    {s : ℂ} (hs : s ∈ leanSaddleSector) :
    1000000 < (log s).re := by
  have hinput := leanSaddleSector_quantitative hs
  have hnormpos : 0 < ‖s‖ := norm_pos_iff.mpr hinput.parameter_ne_zero
  have hlogradial : leanSaddleCutoff < Real.log ‖s‖ :=
    (Real.lt_log_iff_exp_lt hnormpos).2 hs.1
  rw [Complex.log_re]
  simpa only [leanSaddleCutoff] using hlogradial

theorem leanSaddleSector_log_im_abs_lt
    {s : ℂ} (hs : s ∈ leanSaddleSector) :
    |(log s).im| < 1 / 100 := by
  rw [Complex.log_im]
  exact hs.2

theorem leanSaddleSector_log_norm_le_re_add
    {s : ℂ} (hs : s ∈ leanSaddleSector) :
    ‖log s‖ ≤ (log s).re + 1 / 100 := by
  have hre : 0 ≤ (log s).re := (leanSaddleSector_log_re_gt hs).le.trans'
    (by norm_num)
  calc
    ‖log s‖ ≤ |(log s).re| + |(log s).im| :=
      Complex.norm_le_abs_re_add_abs_im _
    _ = (log s).re + |(log s).im| := by rw [abs_of_nonneg hre]
    _ ≤ (log s).re + 1 / 100 := by
      gcongr
      exact (leanSaddleSector_log_im_abs_lt hs).le

theorem saddleComparisonCenter_re_gt
    {s : ℂ} (hs : s ∈ leanSaddleSector) :
    900000 < (saddleComparisonCenter s).re := by
  let correction : ℂ := log (log s) + log (Real.pi : ℂ)
  have hinput := leanSaddleSector_quantitative hs
  have hcorr : ‖correction‖ ≤ ‖log s‖ / 100 := hinput.logCorrection_le
  have hcorrRe : correction.re ≤ ‖correction‖ := Complex.re_le_norm correction
  have hnorm := leanSaddleSector_log_norm_le_re_add hs
  have hwre := leanSaddleSector_log_re_gt hs
  have hidentity : saddleComparisonCenter s = log s - correction := by
    simp only [saddleComparisonCenter, correction]
    ring
  rw [hidentity, sub_re]
  nlinarith

theorem quantitativeSaddleBranch_re_gt
    {s : ℂ} (hs : s ∈ leanSaddleSector) :
    1000 < (quantitativeSaddleBranch s).re := by
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
  have hlower := (neg_le_of_abs_le hdiff)
  nlinarith

theorem leanSaddleSector_log_arg_abs_lt
    {s : ℂ} (hs : s ∈ leanSaddleSector) :
    |(log s).arg| < 1 / 100 := by
  let w : ℂ := log s
  have hwre : 0 < w.re := by
    change 0 < (log s).re
    linarith [leanSaddleSector_log_re_gt hs]
  have hwnorm : 1000000 < ‖w‖ :=
    (leanSaddleSector_log_re_gt hs).trans_le (Complex.re_le_norm w)
  have hwne : w ≠ 0 := norm_pos_iff.mp (lt_trans (by norm_num) hwnorm)
  have hwim : |w.im| < 1 / 100 := leanSaddleSector_log_im_abs_lt hs
  have hsinSmall : |Real.sin w.arg| < 1 / 100000000 := by
    rw [Complex.sin_arg, abs_div, abs_of_nonneg (norm_nonneg w)]
    apply (div_lt_iff₀ (norm_pos_iff.mpr hwne)).2
    nlinarith
  have hargRange : |w.arg| ≤ Real.pi / 2 :=
    Complex.abs_arg_le_pi_div_two_iff.mpr hwre.le
  have hjordan : 2 / Real.pi * |w.arg| ≤ |Real.sin w.arg| :=
    Real.mul_abs_le_abs_sin hargRange
  calc
    |w.arg| = (Real.pi / 2) * (2 / Real.pi * |w.arg|) := by
      field_simp [Real.pi_ne_zero]
    _ ≤ (Real.pi / 2) * |Real.sin w.arg| := by
      gcongr
    _ < (Real.pi / 2) * (1 / 100000000) := by
      gcongr
    _ < 1 / 100 := by
      nlinarith [Real.pi_pos, Real.pi_le_four]

theorem saddleComparisonCenter_im_abs_lt
    {s : ℂ} (hs : s ∈ leanSaddleSector) :
    |(saddleComparisonCenter s).im| < 1 / 50 := by
  have hsarg : |s.arg| < 1 / 100 := hs.2
  have hwarg := leanSaddleSector_log_arg_abs_lt hs
  have hidentity : (saddleComparisonCenter s).im = s.arg - (log s).arg := by
    unfold saddleComparisonCenter
    rw [sub_im, sub_im, Complex.log_im, Complex.log_im, Complex.log_im]
    simp [Complex.arg_ofReal_of_nonneg Real.pi_pos.le]
  rw [hidentity]
  calc
    |s.arg - (log s).arg| ≤ |s.arg| + |(log s).arg| := abs_sub _ _
    _ < 1 / 100 + 1 / 100 := add_lt_add hsarg hwarg
    _ = 1 / 50 := by ring

theorem quantitativeSaddleBranch_im_abs_lt
    {s : ℂ} (hs : s ∈ leanSaddleSector) :
    |(quantitativeSaddleBranch s).im| < 1 / 20 := by
  have hq : s ∈ quantitativeSaddleDomain := leanSaddleSector_quantitative hs
  have hdist := quantitativeSaddleBranch_dist_center_le hq
  have himdiff : |(quantitativeSaddleBranch s).im -
      (saddleComparisonCenter s).im| ≤
      dist (quantitativeSaddleBranch s) (saddleComparisonCenter s) := by
    calc
      |(quantitativeSaddleBranch s).im - (saddleComparisonCenter s).im| =
          |(quantitativeSaddleBranch s - saddleComparisonCenter s).im| := by
        rw [sub_im]
      _ ≤ ‖quantitativeSaddleBranch s - saddleComparisonCenter s‖ :=
        Complex.abs_im_le_norm _
      _ = dist (quantitativeSaddleBranch s) (saddleComparisonCenter s) := by
        rw [dist_eq]
  have hcenter := saddleComparisonCenter_im_abs_lt hs
  calc
    |(quantitativeSaddleBranch s).im| =
        |((quantitativeSaddleBranch s).im - (saddleComparisonCenter s).im) +
          (saddleComparisonCenter s).im| := by ring_nf
    _ ≤ |(quantitativeSaddleBranch s).im - (saddleComparisonCenter s).im| +
        |(saddleComparisonCenter s).im| := abs_add_le _ _
    _ < 11 / 750 + 1 / 50 := add_lt_add_of_le_of_lt
      (himdiff.trans hdist) hcenter
    _ < 1 / 20 := by norm_num

/-! ## Exact differential tower -/

def leadingLogD1 (s u : ℂ) : ℂ :=
  s / u + 1 / 4 - (Real.pi : ℂ) * exp u

def leadingLogD2 (s u : ℂ) : ℂ :=
  -s / u ^ 2 - (Real.pi : ℂ) * exp u

def leadingLogD3 (s u : ℂ) : ℂ :=
  2 * s / u ^ 3 - (Real.pi : ℂ) * exp u

def leadingLogD4 (s u : ℂ) : ℂ :=
  -6 * s / u ^ 4 - (Real.pi : ℂ) * exp u

theorem hasDerivAt_leadingLogIntegrand
    {s u : ℂ} (hu : u ∈ slitPlane) :
    HasDerivAt (leadingLogIntegrand s) (leadingLogD1 s u) u := by
  unfold leadingLogIntegrand leadingLogD1
  have hlog := (Complex.hasDerivAt_log hu).const_mul s
  have hlinear := (hasDerivAt_id' u).div_const 4
  have hexp := (hasDerivAt_exp u).const_mul (Real.pi : ℂ)
  convert! (hlog.add hlinear).sub hexp using 1 <;> ring

theorem hasDerivAt_leadingLogD1
    {s u : ℂ} (hu : u ≠ 0) :
    HasDerivAt (leadingLogD1 s) (leadingLogD2 s u) u := by
  unfold leadingLogD1 leadingLogD2
  have hquot := (hasDerivAt_const u s).div (hasDerivAt_id' u) hu
  have hexp := (hasDerivAt_exp u).const_mul (Real.pi : ℂ)
  convert! (hquot.add_const (1 / 4)).sub hexp using 1 <;>
    field_simp [hu] <;> ring

theorem hasDerivAt_leadingLogD2
    {s u : ℂ} (hu : u ≠ 0) :
    HasDerivAt (leadingLogD2 s) (leadingLogD3 s u) u := by
  unfold leadingLogD2 leadingLogD3
  have hinv2 := ((hasDerivAt_id' u).pow 2).inv (pow_ne_zero 2 hu)
  have hterm := hinv2.const_mul (-s)
  simp only [Pi.pow_apply] at hterm
  have hexp := (hasDerivAt_exp u).const_mul (Real.pi : ℂ)
  convert! hterm.sub hexp using 1 <;>
    field_simp [hu] <;> ring

theorem hasDerivAt_leadingLogD3
    {s u : ℂ} (hu : u ≠ 0) :
    HasDerivAt (leadingLogD3 s) (leadingLogD4 s u) u := by
  unfold leadingLogD3 leadingLogD4
  have hinv3 := ((hasDerivAt_id' u).pow 3).inv (pow_ne_zero 3 hu)
  have hterm := hinv3.const_mul (2 * s)
  simp only [Pi.pow_apply] at hterm
  have hexp := (hasDerivAt_exp u).const_mul (Real.pi : ℂ)
  convert! hterm.sub hexp using 1 <;>
    field_simp [hu] <;> ring

theorem leadingLogIntegrand_differentiableOn_domain (s : ℂ) :
    DifferentiableOn ℂ (leadingLogIntegrand s) leadingLogDomain := by
  intro u hu
  exact (hasDerivAt_leadingLogIntegrand (Or.inl hu)).differentiableAt.differentiableWithinAt

theorem leadingIntegrand_differentiableOn_domain (s : ℂ) :
    DifferentiableOn ℂ (leadingIntegrand s) leadingLogDomain := by
  intro u hu
  have heq : leadingIntegrand s = fun z => exp (leadingLogIntegrand s z) := by
    funext z
    exact leadingIntegrand_eq_exp_logIntegrand s z
  rw [heq]
  exact ((hasDerivAt_leadingLogIntegrand (s := s) (u := u) (Or.inl hu)).cexp).differentiableAt.differentiableWithinAt

/-! ## Saddle identities -/

/-- Curvature in the normalization of the paper, `K = Q / L^2`. -/
def leadingCurvature (s L : ℂ) : ℂ :=
  sectorialSaddleCurvature s L / L ^ 2

theorem leadingCurvature_eq_paper
    {s L : ℂ} (hL : L ≠ 0) :
    leadingCurvature s L = s * (1 / L + 1 / L ^ 2) - 3 / 4 := by
  unfold leadingCurvature sectorialSaddleCurvature
  field_simp [hL]
  ring

theorem leadingCurvature_factor
    {s L : ℂ} (hs : s ≠ 0) (hL : L ≠ 0) :
    leadingCurvature s L =
      (s / L) * (1 + 1 / L - (3 / 4) * (L / s)) := by
  rw [leadingCurvature_eq_paper hL]
  field_simp [hs, hL]

/-- The concrete saddle curvature lies in the open right half-plane.  This is
the sign needed by the horizontal Gaussian, proved from the T2 branch boxes
and the small imaginary part rather than assumed in a certificate. -/
theorem quantitativeSaddleBranch_curvature_strong_bounds
    {s : ℂ} (hs : s ∈ leanSaddleSector) :
    1 < (leadingCurvature s (quantitativeSaddleBranch s)).re ∧
      ‖leadingCurvature s (quantitativeSaddleBranch s)‖ ≤
        2 * (leadingCurvature s (quantitativeSaddleBranch s)).re := by
  let L : ℂ := quantitativeSaddleBranch s
  let B : ℂ := s / L
  let a : ℂ := 1 + 1 / L - (3 / 4) * (L / s)
  let A : ℝ := Real.pi * Real.exp L.re
  have hinput := leanSaddleSector_quantitative hs
  have hq : s ∈ quantitativeSaddleDomain := hinput
  have hbounds := quantitativeSaddleBranch_scaled_bounds hq
  have hLne : L ≠ 0 := hbounds.1
  have hsne : s ≠ 0 := hinput.parameter_ne_zero
  have hroot : sectorialSaddleEquation s L = 0 :=
    (quantitativeSaddleBranch_spec hq).2.1
  have hmap : s = L * ((Real.pi : ℂ) * exp L + 3 / 4) := by
    unfold sectorialSaddleEquation saddleParameterMap at hroot
    exact (eq_of_sub_eq_zero hroot).symm
  have hB : B = (Real.pi : ℂ) * exp L + 3 / 4 := by
    simp only [B]
    rw [hmap]
    field_simp [hLne]
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
  have haRe : 3 / 4 ≤ a.re := by
    have hre := Complex.abs_re_le_norm (a - 1)
    have hlower := neg_le_of_abs_le (hre.trans haNorm)
    simp only [sub_re, one_re] at hlower
    linarith
  have haReUpper : a.re ≤ 5 / 4 := by
    have hre := (Complex.abs_re_le_norm (a - 1)).trans haNorm
    have hupper := le_of_abs_le hre
    simp only [sub_re, one_re] at hupper
    linarith
  have haIm : |a.im| ≤ 1 / 4 := by
    have him := (Complex.abs_im_le_norm (a - 1)).trans haNorm
    simpa only [sub_im, one_im, sub_zero] using him
  have hAim : |L.im| < 1 / 20 := quantitativeSaddleBranch_im_abs_lt hs
  have hApos : 0 < A := mul_pos Real.pi_pos (Real.exp_pos _)
  have hAgt : 3 < A := by
    have hLre := quantitativeSaddleBranch_re_gt hs
    have hexpgt : 1 < Real.exp L.re := by
      rw [← Real.exp_zero]
      exact Real.exp_lt_exp.mpr (by linarith)
    calc
      3 = 3 * 1 := by ring
      _ < Real.pi * 1 := mul_lt_mul_of_pos_right Real.pi_gt_three zero_lt_one
      _ < Real.pi * Real.exp L.re :=
        mul_lt_mul_of_pos_left hexpgt Real.pi_pos
      _ = A := by rfl
  have hcos : 99 / 100 < Real.cos L.im := by
    calc
      99 / 100 < 1 - L.im ^ 2 / 2 := by
        nlinarith [sq_abs L.im, abs_nonneg L.im]
      _ ≤ Real.cos L.im := Real.one_sub_sq_div_two_le_cos
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
    have hcosPos : 0 < Real.cos L.im := by linarith [hcos]
    nlinarith [mul_pos hApos hcosPos]
  have hBreGt : 3 < B.re := by
    rw [hBre]
    have hAcos : A * (99 / 100) < A * Real.cos L.im :=
      mul_lt_mul_of_pos_left hcos hApos
    nlinarith
  have hBimSmall : |B.im| < B.re / 10 := by
    rw [hBim, abs_mul, abs_of_pos hApos]
    have hsin : |Real.sin L.im| ≤ |L.im| := Real.abs_sin_le_abs
    have hleft : A * |Real.sin L.im| < A / 20 := by
      calc
        A * |Real.sin L.im| ≤ A * |L.im| :=
          mul_le_mul_of_nonneg_left hsin hApos.le
        _ < A * (1 / 20) := mul_lt_mul_of_pos_left hAim hApos
        _ = A / 20 := by ring
    rw [hBre]
    nlinarith
  rw [leadingCurvature_factor hsne hLne]
  change 1 < (B * a).re ∧ ‖B * a‖ ≤ 2 * (B * a).re
  have hreal : B.re * (3 / 4) ≤ B.re * a.re := by
    exact mul_le_mul_of_nonneg_left haRe hBrePos.le
  have himul : |B.im * a.im| < B.re / 40 := by
    rw [abs_mul]
    calc
      |B.im| * |a.im| ≤ |B.im| * (1 / 4) := by
        gcongr
      _ < (B.re / 10) * (1 / 4) := by
        exact mul_lt_mul_of_pos_right hBimSmall (by norm_num)
      _ = B.re / 40 := by ring
  have hproduct : B.im * a.im ≤ |B.im * a.im| := le_abs_self _
  have hKreLower : B.re * (29 / 40) < (B * a).re := by
    rw [mul_re]
    nlinarith
  have hKreGt : 1 < (B * a).re := by
    nlinarith
  have hKImSmall : |(B * a).im| < B.re * (3 / 8) := by
    rw [mul_im]
    calc
      |B.re * a.im + B.im * a.re| ≤
          |B.re * a.im| + |B.im * a.re| := abs_add_le _ _
      _ = B.re * |a.im| + |B.im| * a.re := by
        rw [abs_mul, abs_mul, abs_of_pos hBrePos,
          abs_of_nonneg (haRe.trans' (by norm_num))]
      _ ≤ B.re * (1 / 4) + |B.im| * (5 / 4) := by
        gcongr
      _ < B.re * (1 / 4) + (B.re / 10) * (5 / 4) := by
        gcongr
      _ = B.re * (3 / 8) := by ring
  have hKImLeRe : |(B * a).im| ≤ (B * a).re := by
    exact (hKImSmall.trans (by nlinarith [hKreLower])).le
  constructor
  · exact hKreGt
  · calc
      ‖B * a‖ ≤ |(B * a).re| + |(B * a).im| :=
        Complex.norm_le_abs_re_add_abs_im _
      _ = (B * a).re + |(B * a).im| := by
        rw [abs_of_pos (lt_trans zero_lt_one hKreGt)]
      _ ≤ 2 * (B * a).re := by linarith

theorem quantitativeSaddleBranch_curvature_re_pos
    {s : ℂ} (hs : s ∈ leanSaddleSector) :
    0 < (leadingCurvature s (quantitativeSaddleBranch s)).re :=
  (by linarith [quantitativeSaddleBranch_curvature_strong_bounds hs |>.1])

theorem leadingLogD1_at_saddle
    {s L : ℂ} (hL : L ≠ 0)
    (hroot : sectorialSaddleEquation s L = 0) :
    leadingLogD1 s L = 1 := by
  have hs : s = L * ((Real.pi : ℂ) * exp L + 3 / 4) := by
    unfold sectorialSaddleEquation saddleParameterMap at hroot
    exact (eq_of_sub_eq_zero hroot).symm
  unfold leadingLogD1
  rw [hs]
  field_simp [hL]
  ring

theorem leadingLogD2_at_saddle
    {s L : ℂ} (hL : L ≠ 0)
    (hroot : sectorialSaddleEquation s L = 0) :
    leadingLogD2 s L = -leadingCurvature s L := by
  have hs : s = L * ((Real.pi : ℂ) * exp L + 3 / 4) := by
    unfold sectorialSaddleEquation saddleParameterMap at hroot
    exact (eq_of_sub_eq_zero hroot).symm
  unfold leadingLogD2 leadingCurvature sectorialSaddleCurvature
  rw [hs]
  field_simp [hL]
  ring

theorem leadingLogIntegrand_at_saddle
    {s L : ℂ} (hL : L ≠ 0)
    (hroot : sectorialSaddleEquation s L = 0) :
    leadingLogIntegrand s L =
      s * log L + L / 4 - s / L + 3 / 4 := by
  have hs : s = L * ((Real.pi : ℂ) * exp L + 3 / 4) := by
    unfold sectorialSaddleEquation saddleParameterMap at hroot
    exact (eq_of_sub_eq_zero hroot).symm
  unfold leadingLogIntegrand
  rw [hs]
  field_simp [hL]
  ring

/-- The full-line Gaussian comparison retaining the Jacobian-induced linear
term. -/
def leadingGaussian (K : ℂ) (r : ℝ) : ℂ :=
  exp ((r : ℂ) - K * (r : ℂ) ^ 2 / 2)

theorem integrable_leadingGaussian
    {K : ℂ} (hK : 0 < K.re) :
    Integrable (leadingGaussian K) := by
  have hb : (-(K / 2)).re < 0 := by
    norm_num [Complex.div_re]
    linarith
  convert integrable_cexp_quadratic' hb 1 0 using 1
  ext r
  unfold leadingGaussian
  congr 1
  push_cast
  ring

theorem integral_leadingGaussian
    {K : ℂ} (hK : 0 < K.re) :
    (∫ r : ℝ, leadingGaussian K r) =
      ((2 * Real.pi : ℂ) / K) ^ (1 / 2 : ℂ) * exp (1 / (2 * K)) := by
  have hKne : K ≠ 0 := by
    intro hzero
    rw [hzero] at hK
    simpa using hK
  have hb : (-(K / 2)).re < 0 := by
    norm_num [Complex.div_re]
    linarith
  have h := integral_cexp_quadratic hb (1 : ℂ) 0
  have hbase : (Real.pi : ℂ) / -(-(K / 2)) = (2 * Real.pi : ℂ) / K := by
    field_simp [hKne]
  have hexponent : (0 : ℂ) - 1 ^ 2 / (4 * (-(K / 2))) = 1 / (2 * K) := by
    field_simp [hKne]
    ring
  calc
    (∫ r : ℝ, leadingGaussian K r) =
        ∫ r : ℝ, exp (-(K / 2) * (r : ℂ) ^ 2 + 1 * (r : ℂ) + 0) := by
      apply integral_congr_ae
      filter_upwards with r
      unfold leadingGaussian
      congr 1
      ring
    _ = ((Real.pi : ℂ) / -(-(K / 2))) ^ (1 / 2 : ℂ) *
        exp ((0 : ℂ) - 1 ^ 2 / (4 * (-(K / 2)))) := h
    _ = ((2 * Real.pi : ℂ) / K) ^ (1 / 2 : ℂ) * exp (1 / (2 * K)) := by
      rw [hbase, hexponent]

/-! ## The finite legal rectangle -/

/-- Bottom horizontal side of the rectangle, oriented from `1` to `X`. -/
def leadingBottomSegment (s : ℂ) (X : ℝ) : ℂ :=
  ∫ x : ℝ in 1..X, leadingIntegrand s x

/-- Top horizontal side, with the same left-to-right orientation. -/
def leadingTopSegment (s : ℂ) (b X : ℝ) : ℂ :=
  ∫ x : ℝ in 1..X, leadingIntegrand s (x + b * I)

/-- Right vertical side, parametrized bottom-to-top. -/
def leadingRightSegment (s : ℂ) (b X : ℝ) : ℂ :=
  I * ∫ y : ℝ in 0..b, leadingIntegrand s (X + y * I)

/-- Left endpoint connector, parametrized bottom-to-top. -/
def leadingLeftSegment (s : ℂ) (b : ℝ) : ℂ :=
  I * ∫ y : ℝ in 0..b, leadingIntegrand s (1 + y * I)

theorem leadingRectangle_subset_domain {b X : ℝ} (hX : 1 ≤ X) :
    (Set.uIcc ((1 : ℂ).re) (X + b * I : ℂ).re ×ℂ
      Set.uIcc ((1 : ℂ).im) (X + b * I : ℂ).im) ⊆ leadingLogDomain := by
  intro u hu
  simp only [ofReal_re, add_re, mul_re, ofReal_im, I_re, I_im, mul_zero,
    zero_mul, sub_zero, add_zero] at hu
  have hre : u.re ∈ Set.uIcc 1 X := hu.1
  rw [Set.uIcc_of_le hX] at hre
  exact show 0 < u.re from lt_of_lt_of_le zero_lt_one hre.1

/-- Cauchy-Goursat on the exact branch-safe rectangle with vertices
`1`, `X`, `X+ib`, and `1+ib`.  All four boundary segments remain named in
the conclusion. -/
theorem leading_finite_rectangle_identity
    (s : ℂ) {b X : ℝ} (hX : 1 ≤ X) :
    leadingBottomSegment s X - leadingTopSegment s b X +
        leadingRightSegment s b X - leadingLeftSegment s b = 0 := by
  have hdiff : DifferentiableOn ℂ (leadingIntegrand s)
      (Set.uIcc ((1 : ℂ).re) (X + b * I : ℂ).re ×ℂ
        Set.uIcc ((1 : ℂ).im) (X + b * I : ℂ).im) :=
    (leadingIntegrand_differentiableOn_domain s).mono
      (leadingRectangle_subset_domain hX)
  have hboundary := Complex.integral_boundary_rect_eq_zero_of_differentiableOn
    (leadingIntegrand s) (1 : ℂ) (X + b * I) hdiff
  simpa [leadingBottomSegment, leadingTopSegment, leadingRightSegment,
    leadingLeftSegment, smul_eq_mul] using hboundary

theorem leadingBottomSegment_eq_top_sub_right_add_left
    (s : ℂ) {b X : ℝ} (hX : 1 ≤ X) :
    leadingBottomSegment s X = leadingTopSegment s b X -
      leadingRightSegment s b X + leadingLeftSegment s b := by
  have h := leading_finite_rectangle_identity s (b := b) hX
  linear_combination h

/-! ## Vanishing of the far vertical side -/

theorem norm_log_horizontal_le
    {X y : ℝ} (hX : 1 ≤ X) (hy : |y| ≤ 1 / 20) :
    ‖log (X + y * I)‖ ≤ 5 * X := by
  let u : ℂ := X + y * I
  have hure : u.re = X := by simp [u]
  have huim : u.im = y := by simp [u]
  have hunormLower : X ≤ ‖u‖ := by
    rw [← hure]
    exact (le_abs_self u.re).trans (Complex.abs_re_le_norm u)
  have hunormPos : 0 < ‖u‖ := lt_of_lt_of_le (by linarith) hunormLower
  have hunormUpper : ‖u‖ ≤ X + 1 / 20 := by
    calc
      ‖u‖ ≤ |u.re| + |u.im| := Complex.norm_le_abs_re_add_abs_im u
      _ = X + |y| := by
        rw [hure, huim, abs_of_nonneg (by linarith : 0 ≤ X)]
      _ ≤ X + 1 / 20 := by gcongr
  have hlogNonneg : 0 ≤ Real.log ‖u‖ :=
    Real.log_nonneg (hX.trans hunormLower)
  have hlogUpper : Real.log ‖u‖ ≤ ‖u‖ - 1 :=
    Real.log_le_sub_one_of_pos hunormPos
  calc
    ‖log u‖ ≤ |(log u).re| + |(log u).im| :=
      Complex.norm_le_abs_re_add_abs_im _
    _ = Real.log ‖u‖ + |u.arg| := by
      rw [Complex.log_re, Complex.log_im, abs_of_nonneg hlogNonneg]
    _ ≤ (‖u‖ - 1) + Real.pi := by
      gcongr
      exact Complex.abs_arg_le_pi u
    _ ≤ (X + 1 / 20 - 1) + 4 := by
      gcongr
      exact Real.pi_le_four
    _ ≤ 5 * X := by linarith

theorem norm_leadingIntegrand_right_le_exp_neg
    (s : ℂ) {X y : ℝ}
    (hX : 2 * (5 * ‖s‖ + 1) + 2 ≤ X)
    (hy : |y| ≤ 1 / 20) :
    ‖leadingIntegrand s (X + y * I)‖ ≤ Real.exp (-X) := by
  have hXone : 1 ≤ X := by
    have hsnonneg : 0 ≤ ‖s‖ := norm_nonneg s
    linarith
  have hXpos : 0 < X := lt_of_lt_of_le (by norm_num) hXone
  let u : ℂ := X + y * I
  have hlog := norm_log_horizontal_le hXone hy
  have hslog : (s * log u).re ≤ 5 * ‖s‖ * X := by
    calc
      (s * log u).re ≤ ‖s * log u‖ := Complex.re_le_norm _
      _ = ‖s‖ * ‖log u‖ := norm_mul _ _
      _ ≤ ‖s‖ * (5 * X) := by gcongr
      _ = 5 * ‖s‖ * X := by ring
  have hcos : 99 / 100 < Real.cos y := by
    calc
      99 / 100 < 1 - y ^ 2 / 2 := by
        nlinarith [sq_abs y, abs_nonneg y]
      _ ≤ Real.cos y := Real.one_sub_sq_div_two_le_cos
  have hpiCos : 2 < Real.pi * Real.cos y := by
    nlinarith [Real.pi_gt_three, mul_lt_mul_of_pos_left hcos Real.pi_pos]
  have hexpquad := Real.pow_div_factorial_le_exp X hXpos.le 2
  norm_num [Nat.factorial] at hexpquad
  have hpositive : (s * log u).re + X / 4 ≤ (5 * ‖s‖ + 1) * X := by
    nlinarith
  have hcutProduct : (5 * ‖s‖ + 1) * X ≤ X ^ 2 / 2 - X := by
    have hcoef : 0 ≤ 5 * ‖s‖ + 1 := by positivity
    have hxmul := mul_nonneg (sub_nonneg.mpr hX) hXpos.le
    nlinarith
  have hphase : (leadingLogIntegrand s u).re ≤ -X := by
    have hdecay : X ^ 2 ≤
        Real.pi * Real.exp X * Real.cos y := by
      have hmul := mul_le_mul_of_nonneg_right hexpquad
        (show 0 ≤ 2 from by norm_num)
      have hbase : X ^ 2 ≤ 2 * Real.exp X := by nlinarith
      have hcosExp : 2 * Real.exp X <
          (Real.pi * Real.cos y) * Real.exp X := by
        exact mul_lt_mul_of_pos_right hpiCos (Real.exp_pos X)
      nlinarith
    have hformula : (leadingLogIntegrand s u).re =
        (s * log u).re + X / 4 -
          Real.pi * Real.exp X * Real.cos y := by
      unfold leadingLogIntegrand
      simp only [sub_re, add_re, mul_re, ofReal_re, ofReal_im, zero_mul,
        sub_zero, Complex.exp_re]
      simp only [u, add_re, mul_re, ofReal_re, ofReal_im, I_re, I_im,
        zero_mul, sub_zero, add_zero]
      norm_num [Complex.div_re]
      ring
    rw [hformula]
    nlinarith
  rw [leadingIntegrand_eq_exp_logIntegrand, Complex.norm_exp]
  exact Real.exp_le_exp.mpr hphase

theorem norm_leadingRightSegment_le
    (s : ℂ) {b X : ℝ} (hb : |b| ≤ 1 / 20)
    (hX : 2 * (5 * ‖s‖ + 1) + 2 ≤ X) :
    ‖leadingRightSegment s b X‖ ≤ Real.exp (-X) * |b| := by
  unfold leadingRightSegment
  rw [norm_mul, norm_I, one_mul]
  calc
    ‖∫ y : ℝ in 0..b, leadingIntegrand s (X + y * I)‖ ≤
        Real.exp (-X) * |b - 0| :=
      intervalIntegral.norm_integral_le_of_norm_le_const (C := Real.exp (-X))
        (fun y hy => by
          have hyabs : |y| ≤ |b| := by
            simpa using abs_sub_left_of_mem_uIcc (uIoc_subset_uIcc hy)
          exact norm_leadingIntegrand_right_le_exp_neg s hX (hyabs.trans hb))
    _ = Real.exp (-X) * |b| := by rw [sub_zero]

theorem tendsto_leadingRightSegment_zero
    (s : ℂ) {b : ℝ} (hb : |b| ≤ 1 / 20) :
    Tendsto (fun X : ℝ => leadingRightSegment s b X) atTop (𝓝 0) := by
  rw [tendsto_zero_iff_norm_tendsto_zero]
  have hbound : ∀ᶠ X : ℝ in atTop,
      ‖leadingRightSegment s b X‖ ≤ Real.exp (-X) * |b| := by
    filter_upwards [eventually_ge_atTop
      (2 * (5 * ‖s‖ + 1) + 2)] with X hX
    exact norm_leadingRightSegment_le s hb hX
  have hexp : Tendsto (fun X : ℝ => Real.exp (-X)) atTop (𝓝 0) :=
    Real.tendsto_exp_atBot.comp tendsto_neg_atTop_atBot
  have hupper : Tendsto (fun X : ℝ => Real.exp (-X) * |b|) atTop (𝓝 0) := by
    simpa using hexp.mul_const |b|
  exact squeeze_zero' (Eventually.of_forall fun X => norm_nonneg _) hbound hupper

/-! ## Infinite translated rays -/

/-- The bottom ray of the legal rectangle, beginning at the branch-safe
point `1`. -/
def leadingBottomRay (s : ℂ) : ℂ :=
  ∫ x : ℝ in Ioi 1, leadingIntegrand s x

/-- The translated ray at height `b`, with the same left-to-right
orientation as the bottom ray. -/
def leadingTopRay (s : ℂ) (b : ℝ) : ℂ :=
  ∫ x : ℝ in Ioi 1, leadingIntegrand s (x + b * I)

theorem continuousOn_leadingHorizontalRay (s : ℂ) (b : ℝ) :
    ContinuousOn (fun x : ℝ => leadingIntegrand s (x + b * I)) (Ici 1) := by
  exact (leadingIntegrand_differentiableOn_domain s).continuousOn.comp'
    (by fun_prop) (by
      intro x hx
      simp only [leadingLogDomain, mem_setOf_eq, add_re, ofReal_re, mul_re,
        ofReal_im, I_re, I_im, mul_zero, zero_mul, sub_zero, add_zero]
      have hx' : 1 ≤ x := hx
      linarith)

/-- Both the original and translated rays are absolutely integrable.  The
proof is uniform for `|b| ≤ 1/20`: compact continuity handles the finite
piece and the explicit `exp (-x)` majorant handles the tail. -/
theorem integrableOn_leadingHorizontalRay
    (s : ℂ) {b : ℝ} (hb : |b| ≤ 1 / 20) :
    IntegrableOn (fun x : ℝ => leadingIntegrand s (x + b * I)) (Ioi 1) := by
  let C : ℝ := 2 * (5 * ‖s‖ + 1) + 2
  have hC : 1 ≤ C := by
    have hsnonneg : 0 ≤ ‖s‖ := norm_nonneg s
    dsimp [C]
    linarith
  have hcontinuous := continuousOn_leadingHorizontalRay s b
  have hlocal : IntegrableOn
      (fun x : ℝ => leadingIntegrand s (x + b * I)) (Ioc 1 C) :=
    (hcontinuous.mono Icc_subset_Ici_self).integrableOn_Icc.mono_set
      Ioc_subset_Icc_self
  have htailContinuous : ContinuousOn
      (fun x : ℝ => leadingIntegrand s (x + b * I)) (Ioi C) :=
    hcontinuous.mono (fun _ hx => hC.trans hx.le)
  have htail : IntegrableOn
      (fun x : ℝ => leadingIntegrand s (x + b * I)) (Ioi C) := by
    apply Integrable.mono' (integrableOn_exp_neg_Ioi C)
      (htailContinuous.aestronglyMeasurable measurableSet_Ioi)
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    exact norm_leadingIntegrand_right_le_exp_neg s hx.le hb
  rw [← Ioc_union_Ioi_eq_Ioi hC]
  exact hlocal.union htail

theorem integrableOn_leadingBottomRay (s : ℂ) :
    IntegrableOn (fun x : ℝ => leadingIntegrand s x) (Ioi 1) := by
  simpa using integrableOn_leadingHorizontalRay s (b := 0) (by norm_num)

theorem tendsto_leadingBottomSegment_ray (s : ℂ) :
    Tendsto (leadingBottomSegment s) atTop (𝓝 (leadingBottomRay s)) := by
  change Tendsto (fun X : ℝ =>
    ∫ x : ℝ in 1..X, leadingIntegrand s x) atTop
      (𝓝 (∫ x : ℝ in Ioi 1, leadingIntegrand s x))
  exact intervalIntegral_tendsto_integral_Ioi 1
    (integrableOn_leadingBottomRay s) tendsto_id

theorem tendsto_leadingTopSegment_ray
    (s : ℂ) {b : ℝ} (hb : |b| ≤ 1 / 20) :
    Tendsto (leadingTopSegment s b) atTop (𝓝 (leadingTopRay s b)) := by
  change Tendsto (fun X : ℝ =>
    ∫ x : ℝ in 1..X, leadingIntegrand s (x + b * I)) atTop
      (𝓝 (∫ x : ℝ in Ioi 1, leadingIntegrand s (x + b * I)))
  exact intervalIntegral_tendsto_integral_Ioi 1
    (integrableOn_leadingHorizontalRay s hb) tendsto_id

/-- Exact infinite-ray contour deformation.  The identity is obtained from
finite Cauchy rectangles and the independently proved vanishing of the far
vertical side; no informal infinite contour is invoked. -/
theorem leading_infinite_rectangle_identity
    (s : ℂ) {b : ℝ} (hb : |b| ≤ 1 / 20) :
    leadingBottomRay s = leadingTopRay s b + leadingLeftSegment s b := by
  have hfinite : ∀ᶠ X : ℝ in atTop,
      leadingBottomSegment s X = leadingTopSegment s b X -
        leadingRightSegment s b X + leadingLeftSegment s b := by
    filter_upwards [eventually_ge_atTop (1 : ℝ)] with X hX
    exact leadingBottomSegment_eq_top_sub_right_add_left s hX
  have hbottom := tendsto_leadingBottomSegment_ray s
  have htop := tendsto_leadingTopSegment_ray s hb
  have hright := tendsto_leadingRightSegment_zero s hb
  have hrhs : Tendsto
      (fun X : ℝ => leadingTopSegment s b X - leadingRightSegment s b X +
        leadingLeftSegment s b) atTop
      (𝓝 (leadingTopRay s b - 0 + leadingLeftSegment s b)) :=
    (htop.sub hright).add_const _
  have hreverse : ∀ᶠ X : ℝ in atTop,
      leadingTopSegment s b X - leadingRightSegment s b X +
          leadingLeftSegment s b = leadingBottomSegment s X :=
    hfinite.mono (fun _ h => h.symm)
  have heq := tendsto_nhds_unique hbottom (hrhs.congr' hreverse)
  simpa using heq

end

end Zeta23.Research.JensenWedge
