import Zeta23.Research.JensenWedge.AnalyticAdapters
import Zeta23.Research.JensenWedge.SaddleBounds
import Mathlib.Analysis.SpecialFunctions.Complex.LogDeriv
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.Calculus.MeanValue

/-!
# The sectorial saddle equation

This file fixes the exact complex equation used by the quantitative saddle
lemma and kernel-checks its algebraic differential identities.  Existence,
the moving-disc contraction, and holomorphic patching are added in subsequent
sections; none of those analytic conclusions is assumed here.
-/

namespace Zeta23.Research.JensenWedge

open Complex Filter Function Set Topology

noncomputable section

/-- Inner sector angle used by the contour comparison. -/
def saddleInnerAngle : ℝ := 1 / 400

/-- Manuscript outer sector angle for holomorphic coefficient assembly. -/
def saddleOuterAngle : ℝ := 1 / 200

/-- Wider analytic angle used for the saddle and contour proofs.  The
manuscript outer sector is strictly inside this sector so that the affine
shift `N = 2M - 2` has uniform angular room. -/
def saddleProofAngle : ℝ := 1 / 100

theorem saddle_angles_pos :
    0 < saddleInnerAngle ∧ saddleInnerAngle < saddleOuterAngle ∧
      saddleOuterAngle < Real.pi / 2 := by
  constructor
  · norm_num [saddleInnerAngle]
  constructor
  · norm_num [saddleInnerAngle, saddleOuterAngle]
  · have hpi : (3 : ℝ) < Real.pi := Real.pi_gt_three
    norm_num [saddleOuterAngle]
    linarith

theorem saddleOuterAngle_lt_proofAngle :
    saddleOuterAngle < saddleProofAngle := by
  norm_num [saddleOuterAngle, saddleProofAngle]

theorem saddleProofAngle_lt_pi_div_two :
    saddleProofAngle < Real.pi / 2 := by
  have hpi : (3 : ℝ) < Real.pi := Real.pi_gt_three
  norm_num [saddleProofAngle]
  linarith

/-- The fixed open sector with radial logarithmic cutoff `cutoff`. -/
def saddleSector (cutoff : ℝ) : Set ℂ :=
  {s | Real.exp cutoff < ‖s‖ ∧ |s.arg| < saddleProofAngle}

/-- Comparison point `log s - log(log s) - log pi`. -/
def saddleComparisonCenter (s : ℂ) : ℂ :=
  log s - log (log s) - log (Real.pi : ℂ)

/-- The map whose value is the saddle parameter. -/
def saddleParameterMap (L : ℂ) : ℂ :=
  L * ((Real.pi : ℂ) * exp L + 3 / 4)

/-- The exact saddle equation, normalized to have value zero at a root. -/
def sectorialSaddleEquation (s L : ℂ) : ℂ :=
  saddleParameterMap L - s

/-- Curvature denominator in the implicit derivative formula. -/
def sectorialSaddleCurvature (s L : ℂ) : ℂ :=
  (1 + L) * s - (3 / 4) * L ^ 2

theorem hasDerivAt_saddleParameterMap (L : ℂ) :
    HasDerivAt saddleParameterMap
      ((Real.pi : ℂ) * exp L * (1 + L) + 3 / 4) L := by
  unfold saddleParameterMap
  have h : HasDerivAt (fun z : ℂ => z * ((Real.pi : ℂ) * exp z + 3 / 4))
      (1 * ((Real.pi : ℂ) * exp L + 3 / 4) +
        L * ((Real.pi : ℂ) * exp L)) L := by
    convert! (hasDerivAt_id' L).mul
      (((hasDerivAt_exp L).const_mul (Real.pi : ℂ)).add_const (3 / 4)) using 1
  apply h.congr_deriv
  ring

theorem hasStrictDerivAt_saddleParameterMap (L : ℂ) :
    HasStrictDerivAt saddleParameterMap
      ((Real.pi : ℂ) * exp L * (1 + L) + 3 / 4) L := by
  unfold saddleParameterMap
  have h : HasStrictDerivAt
      (fun z : ℂ => z * ((Real.pi : ℂ) * exp z + 3 / 4))
      (1 * ((Real.pi : ℂ) * exp L + 3 / 4) +
        L * ((Real.pi : ℂ) * exp L)) L := by
    convert! (hasStrictDerivAt_id L).mul
      (((hasStrictDerivAt_exp L).const_mul (Real.pi : ℂ)).add_const (3 / 4)) using 1
  apply h.congr_deriv
  ring

theorem hasDerivAt_sectorialSaddleEquation (s L : ℂ) :
    HasDerivAt (sectorialSaddleEquation s)
      ((Real.pi : ℂ) * exp L * (1 + L) + 3 / 4) L := by
  unfold sectorialSaddleEquation
  exact (hasDerivAt_saddleParameterMap L).sub_const s

/-- At an exact saddle, multiplication of the `L`-derivative by `L`
produces the manuscript curvature denominator. -/
theorem saddle_derivative_mul_eq_curvature {s L : ℂ}
    (hroot : sectorialSaddleEquation s L = 0) :
    (((Real.pi : ℂ) * exp L * (1 + L) + 3 / 4) * L) =
      sectorialSaddleCurvature s L := by
  have hs : s = L * ((Real.pi : ℂ) * exp L + 3 / 4) := by
    unfold sectorialSaddleEquation saddleParameterMap at hroot
    exact (eq_of_sub_eq_zero hroot).symm
  rw [hs]
  unfold sectorialSaddleCurvature
  ring

theorem saddle_derivative_ne_zero {s L : ℂ}
    (hroot : sectorialSaddleEquation s L = 0)
    (hcurvature : sectorialSaddleCurvature s L ≠ 0) :
    (Real.pi : ℂ) * exp L * (1 + L) + 3 / 4 ≠ 0 := by
  intro hzero
  have h := saddle_derivative_mul_eq_curvature hroot
  rw [hzero, zero_mul] at h
  exact hcurvature h.symm

/-- The curvature is exactly the polynomial denominator already bounded by
the finite branch-box certificate. -/
theorem sectorialSaddleCurvature_eq_polynomial (s L : ℂ) :
    sectorialSaddleCurvature s L = saddlePolynomialDenominator s L := by
  unfold sectorialSaddleCurvature saddlePolynomialDenominator
  ring

theorem sectorialSaddleCurvature_scaled
    {s L r sigma : ℂ} (hs : s ≠ 0) (hL : L ≠ 0)
    (hr : r = 1 / L) (hsigma : sigma = L / s) :
    sectorialSaddleCurvature s L =
      s * L * (1 + r - (3 / 4) * sigma) := by
  rw [sectorialSaddleCurvature_eq_polynomial]
  exact saddlePolynomialDenominator_scaled hs hL hr hsigma

theorem sectorialSaddleCurvature_ne_zero_of_box
    {s L r sigma : ℂ} (hs : s ≠ 0) (hL : L ≠ 0)
    (hr : r = 1 / L) (hsigma : sigma = L / s)
    (hrbox : ‖r‖ ≤ 7 / 50) (hsigmabox : ‖sigma‖ ≤ 7 / 50) :
    sectorialSaddleCurvature s L ≠ 0 := by
  rw [sectorialSaddleCurvature_scaled hs hL hr hsigma]
  exact mul_ne_zero (mul_ne_zero hs hL)
    (saddle_scaled_factor_ne_zero hrbox hsigmabox)

/-! ## A uniform closed-disc contraction family -/

/-- Newton's equation-normalized self-map.  Near the distinguished large
saddle its derivative is small; algebraically, its fixed points are exactly
the saddle roots whenever `s != 0`. -/
def saddleNewtonMap (s L : ℂ) : ℂ :=
  L - sectorialSaddleEquation s L / s

theorem saddleNewtonMap_fixed_iff {s L : ℂ} (hs : s ≠ 0) :
    IsFixedPt (saddleNewtonMap s) L ↔ sectorialSaddleEquation s L = 0 := by
  constructor
  · intro hfixed
    have hquot : sectorialSaddleEquation s L / s = 0 := by
      have hneg : -(sectorialSaddleEquation s L / s) = 0 := by
        calc
          -(sectorialSaddleEquation s L / s) = saddleNewtonMap s L - L := by
            unfold saddleNewtonMap
            ring
          _ = 0 := sub_eq_zero.mpr hfixed
      exact neg_eq_zero.mp hneg
    exact (div_eq_zero_iff.mp hquot).resolve_right hs
  · intro hroot
    unfold IsFixedPt saddleNewtonMap
    simp [hroot]

theorem hasDerivAt_saddleNewtonMap {s L : ℂ} :
    HasDerivAt (saddleNewtonMap s)
      (1 - (((Real.pi : ℂ) * exp L * (1 + L) + 3 / 4) / s)) L := by
  unfold saddleNewtonMap
  have h := (hasDerivAt_id' L).sub
    ((hasDerivAt_sectorialSaddleEquation s L).div_const s)
  convert! h using 1

/-- Uniform data sufficient for Banach's theorem on a moving family of
closed discs.  Every quantified estimate is whole-disc, not a sample-point
check. -/
structure SaddleContractionFamily (domain : Set ℂ) where
  center : ℂ → ℂ
  radius : ℂ → ℝ
  contractionConstant : NNReal
  parameter_ne_zero : ∀ s ∈ domain, s ≠ 0
  radius_nonneg : ∀ s ∈ domain, 0 ≤ radius s
  maps_disc : ∀ s ∈ domain,
    MapsTo (saddleNewtonMap s)
      (Metric.closedBall (center s) (radius s))
      (Metric.closedBall (center s) (radius s))
  contracts_disc : ∀ (s : ℂ) (hs : s ∈ domain),
    ContractingWith contractionConstant
      ((maps_disc s hs).restrict (saddleNewtonMap s)
        (Metric.closedBall (center s) (radius s))
        (Metric.closedBall (center s) (radius s)))

theorem SaddleContractionFamily.existsUnique_root_in_disc
    {domain : Set ℂ} (data : SaddleContractionFamily domain)
    {s : ℂ} (hs : s ∈ domain) :
    ∃ L ∈ Metric.closedBall (data.center s) (data.radius s),
      sectorialSaddleEquation s L = 0 ∧
        ∀ z ∈ Metric.closedBall (data.center s) (data.radius s),
          sectorialSaddleEquation s z = 0 → z = L := by
  rcases complexClosedBall_existsUnique_fixedPoint
      (data.radius_nonneg s hs) (data.maps_disc s hs)
      (data.contracts_disc s hs) with ⟨L, hLmem, hfixed, hunique⟩
  refine ⟨L, hLmem, (saddleNewtonMap_fixed_iff (data.parameter_ne_zero s hs)).mp hfixed,
    ?_⟩
  intro z hzmem hzroot
  exact hunique z hzmem
    ((saddleNewtonMap_fixed_iff (data.parameter_ne_zero s hs)).mpr hzroot)

/-- The pointwise branch selected by the uniform contraction family.  Its
value outside `domain` is irrelevant and fixed to zero. -/
noncomputable def contractedSaddleBranch
    {domain : Set ℂ} (data : SaddleContractionFamily domain) (s : ℂ) : ℂ := by
  classical
  exact if hs : s ∈ domain then
      Classical.choose (data.existsUnique_root_in_disc hs)
    else 0

theorem contractedSaddleBranch_spec
    {domain : Set ℂ} (data : SaddleContractionFamily domain)
    {s : ℂ} (hs : s ∈ domain) :
    contractedSaddleBranch data s ∈
        Metric.closedBall (data.center s) (data.radius s) ∧
      sectorialSaddleEquation s (contractedSaddleBranch data s) = 0 ∧
      ∀ z ∈ Metric.closedBall (data.center s) (data.radius s),
        sectorialSaddleEquation s z = 0 →
          z = contractedSaddleBranch data s := by
  classical
  rw [contractedSaddleBranch, dif_pos hs]
  exact Classical.choose_spec (data.existsUnique_root_in_disc hs)

theorem contractedSaddleBranch_mem
    {domain : Set ℂ} (data : SaddleContractionFamily domain)
    {s : ℂ} (hs : s ∈ domain) :
    contractedSaddleBranch data s ∈
      Metric.closedBall (data.center s) (data.radius s) :=
  (contractedSaddleBranch_spec data hs).1

theorem contractedSaddleBranch_equation
    {domain : Set ℂ} (data : SaddleContractionFamily domain)
    {s : ℂ} (hs : s ∈ domain) :
    sectorialSaddleEquation s (contractedSaddleBranch data s) = 0 :=
  (contractedSaddleBranch_spec data hs).2.1

theorem contractedSaddleBranch_unique
    {domain : Set ℂ} (data : SaddleContractionFamily domain)
    {s z : ℂ} (hs : s ∈ domain)
    (hzmem : z ∈ Metric.closedBall (data.center s) (data.radius s))
    (hzroot : sectorialSaddleEquation s z = 0) :
    z = contractedSaddleBranch data s :=
  (contractedSaddleBranch_spec data hs).2.2 z hzmem hzroot

/-! ## Quantitative hypotheses for the concrete Newton discs -/

/-- The four explicit normalized estimates used to instantiate the uniform
contraction family.  A later sector-geometry theorem supplies these estimates
from the fixed angular and radial conditions. -/
structure SaddleQuantitativeInput (s : ℂ) : Prop where
  parameter_ne_zero : s ≠ 0
  logParameter_norm_lower : 1000 ≤ ‖log s‖
  logCorrection_le :
    ‖log (log s) + log (Real.pi : ℂ)‖ ≤ ‖log s‖ / 100
  center_parameter_ratio_le :
    ‖saddleComparisonCenter s / s‖ ≤ 1 / 10000
  parameter_inverse_le : ‖(1 : ℂ) / s‖ ≤ 1 / 1000

theorem SaddleQuantitativeInput.logParameter_ne_zero
    {s : ℂ} (h : SaddleQuantitativeInput s) : log s ≠ 0 := by
  intro hzero
  have := h.logParameter_norm_lower
  rw [hzero, norm_zero] at this
  norm_num at this

/-- Exact exponential identity at the logarithmic comparison center. -/
theorem exp_saddleComparisonCenter {s : ℂ} (hs : s ≠ 0)
    (hw : log s ≠ 0) :
    (Real.pi : ℂ) * exp (saddleComparisonCenter s) = s / log s := by
  have hpi : (Real.pi : ℂ) ≠ 0 := ofReal_ne_zero.mpr Real.pi_ne_zero
  unfold saddleComparisonCenter
  rw [exp_sub, exp_sub, exp_log hs, exp_log hw, exp_log hpi]
  field_simp

/-- The comparison-center residual divided by the parameter, in the exact
normalization used by the self-map estimate. -/
theorem saddleComparisonCenter_residual_div {s : ℂ} (hs : s ≠ 0)
    (hw : log s ≠ 0) :
    sectorialSaddleEquation s (saddleComparisonCenter s) / s =
      -(log (log s) + log (Real.pi : ℂ)) / log s +
        (3 / 4) * (saddleComparisonCenter s / s) := by
  have hcenter := exp_saddleComparisonCenter hs hw
  unfold sectorialSaddleEquation saddleParameterMap
  rw [hcenter]
  unfold saddleComparisonCenter
  field_simp [hs, hw]
  ring

theorem saddleComparisonCenter_residual_norm_le
    {s : ℂ} (h : SaddleQuantitativeInput s) :
    ‖sectorialSaddleEquation s (saddleComparisonCenter s) / s‖ ≤
      11 / 1000 := by
  rw [saddleComparisonCenter_residual_div h.parameter_ne_zero
    h.logParameter_ne_zero]
  calc
    ‖-(log (log s) + log (Real.pi : ℂ)) / log s +
        (3 / 4) * (saddleComparisonCenter s / s)‖
        ≤ ‖-(log (log s) + log (Real.pi : ℂ)) / log s‖ +
          ‖(3 / 4 : ℂ) * (saddleComparisonCenter s / s)‖ := norm_add_le _ _
    _ = ‖log (log s) + log (Real.pi : ℂ)‖ / ‖log s‖ +
        (3 / 4 : ℝ) * ‖saddleComparisonCenter s / s‖ := by
      rw [norm_div, norm_neg, norm_mul]
      norm_num
    _ ≤ (‖log s‖ / 100) / ‖log s‖ +
        (3 / 4 : ℝ) * (1 / 10000) := by
      gcongr
      · exact h.logCorrection_le
      · exact h.center_parameter_ratio_le
    _ = 1 / 100 + (3 / 4 : ℝ) * (1 / 10000) := by
      field_simp [norm_ne_zero_iff.mpr h.logParameter_ne_zero]
    _ ≤ 11 / 1000 := by norm_num

/-- Exact decomposition of the Newton-map derivative around the comparison
center.  This is the algebraic source of the uniform contraction bound. -/
theorem saddleNewton_derivative_decomposition
    {s L : ℂ} (h : SaddleQuantitativeInput s) :
    1 - (((Real.pi : ℂ) * exp L * (1 + L) + 3 / 4) / s) =
      (1 - exp (L - saddleComparisonCenter s)) -
        exp (L - saddleComparisonCenter s) *
          ((1 - (log (log s) + log (Real.pi : ℂ)) +
              (L - saddleComparisonCenter s)) / log s) -
        (3 / 4) / s := by
  have hcenter := exp_saddleComparisonCenter h.parameter_ne_zero
    h.logParameter_ne_zero
  have hexp : (Real.pi : ℂ) * exp L =
      (s / log s) * exp (L - saddleComparisonCenter s) := by
    calc
      (Real.pi : ℂ) * exp L =
          (Real.pi : ℂ) * exp
            (saddleComparisonCenter s + (L - saddleComparisonCenter s)) := by ring_nf
      _ = ((Real.pi : ℂ) * exp (saddleComparisonCenter s)) *
          exp (L - saddleComparisonCenter s) := by rw [exp_add]; ring
      _ = (s / log s) * exp (L - saddleComparisonCenter s) := by rw [hcenter]
  rw [hexp]
  unfold saddleComparisonCenter
  field_simp [h.parameter_ne_zero, h.logParameter_ne_zero]
  ring

theorem saddleNewton_derivative_norm_le
    {s L : ℂ} (h : SaddleQuantitativeInput s)
    (hL : L ∈ Metric.closedBall (saddleComparisonCenter s) (1 / 20)) :
    ‖1 - (((Real.pi : ℂ) * exp L * (1 + L) + 3 / 4) / s)‖ ≤ 1 / 4 := by
  let delta : ℂ := L - saddleComparisonCenter s
  let correction : ℂ := log (log s) + log (Real.pi : ℂ)
  have hdelta : ‖delta‖ ≤ 1 / 20 := by
    simpa [delta, dist_eq] using (Metric.mem_closedBall.mp hL)
  have hdelta_one : ‖delta‖ ≤ 1 := by linarith
  have hexp_sub : ‖1 - exp delta‖ ≤ 1 / 10 := by
    rw [← norm_neg, neg_sub]
    exact (norm_exp_sub_one_le hdelta_one).trans (by linarith)
  have hexp : ‖exp delta‖ ≤ 3 := by
    rw [Complex.norm_exp]
    have hre : delta.re ≤ 1 :=
      (Complex.re_le_norm delta).trans hdelta_one
    exact (Real.exp_le_exp.mpr hre).trans Real.exp_one_lt_three.le
  have hlognorm : 0 < ‖log s‖ := norm_pos_iff.mpr h.logParameter_ne_zero
  have hnumerator : ‖1 - correction + delta‖ ≤
      1 + ‖log s‖ / 100 + 1 / 20 := by
    calc
      ‖1 - correction + delta‖ ≤ ‖(1 : ℂ)‖ + ‖correction‖ + ‖delta‖ := by
        grw [norm_add_le, norm_sub_le]
      _ ≤ 1 + ‖log s‖ / 100 + 1 / 20 := by
        norm_num
        gcongr
        · exact h.logCorrection_le
  have hfraction : ‖(1 - correction + delta) / log s‖ ≤ 221 / 20000 := by
    rw [norm_div]
    apply (div_le_iff₀ hlognorm).2
    calc
      ‖1 - correction + delta‖ ≤ 1 + ‖log s‖ / 100 + 1 / 20 := hnumerator
      _ ≤ (221 / 20000 : ℝ) * ‖log s‖ := by
        nlinarith [h.logParameter_norm_lower]
  have hmiddle : ‖exp delta * ((1 - correction + delta) / log s)‖ ≤
      3 * (221 / 20000 : ℝ) := by
    rw [norm_mul]
    gcongr
  have hlast : ‖(3 / 4 : ℂ) / s‖ ≤ 3 / 4000 := by
    calc
      ‖(3 / 4 : ℂ) / s‖ = (3 / 4 : ℝ) * ‖(1 : ℂ) / s‖ := by
        rw [div_eq_mul_inv, norm_mul, one_div, norm_inv]
        norm_num
      _ ≤ (3 / 4 : ℝ) * (1 / 1000) := by
        gcongr
        exact h.parameter_inverse_le
      _ = 3 / 4000 := by norm_num
  rw [saddleNewton_derivative_decomposition h]
  change ‖(1 - exp delta) - exp delta * ((1 - correction + delta) / log s) -
    (3 / 4) / s‖ ≤ 1 / 4
  calc
    ‖(1 - exp delta) - exp delta * ((1 - correction + delta) / log s) -
        (3 / 4) / s‖
        ≤ ‖1 - exp delta‖ +
            ‖exp delta * ((1 - correction + delta) / log s)‖ +
            ‖(3 / 4 : ℂ) / s‖ := by
          grw [norm_sub_le, norm_sub_le]
    _ ≤ 1 / 10 + 3 * (221 / 20000 : ℝ) + 3 / 4000 := by gcongr
    _ ≤ 1 / 4 := by norm_num

theorem saddleNewton_lipschitzOn_disc
    {s : ℂ} (h : SaddleQuantitativeInput s) :
    LipschitzOnWith (1 / 4 : NNReal) (saddleNewtonMap s)
      (Metric.closedBall (saddleComparisonCenter s) (1 / 20)) := by
  refine Convex.lipschitzOnWith_of_nnnorm_deriv_le ?_ ?_
    (convex_closedBall (saddleComparisonCenter s) (1 / 20))
  · intro L _hL
    exact (hasDerivAt_saddleNewtonMap (s := s) (L := L)).differentiableAt
  · intro L hL
    rw [(hasDerivAt_saddleNewtonMap (s := s) (L := L)).deriv]
    rw [← NNReal.coe_le_coe]
    simpa only [coe_nnnorm, NNReal.coe_div, NNReal.coe_one, NNReal.coe_ofNat] using
      saddleNewton_derivative_norm_le h hL

theorem saddleNewton_maps_disc
    {s : ℂ} (h : SaddleQuantitativeInput s) :
    MapsTo (saddleNewtonMap s)
      (Metric.closedBall (saddleComparisonCenter s) (1 / 20))
      (Metric.closedBall (saddleComparisonCenter s) (1 / 20)) := by
  intro L hL
  have hcenter : saddleComparisonCenter s ∈
      Metric.closedBall (saddleComparisonCenter s) (1 / 20) := by
    simp only [Metric.mem_closedBall, dist_self]
    norm_num
  have hlip := (saddleNewton_lipschitzOn_disc h).dist_le_mul
    L hL (saddleComparisonCenter s) hcenter
  have hlip' : ‖saddleNewtonMap s L -
      saddleNewtonMap s (saddleComparisonCenter s)‖ ≤
      (1 / 4 : ℝ) * ‖L - saddleComparisonCenter s‖ := by
    simpa only [dist_eq, NNReal.coe_div, NNReal.coe_one, NNReal.coe_ofNat] using hlip
  have hcenterResidual : ‖saddleNewtonMap s (saddleComparisonCenter s) -
      saddleComparisonCenter s‖ ≤ 11 / 1000 := by
    calc
      ‖saddleNewtonMap s (saddleComparisonCenter s) - saddleComparisonCenter s‖ =
          ‖sectorialSaddleEquation s (saddleComparisonCenter s) / s‖ := by
        unfold saddleNewtonMap
        rw [show saddleComparisonCenter s -
            sectorialSaddleEquation s (saddleComparisonCenter s) / s -
              saddleComparisonCenter s =
            -(sectorialSaddleEquation s (saddleComparisonCenter s) / s) by ring,
          norm_neg]
      _ ≤ 11 / 1000 := saddleComparisonCenter_residual_norm_le h
  rw [Metric.mem_closedBall, dist_eq] at hL ⊢
  calc
    ‖saddleNewtonMap s L - saddleComparisonCenter s‖ ≤
        ‖saddleNewtonMap s L - saddleNewtonMap s (saddleComparisonCenter s)‖ +
          ‖saddleNewtonMap s (saddleComparisonCenter s) -
            saddleComparisonCenter s‖ := by
      calc
        ‖saddleNewtonMap s L - saddleComparisonCenter s‖ =
            ‖(saddleNewtonMap s L -
                saddleNewtonMap s (saddleComparisonCenter s)) +
              (saddleNewtonMap s (saddleComparisonCenter s) -
                saddleComparisonCenter s)‖ := by ring_nf
        _ ≤ _ := norm_add_le _ _
    _ ≤ (1 / 4 : ℝ) * ‖L - saddleComparisonCenter s‖ + 11 / 1000 := by gcongr
    _ ≤ (1 / 4 : ℝ) * (1 / 20) + 11 / 1000 := by gcongr
    _ ≤ 1 / 20 := by norm_num

/-- Parameters satisfying the four explicit normalized estimates. -/
def quantitativeSaddleDomain : Set ℂ := {s | SaddleQuantitativeInput s}

/-- Concrete Banach family on the quantitative domain. -/
noncomputable def quantitativeSaddleContractionFamily :
    SaddleContractionFamily quantitativeSaddleDomain where
  center := saddleComparisonCenter
  radius := fun _ => 1 / 20
  contractionConstant := 1 / 4
  parameter_ne_zero := by
    intro s hs
    exact hs.parameter_ne_zero
  radius_nonneg := by
    intro _ _
    norm_num
  maps_disc := by
    intro s hs
    exact saddleNewton_maps_disc hs
  contracts_disc := by
    intro s hs
    refine ⟨by norm_num, ?_⟩
    intro x y
    exact saddleNewton_lipschitzOn_disc hs x.property y.property

abbrev quantitativeSaddleBranch : ℂ → ℂ :=
  contractedSaddleBranch quantitativeSaddleContractionFamily

theorem quantitativeSaddleBranch_spec
    {s : ℂ} (hs : s ∈ quantitativeSaddleDomain) :
    quantitativeSaddleBranch s ∈
        Metric.closedBall (saddleComparisonCenter s) (1 / 20) ∧
      sectorialSaddleEquation s (quantitativeSaddleBranch s) = 0 ∧
      ∀ z ∈ Metric.closedBall (saddleComparisonCenter s) (1 / 20),
        sectorialSaddleEquation s z = 0 → z = quantitativeSaddleBranch s := by
  exact contractedSaddleBranch_spec quantitativeSaddleContractionFamily hs

theorem saddle_disc_scaled_bounds
    {s L : ℂ} (h : SaddleQuantitativeInput s)
    (hL : L ∈ Metric.closedBall (saddleComparisonCenter s) (1 / 20)) :
    L ≠ 0 ∧ ‖(1 : ℂ) / L‖ ≤ 7 / 50 ∧ ‖L / s‖ ≤ 7 / 50 := by
  let correction : ℂ := log (log s) + log (Real.pi : ℂ)
  let delta : ℂ := L - saddleComparisonCenter s
  have hdelta : ‖delta‖ ≤ 1 / 20 := by
    simpa [delta, dist_eq] using (Metric.mem_closedBall.mp hL)
  have hcenterIdentity : log s = saddleComparisonCenter s + correction := by
    simp only [saddleComparisonCenter, correction]
    ring
  have hcenterLower : 990 ≤ ‖saddleComparisonCenter s‖ := by
    have htri : ‖log s‖ ≤ ‖saddleComparisonCenter s‖ + ‖correction‖ := by
      rw [hcenterIdentity]
      exact norm_add_le _ _
    have hcorr := h.logCorrection_le
    change ‖correction‖ ≤ ‖log s‖ / 100 at hcorr
    nlinarith [h.logParameter_norm_lower]
  have hLnorm : 989 ≤ ‖L‖ := by
    have htri : ‖saddleComparisonCenter s‖ ≤ ‖L‖ + ‖delta‖ := by
      have hid : saddleComparisonCenter s = L - delta := by
        simp only [delta]
        ring
      rw [hid]
      exact norm_sub_le _ _
    nlinarith
  have hLpos : 0 < ‖L‖ := lt_of_lt_of_le (by norm_num) hLnorm
  have hLne : L ≠ 0 := norm_pos_iff.mp hLpos
  have hinv : ‖(1 : ℂ) / L‖ ≤ 7 / 50 := by
    rw [norm_div]
    norm_num
    rw [inv_le_iff_one_le_mul₀' hLpos]
    nlinarith
  have hratio : ‖L / s‖ ≤ 7 / 50 := by
    have hdecomp : L / s = saddleComparisonCenter s / s + delta / s := by
      simp only [delta]
      ring
    rw [hdecomp]
    calc
      ‖saddleComparisonCenter s / s + delta / s‖ ≤
          ‖saddleComparisonCenter s / s‖ + ‖delta / s‖ := norm_add_le _ _
      _ = ‖saddleComparisonCenter s / s‖ + ‖delta‖ * ‖(1 : ℂ) / s‖ := by
        have hone : ‖(1 : ℂ) / s‖ = 1 / ‖s‖ := by
          rw [norm_div, norm_one]
        rw [norm_div, norm_div, hone]
        ring
      _ ≤ 1 / 10000 + (1 / 20 : ℝ) * (1 / 1000) := by
        gcongr
        · exact h.center_parameter_ratio_le
        · exact h.parameter_inverse_le
      _ ≤ 7 / 50 := by norm_num
  exact ⟨hLne, hinv, hratio⟩

theorem quantitativeSaddleBranch_scaled_bounds
    {s : ℂ} (hs : s ∈ quantitativeSaddleDomain) :
    quantitativeSaddleBranch s ≠ 0 ∧
      ‖(1 : ℂ) / quantitativeSaddleBranch s‖ ≤ 7 / 50 ∧
      ‖quantitativeSaddleBranch s / s‖ ≤ 7 / 50 := by
  change SaddleQuantitativeInput s at hs
  exact saddle_disc_scaled_bounds hs (quantitativeSaddleBranch_spec hs).1

theorem quantitativeSaddleBranch_curvature_ne_zero
    {s : ℂ} (hs : s ∈ quantitativeSaddleDomain) :
    sectorialSaddleCurvature s (quantitativeSaddleBranch s) ≠ 0 := by
  change SaddleQuantitativeInput s at hs
  have hbounds := quantitativeSaddleBranch_scaled_bounds hs
  exact sectorialSaddleCurvature_ne_zero_of_box hs.parameter_ne_zero hbounds.1
    rfl rfl hbounds.2.1 hbounds.2.2

/-! ## Supplying the quantitative inputs from an explicit fixed sector -/

/-- Conservative effective cutoff used by the Lean closure.  Sharpness is
irrelevant for the eventual theorem; the paper's smaller cutoff is retained
in the independent interval evidence. -/
def leanSaddleCutoff : ℝ := 1000000

/-- The actual outer sector on which the Lean branch is exported. -/
def leanSaddleSector : Set ℂ := saddleSector leanSaddleCutoff

private theorem real_log_le_div_twoHundred_add
    {x : ℝ} (hx : 0 < x) : Real.log x ≤ x / 200 + 198 := by
  have htwo : (200 : ℝ) ≠ 0 := by norm_num
  have hxdiv : x / 200 ≠ 0 := div_ne_zero hx.ne' htwo
  have hfactor : x = 200 * (x / 200) := by field_simp
  rw [hfactor, Real.log_mul htwo hxdiv]
  nlinarith [Real.log_le_sub_one_of_pos (show (0 : ℝ) < 200 by norm_num),
    Real.log_le_sub_one_of_pos (div_pos hx (by norm_num : (0 : ℝ) < 200))]

private theorem real_log_le_div_hundredThousand_add
    {x : ℝ} (hx : 0 < x) : Real.log x ≤ x / 100000 + 99998 := by
  have hscale : (100000 : ℝ) ≠ 0 := by norm_num
  have hxdiv : x / 100000 ≠ 0 := div_ne_zero hx.ne' hscale
  have hfactor : x = 100000 * (x / 100000) := by field_simp
  rw [hfactor, Real.log_mul hscale hxdiv]
  nlinarith [Real.log_le_sub_one_of_pos (show (0 : ℝ) < 100000 by norm_num),
    Real.log_le_sub_one_of_pos (div_pos hx (by norm_num : (0 : ℝ) < 100000))]

private theorem complex_log_pi_norm_le_three :
    ‖log (Real.pi : ℂ)‖ ≤ 3 := by
  have hpi1 : (1 : ℝ) ≤ Real.pi := by linarith [Real.pi_gt_three]
  have hlognonneg : 0 ≤ Real.log Real.pi := Real.log_nonneg hpi1
  have hlogle : Real.log Real.pi ≤ Real.pi - 1 :=
    Real.log_le_sub_one_of_pos Real.pi_pos
  calc
    ‖log (Real.pi : ℂ)‖ ≤
        |(log (Real.pi : ℂ)).re| + |(log (Real.pi : ℂ)).im| :=
      Complex.norm_le_abs_re_add_abs_im _
    _ = Real.log Real.pi := by
      rw [Complex.log_re, Complex.log_im, norm_real,
        Real.norm_eq_abs, abs_of_pos Real.pi_pos,
        Complex.arg_ofReal_of_nonneg Real.pi_pos.le,
        abs_zero, add_zero, abs_of_nonneg hlognonneg]
    _ ≤ 3 := by linarith [Real.pi_le_four]

theorem leanSaddleSector_quantitative
    {s : ℂ} (hs : s ∈ leanSaddleSector) : SaddleQuantitativeInput s := by
  rcases hs with ⟨hradial, hangle⟩
  have hnormpos : 0 < ‖s‖ :=
    (Real.exp_pos leanSaddleCutoff).trans hradial
  have hsne : s ≠ 0 := norm_pos_iff.mp hnormpos
  have hlogradial : leanSaddleCutoff < Real.log ‖s‖ :=
    (Real.lt_log_iff_exp_lt hnormpos).2 hradial
  have hwre : (log s).re = Real.log ‖s‖ := Complex.log_re s
  have hwlower : (1000000 : ℝ) < ‖log s‖ := by
    have hrele : (log s).re ≤ ‖log s‖ := Complex.re_le_norm (log s)
    rw [hwre] at hrele
    simpa only [leanSaddleCutoff] using hlogradial.trans_le hrele
  have hnormLarge : (500000000000 : ℝ) ≤ ‖s‖ := by
    have hquad := Real.pow_div_factorial_le_exp leanSaddleCutoff
      (show (0 : ℝ) ≤ leanSaddleCutoff by norm_num [leanSaddleCutoff]) 2
    have hcut : (500000000000 : ℝ) ≤ Real.exp leanSaddleCutoff := by
      norm_num [leanSaddleCutoff] at hquad
      exact hquad
    exact hcut.trans hradial.le
  have hwpos : 0 < ‖log s‖ := lt_trans (by norm_num) hwlower
  have hwlognonneg : 0 ≤ Real.log ‖log s‖ :=
    Real.log_nonneg (by linarith : (1 : ℝ) ≤ ‖log s‖)
  have hlogw : ‖log (log s)‖ ≤ ‖log s‖ / 200 + 202 := by
    calc
      ‖log (log s)‖ ≤ |(log (log s)).re| + |(log (log s)).im| :=
        Complex.norm_le_abs_re_add_abs_im _
      _ = |Real.log ‖log s‖| + |(log s).arg| := by
        rw [Complex.log_re, Complex.log_im]
      _ ≤ Real.log ‖log s‖ + Real.pi := by
        rw [abs_of_nonneg hwlognonneg]
        gcongr
        exact Complex.abs_arg_le_pi _
      _ ≤ (‖log s‖ / 200 + 198) + 4 := by
        gcongr
        · exact real_log_le_div_twoHundred_add hwpos
        · exact Real.pi_le_four
      _ = ‖log s‖ / 200 + 202 := by ring
  have hcorrection :
      ‖log (log s) + log (Real.pi : ℂ)‖ ≤ ‖log s‖ / 100 := by
    calc
      ‖log (log s) + log (Real.pi : ℂ)‖ ≤
          ‖log (log s)‖ + ‖log (Real.pi : ℂ)‖ := norm_add_le _ _
      _ ≤ (‖log s‖ / 200 + 202) + 3 := by
        gcongr
        exact complex_log_pi_norm_le_three
      _ ≤ ‖log s‖ / 100 := by nlinarith
  have hlogsnonneg : 0 ≤ Real.log ‖s‖ := by
    have : (1 : ℝ) ≤ ‖s‖ := by linarith
    exact Real.log_nonneg this
  have hlogParameterUpper : ‖log s‖ ≤ ‖s‖ / 50000 := by
    calc
      ‖log s‖ ≤ |(log s).re| + |(log s).im| :=
        Complex.norm_le_abs_re_add_abs_im _
      _ = |Real.log ‖s‖| + |s.arg| := by rw [Complex.log_re, Complex.log_im]
      _ ≤ Real.log ‖s‖ + 1 / 100 := by
        rw [abs_of_nonneg hlogsnonneg]
        gcongr
        exact hangle.le
      _ ≤ (‖s‖ / 100000 + 99998) + 1 / 100 := by
        gcongr
        exact real_log_le_div_hundredThousand_add hnormpos
      _ ≤ ‖s‖ / 50000 := by nlinarith
  have hcenterNorm : ‖saddleComparisonCenter s‖ ≤ ‖s‖ / 10000 := by
    calc
      ‖saddleComparisonCenter s‖ ≤ ‖log s‖ +
          ‖log (log s) + log (Real.pi : ℂ)‖ := by
        unfold saddleComparisonCenter
        have hid : log s - log (log s) - log (Real.pi : ℂ) =
            log s - (log (log s) + log (Real.pi : ℂ)) := by ring
        rw [hid]
        exact norm_sub_le _ _
      _ ≤ ‖log s‖ + ‖log s‖ / 100 := by gcongr
      _ ≤ ‖s‖ / 50000 + (‖s‖ / 50000) / 100 := by gcongr
      _ ≤ ‖s‖ / 10000 := by
        have := norm_nonneg s
        nlinarith
  have hcenterRatio : ‖saddleComparisonCenter s / s‖ ≤ 1 / 10000 := by
    rw [norm_div]
    apply (div_le_iff₀ hnormpos).2
    rw [div_eq_mul_inv] at hcenterNorm
    simpa [mul_comm] using hcenterNorm
  have hinverse : ‖(1 : ℂ) / s‖ ≤ 1 / 1000 := by
    rw [norm_div, norm_one, one_div]
    rw [inv_le_comm₀ hnormpos (by norm_num : (0 : ℝ) < 1 / 1000)]
    norm_num
    linarith
  exact
    { parameter_ne_zero := hsne
      logParameter_norm_lower := hwlower.le.trans' (by norm_num)
      logCorrection_le := hcorrection
      center_parameter_ratio_le := hcenterRatio
      parameter_inverse_le := hinverse }

theorem isOpen_leanSaddleSector : IsOpen leanSaddleSector := by
  rw [isOpen_iff_mem_nhds]
  intro s hs
  rcases hs with ⟨hradial, hangle⟩
  have hnormpos : 0 < ‖s‖ :=
    (Real.exp_pos leanSaddleCutoff).trans hradial
  have hsne : s ≠ 0 := norm_pos_iff.mp hnormpos
  have hargSmall : |s.arg| < Real.pi / 2 :=
    hangle.trans saddleProofAngle_lt_pi_div_two
  have hsre : 0 < s.re :=
    (Complex.abs_arg_lt_pi_div_two_iff.mp hargSmall).resolve_right hsne
  have hslit : s ∈ slitPlane := Or.inl hsre
  have hradialN : {z : ℂ | Real.exp leanSaddleCutoff < ‖z‖} ∈ 𝓝 s :=
    continuous_norm.continuousAt (Ioi_mem_nhds hradial)
  have hangleN : {z : ℂ | |z.arg| < saddleProofAngle} ∈ 𝓝 s :=
    (Complex.continuousAt_arg hslit).abs (Iio_mem_nhds hangle)
  exact inter_mem hradialN hangleN

theorem continuousAt_saddleComparisonCenter
    {s : ℂ} (hs : s ∈ leanSaddleSector) :
    ContinuousAt saddleComparisonCenter s := by
  have hquant := leanSaddleSector_quantitative hs
  have hargSmall : |s.arg| < Real.pi / 2 :=
    hs.2.trans saddleProofAngle_lt_pi_div_two
  have hsre : 0 < s.re :=
    (Complex.abs_arg_lt_pi_div_two_iff.mp hargSmall).resolve_right
      hquant.parameter_ne_zero
  have hslit : s ∈ slitPlane := Or.inl hsre
  have hlogs : ContinuousAt log s :=
    (Complex.differentiableAt_log hslit).continuousAt
  have hwre : (log s).re = Real.log ‖s‖ := Complex.log_re s
  have hnormpos : 0 < ‖s‖ := norm_pos_iff.mpr hquant.parameter_ne_zero
  have hlogradial : leanSaddleCutoff < Real.log ‖s‖ :=
    (Real.lt_log_iff_exp_lt hnormpos).2 hs.1
  have hwrepos : 0 < (log s).re := by
    rw [hwre]
    have hcutpos : (0 : ℝ) < leanSaddleCutoff := by norm_num [leanSaddleCutoff]
    exact hcutpos.trans hlogradial
  have hwslit : log s ∈ slitPlane := Or.inl hwrepos
  unfold saddleComparisonCenter
  exact hlogs.sub ((Complex.differentiableAt_log hwslit).continuousAt.comp hlogs) |>.sub_const _

theorem quantitativeSaddleBranch_dist_center_le
    {s : ℂ} (hs : s ∈ quantitativeSaddleDomain) :
    dist (quantitativeSaddleBranch s) (saddleComparisonCenter s) ≤ 11 / 750 := by
  change SaddleQuantitativeInput s at hs
  have hspec := quantitativeSaddleBranch_spec hs
  have hfixed : IsFixedPt (saddleNewtonMap s) (quantitativeSaddleBranch s) :=
    (saddleNewtonMap_fixed_iff hs.parameter_ne_zero).2 hspec.2.1
  have hcenter : saddleComparisonCenter s ∈
      Metric.closedBall (saddleComparisonCenter s) (1 / 20) := by
    simp only [Metric.mem_closedBall, dist_self]
    norm_num
  have hlip := (saddleNewton_lipschitzOn_disc hs).dist_le_mul
    (quantitativeSaddleBranch s) hspec.1 (saddleComparisonCenter s) hcenter
  have hresidual : dist (saddleNewtonMap s (saddleComparisonCenter s))
      (saddleComparisonCenter s) ≤ 11 / 1000 := by
    rw [dist_eq]
    calc
      ‖saddleNewtonMap s (saddleComparisonCenter s) - saddleComparisonCenter s‖ =
          ‖sectorialSaddleEquation s (saddleComparisonCenter s) / s‖ := by
        unfold saddleNewtonMap
        rw [show saddleComparisonCenter s -
            sectorialSaddleEquation s (saddleComparisonCenter s) / s -
              saddleComparisonCenter s =
            -(sectorialSaddleEquation s (saddleComparisonCenter s) / s) by ring,
          norm_neg]
      _ ≤ 11 / 1000 := saddleComparisonCenter_residual_norm_le hs
  have htriangle := dist_triangle (quantitativeSaddleBranch s)
    (saddleNewtonMap s (saddleComparisonCenter s)) (saddleComparisonCenter s)
  rw [hfixed] at hlip
  have hbound : dist (quantitativeSaddleBranch s) (saddleComparisonCenter s) ≤
      (1 / 4 : ℝ) * dist (quantitativeSaddleBranch s)
        (saddleComparisonCenter s) + 11 / 1000 := by
    calc
      dist (quantitativeSaddleBranch s) (saddleComparisonCenter s) ≤
          dist (quantitativeSaddleBranch s)
              (saddleNewtonMap s (saddleComparisonCenter s)) +
            dist (saddleNewtonMap s (saddleComparisonCenter s))
              (saddleComparisonCenter s) := htriangle
      _ ≤ (1 / 4 : ℝ) * dist (quantitativeSaddleBranch s)
            (saddleComparisonCenter s) + 11 / 1000 := by
          simpa only [NNReal.coe_div, NNReal.coe_one, NNReal.coe_ofNat] using
            add_le_add hlip hresidual
  nlinarith

theorem quantitativeSaddleBranch_dist_center_lt
    {s : ℂ} (hs : s ∈ quantitativeSaddleDomain) :
    dist (quantitativeSaddleBranch s) (saddleComparisonCenter s) < 1 / 20 := by
  have h := quantitativeSaddleBranch_dist_center_le hs
  norm_num at h ⊢
  linarith

/-- On the fixed outer sector the selected branch is holomorphic, with the
exact implicit derivative `L/Q`. -/
theorem hasDerivAt_quantitativeSaddleBranch
    {s : ℂ} (hs : s ∈ leanSaddleSector) :
    HasDerivAt quantitativeSaddleBranch
      (quantitativeSaddleBranch s /
        sectorialSaddleCurvature s (quantitativeSaddleBranch s)) s := by
  have hsinput : SaddleQuantitativeInput s := leanSaddleSector_quantitative hs
  have hsq : s ∈ quantitativeSaddleDomain := hsinput
  let L : ℂ := quantitativeSaddleBranch s
  have hspec := quantitativeSaddleBranch_spec hsq
  have hroot : sectorialSaddleEquation s L = 0 := hspec.2.1
  have hmap : saddleParameterMap L = s := by
    unfold sectorialSaddleEquation at hroot
    exact eq_of_sub_eq_zero hroot
  have hcurvature : sectorialSaddleCurvature s L ≠ 0 :=
    quantitativeSaddleBranch_curvature_ne_zero hsq
  let derivative : ℂ :=
    (Real.pi : ℂ) * exp L * (1 + L) + 3 / 4
  have hderivative : derivative ≠ 0 := by
    exact saddle_derivative_ne_zero hroot hcurvature
  have hstrict : HasStrictDerivAt saddleParameterMap derivative L := by
    exact hasStrictDerivAt_saddleParameterMap L
  let g : ℂ → ℂ :=
    hstrict.localInverse saddleParameterMap derivative L hderivative
  have hgderiv : HasStrictDerivAt g derivative⁻¹ s := by
    simpa only [g, hmap] using hstrict.to_localInverse hderivative
  have hgs : g s = L := by
    have hleft := hstrict.eventually_left_inverse hderivative
    have hleftAt := hleft.self_of_nhds
    simpa only [g, hmap] using hleftAt
  have hright : ∀ᶠ y in 𝓝 s, saddleParameterMap (g y) = y := by
    simpa only [g, hmap] using hstrict.eventually_right_inverse hderivative
  have hsector : leanSaddleSector ∈ 𝓝 s :=
    isOpen_leanSaddleSector.mem_nhds hs
  have hcenterContinuous : ContinuousAt saddleComparisonCenter s :=
    continuousAt_saddleComparisonCenter hs
  have hdistContinuous : ContinuousAt
      (fun y => dist (g y) (saddleComparisonCenter y)) s :=
    hgderiv.hasDerivAt.continuousAt.dist hcenterContinuous
  have hdistAt : dist (g s) (saddleComparisonCenter s) < 1 / 20 := by
    rw [hgs]
    exact quantitativeSaddleBranch_dist_center_lt hsq
  have hdist : ∀ᶠ y in 𝓝 s,
      dist (g y) (saddleComparisonCenter y) < 1 / 20 :=
    hdistContinuous (Iio_mem_nhds hdistAt)
  have hbranchEq : quantitativeSaddleBranch =ᶠ[𝓝 s] g := by
    filter_upwards [hsector, hright, hdist] with y hysector hyright hydist
    have hyinput : SaddleQuantitativeInput y := leanSaddleSector_quantitative hysector
    have hyq : y ∈ quantitativeSaddleDomain := hyinput
    have hgmem : g y ∈ Metric.closedBall (saddleComparisonCenter y) (1 / 20) :=
      Metric.mem_closedBall.mpr hydist.le
    have hgroot : sectorialSaddleEquation y (g y) = 0 := by
      unfold sectorialSaddleEquation
      exact sub_eq_zero.mpr hyright
    exact ((quantitativeSaddleBranch_spec hyq).2.2 (g y) hgmem hgroot).symm
  have hbranchDeriv : HasDerivAt quantitativeSaddleBranch derivative⁻¹ s :=
    hgderiv.hasDerivAt.congr_of_eventuallyEq hbranchEq
  apply hbranchDeriv.congr_deriv
  have hcurvatureIdentity := saddle_derivative_mul_eq_curvature hroot
  change derivative⁻¹ = L / sectorialSaddleCurvature s L
  field_simp [hderivative, hcurvature]
  exact hcurvatureIdentity.symm

theorem quantitativeSaddleBranch_differentiableOn_leanSector :
    DifferentiableOn ℂ quantitativeSaddleBranch leanSaddleSector := by
  intro s hs
  exact (hasDerivAt_quantitativeSaddleBranch hs).differentiableAt.differentiableWithinAt

/-- The concrete T2 certificate on the full fixed outer sector. -/
noncomputable def leanSectorialSaddleCertificate :
    SectorialSaddleCertificate leanSaddleSector sectorialSaddleEquation
      sectorialSaddleCurvature where
  branch := quantitativeSaddleBranch
  admissible := fun s => Metric.closedBall (saddleComparisonCenter s) (1 / 20)
  branch_mem := by
    intro s hs
    exact (quantitativeSaddleBranch_spec (leanSaddleSector_quantitative hs)).1
  branch_differentiable := quantitativeSaddleBranch_differentiableOn_leanSector
  equation_zero := by
    intro s hs
    exact (quantitativeSaddleBranch_spec (leanSaddleSector_quantitative hs)).2.1
  root_unique := by
    intro s hs z hzmem hzroot
    exact (quantitativeSaddleBranch_spec (leanSaddleSector_quantitative hs)).2.2
      z hzmem hzroot
  curvature_ne_zero := by
    intro s hs
    exact quantitativeSaddleBranch_curvature_ne_zero (leanSaddleSector_quantitative hs)

end

end Zeta23.Research.JensenWedge
