import Zeta23.Research.JensenWedge.RiemannXiJensen
import Mathlib.Analysis.SpecialFunctions.Complex.LogBounds

/-!
# Holomorphic logarithmic error for the xi auxiliary moment

The manuscript differentiates `h = Log M_z`, not the coefficient itself.
This module proves that the explicit coefficient relative error is already
smaller than one half on the fixed Lean sector, defines the principal
`Log (1 + error)` there, and transports that logarithmic error through six
derivatives on the paper's proportional Cauchy discs.
-/

namespace Zeta23.Research.JensenWedge

open Complex Set

noncomputable section

private theorem leanSaddleSector_norm_ge_ten_pow_eighty
    {s : ℂ} (hs : s ∈ leanSaddleSector) :
    (10 : ℝ) ^ 80 ≤ ‖s‖ := by
  have hpow := Real.pow_div_factorial_le_exp leanSaddleCutoff
    (show (0 : ℝ) ≤ leanSaddleCutoff by norm_num [leanSaddleCutoff]) 16
  have hcut : (10 : ℝ) ^ 80 ≤ Real.exp leanSaddleCutoff := by
    apply le_trans ?_ hpow
    norm_num [leanSaddleCutoff, Nat.factorial]
  exact hcut.trans hs.1.le

private theorem real_log_le_two_mul_div_ten_pow_forty
    {x : ℝ} (hx : 0 < x) (hlarge : (10 : ℝ) ^ 80 ≤ x) :
    Real.log x ≤ 2 * x / (10 : ℝ) ^ 40 := by
  let a : ℝ := (10 : ℝ) ^ 40
  have ha : 0 < a := by positivity
  have hxdiv : 0 < x / a := div_pos hx ha
  have hfactor : x = a * (x / a) := by field_simp
  have hloga := Real.log_le_sub_one_of_pos ha
  have hlogdiv := Real.log_le_sub_one_of_pos hxdiv
  have haa : a * a = (10 : ℝ) ^ 80 := by
    dsimp only [a]
    ring
  have ha_le : a ≤ x / a := by
    apply (le_div_iff₀ ha).2
    rw [haa]
    exact hlarge
  calc
    Real.log x = Real.log (a * (x / a)) := congrArg Real.log hfactor
    _ = Real.log a + Real.log (x / a) :=
      Real.log_mul ha.ne' hxdiv.ne'
    _ ≤ (a - 1) + (x / a - 1) := add_le_add hloga hlogdiv
    _ ≤ 2 * (x / a) := by linarith
    _ = 2 * x / (10 : ℝ) ^ 40 := by
      dsimp only [a]
      ring

/-- The enormous conservative saddle cutoff makes the entire displayed
coefficient-error envelope at most one half.  Exposing the rate estimate
separately lets Gamma-free auxiliary errors reuse the same cutoff audit. -/
theorem manuscriptXiCoefficientErrorRate_le_half
    {M : ℂ} (hM : M ∈ leanXiCoefficientSector) :
    manuscriptXiCoefficientErrorCoefficient *
        Real.log ‖coefficientMellinParameter M‖ /
          ‖coefficientMellinParameter M‖ ≤ 1 / 2 := by
  let N : ℂ := coefficientMellinParameter M
  let C : ℝ := manuscriptXiCoefficientErrorCoefficient
  have hN : N ∈ leanSaddleSector :=
    leanTwoShiftAdmissible_base (leanCoefficientSector_admissible hM.2)
  have hNlarge : (10 : ℝ) ^ 80 ≤ ‖N‖ :=
    leanSaddleSector_norm_ge_ten_pow_eighty hN
  have hNpos : 0 < ‖N‖ := by positivity
  have hlog : Real.log ‖N‖ ≤ 2 * ‖N‖ / (10 : ℝ) ^ 40 :=
    real_log_le_two_mul_div_ten_pow_forty hNpos hNlarge
  have hC : 0 ≤ C := by
    norm_num [C, manuscriptXiCoefficientErrorCoefficient,
      complexXiCoefficientErrorCoefficient, fullThetaMomentErrorCoefficient,
      Nat.factorial]
  change C * Real.log ‖N‖ / ‖N‖ ≤ (1 / 2 : ℝ)
  calc
    C * Real.log ‖N‖ / ‖N‖ ≤
        C * (2 * ‖N‖ / (10 : ℝ) ^ 40) / ‖N‖ := by
      exact div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_left hlog hC) hNpos.le
    _ = 2 * C / (10 : ℝ) ^ 40 := by
      field_simp [hNpos.ne']
    _ ≤ 1 / 2 := by
      norm_num [C, manuscriptXiCoefficientErrorCoefficient,
        complexXiCoefficientErrorCoefficient, fullThetaMomentErrorCoefficient,
        Nat.factorial]

/-- The enormous conservative saddle cutoff makes the fully explicit error
constant harmless: the relative error is at most one half everywhere on the
paired coefficient sector. -/
theorem manuscriptXiCoefficientRelativeError_norm_le_half
    {M : ℂ} (hM : M ∈ leanXiCoefficientSector) :
    ‖manuscriptXiCoefficientRelativeError M‖ ≤ 1 / 2 := by
  exact (manuscriptXiCoefficientRelativeError_norm_le hM).trans
    (manuscriptXiCoefficientErrorRate_le_half hM)

theorem one_add_manuscriptXiCoefficientRelativeError_ne_zero
    {M : ℂ} (hM : M ∈ leanXiCoefficientSector) :
    1 + manuscriptXiCoefficientRelativeError M ≠ 0 := by
  intro hzero
  have herr : manuscriptXiCoefficientRelativeError M = -1 := by
    linear_combination hzero
  have hhalf := manuscriptXiCoefficientRelativeError_norm_le_half hM
  rw [herr] at hhalf
  norm_num at hhalf

theorem one_add_manuscriptXiCoefficientRelativeError_re_pos
    {M : ℂ} (hM : M ∈ leanXiCoefficientSector) :
    0 < (1 + manuscriptXiCoefficientRelativeError M).re := by
  have hhalf := manuscriptXiCoefficientRelativeError_norm_le_half hM
  have habs := Complex.abs_re_le_norm
    (manuscriptXiCoefficientRelativeError M)
  rw [abs_le] at habs
  norm_num
  linarith

/-- The auxiliary moment is nonzero on the full paired coefficient sector,
so the logarithmic-derivative object used by the manuscript is legitimate.
-/
theorem complexXiAuxiliaryMoment_ne_zero
    {M : ℂ} (hM : M ∈ leanXiCoefficientSector) :
    complexXiAuxiliaryMoment M ≠ 0 := by
  rw [complexXiAuxiliaryMoment_manuscript_factorization hM]
  exact mul_ne_zero (manuscriptXiAuxiliaryMain_ne_zero hM)
    (one_add_manuscriptXiCoefficientRelativeError_ne_zero hM)

/-- The local logarithmic error in `Log M_z`.  Its argument lies in the open
right half-plane on the entire fixed sector, fixing the branch unambiguously.
-/
def manuscriptXiLogRelativeError (M : ℂ) : ℂ :=
  log (1 + manuscriptXiCoefficientRelativeError M)

theorem exp_manuscriptXiLogRelativeError
    {M : ℂ} (hM : M ∈ leanXiCoefficientSector) :
    exp (manuscriptXiLogRelativeError M) =
      1 + manuscriptXiCoefficientRelativeError M := by
  unfold manuscriptXiLogRelativeError
  exact exp_log (one_add_manuscriptXiCoefficientRelativeError_ne_zero hM)

theorem differentiableAt_manuscriptXiLogRelativeError
    {M : ℂ} (hM : M ∈ leanXiCoefficientSector) :
    DifferentiableAt ℂ manuscriptXiLogRelativeError M := by
  have hinner : DifferentiableAt ℂ
      (fun z => 1 + manuscriptXiCoefficientRelativeError z) M :=
    DifferentiableAt.add (differentiableAt_const _)
      (differentiableAt_manuscriptXiCoefficientRelativeError hM)
  have hslit : 1 + manuscriptXiCoefficientRelativeError M ∈ slitPlane :=
    Or.inl (one_add_manuscriptXiCoefficientRelativeError_re_pos hM)
  unfold manuscriptXiLogRelativeError
  exact (Complex.differentiableAt_log hslit).comp M hinner

theorem differentiableOn_manuscriptXiLogRelativeError :
    DifferentiableOn ℂ manuscriptXiLogRelativeError
      leanXiCoefficientSector := by
  intro M hM
  exact (differentiableAt_manuscriptXiLogRelativeError hM).differentiableWithinAt

theorem manuscriptXiLogRelativeError_norm_le
    {M : ℂ} (hM : M ∈ leanXiCoefficientSector) :
    ‖manuscriptXiLogRelativeError M‖ ≤
      (3 / 2 : ℝ) * ‖manuscriptXiCoefficientRelativeError M‖ := by
  unfold manuscriptXiLogRelativeError
  exact Complex.norm_log_one_add_half_le_self
    (manuscriptXiCoefficientRelativeError_norm_le_half hM)

/-- Cauchy transport for the actual logarithmic error entering
`h = Log M_z`, simultaneously through order six. -/
theorem manuscriptXiLogRelativeError_derivatives_through_six
    {x : ℝ} (hx : Real.exp (leanSaddleCutoff + 2) < x) :
    ∀ j ≤ 6,
      ‖iteratedDeriv j manuscriptXiLogRelativeError (x : ℂ)‖ ≤
        j.factorial * ((3 / 2 : ℝ) * manuscriptCauchyEpsilon x) /
          manuscriptCauchyRadius x ^ j := by
  have hxpos : 0 < x := (manuscriptCauchy_large_properties hx).2.2.2
  have hradius : 0 < manuscriptCauchyRadius x := by
    unfold manuscriptCauchyRadius
    exact div_pos hxpos (by norm_num)
  let D : Set ℂ := Metric.closedBall (x : ℂ) (manuscriptCauchyRadius x)
  have hD : D ⊆ leanXiCoefficientSector :=
    manuscriptCauchy_closedBall_subset_sector hx
  have hdiff : DifferentiableOn ℂ manuscriptXiLogRelativeError D :=
    differentiableOn_manuscriptXiLogRelativeError.mono hD
  have hdisc : DiffContOnCl ℂ manuscriptXiLogRelativeError
      (Metric.ball (x : ℂ) (manuscriptCauchyRadius x)) :=
    hdiff.diffContOnCl_ball Subset.rfl
  intro j _hj
  apply Complex.norm_iteratedDeriv_le_of_forall_mem_sphere_norm_le
    j hradius hdisc
  intro z hz
  have hzD : z ∈ D := Metric.sphere_subset_closedBall hz
  calc
    ‖manuscriptXiLogRelativeError z‖ ≤
        (3 / 2 : ℝ) * ‖manuscriptXiCoefficientRelativeError z‖ :=
      manuscriptXiLogRelativeError_norm_le (hD hzD)
    _ ≤ (3 / 2 : ℝ) * manuscriptCauchyEpsilon x := by
      gcongr
      exact manuscriptCauchy_error_norm_le hx hzD

/-- The inner radius used to make the Cauchy estimate uniform in a complex
neighborhood of the positive real center.  A disc of this radius about any
point in the corresponding inner closed ball stays in the original
`x / 1000` manuscript disc. -/
def manuscriptInteriorCauchyRadius (x : ℝ) : ℝ := x / 2000

/-- Two nested half-radius discs stay inside the original manuscript disc.
This is the missing geometry needed to transport the sixth logarithmic
derivative uniformly over the complex residual domain, rather than only at
the positive real center. -/
theorem manuscriptInterior_closedBall_subset_manuscriptDisc
    {x : ℝ} {z : ℂ}
    (hz : z ∈ Metric.closedBall (x : ℂ) (manuscriptInteriorCauchyRadius x)) :
    Metric.closedBall z (manuscriptInteriorCauchyRadius x) ⊆
      Metric.closedBall (x : ℂ) (manuscriptCauchyRadius x) := by
  intro w hw
  have hwz : dist w z ≤ x / 2000 := by
    simpa only [manuscriptInteriorCauchyRadius, Metric.mem_closedBall] using hw
  have hzx : dist z (x : ℂ) ≤ x / 2000 := by
    simpa only [manuscriptInteriorCauchyRadius, Metric.mem_closedBall] using hz
  have htriangle : dist w (x : ℂ) ≤ dist w z + dist z (x : ℂ) :=
    dist_triangle _ _ _
  have : dist w (x : ℂ) ≤ x / 1000 := by linarith
  simpa only [manuscriptCauchyRadius, Metric.mem_closedBall] using this

/-- Uniform Cauchy transport of the logarithmic xi error throughout the
half-radius complex disc.  This is the form consumed by the sixth-residual
estimate: every point `z` in the inner disc has all derivatives through
order six bounded using a second inner disc about `z`, while the values on
that second boundary are controlled on the original manuscript disc. -/
theorem manuscriptXiLogRelativeError_derivatives_through_six_on_half_disc
    {x : ℝ} (hx : Real.exp (leanSaddleCutoff + 2) < x)
    {z : ℂ}
    (hz : z ∈ Metric.closedBall (x : ℂ) (manuscriptInteriorCauchyRadius x)) :
    ∀ j ≤ 6,
      ‖iteratedDeriv j manuscriptXiLogRelativeError z‖ ≤
        j.factorial * ((3 / 2 : ℝ) * manuscriptCauchyEpsilon x) /
          manuscriptInteriorCauchyRadius x ^ j := by
  have hxpos : 0 < x := (manuscriptCauchy_large_properties hx).2.2.2
  have hradius : 0 < manuscriptInteriorCauchyRadius x := by
    unfold manuscriptInteriorCauchyRadius
    positivity
  let D : Set ℂ := Metric.closedBall z (manuscriptInteriorCauchyRadius x)
  have hDinner : D ⊆ Metric.closedBall (x : ℂ) (manuscriptCauchyRadius x) :=
    manuscriptInterior_closedBall_subset_manuscriptDisc hz
  have hDsector : D ⊆ leanXiCoefficientSector :=
    hDinner.trans (manuscriptCauchy_closedBall_subset_sector hx)
  have hdiff : DifferentiableOn ℂ manuscriptXiLogRelativeError D :=
    differentiableOn_manuscriptXiLogRelativeError.mono hDsector
  have hdisc : DiffContOnCl ℂ manuscriptXiLogRelativeError
      (Metric.ball z (manuscriptInteriorCauchyRadius x)) :=
    hdiff.diffContOnCl_ball Subset.rfl
  intro j _hj
  apply Complex.norm_iteratedDeriv_le_of_forall_mem_sphere_norm_le
    j hradius hdisc
  intro w hw
  have hwD : w ∈ D := Metric.sphere_subset_closedBall hw
  calc
    ‖manuscriptXiLogRelativeError w‖ ≤
        (3 / 2 : ℝ) * ‖manuscriptXiCoefficientRelativeError w‖ :=
      manuscriptXiLogRelativeError_norm_le (hDsector hwD)
    _ ≤ (3 / 2 : ℝ) * manuscriptCauchyEpsilon x := by
      gcongr
      exact manuscriptCauchy_error_norm_le hx (hDinner hwD)

end

end Zeta23.Research.JensenWedge
