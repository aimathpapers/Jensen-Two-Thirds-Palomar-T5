import Zeta23.Research.JensenWedge.XiNaturalLogError
import Zeta23.Research.JensenWedge.XiLogErrorForwardDifferences

/-!
# Cauchy and forward-difference transport for the natural xi log error

The natural auxiliary factorization removes the exact Gamma quotient and
therefore has the sharper moment-only error.  This module transports that
specific logarithmic error through the same proportional discs as the
coefficient theorem, then applies the localized repeated-FTC adapter to the
integer nodes used by the four xi saddle coordinates.
-/

namespace Zeta23.Research.JensenWedge

open Complex Set

noncomputable section

def naturalXiCauchyEpsilon (x : ℝ) : ℝ :=
  (100 * fullThetaMomentErrorCoefficient) * Real.log (3 * x) / x

theorem complexXiNaturalAuxiliaryRelativeError_cauchy_norm_le
    {x : ℝ} (hx : Real.exp (leanSaddleCutoff + 2) < x)
    {z : ℂ} (hz : z ∈ Metric.closedBall (x : ℂ) (manuscriptCauchyRadius x)) :
    ‖complexXiNaturalAuxiliaryRelativeError z‖ ≤
      naturalXiCauchyEpsilon x := by
  have hzSector := manuscriptCauchy_closedBall_subset_sector hx hz
  have hbase := complexXiNaturalAuxiliaryRelativeError_norm_le hzSector
  rcases manuscriptCauchy_shifted_norm_bounds hx hz with ⟨hNlower, hNupper⟩
  let N : ℂ := coefficientMellinParameter z
  let C : ℝ := 100 * fullThetaMomentErrorCoefficient
  have hxpos : 0 < x := (manuscriptCauchy_large_properties hx).2.2.2
  have hNpos : 0 < ‖N‖ := hxpos.trans_le hNlower
  have hlogUpper : Real.log ‖N‖ ≤ Real.log (3 * x) :=
    Real.log_le_log hNpos hNupper
  have hlogNonneg : 0 ≤ Real.log ‖N‖ := by
    apply Real.log_nonneg
    have hxThousand := (manuscriptCauchy_large_properties hx).1
    linarith
  have hlogThreeNonneg : 0 ≤ Real.log (3 * x) := by
    apply Real.log_nonneg
    have hxThousand := (manuscriptCauchy_large_properties hx).1
    nlinarith
  have hC : 0 ≤ C := by
    norm_num [C, fullThetaMomentErrorCoefficient]
  change ‖complexXiNaturalAuxiliaryRelativeError z‖ ≤
    C * Real.log (3 * x) / x
  calc
    ‖complexXiNaturalAuxiliaryRelativeError z‖ ≤
        C * Real.log ‖N‖ / ‖N‖ := by
      simpa only [C, N] using hbase
    _ ≤ C * Real.log (3 * x) / ‖N‖ := by
      apply div_le_div_of_nonneg_right _ (norm_nonneg N)
      exact mul_le_mul_of_nonneg_left hlogUpper hC
    _ ≤ C * Real.log (3 * x) / x := by
      exact div_le_div_of_nonneg_left
        (mul_nonneg hC hlogThreeNonneg) hxpos hNlower

/-- Uniform Cauchy transport of the natural logarithmic error throughout
the inner half-radius disc, at every order needed by the certificate. -/
theorem complexXiNaturalAuxiliaryLogError_derivatives_through_six_on_half_disc
    {x : ℝ} (hx : Real.exp (leanSaddleCutoff + 2) < x)
    {z : ℂ}
    (hz : z ∈ Metric.closedBall (x : ℂ) (manuscriptInteriorCauchyRadius x)) :
    ∀ j ≤ 6,
      ‖iteratedDeriv j complexXiNaturalAuxiliaryLogError z‖ ≤
        j.factorial * ((3 / 2 : ℝ) * naturalXiCauchyEpsilon x) /
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
  have hdiff : DifferentiableOn ℂ complexXiNaturalAuxiliaryLogError D :=
    differentiableOn_complexXiNaturalAuxiliaryLogError.mono hDsector
  have hdisc : DiffContOnCl ℂ complexXiNaturalAuxiliaryLogError
      (Metric.ball z (manuscriptInteriorCauchyRadius x)) :=
    hdiff.diffContOnCl_ball Subset.rfl
  intro j _hj
  apply Complex.norm_iteratedDeriv_le_of_forall_mem_sphere_norm_le
    j hradius hdisc
  intro w hw
  have hwD : w ∈ D := Metric.sphere_subset_closedBall hw
  calc
    ‖complexXiNaturalAuxiliaryLogError w‖ ≤
        (3 / 2 : ℝ) * ‖complexXiNaturalAuxiliaryRelativeError w‖ :=
      complexXiNaturalAuxiliaryLogError_norm_le (hDsector hwD)
    _ ≤ (3 / 2 : ℝ) * naturalXiCauchyEpsilon x := by
      gcongr
      exact complexXiNaturalAuxiliaryRelativeError_cauchy_norm_le hx
        (hDinner hwD)

theorem complexXiNaturalAuxiliaryLogError_analyticOnNhd :
    AnalyticOnNhd ℂ complexXiNaturalAuxiliaryLogError
      leanXiCoefficientSector :=
  differentiableOn_complexXiNaturalAuxiliaryLogError.analyticOnNhd
    isOpen_leanXiCoefficientSector

theorem hasDerivAt_iteratedDeriv_complexXiNaturalAuxiliaryLogError
    (s : ℕ) {z : ℂ} (hz : z ∈ leanXiCoefficientSector) :
    HasDerivAt (iteratedDeriv s complexXiNaturalAuxiliaryLogError)
      (iteratedDeriv (s + 1) complexXiNaturalAuxiliaryLogError z) z := by
  have h :=
    (complexXiNaturalAuxiliaryLogError_analyticOnNhd.iterated_deriv s) z hz
  rw [iteratedDeriv_succ, iteratedDeriv_eq_iterate]
  exact h.differentiableAt.hasDerivAt

/-- The natural log error contributes at most its local Cauchy derivative
bound to every forward difference through order five. -/
theorem complexXiNaturalAuxiliaryLogError_forwardDiff_bound
    {n q : ℕ} (hn : Real.exp (leanSaddleCutoff + 2) < (n : ℝ))
    (hq5 : q ≤ 5) :
    ‖complexForwardDiff q complexXiNaturalAuxiliaryLogError (n : ℂ)‖ ≤
      q.factorial * ((3 / 2 : ℝ) * naturalXiCauchyEpsilon (n : ℝ)) /
        manuscriptInteriorCauchyRadius (n : ℝ) ^ q := by
  let derivs : ℕ → ℂ → ℂ := fun s =>
    iteratedDeriv s complexXiNaturalAuxiliaryLogError
  have hinterval : Set.Icc (n : ℝ) ((n : ℝ) + (q : ℝ)) ⊆
      Set.Icc (n : ℝ) ((n : ℝ) + 5) := by
    intro y hy
    constructor
    · exact hy.1
    · have hq5R : (q : ℝ) ≤ 5 := by exact_mod_cast hq5
      linarith [hy.2]
  have hderiv : ∀ s y,
      y ∈ Set.Icc (n : ℝ) ((n : ℝ) + (q : ℝ)) →
      HasDerivAt (derivs s) (derivs (s + 1) (y : ℂ)) (y : ℂ) := by
    intro s y hy
    have hyInner := nat_five_interval_mem_manuscriptInteriorDisc hn
      (hinterval hy)
    have hyOuter : (y : ℂ) ∈
        Metric.closedBall (n : ℂ) (manuscriptCauchyRadius (n : ℝ)) := by
      have hdist : dist (y : ℂ) (n : ℂ) ≤
          manuscriptInteriorCauchyRadius (n : ℝ) := hyInner
      have hradius : manuscriptInteriorCauchyRadius (n : ℝ) ≤
          manuscriptCauchyRadius (n : ℝ) := by
        unfold manuscriptInteriorCauchyRadius manuscriptCauchyRadius
        have hnpos : (0 : ℝ) < n :=
          (manuscriptCauchy_large_properties hn).2.2.2
        linarith
      exact hdist.trans hradius
    have hySector := manuscriptCauchy_closedBall_subset_sector hn hyOuter
    exact hasDerivAt_iteratedDeriv_complexXiNaturalAuxiliaryLogError s hySector
  have hbound : ∀ y,
      y ∈ Set.Icc (n : ℝ) ((n : ℝ) + (q : ℝ)) →
      ‖derivs (0 + q) (y : ℂ) - 0‖ ≤
        q.factorial * ((3 / 2 : ℝ) * naturalXiCauchyEpsilon (n : ℝ)) /
          manuscriptInteriorCauchyRadius (n : ℝ) ^ q := by
    intro y hy
    have hyInner := nat_five_interval_mem_manuscriptInteriorDisc hn
      (hinterval hy)
    have hq6 : q ≤ 6 := hq5.trans (by norm_num)
    simpa only [derivs, zero_add, sub_zero] using
      complexXiNaturalAuxiliaryLogError_derivatives_through_six_on_half_disc
        hn hyInner q hq6
  rw [show (n : ℂ) = ((n : ℝ) : ℂ) by norm_num]
  simpa only [derivs, iteratedDeriv_zero, sub_zero] using
    norm_complexForwardDiff_sub_constant_le_on_real_interval
      derivs q 0 (n : ℝ) 0 hderiv hbound

end

end Zeta23.Research.JensenWedge
