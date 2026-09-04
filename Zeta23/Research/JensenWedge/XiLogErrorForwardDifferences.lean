import Zeta23.Research.JensenWedge.LocalForwardDifferenceCalculus
import Zeta23.Research.JensenWedge.XiLogError

/-!
# Forward differences of the xi logarithmic error

This module instantiates the local repeated-FTC adapter for the actual
holomorphic error in `Log M_z`.  It proves, without a global analyticity
hypothesis, that every forward difference of order two through five is
controlled by the corresponding Cauchy derivative estimate.
-/

namespace Zeta23.Research.JensenWedge

open Complex Set

noncomputable section

theorem manuscriptCauchy_large_tenThousand
    {x : ℝ} (hx : Real.exp (leanSaddleCutoff + 2) < x) :
    10000 < x := by
  have hnonneg : (0 : ℝ) ≤ leanSaddleCutoff + 2 := by
    norm_num [leanSaddleCutoff]
  have hpow := Real.pow_div_factorial_le_exp
    (leanSaddleCutoff + 2) hnonneg 2
  have : (10000 : ℝ) < Real.exp (leanSaddleCutoff + 2) := by
    norm_num [leanSaddleCutoff, Nat.factorial] at hpow ⊢
    nlinarith
  exact this.trans hx

theorem manuscriptXiLogRelativeError_analyticOnNhd :
    AnalyticOnNhd ℂ manuscriptXiLogRelativeError leanXiCoefficientSector :=
  differentiableOn_manuscriptXiLogRelativeError.analyticOnNhd
    isOpen_leanXiCoefficientSector

theorem hasDerivAt_iteratedDeriv_manuscriptXiLogRelativeError
    (s : ℕ) {z : ℂ} (hz : z ∈ leanXiCoefficientSector) :
    HasDerivAt (iteratedDeriv s manuscriptXiLogRelativeError)
      (iteratedDeriv (s + 1) manuscriptXiLogRelativeError z) z := by
  have h :=
    (manuscriptXiLogRelativeError_analyticOnNhd.iterated_deriv s) z hz
  rw [iteratedDeriv_succ, iteratedDeriv_eq_iterate]
  exact h.differentiableAt.hasDerivAt

/-- Every real point from `n` through `n+5` lies in the inner Cauchy disc.
This is the explicit domain bridge from the integer forward differences to
the holomorphic coefficient sector. -/
theorem nat_five_interval_mem_manuscriptInteriorDisc
    {n : ℕ} (hn : Real.exp (leanSaddleCutoff + 2) < (n : ℝ))
    {y : ℝ} (hy : y ∈ Set.Icc (n : ℝ) ((n : ℝ) + 5)) :
    (y : ℂ) ∈ Metric.closedBall (n : ℂ)
      (manuscriptInteriorCauchyRadius (n : ℝ)) := by
  have hnTen : (10000 : ℝ) < n := manuscriptCauchy_large_tenThousand hn
  have hdiff : 0 ≤ y - (n : ℝ) := sub_nonneg.mpr hy.1
  have hupper : y - (n : ℝ) ≤ 5 := by linarith [hy.2]
  have hradius : 5 ≤ (n : ℝ) / 2000 := by linarith
  rw [Metric.mem_closedBall, dist_eq_norm]
  change ‖(y : ℂ) - (n : ℂ)‖ ≤ manuscriptInteriorCauchyRadius (n : ℝ)
  rw [show (n : ℂ) = ((n : ℝ) : ℂ) by norm_num]
  rw [← ofReal_sub, norm_real, Real.norm_eq_abs, abs_of_nonneg hdiff]
  simpa only [manuscriptInteriorCauchyRadius] using hupper.trans hradius

/-- The logarithmic relative error contributes at most its local Cauchy
derivative bound to every order-two-through-five unit forward difference.
There is no factorial beyond the one already present in Cauchy's estimate.
-/
theorem manuscriptXiLogRelativeError_forwardDiff_bound
    {n q : ℕ} (hn : Real.exp (leanSaddleCutoff + 2) < (n : ℝ))
    (hq5 : q ≤ 5) :
    ‖complexForwardDiff q manuscriptXiLogRelativeError (n : ℂ)‖ ≤
      q.factorial * ((3 / 2 : ℝ) * manuscriptCauchyEpsilon (n : ℝ)) /
        manuscriptInteriorCauchyRadius (n : ℝ) ^ q := by
  let derivs : ℕ → ℂ → ℂ := fun s =>
    iteratedDeriv s manuscriptXiLogRelativeError
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
    exact hasDerivAt_iteratedDeriv_manuscriptXiLogRelativeError s hySector
  have hbound : ∀ y,
      y ∈ Set.Icc (n : ℝ) ((n : ℝ) + (q : ℝ)) →
      ‖derivs (0 + q) (y : ℂ) - 0‖ ≤
        q.factorial * ((3 / 2 : ℝ) * manuscriptCauchyEpsilon (n : ℝ)) /
          manuscriptInteriorCauchyRadius (n : ℝ) ^ q := by
    intro y hy
    have hyInner := nat_five_interval_mem_manuscriptInteriorDisc hn
      (hinterval hy)
    have hq6 : q ≤ 6 := hq5.trans (by norm_num)
    simpa only [derivs, zero_add, sub_zero] using
      manuscriptXiLogRelativeError_derivatives_through_six_on_half_disc
        hn hyInner q hq6
  rw [show (n : ℂ) = ((n : ℝ) : ℂ) by norm_num]
  simpa only [derivs, iteratedDeriv_zero, sub_zero] using
    norm_complexForwardDiff_sub_constant_le_on_real_interval
      derivs q 0 (n : ℝ) 0 hderiv hbound

end

end Zeta23.Research.JensenWedge
