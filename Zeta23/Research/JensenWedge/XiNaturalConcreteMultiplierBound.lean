import Zeta23.Research.JensenWedge.XiNaturalConcreteMultiplier

/-!
# Uniform control of the concrete xi multiplier

The exact six node values from `XiNaturalConcreteMultiplier` are combined
with the formal complex Hermite--Genocchi theorem.  The result is a uniform
bound for the logarithmic multiplier on a closed disc, derived solely from
the explicit sixth-residual rate.
-/

open Complex Metric Set

noncomputable section

namespace Zeta23.Research.JensenWedge

theorem analyticOnNhd_xiNaturalConcreteLogMultiplier_ball
    {n : ℕ} {L : ℝ} {y : BranchPoint} {R : ℝ}
    (hhalf : R < (n : ℝ) + 1 / 2)
    (hA : R < residualParameterA y n (1 / L))
    (hB : R < residualParameterB y n (1 / L))
    (hC : R < residualParameterC y n)
    (hD : R < residualParameterD y n (1 / L))
    (hsector : ∀ z ∈ Metric.ball (0 : ℂ) R,
      (n : ℂ) + z ∈ leanXiCoefficientSector) :
    AnalyticOnNhd ℂ (xiNaturalConcreteLogMultiplier n L y)
      (Metric.ball (0 : ℂ) R) := by
  intro z hz
  unfold xiNaturalConcreteLogMultiplier
  exact (analyticAt_xiNaturalActualLogExtension hhalf hz (hsector z hz)).sub
    (analyticAt_xiNaturalModelLogExtension hz hA hB hC hD)

/-- Six exact node values plus the actual sixth-residual estimate give a
uniform logarithmic multiplier bound on a closed disc. -/
theorem xiNaturalConcreteLogMultiplier_norm_le_of_radius
    {y : BranchPoint} (hy : InOuterParameterBox y)
    {n : ℕ} (hn : 8 ≤ n)
    (hnLarge : Real.exp (leanSaddleCutoff + 2) < (n : ℝ))
    {L : ℝ} (hL : 0 < L)
    (hL12 : 1 / L ≤ (1 : ℝ) / 12)
    (hLLog : 1 / L ≤ 2 / Real.log (n : ℝ))
    (hmap : exactXiParameterMap n L y = 0)
    {r : ℝ} (hr5 : 5 ≤ r)
    (hrInterior : r ≤ manuscriptInteriorCauchyRadius (n : ℝ))
    (h2rHalf : 2 * r < (n : ℝ) + 1 / 2)
    (h2rA : 2 * r < residualParameterA y n (1 / L))
    (h2rB : 2 * r < residualParameterB y n (1 / L))
    (h2rC : 2 * r < residualParameterC y n)
    (h2rD : 2 * r < residualParameterD y n (1 / L))
    {z : ℂ} (hz : z ∈ Metric.closedBall (0 : ℂ) r) :
    ‖xiNaturalConcreteLogMultiplier n L y z‖ ≤
      (xiNaturalConcreteSixthResidualRateConstant /
        ((n : ℝ) ^ 5 * Real.log (n : ℝ))) * (r + 5) ^ 6 / 720 := by
  have hrpos : 0 < r := lt_of_lt_of_le (by norm_num) hr5
  have hnpos : 0 < n := by omega
  have hsectorBall : ∀ w ∈ Metric.ball (0 : ℂ) (2 * r),
      (n : ℂ) + w ∈ leanXiCoefficientSector := by
    intro w hw
    have hwNorm : ‖w‖ < 2 * r := by simpa [Metric.mem_ball] using hw
    have hwOuter : (n : ℂ) + w ∈
        Metric.closedBall ((n : ℝ) : ℂ) (manuscriptCauchyRadius (n : ℝ)) := by
      rw [Metric.mem_closedBall]
      calc
        dist ((n : ℂ) + w) ((n : ℝ) : ℂ) = ‖w‖ := by
          rw [dist_eq_norm]
          congr 1
          push_cast
          ring
        _ ≤ manuscriptCauchyRadius (n : ℝ) :=
          hwNorm.le.trans (by
            unfold manuscriptInteriorCauchyRadius at hrInterior
            unfold manuscriptCauchyRadius
            linarith)
    exact manuscriptCauchy_closedBall_subset_sector hnLarge hwOuter
  have hanalytic := analyticOnNhd_xiNaturalConcreteLogMultiplier_ball
    h2rHalf h2rA h2rB h2rC h2rD hsectorBall
  let derivs : ℕ → ℂ → ℂ := fun q =>
    iteratedDeriv q (xiNaturalConcreteLogMultiplier n L y)
  have hderiv : ∀ q w, w ∈ Metric.ball (0 : ℂ) (2 * r) →
      HasDerivAt (derivs q) (derivs (q + 1) w) w := by
    intro q w hw
    have h := (hanalytic.iterated_deriv q) w hw
    change HasDerivAt
      (iteratedDeriv q (xiNaturalConcreteLogMultiplier n L y))
      (iteratedDeriv (q + 1) (xiNaturalConcreteLogMultiplier n L y) w) w
    rw [iteratedDeriv_succ, iteratedDeriv_eq_iterate]
    exact h.differentiableAt.hasDerivAt
  have hcont : ∀ q, ContinuousOn (derivs q)
      (Metric.ball (0 : ℂ) (2 * r)) := by
    intro q
    simpa only [derivs, iteratedDeriv_eq_iterate] using
      (hanalytic.iterated_deriv q).continuousOn
  have hsectorNodes : ∀ j : ℕ, j ≤ 5 →
      ((n + j : ℕ) : ℂ) ∈ leanXiCoefficientSector := by
    intro j hj
    have hjBall : (j : ℂ) ∈ Metric.ball (0 : ℂ) (2 * r) := by
      rw [Metric.mem_ball, dist_zero_right, Complex.norm_natCast]
      have hjR : (j : ℝ) ≤ 5 := by exact_mod_cast hj
      nlinarith
    simpa only [Nat.cast_add] using hsectorBall (j : ℂ) hjBall
  have hzeroFin := xiNaturalConcreteLogMultiplier_six_nodes hnpos hL hy hL12
    hmap hsectorNodes
  have hzero : derivs 0 0 = 0 ∧ derivs 0 1 = 0 ∧ derivs 0 2 = 0 ∧
      derivs 0 3 = 0 ∧ derivs 0 4 = 0 ∧ derivs 0 5 = 0 := by
    change xiNaturalConcreteLogMultiplier n L y 0 = 0 ∧
      xiNaturalConcreteLogMultiplier n L y 1 = 0 ∧
      xiNaturalConcreteLogMultiplier n L y 2 = 0 ∧
      xiNaturalConcreteLogMultiplier n L y 3 = 0 ∧
      xiNaturalConcreteLogMultiplier n L y 4 = 0 ∧
      xiNaturalConcreteLogMultiplier n L y 5 = 0
    constructor
    · simpa using hzeroFin (0 : Fin 6)
    constructor
    · simpa using hzeroFin (1 : Fin 6)
    constructor
    · simpa using hzeroFin (2 : Fin 6)
    constructor
    · simpa using hzeroFin (3 : Fin 6)
    constructor
    · simpa using hzeroFin (4 : Fin 6)
    · simpa using hzeroFin (5 : Fin 6)
  have hsU : Metric.closedBall (0 : ℂ) r ⊆ Metric.ball (0 : ℂ) (2 * r) := by
    intro w hw
    rw [Metric.mem_closedBall] at hw
    rw [Metric.mem_ball]
    linarith
  have hbound : ∀ w ∈ Metric.closedBall (0 : ℂ) r,
      ‖derivs 6 w‖ ≤ xiNaturalConcreteSixthResidualRateConstant /
        ((n : ℝ) ^ 5 * Real.log (n : ℝ)) := by
    intro w hw
    have hwNorm : ‖w‖ ≤ r := by simpa [Metric.mem_closedBall] using hw
    have hwRe : -(n : ℝ) / 2 ≤ w.re := by
      have hre : -‖w‖ ≤ w.re := neg_le_of_abs_le (Complex.abs_re_le_norm w)
      unfold manuscriptInteriorCauchyRadius at hrInterior
      have hnR : (0 : ℝ) < n := by exact_mod_cast hnpos
      linarith
    exact xiNaturalConcreteLogMultiplier_sixth_norm_le hy hn hnLarge hL hL12
      hLLog (hsU hw) (hwNorm.trans hrInterior) hwRe
      (hsectorBall w (hsU hw)) h2rHalf h2rA h2rB h2rC h2rD
  have hnodes : ‖z‖ ≤ r + 5 ∧ ‖z - 1‖ ≤ r + 5 ∧
      ‖z - 2‖ ≤ r + 5 ∧ ‖z - 3‖ ≤ r + 5 ∧
      ‖z - 4‖ ≤ r + 5 ∧ ‖z - 5‖ ≤ r + 5 := by
    have hzNorm : ‖z‖ ≤ r := by simpa [Metric.mem_closedBall] using hz
    constructor
    · linarith
    constructor
    · calc
        ‖z - 1‖ ≤ ‖z‖ + ‖(1 : ℂ)‖ := norm_sub_le z (1 : ℂ)
        _ ≤ r + 5 := by norm_num; linarith
    constructor
    · calc
        ‖z - 2‖ ≤ ‖z‖ + ‖(2 : ℂ)‖ := norm_sub_le z (2 : ℂ)
        _ ≤ r + 5 := by norm_num; linarith
    constructor
    · calc
        ‖z - 3‖ ≤ ‖z‖ + ‖(3 : ℂ)‖ := norm_sub_le z (3 : ℂ)
        _ ≤ r + 5 := by norm_num; linarith
    constructor
    · calc
        ‖z - 4‖ ≤ ‖z‖ + ‖(4 : ℂ)‖ := norm_sub_le z (4 : ℂ)
        _ ≤ r + 5 := by norm_num; linarith
    · calc
        ‖z - 5‖ ≤ ‖z‖ + ‖(5 : ℂ)‖ := norm_sub_le z (5 : ℂ)
        _ ≤ r + 5 := by norm_num; linarith
  have hM : 0 ≤ xiNaturalConcreteSixthResidualRateConstant /
      ((n : ℝ) ^ 5 * Real.log (n : ℝ)) := by
    have hlog : 0 < Real.log (n : ℝ) := by
      apply Real.log_pos
      exact_mod_cast (show 1 < n by omega)
    have hconstant : 0 ≤ xiNaturalConcreteSixthResidualRateConstant := by
      norm_num [xiNaturalConcreteSixthResidualRateConstant,
        manuscriptSixthResidualRateConstant,
        xiNaturalMainCorrectionSixthRateConstant,
        manuscriptSixthResidualCauchyConstant,
        manuscriptSixthResidualBCConstant,
        manuscriptSixthResidualDConstant,
        manuscriptSixthResidualAConstant, Nat.factorial]
    exact div_nonneg hconstant (mul_nonneg (by positivity) hlog.le)
  simpa only [derivs, iteratedDeriv_zero] using
    hermiteGenocchiSix_remainder_bound_on
      (Metric.ball (0 : ℂ) (2 * r)) (Metric.closedBall (0 : ℂ) r)
      isOpen_ball (convex_ball (0 : ℂ) (2 * r)) derivs hM (by linarith)
      hderiv hcont hzero (convex_closedBall (0 : ℂ) r) hsU
      (by simpa [Metric.mem_closedBall] using hrpos.le)
      (by norm_num [Metric.mem_closedBall, dist_zero_right]; linarith)
      (by norm_num [Metric.mem_closedBall, dist_zero_right]; linarith)
      (by norm_num [Metric.mem_closedBall, dist_zero_right]; linarith)
      (by norm_num [Metric.mem_closedBall, dist_zero_right]; linarith)
      (by norm_num [Metric.mem_closedBall, dist_zero_right]; linarith)
      hz hbound hnodes

/-- If the explicit Hermite--Genocchi budget is below one half, the concrete
coefficient multiplier lies in the open unit disc around `1`. -/
theorem xiNaturalConcreteMultiplier_sub_one_norm_lt_one_of_radius
    {y : BranchPoint} (hy : InOuterParameterBox y)
    {n : ℕ} (hn : 8 ≤ n)
    (hnLarge : Real.exp (leanSaddleCutoff + 2) < (n : ℝ))
    {L : ℝ} (hL : 0 < L)
    (hL12 : 1 / L ≤ (1 : ℝ) / 12)
    (hLLog : 1 / L ≤ 2 / Real.log (n : ℝ))
    (hmap : exactXiParameterMap n L y = 0)
    {r : ℝ} (hr5 : 5 ≤ r)
    (hrInterior : r ≤ manuscriptInteriorCauchyRadius (n : ℝ))
    (h2rHalf : 2 * r < (n : ℝ) + 1 / 2)
    (h2rA : 2 * r < residualParameterA y n (1 / L))
    (h2rB : 2 * r < residualParameterB y n (1 / L))
    (h2rC : 2 * r < residualParameterC y n)
    (h2rD : 2 * r < residualParameterD y n (1 / L))
    (hbudget :
      (xiNaturalConcreteSixthResidualRateConstant /
        ((n : ℝ) ^ 5 * Real.log (n : ℝ))) * (r + 5) ^ 6 / 720 < 1 / 2)
    {z : ℂ} (hz : z ∈ Metric.closedBall (0 : ℂ) r) :
    ‖xiNaturalConcreteMultiplier n L y z - 1‖ < 1 := by
  have hlog := xiNaturalConcreteLogMultiplier_norm_le_of_radius hy hn hnLarge
    hL hL12 hLLog hmap hr5 hrInterior h2rHalf h2rA h2rB h2rC h2rD hz
  have hlogOne : ‖xiNaturalConcreteLogMultiplier n L y z‖ ≤ 1 :=
    hlog.trans (le_of_lt (hbudget.trans (by norm_num)))
  unfold xiNaturalConcreteMultiplier
  exact (Complex.norm_exp_sub_one_le hlogOne).trans_lt (by linarith)

end Zeta23.Research.JensenWedge
