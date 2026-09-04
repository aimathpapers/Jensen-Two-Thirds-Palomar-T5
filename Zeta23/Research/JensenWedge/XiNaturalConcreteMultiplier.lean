import Zeta23.Research.JensenWedge.XiNaturalCriticalRadius
import Zeta23.Research.JensenWedge.ComplexHermiteGenocchi
import Zeta23.Research.JensenWedge.XiNaturalMainCorrectionBounds
import Zeta23.GammaFacts.StirlingRight
import Mathlib.Analysis.Complex.HasPrimitives

/-!
# The concrete xi multiplier

This module constructs the holomorphic coefficient multiplier comparing the
actual normalized xi Jensen coefficients with the terminating `3F2` model.
It proves the multiplier's exact values at the six interpolation nodes and
identifies and bounds its sixth logarithmic derivative.  In particular, the
previously separate saddle-main correction is retained explicitly rather
than silently absorbed into the reduced residual.
-/

open Complex Metric Set

noncomputable section

namespace Zeta23.Research.JensenWedge

noncomputable def shiftedLogGammaPrimitive (a : ℝ) (z : ℂ) : ℂ :=
  Complex.wedgeIntegral 0 z (fun w => Complex.digamma ((a : ℂ) + w))

theorem shiftedLogGammaPrimitive_ofReal_eq_integral (a x : ℝ) :
    shiftedLogGammaPrimitive a (x : ℂ) =
      ∫ t : ℝ in 0..x, Complex.digamma ((a + t : ℝ) : ℂ) := by
  unfold shiftedLogGammaPrimitive Complex.wedgeIntegral
  simp

theorem shiftedLogGammaPrimitive_hasDerivAt
    {a R : ℝ} (ha : R < a) {z : ℂ} (hz : z ∈ ball (0 : ℂ) R) :
    HasDerivAt (shiftedLogGammaPrimitive a)
      (Complex.digamma ((a : ℂ) + z)) z := by
  let f : ℂ → ℂ := fun w => Complex.digamma ((a : ℂ) + w)
  have hdiff : DifferentiableOn ℂ f (ball (0 : ℂ) R) := by
    intro w hw
    have hpsi := Zeta23.StirlingRight.differentiableAt_digamma_re (w := (a : ℂ) + w) ?_
    exact (hpsi.comp w
      ((differentiableAt_const (c := (a : ℂ))).add differentiableAt_id)).differentiableWithinAt
    have hwre : -‖w‖ ≤ w.re := neg_le_of_abs_le (Complex.abs_re_le_norm w)
    have hwnorm : ‖w‖ < R := by simpa [Metric.mem_ball] using hw
    change 0 < a + w.re
    linarith
  unfold shiftedLogGammaPrimitive
  exact
    (Complex.IsConservativeOn.hasDerivAt_wedgeIntegral
      hdiff.continuousOn hz hdiff.isConservativeOn)

theorem iteratedDeriv_six_shiftedLogGammaPrimitive
    {a R : ℝ} (ha : R < a) {z : ℂ} (hz : z ∈ ball (0 : ℂ) R) :
    iteratedDeriv 6 (shiftedLogGammaPrimitive a) z =
      iteratedDeriv 5 Complex.digamma ((a : ℂ) + z) := by
  have heq : deriv (shiftedLogGammaPrimitive a) =ᶠ[nhds z]
      (fun w => Complex.digamma ((a : ℂ) + w)) := by
    filter_upwards [isOpen_ball.mem_nhds hz] with w hw
    exact (shiftedLogGammaPrimitive_hasDerivAt ha hw).deriv
  rw [show 6 = 5 + 1 by norm_num, iteratedDeriv_succ',
    heq.iteratedDeriv_eq]
  rw [iteratedDeriv_comp_const_add]

theorem analyticAt_shiftedLogGammaPrimitive
    {a R : ℝ} (ha : R < a) {z : ℂ} (hz : z ∈ ball (0 : ℂ) R) :
    AnalyticAt ℂ (shiftedLogGammaPrimitive a) z := by
  rw [analyticAt_iff_eventually_differentiableAt]
  filter_upwards [isOpen_ball.mem_nhds hz] with w hw
  exact (shiftedLogGammaPrimitive_hasDerivAt ha hw).differentiableAt

theorem hasDerivAt_real_shifted_logGamma
    {a x : ℝ} (hax : 0 < a + x) :
    HasDerivAt
      (fun t : ℝ => Complex.log (Complex.Gamma ((a + t : ℝ) : ℂ)))
      (Complex.digamma ((a + x : ℝ) : ℂ)) x := by
  let z : ℂ := ((a + x : ℝ) : ℂ)
  have hG : DifferentiableAt ℂ Complex.Gamma z :=
    Complex.differentiableAt_Gamma z (by
      intro m hm
      have hre := congrArg Complex.re hm
      simp only [z, ofReal_re, neg_re, natCast_re] at hre
      nlinarith [Nat.cast_nonneg (α := ℝ) m])
  have hGpos : 0 < (Complex.Gamma z).re := by
    simp only [z, Complex.Gamma_ofReal, ofReal_re]
    exact Real.Gamma_pos_of_pos hax
  have hslit : Complex.Gamma z ∈ Complex.slitPlane :=
    Complex.mem_slitPlane_iff.mpr (Or.inl hGpos)
  have hc : HasDerivAt (Complex.log ∘ Complex.Gamma)
      (Complex.digamma z) z := by
    have hcomp := (Complex.hasDerivAt_log hslit).comp z hG.hasDerivAt
    rw [Complex.digamma_def, logDeriv_apply, div_eq_mul_inv, mul_comm]
    exact hcomp
  have hreal := hc.comp_ofReal
  have haffine : HasDerivAt (fun t : ℝ => a + t) 1 x :=
    (hasDerivAt_id x).const_add a
  change HasDerivAt
    ((fun y : ℝ => (Complex.log ∘ Complex.Gamma) (y : ℂ)) ∘
      fun t : ℝ => a + t) (Complex.digamma z) x
  simpa only [one_smul] using hreal.scomp x haffine

theorem shiftedLogGammaPrimitive_ofReal_eq_logGamma
    {a x : ℝ} (ha : 0 < a) (hx : 0 ≤ x) :
    shiftedLogGammaPrimitive a (x : ℂ) =
      ((Real.log (Real.Gamma (a + x)) - Real.log (Real.Gamma a) : ℝ) : ℂ) := by
  have hderiv : ∀ t ∈ Set.uIcc (0 : ℝ) x,
      HasDerivAt
        (fun u : ℝ => Complex.log (Complex.Gamma ((a + u : ℝ) : ℂ)))
        (Complex.digamma ((a + t : ℝ) : ℂ)) t := by
    intro t ht
    rw [Set.uIcc_of_le hx] at ht
    exact hasDerivAt_real_shifted_logGamma (by linarith [ht.1])
  have hint : IntervalIntegrable
      (fun t : ℝ => Complex.digamma ((a + t : ℝ) : ℂ))
      MeasureTheory.volume 0 x := by
    apply ContinuousOn.intervalIntegrable
    intro t ht
    rw [Set.uIcc_of_le hx] at ht
    have hpsi := Zeta23.StirlingRight.differentiableAt_digamma_re
      (w := ((a + t : ℝ) : ℂ)) (by change 0 < a + t; linarith [ht.1])
    have hreal := hpsi.hasDerivAt.comp_ofReal
    have haffine : HasDerivAt (fun u : ℝ => a + u) 1 t :=
      (hasDerivAt_id t).const_add a
    exact (hreal.scomp t haffine).continuousAt.continuousWithinAt
  rw [shiftedLogGammaPrimitive_ofReal_eq_integral]
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint]
  simp only [add_zero]
  rw [Complex.Gamma_ofReal, Complex.Gamma_ofReal,
    ← Complex.ofReal_log (Real.Gamma_pos_of_pos (add_pos_of_pos_of_nonneg ha hx)).le,
    ← Complex.ofReal_log (Real.Gamma_pos_of_pos ha).le, Complex.ofReal_sub]

theorem real_logGamma_add_nat_sub
    {a : ℝ} (ha : 0 < a) (j : ℕ) :
    Real.log (Real.Gamma (a + j)) - Real.log (Real.Gamma a) =
      ∑ k ∈ Finset.range j, Real.log (a + k) := by
  induction j with
  | zero => simp
  | succ j ih =>
      have haj : 0 < a + (j : ℝ) := by positivity
      rw [show a + ((j + 1 : ℕ) : ℝ) = (a + j) + 1 by push_cast; ring,
        Real.Gamma_add_one haj.ne', Real.log_mul haj.ne'
          (Real.Gamma_pos_of_pos haj).ne', Finset.sum_range_succ]
      calc
        Real.log (a + (j : ℝ)) + Real.log (Real.Gamma (a + j)) -
              Real.log (Real.Gamma a) =
            Real.log (a + (j : ℝ)) +
              (Real.log (Real.Gamma (a + j)) - Real.log (Real.Gamma a)) := by ring
        _ = Real.log (a + (j : ℝ)) +
              ∑ k ∈ Finset.range j, Real.log (a + k) := by rw [ih]
        _ = ∑ k ∈ Finset.range j, Real.log (a + k) +
              Real.log (a + (j : ℝ)) := by ring

theorem shiftedLogGammaPrimitive_nat
    {a : ℝ} (ha : 0 < a) (j : ℕ) :
    shiftedLogGammaPrimitive a (j : ℂ) =
      ((∑ k ∈ Finset.range j, Real.log (a + k) : ℝ) : ℂ) := by
  rw [show (j : ℂ) = (((j : ℕ) : ℝ) : ℂ) by norm_num,
    shiftedLogGammaPrimitive_ofReal_eq_logGamma ha (Nat.cast_nonneg j),
    real_logGamma_add_nat_sub ha]

theorem log_xiFactorialRatioReal_succ (m : ℕ) :
    Real.log (Zeta23.Research.JensenWedge.xiFactorialRatioReal (m + 1)) -
        Real.log (Zeta23.Research.JensenWedge.xiFactorialRatioReal m) =
      -2 * Real.log 2 - Real.log ((m : ℝ) + 1 / 2) := by
  open Zeta23.Research.JensenWedge in
  rw [xiFactorialRatioReal_succ,
    Real.log_div (xiFactorialRatioReal_pos m).ne'
      (by positivity : (2 * (2 * (m : ℝ) + 1) : ℝ) ≠ 0)]
  have hden : (2 * (2 * (m : ℝ) + 1) : ℝ) =
      4 * ((m : ℝ) + 1 / 2) := by ring
  rw [hden, Real.log_mul (by norm_num : (4 : ℝ) ≠ 0)
    (by positivity : ((m : ℝ) + 1 / 2) ≠ 0)]
  have hlog4 : Real.log 4 = 2 * Real.log 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]
    norm_num
  rw [hlog4]
  ring

theorem log_xiFactorialRatioReal_add_nat
    (n j : ℕ) :
    Real.log (Zeta23.Research.JensenWedge.xiFactorialRatioReal (n + j)) -
        Real.log (Zeta23.Research.JensenWedge.xiFactorialRatioReal n) =
      -∑ k ∈ Finset.range j, Real.log ((n + k : ℕ) + (1 / 2 : ℝ)) -
        2 * (j : ℝ) * Real.log 2 := by
  induction j with
  | zero => simp
  | succ j ih =>
      rw [show n + (j + 1) = (n + j) + 1 by omega]
      have hstep := log_xiFactorialRatioReal_succ (n + j)
      rw [Finset.sum_range_succ]
      push_cast at hstep ⊢
      simp only [Nat.cast_add] at ih ⊢
      linear_combination ih + hstep

/-- Holomorphic continuation of the actual normalized xi coefficient
logarithm, anchored at coefficient `n`. -/
noncomputable def xiNaturalActualLogExtension
    (n : ℕ) (L : ℝ) (y : BranchPoint) (z : ℂ) : ℂ :=
  complexXiNaturalAuxiliaryLog ((n : ℂ) + z) -
    complexXiNaturalAuxiliaryLog (n : ℂ) -
    shiftedLogGammaPrimitive ((n : ℝ) + 1 / 2) z -
    2 * z * Complex.log 2 -
    z * Complex.log (xiNaturalJensenScale n L y)

/-- Holomorphic continuation of the comparison coefficient logarithm. -/
noncomputable def xiNaturalModelLogExtension
    (n : ℕ) (L : ℝ) (y : BranchPoint) (z : ℂ) : ℂ :=
  let A := residualParameterA y n (1 / L)
  let B := residualParameterB y n (1 / L)
  let C := residualParameterC y n
  let D := residualParameterD y n (1 / L)
  z * (Complex.log D - Complex.log A - Complex.log C) +
    shiftedLogGammaPrimitive A z + shiftedLogGammaPrimitive C z -
    shiftedLogGammaPrimitive B z - shiftedLogGammaPrimitive D z

/-- The concrete analytic logarithm of the coefficient multiplier. -/
noncomputable def xiNaturalConcreteLogMultiplier
    (n : ℕ) (L : ℝ) (y : BranchPoint) (z : ℂ) : ℂ :=
  xiNaturalActualLogExtension n L y z -
    xiNaturalModelLogExtension n L y z

/-- The concrete xi coefficient multiplier itself. -/
noncomputable def xiNaturalConcreteMultiplier
    (n : ℕ) (L : ℝ) (y : BranchPoint) (z : ℂ) : ℂ :=
  Complex.exp (xiNaturalConcreteLogMultiplier n L y z)

theorem analyticAt_xiNaturalActualLogExtension
    {n : ℕ} {L : ℝ} {y : BranchPoint} {R : ℝ}
    (hhalf : R < (n : ℝ) + 1 / 2) {z : ℂ}
    (hz : z ∈ Metric.ball (0 : ℂ) R)
    (hsector : (n : ℂ) + z ∈ leanXiCoefficientSector) :
    AnalyticAt ℂ (xiNaturalActualLogExtension n L y) z := by
  have hlog : AnalyticAt ℂ complexXiNaturalAuxiliaryLog ((n : ℂ) + z) :=
    (differentiableOn_complexXiNaturalAuxiliaryLog.analyticOnNhd
      isOpen_leanXiCoefficientSector) ((n : ℂ) + z) hsector
  unfold xiNaturalActualLogExtension
  apply ((((hlog.comp (by fun_prop)).sub (by fun_prop)).sub
    (analyticAt_shiftedLogGammaPrimitive hhalf hz)).sub (by fun_prop)).sub
    (by fun_prop)

theorem analyticAt_xiNaturalModelLogExtension
    {n : ℕ} {L : ℝ} {y : BranchPoint} {R : ℝ} {z : ℂ}
    (hz : z ∈ Metric.ball (0 : ℂ) R)
    (hA : R < residualParameterA y n (1 / L))
    (hB : R < residualParameterB y n (1 / L))
    (hC : R < residualParameterC y n)
    (hD : R < residualParameterD y n (1 / L)) :
    AnalyticAt ℂ (xiNaturalModelLogExtension n L y) z := by
  unfold xiNaturalModelLogExtension
  dsimp only
  exact ((((by fun_prop : AnalyticAt ℂ
      (fun w : ℂ => w *
        (Complex.log (residualParameterD y n (1 / L) : ℂ) -
          Complex.log (residualParameterA y n (1 / L) : ℂ) -
          Complex.log (residualParameterC y n : ℂ))) z).add
      (analyticAt_shiftedLogGammaPrimitive hA hz)).add
      (analyticAt_shiftedLogGammaPrimitive hC hz)).sub
      (analyticAt_shiftedLogGammaPrimitive hB hz)).sub
      (analyticAt_shiftedLogGammaPrimitive hD hz)

private theorem iteratedDeriv_six_linear_eq_zero (a z : ℂ) :
    iteratedDeriv 6 (fun w : ℂ => w * a) z = 0 := by
  rw [iteratedDeriv_mul_const_field, iteratedDeriv_fun_id]
  norm_num

private theorem iteratedDeriv_pointwise_sub
    {n : ℕ} {f g : ℂ → ℂ} {z : ℂ}
    (hf : ContDiffAt ℂ n f z) (hg : ContDiffAt ℂ n g z) :
    iteratedDeriv n (fun w => f w - g w) z =
      iteratedDeriv n f z - iteratedDeriv n g z := by
  exact iteratedDeriv_sub hf hg

private theorem iteratedDeriv_pointwise_add
    {n : ℕ} {f g : ℂ → ℂ} {z : ℂ}
    (hf : ContDiffAt ℂ n f z) (hg : ContDiffAt ℂ n g z) :
    iteratedDeriv n (fun w => f w + g w) z =
      iteratedDeriv n f z + iteratedDeriv n g z := by
  exact iteratedDeriv_add hf hg

theorem iteratedDeriv_six_xiNaturalActualLogExtension
    {n : ℕ} {L : ℝ} {y : BranchPoint} {R : ℝ}
    (hhalf : R < (n : ℝ) + 1 / 2) {z : ℂ}
    (hz : z ∈ Metric.ball (0 : ℂ) R)
    (hsector : (n : ℂ) + z ∈ leanXiCoefficientSector) :
    iteratedDeriv 6 (xiNaturalActualLogExtension n L y) z =
      iteratedDeriv 6 complexXiNaturalAuxiliaryLog ((n : ℂ) + z) -
        iteratedDeriv 5 Complex.digamma ((n : ℂ) + 1 / 2 + z) := by
  have hlogAnalytic : AnalyticOnNhd ℂ complexXiNaturalAuxiliaryLog
      leanXiCoefficientSector :=
    differentiableOn_complexXiNaturalAuxiliaryLog.analyticOnNhd
      isOpen_leanXiCoefficientSector
  have hshift : ContDiffAt ℂ 6
      (fun w => complexXiNaturalAuxiliaryLog ((n : ℂ) + w)) z :=
    ((hlogAnalytic ((n : ℂ) + z) hsector).comp
      (by fun_prop : AnalyticAt ℂ (fun w : ℂ => (n : ℂ) + w) z)).contDiffAt
  have hconst : ContDiffAt ℂ 6
      (fun _w : ℂ => complexXiNaturalAuxiliaryLog (n : ℂ)) z := by fun_prop
  have hprim : ContDiffAt ℂ 6
      (shiftedLogGammaPrimitive ((n : ℝ) + 1 / 2)) z :=
    (analyticAt_shiftedLogGammaPrimitive hhalf hz).contDiffAt
  have hdyadic : ContDiffAt ℂ 6 (fun w : ℂ => 2 * w * Complex.log 2) z := by
    fun_prop
  have hscale : ContDiffAt ℂ 6
      (fun w : ℂ => w * Complex.log (xiNaturalJensenScale n L y)) z := by
    fun_prop
  unfold xiNaturalActualLogExtension
  rw [iteratedDeriv_pointwise_sub (((hshift.sub hconst).sub hprim).sub hdyadic) hscale,
    iteratedDeriv_pointwise_sub ((hshift.sub hconst).sub hprim) hdyadic,
    iteratedDeriv_pointwise_sub (hshift.sub hconst) hprim,
    iteratedDeriv_pointwise_sub hshift hconst]
  have hshift6 : iteratedDeriv 6
      (fun w => complexXiNaturalAuxiliaryLog ((n : ℂ) + w)) z =
      iteratedDeriv 6 complexXiNaturalAuxiliaryLog ((n : ℂ) + z) := by
    rw [iteratedDeriv_comp_const_add]
  have hconst6 : iteratedDeriv 6
      (fun _w : ℂ => complexXiNaturalAuxiliaryLog (n : ℂ)) z = 0 := by
    rw [iteratedDeriv_const]
    norm_num
  have hdyadic6 : iteratedDeriv 6 (fun w : ℂ => 2 * w * Complex.log 2) z = 0 := by
    have h := iteratedDeriv_six_linear_eq_zero (2 * Complex.log 2) z
    have heq : (fun w : ℂ => 2 * w * Complex.log 2) =
        fun w : ℂ => w * (2 * Complex.log 2) := by
      funext w
      ring
    rw [heq]
    exact h
  have hscale6 : iteratedDeriv 6
      (fun w : ℂ => w * Complex.log (xiNaturalJensenScale n L y)) z = 0 :=
    iteratedDeriv_six_linear_eq_zero _ _
  rw [hshift6, hconst6,
    iteratedDeriv_six_shiftedLogGammaPrimitive hhalf hz,
    hdyadic6, hscale6]
  have harg : ((((n : ℝ) + 1 / 2 : ℝ) : ℂ) + z) =
      (n : ℂ) + 1 / 2 + z := by
    push_cast
    ring
  rw [harg]
  ring

theorem iteratedDeriv_six_xiNaturalModelLogExtension
    {n : ℕ} {L : ℝ} {y : BranchPoint} {R : ℝ} {z : ℂ}
    (hz : z ∈ Metric.ball (0 : ℂ) R)
    (hA : R < residualParameterA y n (1 / L))
    (hB : R < residualParameterB y n (1 / L))
    (hC : R < residualParameterC y n)
    (hD : R < residualParameterD y n (1 / L)) :
    iteratedDeriv 6 (xiNaturalModelLogExtension n L y) z =
      iteratedDeriv 5 Complex.digamma
          ((residualParameterA y n (1 / L) : ℂ) + z) +
        iteratedDeriv 5 Complex.digamma
          ((residualParameterC y n : ℂ) + z) -
        iteratedDeriv 5 Complex.digamma
          ((residualParameterB y n (1 / L) : ℂ) + z) -
        iteratedDeriv 5 Complex.digamma
          ((residualParameterD y n (1 / L) : ℂ) + z) := by
  let A := residualParameterA y n (1 / L)
  let B := residualParameterB y n (1 / L)
  let C := residualParameterC y n
  let D := residualParameterD y n (1 / L)
  have hlin : ContDiffAt ℂ 6
      (fun w : ℂ => w * (Complex.log D - Complex.log A - Complex.log C)) z := by
    fun_prop
  have hpA : ContDiffAt ℂ 6 (shiftedLogGammaPrimitive A) z :=
    (analyticAt_shiftedLogGammaPrimitive hA hz).contDiffAt
  have hpB : ContDiffAt ℂ 6 (shiftedLogGammaPrimitive B) z :=
    (analyticAt_shiftedLogGammaPrimitive hB hz).contDiffAt
  have hpC : ContDiffAt ℂ 6 (shiftedLogGammaPrimitive C) z :=
    (analyticAt_shiftedLogGammaPrimitive hC hz).contDiffAt
  have hpD : ContDiffAt ℂ 6 (shiftedLogGammaPrimitive D) z :=
    (analyticAt_shiftedLogGammaPrimitive hD hz).contDiffAt
  unfold xiNaturalModelLogExtension
  dsimp only
  rw [iteratedDeriv_pointwise_sub (((hlin.add hpA).add hpC).sub hpB) hpD,
    iteratedDeriv_pointwise_sub ((hlin.add hpA).add hpC) hpB,
    iteratedDeriv_pointwise_add (hlin.add hpA) hpC,
    iteratedDeriv_pointwise_add hlin hpA]
  rw [iteratedDeriv_six_linear_eq_zero,
    iteratedDeriv_six_shiftedLogGammaPrimitive hA hz,
    iteratedDeriv_six_shiftedLogGammaPrimitive hB hz,
    iteratedDeriv_six_shiftedLogGammaPrimitive hC hz,
    iteratedDeriv_six_shiftedLogGammaPrimitive hD hz]
  ring

/-- Exact identification of the sixth derivative of the concrete log
multiplier with the manuscript residual, before quantitative bounding. -/
theorem iteratedDeriv_six_xiNaturalConcreteLogMultiplier
    {n : ℕ} {L : ℝ} {y : BranchPoint} {R : ℝ} {z : ℂ}
    (hz : z ∈ Metric.ball (0 : ℂ) R)
    (hsector : (n : ℂ) + z ∈ leanXiCoefficientSector)
    (hhalf : R < (n : ℝ) + 1 / 2)
    (hA : R < residualParameterA y n (1 / L))
    (hB : R < residualParameterB y n (1 / L))
    (hC : R < residualParameterC y n)
    (hD : R < residualParameterD y n (1 / L)) :
    iteratedDeriv 6 (xiNaturalConcreteLogMultiplier n L y) z =
      manuscriptSixthResidualValue
        (iteratedDeriv 6 complexXiNaturalAuxiliaryLog ((n : ℂ) + z)) n
        (residualParameterA y n (1 / L))
        (residualParameterB y n (1 / L))
        (residualParameterC y n)
        (residualParameterD y n (1 / L)) z := by
  have hactual : AnalyticAt ℂ (xiNaturalActualLogExtension n L y) z :=
    analyticAt_xiNaturalActualLogExtension hhalf hz hsector
  have hmodel : AnalyticAt ℂ (xiNaturalModelLogExtension n L y) z :=
    analyticAt_xiNaturalModelLogExtension hz hA hB hC hD
  unfold xiNaturalConcreteLogMultiplier
  rw [iteratedDeriv_pointwise_sub hactual.contDiffAt hmodel.contDiffAt,
    iteratedDeriv_six_xiNaturalActualLogExtension hhalf hz hsector,
    iteratedDeriv_six_xiNaturalModelLogExtension hz hA hB hC hD]
  unfold manuscriptSixthResidualValue
  ring

theorem iteratedDeriv_six_complexXiNaturalAuxiliaryLogMain_eq
    {M : ℂ} (hM : M ∈ leanXiCoefficientSector) :
    iteratedDeriv 6 complexXiNaturalAuxiliaryLogMain M =
      manuscriptMomentSaddleMainSix M +
        iteratedDeriv 6 xiNaturalMainSaddleRemainder M := by
  have hN : coefficientMellinParameter M ∈ leanSaddleSector :=
    leanTwoShiftAdmissible_base (leanCoefficientSector_admissible hM.2)
  have hrem := iteratedDeriv_xiNaturalMainSaddleRemainder_eq
    6 (by norm_num) hM
  have hident := (manuscriptG0SixthIdentification_of_mem_sector hN).exact_value
  rw [hident] at hrem
  unfold manuscriptMomentSaddleMainSix
  linear_combination -hrem

theorem iteratedDeriv_six_complexXiNaturalAuxiliaryLog_eq
    {M : ℂ} (hM : M ∈ leanXiCoefficientSector) :
    iteratedDeriv 6 complexXiNaturalAuxiliaryLog M =
      manuscriptMomentSaddleMainSix M +
        iteratedDeriv 6 xiNaturalMainSaddleRemainder M +
        iteratedDeriv 6 complexXiNaturalAuxiliaryLogError M := by
  have hmain : ContDiffAt ℂ 6 complexXiNaturalAuxiliaryLogMain M :=
    ((differentiableOn_complexXiNaturalAuxiliaryLogMain.analyticOnNhd
      isOpen_leanXiCoefficientSector) M hM).contDiffAt
  have herr : ContDiffAt ℂ 6 complexXiNaturalAuxiliaryLogError M :=
    ((differentiableOn_complexXiNaturalAuxiliaryLogError.analyticOnNhd
      isOpen_leanXiCoefficientSector) M hM).contDiffAt
  unfold complexXiNaturalAuxiliaryLog
  rw [iteratedDeriv_pointwise_add hmain herr,
    iteratedDeriv_six_complexXiNaturalAuxiliaryLogMain_eq hM]

theorem iteratedDeriv_six_complexXiNaturalAuxiliaryLog_norm_le
    {n : ℕ} (hnLarge : Real.exp (leanSaddleCutoff + 2) < (n : ℝ))
    {z : ℂ} (hzNorm : ‖z‖ ≤ manuscriptInteriorCauchyRadius (n : ℝ)) :
    ‖iteratedDeriv 6 complexXiNaturalAuxiliaryLog ((n : ℂ) + z)‖ ≤
      1280000 / ((n : ℝ) ^ 5 * Real.log (n : ℝ)) +
        Nat.factorial 6 * (40 * Real.log (3 * (n : ℝ))) /
          manuscriptInteriorCauchyRadius (n : ℝ) ^ 6 +
        Nat.factorial 6 * ((3 / 2 : ℝ) *
          naturalXiCauchyEpsilon (n : ℝ)) /
          manuscriptInteriorCauchyRadius (n : ℝ) ^ 6 := by
  have hzCenter : (n : ℂ) + z ∈
      Metric.closedBall ((n : ℝ) : ℂ)
        (manuscriptInteriorCauchyRadius (n : ℝ)) := by
    rw [Metric.mem_closedBall, dist_eq_norm]
    convert hzNorm using 1 <;> push_cast <;> ring
  have hzOuter : (n : ℂ) + z ∈
      Metric.closedBall ((n : ℝ) : ℂ) (manuscriptCauchyRadius (n : ℝ)) := by
    rw [Metric.mem_closedBall] at hzCenter ⊢
    unfold manuscriptInteriorCauchyRadius at hzCenter
    unfold manuscriptCauchyRadius
    have hnpos : (0 : ℝ) < n := (Real.exp_pos _).trans hnLarge
    linarith
  have hsector := manuscriptCauchy_closedBall_subset_sector hnLarge hzOuter
  have hmain := manuscriptMomentSaddleMainSix_norm_le_on_innerDisc
    hnLarge hzNorm
  have hrem := xiNaturalMainSaddleRemainder_derivatives_through_six_on_half_disc
    hnLarge hzCenter 6 (by norm_num)
  have herr := complexXiNaturalAuxiliaryLogError_derivatives_through_six_on_half_disc
    hnLarge hzCenter 6 (by norm_num)
  rw [iteratedDeriv_six_complexXiNaturalAuxiliaryLog_eq hsector]
  calc
    ‖manuscriptMomentSaddleMainSix ((n : ℂ) + z) +
          iteratedDeriv 6 xiNaturalMainSaddleRemainder ((n : ℂ) + z) +
          iteratedDeriv 6 complexXiNaturalAuxiliaryLogError ((n : ℂ) + z)‖ ≤
        ‖manuscriptMomentSaddleMainSix ((n : ℂ) + z)‖ +
          ‖iteratedDeriv 6 xiNaturalMainSaddleRemainder ((n : ℂ) + z)‖ +
          ‖iteratedDeriv 6 complexXiNaturalAuxiliaryLogError ((n : ℂ) + z)‖ := by
      exact (norm_add_le _ _).trans (add_le_add (norm_add_le _ _) (le_refl _))
    _ ≤ _ := by gcongr

theorem naturalXiCauchyEpsilon_le_manuscript
    {n : ℕ} (hnLarge : Real.exp (leanSaddleCutoff + 2) < (n : ℝ)) :
    naturalXiCauchyEpsilon (n : ℝ) ≤ manuscriptCauchyEpsilon (n : ℝ) := by
  have hnpos : (0 : ℝ) < n := (Real.exp_pos _).trans hnLarge
  have hnOne : (1 : ℝ) ≤ n := by
    exact_mod_cast (Nat.one_le_iff_ne_zero.mpr (by
      intro hn0
      subst n
      norm_num at hnpos))
  have hlog : 0 ≤ Real.log (3 * (n : ℝ)) := by
    apply Real.log_nonneg
    nlinarith
  unfold naturalXiCauchyEpsilon manuscriptCauchyEpsilon
  apply div_le_div_of_nonneg_right _ hnpos.le
  apply mul_le_mul_of_nonneg_right _ hlog
  norm_num [manuscriptXiCoefficientErrorCoefficient,
    complexXiCoefficientErrorCoefficient, fullThetaMomentErrorCoefficient,
    Nat.factorial]

/-- Extra constant needed to transport the explicit natural-main correction
through the sixth-order residual rate. -/
def xiNaturalMainCorrectionSixthRateConstant : ℝ :=
  8 * Nat.factorial 6 * 40 * 2000 ^ 6

theorem xiNaturalMainCorrection_sixth_term_le
    {n : ℕ} (hnLarge : Real.exp (leanSaddleCutoff + 2) < (n : ℝ)) :
    Nat.factorial 6 * (40 * Real.log (3 * (n : ℝ))) /
        manuscriptInteriorCauchyRadius (n : ℝ) ^ 6 ≤
      xiNaturalMainCorrectionSixthRateConstant /
        ((n : ℝ) ^ 5 * Real.log (n : ℝ)) := by
  have hnpos : (0 : ℝ) < n := (Real.exp_pos _).trans hnLarge
  have hnnonneg : (0 : ℝ) ≤ n := hnpos.le
  have hthreepos : 0 < 3 * (n : ℝ) := by positivity
  have hlognPos : 0 < Real.log (n : ℝ) := by
    apply Real.log_pos
    have hcut : (1 : ℝ) < Real.exp (leanSaddleCutoff + 2) :=
      Real.one_lt_exp_iff.mpr (by norm_num [leanSaddleCutoff])
    exact hcut.trans hnLarge
  have hlognRaw := Real.log_le_rpow_div hnnonneg
    (by norm_num : (0 : ℝ) < 1 / 2)
  have hlogThreeRaw := Real.log_le_rpow_div hthreepos.le
    (by norm_num : (0 : ℝ) < 1 / 2)
  have hlogn : Real.log (n : ℝ) ≤ 2 * Real.sqrt (n : ℝ) := by
    rw [Real.sqrt_eq_rpow]
    calc
      Real.log (n : ℝ) ≤ (n : ℝ) ^ (1 / 2 : ℝ) / (1 / 2 : ℝ) := hlognRaw
      _ = 2 * (n : ℝ) ^ (1 / 2 : ℝ) := by ring
  have hlogThree : Real.log (3 * (n : ℝ)) ≤
      2 * Real.sqrt (3 * (n : ℝ)) := by
    rw [Real.sqrt_eq_rpow]
    calc
      Real.log (3 * (n : ℝ)) ≤
          (3 * (n : ℝ)) ^ (1 / 2 : ℝ) / (1 / 2 : ℝ) := hlogThreeRaw
      _ = 2 * (3 * (n : ℝ)) ^ (1 / 2 : ℝ) := by ring
  have hsqrtThree : Real.sqrt (3 * (n : ℝ)) ≤ 2 * Real.sqrt (n : ℝ) := by
    rw [Real.sqrt_le_iff]
    constructor
    · positivity
    · have hsquare := Real.sq_sqrt hnnonneg
      nlinarith
  have hsqrtNonneg := Real.sqrt_nonneg (n : ℝ)
  have hsquare := Real.sq_sqrt hnnonneg
  have hnOne : (1 : ℝ) ≤ n := by
    exact_mod_cast (Nat.one_le_iff_ne_zero.mpr (by
      intro hn0
      subst n
      norm_num at hnpos))
  have hlognNonneg : 0 ≤ Real.log (n : ℝ) := Real.log_nonneg hnOne
  have hlogThreeNonneg : 0 ≤ Real.log (3 * (n : ℝ)) :=
    Real.log_nonneg (by nlinarith)
  have hlogThree' : Real.log (3 * (n : ℝ)) ≤ 4 * Real.sqrt (n : ℝ) := by
    calc
      Real.log (3 * (n : ℝ)) ≤ 2 * Real.sqrt (3 * (n : ℝ)) := hlogThree
      _ ≤ 2 * (2 * Real.sqrt (n : ℝ)) :=
        mul_le_mul_of_nonneg_left hsqrtThree (by norm_num)
      _ = 4 * Real.sqrt (n : ℝ) := by ring
  have hlogs : Real.log (n : ℝ) * Real.log (3 * (n : ℝ)) ≤
      8 * (n : ℝ) := by
    calc
      Real.log (n : ℝ) * Real.log (3 * (n : ℝ)) ≤
          (2 * Real.sqrt (n : ℝ)) * (4 * Real.sqrt (n : ℝ)) :=
        mul_le_mul hlogn hlogThree' hlogThreeNonneg
          (mul_nonneg (by norm_num) hsqrtNonneg)
      _ = 8 * (Real.sqrt (n : ℝ) ^ 2) := by ring
      _ = 8 * (n : ℝ) := by rw [hsquare]
  have hlogDiv : Real.log (3 * (n : ℝ)) ≤
      8 * (n : ℝ) / Real.log (n : ℝ) := by
    rw [le_div_iff₀ hlognPos]
    simpa [mul_comm] using hlogs
  calc
    Nat.factorial 6 * (40 * Real.log (3 * (n : ℝ))) /
          manuscriptInteriorCauchyRadius (n : ℝ) ^ 6 ≤
        Nat.factorial 6 * (40 *
          (8 * (n : ℝ) / Real.log (n : ℝ))) /
          manuscriptInteriorCauchyRadius (n : ℝ) ^ 6 := by
      gcongr
    _ = xiNaturalMainCorrectionSixthRateConstant /
          ((n : ℝ) ^ 5 * Real.log (n : ℝ)) := by
      unfold xiNaturalMainCorrectionSixthRateConstant
        manuscriptInteriorCauchyRadius
      norm_num [Nat.factorial]
      field_simp [hnpos.ne', hlognPos.ne']
      ring

/-- Rate constant for the sixth derivative of the concrete xi log
multiplier.  It is the manuscript residual constant plus the explicit
natural-main saddle correction which is absent from the reduced model. -/
def xiNaturalConcreteSixthResidualRateConstant : ℝ :=
  manuscriptSixthResidualRateConstant +
    xiNaturalMainCorrectionSixthRateConstant

/-- The actual auxiliary logarithm, rather than the reduced saddle model,
obeys the same sixth-residual rate after adding the explicit correction
constant. -/
theorem xiNaturalConcreteSixthResidualValue_outerBox_rate
    {y : BranchPoint} (hy : InOuterParameterBox y)
    {n : ℕ} (hn : 8 ≤ n)
    (hnLarge : Real.exp (leanSaddleCutoff + 2) < (n : ℝ))
    {e : ℝ} (he : 0 < e) (he12 : e ≤ 1 / 12)
    (heLog : e ≤ 2 / Real.log (n : ℝ))
    {z : ℂ}
    (hzNorm : ‖z‖ ≤ manuscriptInteriorCauchyRadius (n : ℝ))
    (hzRe : -(n : ℝ) / 2 ≤ z.re) :
    ‖manuscriptSixthResidualValue
        (iteratedDeriv 6 complexXiNaturalAuxiliaryLog ((n : ℂ) + z)) n
        (residualParameterA y n e)
        (residualParameterB y n e)
        (residualParameterC y n)
        (residualParameterD y n e) z‖ ≤
      xiNaturalConcreteSixthResidualRateConstant /
        ((n : ℝ) ^ 5 * Real.log (n : ℝ)) := by
  let C := residualParameterCertificate_of_outerBox hy hn he he12 hzRe
  have hA := residualParameterA_floor_anchor_of_outerBox hy hn he he12 hzRe
  have hSix := iteratedDeriv_six_complexXiNaturalAuxiliaryLog_norm_le
    hnLarge hzNorm
  have hbase := manuscriptSixthResidualValue_norm_le_separateA
    C.anchor_two hA.1 hSix C.B_right C.C_right C.D_right C.half_right hA.2
  have hCorrection := xiNaturalMainCorrection_sixth_term_le hnLarge
  have hNaturalCauchy :
      Nat.factorial 6 * ((3 / 2 : ℝ) * naturalXiCauchyEpsilon (n : ℝ)) /
          manuscriptInteriorCauchyRadius (n : ℝ) ^ 6 ≤
        manuscriptSixthResidualCauchyConstant /
          ((n : ℝ) ^ 5 * Real.log (n : ℝ)) := by
    apply le_trans ?_ (manuscriptSixthResidual_cauchy_term_le hnLarge)
    gcongr
    exact naturalXiCauchyEpsilon_le_manuscript hnLarge
  have hBC := manuscriptSixthResidual_BC_term_le hn hnLarge he heLog
  have hD := manuscriptSixthResidual_D_term_le hn hnLarge he heLog
  have hFar := manuscriptSixthResidual_A_term_le hn hnLarge he he12 heLog
  apply hbase.trans
  calc
    (1280000 / ((n : ℝ) ^ 5 * Real.log (n : ℝ)) +
          Nat.factorial 6 * (40 * Real.log (3 * (n : ℝ))) /
            manuscriptInteriorCauchyRadius (n : ℝ) ^ 6 +
          Nat.factorial 6 * ((3 / 2 : ℝ) * naturalXiCauchyEpsilon (n : ℝ)) /
            manuscriptInteriorCauchyRadius (n : ℝ) ^ 6) +
        120 * ‖((residualParameterB y n e : ℝ) : ℂ) -
          ((residualParameterC y n : ℝ) : ℂ)‖ /
            (((n / 4 - 1 : ℕ) : ℝ) ^ 6) +
        120 * ‖((residualParameterD y n e : ℝ) : ℂ) -
          ((n : ℂ) + 1 / 2)‖ /
            (((n / 4 - 1 : ℕ) : ℝ) ^ 6) +
        24 / (((⌊(n : ℝ) / e⌋₊ - 1 : ℕ) : ℝ) ^ 5) ≤
      (1280000 / ((n : ℝ) ^ 5 * Real.log (n : ℝ)) +
          Nat.factorial 6 * (40 * Real.log (3 * (n : ℝ))) /
            manuscriptInteriorCauchyRadius (n : ℝ) ^ 6 +
          Nat.factorial 6 * ((3 / 2 : ℝ) * naturalXiCauchyEpsilon (n : ℝ)) /
            manuscriptInteriorCauchyRadius (n : ℝ) ^ 6) +
        120 * (6 * n * e) /
            (((n / 4 - 1 : ℕ) : ℝ) ^ 6) +
        120 * ((5 / 12 : ℝ) * n * e + 1 / 2) /
            (((n / 4 - 1 : ℕ) : ℝ) ^ 6) +
        24 / (((⌊(n : ℝ) / e⌋₊ - 1 : ℕ) : ℝ) ^ 5) := by
      gcongr
      · exact C.BC_distance
      · exact C.Dhalf_distance
    _ ≤
      1280000 / ((n : ℝ) ^ 5 * Real.log (n : ℝ)) +
        xiNaturalMainCorrectionSixthRateConstant /
          ((n : ℝ) ^ 5 * Real.log (n : ℝ)) +
        manuscriptSixthResidualCauchyConstant /
          ((n : ℝ) ^ 5 * Real.log (n : ℝ)) +
        manuscriptSixthResidualBCConstant /
          ((n : ℝ) ^ 5 * Real.log (n : ℝ)) +
        manuscriptSixthResidualDConstant /
          ((n : ℝ) ^ 5 * Real.log (n : ℝ)) +
        manuscriptSixthResidualAConstant /
          ((n : ℝ) ^ 5 * Real.log (n : ℝ)) := by
      gcongr
    _ = xiNaturalConcreteSixthResidualRateConstant /
          ((n : ℝ) ^ 5 * Real.log (n : ℝ)) := by
      unfold xiNaturalConcreteSixthResidualRateConstant
        manuscriptSixthResidualRateConstant
      ring

/-- Direct sixth-derivative bound for the concrete log multiplier on any
disc on which its five holomorphic constituents are defined. -/
theorem xiNaturalConcreteLogMultiplier_sixth_norm_le
    {y : BranchPoint} (hy : InOuterParameterBox y)
    {n : ℕ} (hn : 8 ≤ n)
    (hnLarge : Real.exp (leanSaddleCutoff + 2) < (n : ℝ))
    {L R : ℝ} (hL : 0 < L)
    (hL12 : 1 / L ≤ (1 : ℝ) / 12)
    (hLLog : 1 / L ≤ 2 / Real.log (n : ℝ))
    {z : ℂ} (hz : z ∈ Metric.ball (0 : ℂ) R)
    (hzNorm : ‖z‖ ≤ manuscriptInteriorCauchyRadius (n : ℝ))
    (hzRe : -(n : ℝ) / 2 ≤ z.re)
    (hsector : (n : ℂ) + z ∈ leanXiCoefficientSector)
    (hhalf : R < (n : ℝ) + 1 / 2)
    (hA : R < residualParameterA y n (1 / L))
    (hB : R < residualParameterB y n (1 / L))
    (hC : R < residualParameterC y n)
    (hD : R < residualParameterD y n (1 / L)) :
    ‖iteratedDeriv 6 (xiNaturalConcreteLogMultiplier n L y) z‖ ≤
      xiNaturalConcreteSixthResidualRateConstant /
        ((n : ℝ) ^ 5 * Real.log (n : ℝ)) := by
  rw [iteratedDeriv_six_xiNaturalConcreteLogMultiplier hz hsector hhalf hA hB hC hD]
  exact xiNaturalConcreteSixthResidualValue_outerBox_rate hy hn hnLarge
    (one_div_pos.mpr hL) hL12 hLLog hzNorm hzRe

theorem xiNaturalActualLogExtension_nat
    {n : ℕ} (hn : 0 < n) {L : ℝ} {y : BranchPoint}
    (hscale : 0 < xiNaturalJensenScale n L y) (j : ℕ)
    (h0 : (n : ℂ) ∈ leanXiCoefficientSector)
    (hj : ((n + j : ℕ) : ℂ) ∈ leanXiCoefficientSector) :
    xiNaturalActualLogExtension n L y (j : ℂ) =
      (xiNaturalActualLogCoordinate n L y j : ℂ) := by
  have haux0 := complexXiNaturalAuxiliaryLog_nat_eq_discrete hn h0
  have hauxj := complexXiNaturalAuxiliaryLog_nat_eq_discrete (by omega : 0 < n + j) hj
  have haux0' := ofReal_log_riemannXiAuxiliaryMomentReal hn
  have hauxj' := ofReal_log_riemannXiAuxiliaryMomentReal (by omega : 0 < n + j)
  have hprim := shiftedLogGammaPrimitive_nat
    (by positivity : 0 < (n : ℝ) + 1 / 2) j
  have hfactor := log_xiFactorialRatioReal_add_nat n j
  unfold xiNaturalActualLogExtension xiNaturalActualLogCoordinate
  rw [show (n : ℂ) + (j : ℂ) = ((n + j : ℕ) : ℂ) by push_cast; ring,
    hauxj, haux0, ← hauxj', ← haux0', hprim,
    show Real.log (riemannXiCoefficientReal (n + j)) =
      exactXiCoefficientLog (n + j) by rfl,
    show Real.log (riemannXiCoefficientReal n) =
      exactXiCoefficientLog n by rfl,
    exactXiCoefficientLog_eq_factorial_add_auxiliary,
    exactXiCoefficientLog_eq_factorial_add_auxiliary]
  rw [← Complex.ofReal_log hscale.le]
  have hlog2 : Complex.log 2 = (Real.log 2 : ℂ) := by
    simpa using (Complex.ofReal_log (by norm_num : (0 : ℝ) ≤ 2)).symm
  rw [hlog2]
  have hsum :
      (∑ k ∈ Finset.range j, Real.log ((n : ℝ) + 1 / 2 + k)) =
        ∑ k ∈ Finset.range j, Real.log ((n : ℝ) + k + 1 / 2) := by
    apply Finset.sum_congr rfl
    intro k hk
    congr 1
    ring
  rw [hsum]
  have hfactorC := congrArg (fun r : ℝ => (r : ℂ)) hfactor
  push_cast at hfactorC ⊢
  linear_combination -hfactorC

theorem xiNaturalModelLogExtension_nat
    {n : ℕ} {L : ℝ} {y : BranchPoint} (j : ℕ)
    (hpos : 0 < residualParameterA y n (1 / L) ∧
      0 < residualParameterB y n (1 / L) ∧
      0 < residualParameterC y n ∧
      0 < residualParameterD y n (1 / L)) :
    xiNaturalModelLogExtension n L y (j : ℂ) =
      (xiNaturalModelLogCoordinate n L y j : ℂ) := by
  let A := residualParameterA y n (1 / L)
  let B := residualParameterB y n (1 / L)
  let C := residualParameterC y n
  let D := residualParameterD y n (1 / L)
  rcases hpos with ⟨hA, hB, hC, hD⟩
  have hpA := shiftedLogGammaPrimitive_nat hA j
  have hpB := shiftedLogGammaPrimitive_nat hB j
  have hpC := shiftedLogGammaPrimitive_nat hC j
  have hpD := shiftedLogGammaPrimitive_nat hD j
  have hlA : Complex.log (residualParameterA y n (1 / L) : ℂ) =
      (Real.log (residualParameterA y n (1 / L)) : ℂ) := by
    simpa using (Complex.ofReal_log hA.le).symm
  have hlB : Complex.log (residualParameterB y n (1 / L) : ℂ) =
      (Real.log (residualParameterB y n (1 / L)) : ℂ) := by
    simpa using (Complex.ofReal_log hB.le).symm
  have hlC : Complex.log (residualParameterC y n : ℂ) =
      (Real.log (residualParameterC y n) : ℂ) := by
    simpa using (Complex.ofReal_log hC.le).symm
  have hlD : Complex.log (residualParameterD y n (1 / L) : ℂ) =
      (Real.log (residualParameterD y n (1 / L)) : ℂ) := by
    simpa using (Complex.ofReal_log hD.le).symm
  unfold xiNaturalModelLogExtension xiNaturalModelLogCoordinate
    xiNaturalModelLogIncrement
  dsimp only
  rw [hpA, hpB, hpC, hpD, hlA, hlC, hlD]
  push_cast
  simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib,
    Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  push_cast
  ring

theorem xiNaturalConcreteLogMultiplier_nat
    {n : ℕ} (hn : 0 < n) {L : ℝ} (hL : 0 < L)
    {y : BranchPoint} (hy : InOuterParameterBox y)
    (hL12 : 1 / L ≤ (1 : ℝ) / 12) (j : ℕ)
    (h0 : (n : ℂ) ∈ leanXiCoefficientSector)
    (hj : ((n + j : ℕ) : ℂ) ∈ leanXiCoefficientSector) :
    xiNaturalConcreteLogMultiplier n L y (j : ℂ) =
      ((xiNaturalActualLogCoordinate n L y j -
        xiNaturalModelLogCoordinate n L y j : ℝ) : ℂ) := by
  have hscale := xiNaturalJensenScale_pos hn hL hy
  have hpos := xiNaturalResidualParameters_pos hn hL hL12 hy
  unfold xiNaturalConcreteLogMultiplier
  rw [xiNaturalActualLogExtension_nat hn hscale j h0 hj,
    xiNaturalModelLogExtension_nat j hpos]
  push_cast
  rfl

/-- The exact branch equation gives the concrete analytic multiplier its six
required interpolation-node values. -/
theorem xiNaturalConcreteLogMultiplier_six_nodes
    {n : ℕ} (hn : 0 < n) {L : ℝ} (hL : 0 < L)
    {y : BranchPoint} (hy : InOuterParameterBox y)
    (hL12 : 1 / L ≤ (1 : ℝ) / 12)
    (hmap : exactXiParameterMap n L y = 0)
    (hsector : ∀ j : ℕ, j ≤ 5 →
      ((n + j : ℕ) : ℂ) ∈ leanXiCoefficientSector) :
    ∀ j : Fin 6, xiNaturalConcreteLogMultiplier n L y (j : ℂ) = 0 := by
  intro j
  have h0 : (n : ℂ) ∈ leanXiCoefficientSector := by
    simpa using hsector 0 (by norm_num)
  rw [xiNaturalConcreteLogMultiplier_nat hn hL hy hL12 j h0
    (hsector j (by omega))]
  rw [xiNaturalSixLogCoordinates_match hn hL hy hmap j]
  norm_num

theorem xiNaturalConcreteMultiplier_six_nodes
    {n : ℕ} (hn : 0 < n) {L : ℝ} (hL : 0 < L)
    {y : BranchPoint} (hy : InOuterParameterBox y)
    (hL12 : 1 / L ≤ (1 : ℝ) / 12)
    (hmap : exactXiParameterMap n L y = 0)
    (hsector : ∀ j : ℕ, j ≤ 5 →
      ((n + j : ℕ) : ℂ) ∈ leanXiCoefficientSector) :
    ∀ j : Fin 6, xiNaturalConcreteMultiplier n L y (j : ℂ) = 1 := by
  intro j
  unfold xiNaturalConcreteMultiplier
  rw [xiNaturalConcreteLogMultiplier_six_nodes hn hL hy hL12 hmap hsector j]
  exact Complex.exp_zero

end Zeta23.Research.JensenWedge
