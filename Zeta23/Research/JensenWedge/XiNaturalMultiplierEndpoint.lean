import Zeta23.Research.JensenWedge.FiniteMultiplierStability
import Zeta23.Research.JensenWedge.XiNaturalConcreteMultiplierSpecialization
import Zeta23.Research.JensenWedge.XiNaturalCriticalRadius
import Zeta23.Research.JensenWedge.XiNaturalSixCoefficientMatch

/-!
# Concrete xi multiplier endpoint

This module connects the analytic xi multiplier to the actual transformed
xi Jensen polynomial and instantiates the finite Newton--Cauchy estimate.
-/

namespace Zeta23.Research.JensenWedge

open Complex Finset Metric Polynomial Set
open fwdDiff

noncomputable section

/-- Real integer-node sequence carried by the concrete analytic multiplier. -/
def xiNaturalConcreteRealMultiplier
    (n : ℕ) (L : ℝ) (y : BranchPoint) (j : ℕ) : ℝ :=
  (xiNaturalConcreteMultiplier n L y (j : ℂ)).re

theorem xiNaturalConcreteRealMultiplier_nat
    {n : ℕ} (hn : 0 < n) {L : ℝ} (hL : 0 < L)
    {y : BranchPoint} (hy : InOuterParameterBox y)
    (hL12 : 1 / L ≤ (1 : ℝ) / 12) (j : ℕ)
    (h0 : (n : ℂ) ∈ leanXiCoefficientSector)
    (hj : ((n + j : ℕ) : ℂ) ∈ leanXiCoefficientSector) :
    xiNaturalConcreteRealMultiplier n L y j =
      Real.exp (xiNaturalActualLogCoordinate n L y j -
        xiNaturalModelLogCoordinate n L y j) := by
  unfold xiNaturalConcreteRealMultiplier xiNaturalConcreteMultiplier
  rw [xiNaturalConcreteLogMultiplier_nat hn hL hy hL12 j h0 hj]
  change (Complex.exp
      ((xiNaturalActualLogCoordinate n L y j -
        xiNaturalModelLogCoordinate n L y j : ℝ) : ℂ)).re = _
  rw [Complex.exp_re]
  simp

/-- The actual transformed-xi polynomial is literally the comparison
polynomial with its coefficients multiplied by the concrete xi multiplier.
-/
theorem xiNaturalActualLogPolynomial_eq_concreteMultiplierTransform
    {n : ℕ} (hn : 0 < n) {d : ℕ} {L : ℝ} (hL : 0 < L)
    (hL12 : 1 / L ≤ (1 : ℝ) / 12)
    {y : BranchPoint} (hy : InOuterParameterBox y)
    (hsector : ∀ j : ℕ, j ≤ d →
      ((n + j : ℕ) : ℂ) ∈ leanXiCoefficientSector) :
    xiNaturalActualLogPolynomial n d L y =
      coefficientMultiplierTransform
        (xiNaturalModelLogPolynomial n d L y)
        (xiNaturalConcreteRealMultiplier n L y) := by
  have h0 : (n : ℂ) ∈ leanXiCoefficientSector := by
    simpa using hsector 0 (Nat.zero_le d)
  ext j
  rw [coeff_xiNaturalActualLogPolynomial,
    coeff_coefficientMultiplierTransform,
    coeff_xiNaturalModelLogPolynomial]
  by_cases hjd : j ≤ d
  · rw [if_pos hjd, if_pos hjd,
      xiNaturalConcreteRealMultiplier_nat hn hL hy hL12 j h0
        (hsector j hjd), Real.exp_sub]
    have hmodel : Real.exp (xiNaturalModelLogCoordinate n L y j) ≠ 0 :=
      (Real.exp_pos _).ne'
    field_simp
  · rw [if_neg hjd, if_neg hjd]
    simp

theorem xiNaturalActualLogPolynomial_eq_comparisonMultiplierTransform_of_explicitCutoff
    {n : ℕ} (hn : xiNaturalExplicitCutoffIndex ≤ n) (d : ℕ) :
    xiNaturalActualLogPolynomial n d (xiNaturalSaddleScale n)
        (exactXiPositiveParameterBranch_of_explicitCutoff hn).parameters =
      coefficientMultiplierTransform
        (xiNaturalComparisonPolynomial n d (xiNaturalSaddleScale n)
          (exactXiPositiveParameterBranch_of_explicitCutoff hn).parameters)
        (xiNaturalConcreteRealMultiplier n (xiNaturalSaddleScale n)
          (exactXiPositiveParameterBranch_of_explicitCutoff hn).parameters) := by
  let B := exactXiPositiveParameterBranch_of_explicitCutoff hn
  let C := xiNaturalSaddleIntervalConditions_of_explicitCutoff hn
  rw [← xiNaturalModelLogPolynomial_eq_comparison_of_explicitCutoff hn d]
  apply xiNaturalActualLogPolynomial_eq_concreteMultiplierTransform
    C.n_pos C.saddleScale_pos
    (explicitCutoff_inverse_xiNaturalSaddleScale_le_twelve hn) B.in_outer_box
  intro j hjd
  apply nat_mem_leanXiCoefficientSector
  exact C.coefficient_center_in_remote_sector.trans_le (by
    exact_mod_cast Nat.le_add_right n j)

/-- The real node sequence has the exact first six values required by the
finite multiplier theorem. -/
theorem xiNaturalConcreteRealMultiplier_six_nodes_of_explicitCutoff
    {n : ℕ} (hn : xiNaturalExplicitCutoffIndex ≤ n) :
    ∀ j : Fin 6,
      xiNaturalConcreteRealMultiplier n (xiNaturalSaddleScale n)
        (exactXiPositiveParameterBranch_of_explicitCutoff hn).parameters j = 1 := by
  let B := exactXiPositiveParameterBranch_of_explicitCutoff hn
  let C := xiNaturalSaddleIntervalConditions_of_explicitCutoff hn
  intro j
  unfold xiNaturalConcreteRealMultiplier
  rw [xiNaturalConcreteMultiplier_six_nodes C.n_pos C.saddleScale_pos
    B.in_outer_box (explicitCutoff_inverse_xiNaturalSaddleScale_le_twelve hn)
    B.equation (nat_six_samples_mem_leanXiCoefficientSector
      C.coefficient_center_in_remote_sector) j]
  norm_num

/-- Consequently the first four positive forward differences vanish. -/
theorem xiNaturalConcreteRealMultiplier_forwardDiff_zero_of_explicitCutoff
    {n : ℕ} (hn : xiNaturalExplicitCutoffIndex ≤ n)
    (k : ℕ) (hk1 : 1 ≤ k) (hk4 : k ≤ 4) :
    ((fwdDiff 1)^[k]
      (xiNaturalConcreteRealMultiplier n (xiNaturalSaddleScale n)
        (exactXiPositiveParameterBranch_of_explicitCutoff hn).parameters)) 0 = 0 := by
  let c := xiNaturalConcreteMultiplier n (xiNaturalSaddleScale n)
    (exactXiPositiveParameterBranch_of_explicitCutoff hn).parameters
  have hcomplex : complexForwardDiff k c 0 = 0 := by
    simpa using complexForwardDiff_eq_zero_of_eq_const_on_nat_segment c 1 k hk1 0 (by
      intro j hj
      let j6 : Fin 6 := ⟨j, by omega⟩
      simpa only [Nat.zero_add] using
        xiNaturalConcreteMultiplier_six_nodes
          (xiNaturalSaddleIntervalConditions_of_explicitCutoff hn).n_pos
          (xiNaturalSaddleIntervalConditions_of_explicitCutoff hn).saddleScale_pos
          (exactXiPositiveParameterBranch_of_explicitCutoff hn).in_outer_box
          (explicitCutoff_inverse_xiNaturalSaddleScale_le_twelve hn)
          (exactXiPositiveParameterBranch_of_explicitCutoff hn).equation
          (nat_six_samples_mem_leanXiCoefficientSector
            (xiNaturalSaddleIntervalConditions_of_explicitCutoff hn).coefficient_center_in_remote_sector)
          j6)
  have hbridge := complexForwardDiff_nat_eq_fwdDiff_iter c k 0
  have hfdComplex :
      ((fwdDiff 1)^[k] (fun m : ℕ => c (m : ℂ))) 0 = 0 := by
    rw [← hbridge]
    simpa using hcomplex
  have hre := congrArg Complex.re hfdComplex
  rw [re_fwdDiff_iter_nat] at hre
  change ((fwdDiff 1)^[k] (fun m : ℕ => (c (m : ℂ)).re)) 0 = 0
  exact hre

/-- Cauchy's estimate on the explicit multiplier tube supplies all higher
forward-difference bounds with the uniform constant `2`. -/
theorem xiNaturalConcreteRealMultiplier_forwardDiff_bound
    {K : ℝ} (hK : xiNaturalConcreteWedgeConstant ≤ K)
    {n d : ℕ} (hn : xiNaturalExplicitCutoffIndex ≤ n)
    (hW : TwoThirdsWedge K n d) (hd : 6 ≤ d)
    (k : ℕ) (hkd : k ≤ d) :
    let y := (exactXiPositiveParameterBranch_of_explicitCutoff hn).parameters
    let L := xiNaturalSaddleScale n
    let B := residualParameterB y n (1 / L)
    let R := 8192 * Real.sqrt (B * d)
    |((fwdDiff 1)^[k]
      (xiNaturalConcreteRealMultiplier n L y)) 0| ≤
        (k.factorial : ℝ) * 2 / R ^ k := by
  let P := exactXiPositiveParameterBranch_of_explicitCutoff hn
  let C := xiNaturalSaddleIntervalConditions_of_explicitCutoff hn
  let y := P.parameters
  let L := xiNaturalSaddleScale n
  let B := residualParameterB y n (1 / L)
  let S := Real.sqrt (B * d)
  let R : ℝ := 8192 * S
  let r := xiNaturalMultiplierRadius n d L y
  let c := xiNaturalConcreteMultiplier n L y
  have hgeometry := xiNaturalMultiplier_radius_geometry_of_explicitCutoff
    (xiNaturalConcreteWedge_ge_geometry.trans hK) hn hW hd
  dsimp only at hgeometry
  rcases hgeometry with ⟨hr5, hrInterior, hhalf, hA, hB, hC, hD⟩
  have hRpos : 0 < R := by
    have hBpos := (xiNaturalResidualParameters_pos C.n_pos C.saddleScale_pos
      (explicitCutoff_inverse_xiNaturalSaddleScale_le_twelve hn)
      P.in_outer_box).2.1
    have hdpos : (0 : ℝ) < d := by exact_mod_cast (show 0 < d by omega)
    dsimp only [R, S]
    positivity
  have hrpos : 0 < r := lt_of_lt_of_le (by norm_num) hr5
  have hsectorBall : ∀ w ∈ Metric.ball (0 : ℂ) (2 * r),
      (n : ℂ) + w ∈ leanXiCoefficientSector := by
    intro w hw
    have hwNorm : ‖w‖ < 2 * r := by
      simpa [Metric.mem_ball] using hw
    apply manuscriptCauchy_closedBall_subset_sector
      C.coefficient_center_in_remote_sector
    rw [Metric.mem_closedBall, dist_eq_norm]
    have hcast : (((n : ℝ) : ℂ)) = (n : ℂ) := by norm_cast
    rw [hcast]
    have hdiff : (n : ℂ) + w - (n : ℂ) = w := by ring
    rw [hdiff]
    unfold manuscriptInteriorCauchyRadius at hrInterior
    unfold manuscriptCauchyRadius
    linarith
  have hlogAnalytic := analyticOnNhd_xiNaturalConcreteLogMultiplier_ball
    hhalf hA hB hC hD hsectorBall
  have hcAnalytic : AnalyticOnNhd ℂ c (Metric.ball (0 : ℂ) (2 * r)) := by
    change AnalyticOnNhd ℂ
      (fun z => Complex.exp (xiNaturalConcreteLogMultiplier n L y z))
      (Metric.ball (0 : ℂ) (2 * r))
    exact hlogAnalytic.cexp
  have hdisc : ∀ t ∈ Set.Icc (0 : ℝ) (0 + (k : ℝ)),
      DiffContOnCl ℂ c (Metric.ball (t : ℂ) R) := by
    intro t ht
    apply DifferentiableOn.diffContOnCl
    intro z hz
    have hzclosed : z ∈ Metric.closedBall (t : ℂ) R :=
      Metric.closure_ball_subset_closedBall hz
    have hzt : ‖z - (t : ℂ)‖ ≤ R := by
      simpa [Metric.mem_closedBall, dist_eq_norm] using hzclosed
    have ht0 : 0 ≤ t := ht.1
    have htk : t ≤ k := by simpa using ht.2
    have htd : t ≤ d := htk.trans (by exact_mod_cast hkd)
    have htnorm : ‖(t : ℂ)‖ = t := by
      rw [norm_real, Real.norm_eq_abs, abs_of_nonneg ht0]
    have hzbig : z ∈ Metric.ball (0 : ℂ) (2 * r) := by
      rw [Metric.mem_ball, dist_zero_right]
      calc
        ‖z‖ = ‖(z - (t : ℂ)) + (t : ℂ)‖ := by congr 1 <;> ring
        _ ≤ ‖z - (t : ℂ)‖ + ‖(t : ℂ)‖ := norm_add_le _ _
        _ ≤ R + (d : ℝ) := by rw [htnorm]; linarith
        _ = r := by
          dsimp only [R, S, r, xiNaturalMultiplierRadius, B]
          ring
        _ < 2 * r := by linarith
    exact (hcAnalytic z hzbig).differentiableAt.differentiableWithinAt
  have hsphere : ∀ t ∈ Set.Icc (0 : ℝ) (0 + (k : ℝ)),
      ∀ z ∈ Metric.sphere (t : ℂ) R, ‖c z‖ ≤ (2 : ℝ) := by
    intro t ht z hz
    have ht0 : 0 ≤ t := ht.1
    have htk : t ≤ k := by simpa using ht.2
    have htd : t ≤ d := htk.trans (by exact_mod_cast hkd)
    have hzt : ‖z - (t : ℂ)‖ ≤ R := by
      rw [Metric.mem_sphere, dist_eq_norm] at hz
      linarith
    have hztube : z ∈ xiNaturalMultiplierTube n d L y := by
      refine ⟨t, ⟨ht0, htd⟩, ?_⟩
      simpa only [R, S, B] using hzt
    have hunit := xiNaturalConcreteMultiplier_sub_one_norm_lt_one_on_tube
      hK hn hW hd hztube
    calc
      ‖c z‖ = ‖(c z - 1) + 1‖ := by congr 1 <;> ring
      _ ≤ ‖c z - 1‖ + ‖(1 : ℂ)‖ := norm_add_le _ _
      _ ≤ 2 := by norm_num; linarith
  have hcauchy := norm_complexForwardDiff_le_of_cauchy_tube
    c k 0 R 2 hRpos hdisc hsphere
  have hbridge := complexForwardDiff_nat_eq_fwdDiff_iter c k 0
  have hre := re_fwdDiff_iter_nat (fun m : ℕ => c (m : ℂ)) k 0
  change |((fwdDiff 1)^[k] (fun m : ℕ => (c (m : ℂ)).re)) 0| ≤
    (k.factorial : ℝ) * 2 / R ^ k
  rw [← hre, ← hbridge]
  simp only [Nat.cast_zero]
  have hcauchy' : ‖complexForwardDiff k c (0 : ℂ)‖ ≤
      (k.factorial : ℝ) * 2 / R ^ k := by
    simpa using hcauchy
  exact (abs_re_le_norm _).trans hcauchy'

/-- One explicit constant covers both the analytic multiplier tube and the
terminating `_3F_2` critical-radius theorem. -/
def xiNaturalMultiplierEndpointWedgeConstant : ℝ :=
  xiNaturalConcreteWedgeConstant + xiNaturalCriticalRadiusWedgeConstant

theorem xiNaturalMultiplierEndpoint_ge_concrete :
    xiNaturalConcreteWedgeConstant ≤ xiNaturalMultiplierEndpointWedgeConstant := by
  unfold xiNaturalMultiplierEndpointWedgeConstant
  have h : 0 ≤ xiNaturalCriticalRadiusWedgeConstant := by
    norm_num [xiNaturalCriticalRadiusWedgeConstant]
  linarith

theorem xiNaturalMultiplierEndpoint_ge_critical :
    xiNaturalCriticalRadiusWedgeConstant ≤
      xiNaturalMultiplierEndpointWedgeConstant := by
  unfold xiNaturalMultiplierEndpointWedgeConstant
  have hgeom : 0 ≤ xiNaturalMultiplierGeometryWedgeConstant := by
    norm_num [xiNaturalMultiplierGeometryWedgeConstant,
      xiNaturalMultiplierDegreeCap]
  have h : 0 ≤ xiNaturalConcreteWedgeConstant :=
    hgeom.trans xiNaturalConcreteWedge_ge_geometry
  linarith

/-- Concrete relative-error theorem at every nonzero critical value of the
published comparison polynomial.  Its only literature input is the typed
Jacobi/MSS/MMP record already used by the comparison root theorem. -/
theorem xiNaturalActualComparison_relativeError_lt_one_at_critical
    {K : ℝ} (hK : xiNaturalMultiplierEndpointWedgeConstant ≤ K)
    {n d : ℕ} (hn : xiNaturalExplicitCutoffIndex ≤ n)
    (hW : TwoThirdsWedge K n d) (hd : 6 ≤ d)
    (I : XiNaturalClassicalRootInputs n d (xiNaturalSaddleScale n)
      (exactXiPositiveParameterBranch_of_explicitCutoff hn).parameters)
    {x : ℝ}
    (hp : (xiNaturalComparisonPolynomial n d (xiNaturalSaddleScale n)
      (exactXiPositiveParameterBranch_of_explicitCutoff hn).parameters).eval x ≠ 0)
    (hcritical : (xiNaturalComparisonPolynomial n d (xiNaturalSaddleScale n)
      (exactXiPositiveParameterBranch_of_explicitCutoff hn).parameters).derivative.eval x = 0) :
    let y := (exactXiPositiveParameterBranch_of_explicitCutoff hn).parameters
    let L := xiNaturalSaddleScale n
    |(xiNaturalActualLogPolynomial n d L y).eval x /
        (xiNaturalComparisonPolynomial n d L y).eval x - 1| < 1 := by
  let y := (exactXiPositiveParameterBranch_of_explicitCutoff hn).parameters
  let L := xiNaturalSaddleScale n
  let p := xiNaturalComparisonPolynomial n d L y
  let P := xiNaturalActualLogPolynomial n d L y
  let c := xiNaturalConcreteRealMultiplier n L y
  let B := residualParameterB y n (1 / L)
  let S := Real.sqrt (B * d)
  let R : ℝ := 8192 * S
  let T : ℝ := 4096 * S
  have hconcrete : xiNaturalConcreteWedgeConstant ≤ K :=
    xiNaturalMultiplierEndpoint_ge_concrete.trans hK
  have hcriticalK : xiNaturalCriticalRadiusWedgeConstant ≤ K :=
    xiNaturalMultiplierEndpoint_ge_critical.trans hK
  have hdegree : p.natDegree ≤ d := by
    exact terminating3F2Polynomial_natDegree_le d _ _ _ _ _
  have htransform : P = coefficientMultiplierTransform p c := by
    exact xiNaturalActualLogPolynomial_eq_comparisonMultiplierTransform_of_explicitCutoff hn d
  have hc0 : c 0 = 1 := by
    dsimp only [c, L, y, P]
    have hnode :=
      xiNaturalConcreteRealMultiplier_six_nodes_of_explicitCutoff hn (0 : Fin 6)
    convert hnode using 1 <;> norm_num
  have hzero : ∀ k, 1 ≤ k → k ≤ 4 → ((fwdDiff 1)^[k] c) 0 = 0 := by
    intro k hk1 hk4
    exact xiNaturalConcreteRealMultiplier_forwardDiff_zero_of_explicitCutoff
      hn k hk1 hk4
  have hfd : ∀ k, 5 ≤ k → k ≤ d →
      |((fwdDiff 1)^[k] c) 0| ≤ (k.factorial : ℝ) * 2 / R ^ k := by
    intro k _hk5 hkd
    exact xiNaturalConcreteRealMultiplier_forwardDiff_bound
      hconcrete hn hW hd k hkd
  have hcrit : ∀ k ≤ d, |polynomialDerivativeRatio p x k| ≤ T ^ k := by
    exact xiNaturalComparison_critical_radius_of_explicitCutoff
      hcriticalK hn hW I (by omega) hp hcritical
  have hBpos := (xiNaturalResidualParameters_pos
    (xiNaturalSaddleIntervalConditions_of_explicitCutoff hn).n_pos
    (xiNaturalSaddleIntervalConditions_of_explicitCutoff hn).saddleScale_pos
    (explicitCutoff_inverse_xiNaturalSaddleScale_le_twelve hn)
    (exactXiPositiveParameterBranch_of_explicitCutoff hn).in_outer_box).2.1
  have hS : 0 ≤ S := Real.sqrt_nonneg _
  have hR : 0 < R := by
    have hdpos : (0 : ℝ) < d := by exact_mod_cast (show 0 < d by omega)
    dsimp only [R, S, B]
    positivity
  apply finiteNewtonRelativeError_lt_one p P c d x 2 R T
    (by omega) hdegree htransform hp hc0 hzero hfd hcrit
  · norm_num
  · norm_num
  · dsimp only [T]
    positivity
  · exact hR
  · dsimp only [T, R]
    ring_nf
    exact le_rfl

end

end Zeta23.Research.JensenWedge
