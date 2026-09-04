import Zeta23.Research.JensenWedge.ConditionalAssembly
import Zeta23.Research.JensenWedge.LeadingSystem

/-!
# Quantitative four-parameter branch and typed certificate builder

This module kernel-checks the finite bridge used by the parameter-branch
argument.  It fixes the coordinate order `(alpha,t,w,delta)`, the exact
rational parameter boxes, and the inverse of the limiting Jacobian.  An
explicit residual enclosure at the center and an explicit derivative-defect
enclosure on the inner box then imply existence and local uniqueness by the
contraction mapping theorem.

The two enclosures are structures with separately named fields.  This module
does not assert that the Riemann-xi asymptotics supply them.  The final part
splits the formerly monolithic analytic input into branch, comparison-root,
sixth-residual, and xi-identification records and proves that these records
construct the existing `JensenWedgeCertificate`.
-/

namespace Zeta23.Research.JensenWedge

open Metric Set

/-- Four real parameters in the analytic gauge order `(alpha,t,w,delta)`. -/
abbrev BranchPoint := Fin 4 → ℝ

/-- The exact limiting branch point `(3,2,16/3,1/3)`. -/
noncomputable def branchCenter : BranchPoint := ![3, 2, 16 / 3, 1 / 3]

/-- The rational compact parameter box used by the paper estimates. -/
def InOuterParameterBox (y : BranchPoint) : Prop :=
  5 / 2 ≤ y 0 ∧ y 0 ≤ 7 / 2 ∧
  7 / 4 ≤ y 1 ∧ y 1 ≤ 9 / 4 ∧
  5 ≤ y 2 ∧ y 2 ≤ 6 ∧
  1 / 4 ≤ y 3 ∧ y 3 ≤ 5 / 12

/-- A fixed rational inner radius.  It is intentionally conservative: the
analytic interval producer must prove its enclosures on this exact box. -/
noncomputable def branchInnerRadius : ℝ := 1 / 1000000

/-- The exact closed sup-norm box on which the contraction is consumed. -/
def branchInnerBox : Set BranchPoint := closedBall branchCenter branchInnerRadius

theorem branchInnerRadius_pos : 0 < branchInnerRadius := by
  norm_num [branchInnerRadius]

theorem branchCenter_mem_inner : branchCenter ∈ branchInnerBox := by
  simp [branchInnerBox, branchInnerRadius]

/-- The fixed inner box lies strictly inside every face of the outer box. -/
theorem branchInnerBox_subset_outer :
    branchInnerBox ⊆ {y | InOuterParameterBox y} := by
  intro y hy
  have hdist : dist y branchCenter ≤ branchInnerRadius := by
    simpa [branchInnerBox, dist_comm] using hy
  have hcoord : ∀ i, |y i - branchCenter i| ≤ branchInnerRadius := by
    intro i
    have hi := (dist_pi_le_iff branchInnerRadius_pos.le).mp hdist i
    simpa [Real.dist_eq] using hi
  have h0 := hcoord 0
  have h1 := hcoord 1
  have h2 := hcoord 2
  have h3 := hcoord 3
  simp [branchCenter] at h0 h1 h2 h3
  norm_num [branchInnerRadius] at h0 h1 h2 h3 ⊢
  rw [abs_le] at h0 h1 h2 h3
  constructor
  · linarith
  constructor
  · linarith
  constructor
  · linarith
  constructor
  · linarith
  constructor
  · linarith
  constructor
  · linarith
  constructor <;> linarith

/-- Jacobi parameters reconstructed from the four gauge coordinates. -/
noncomputable def jacobiA (y : BranchPoint) (x e : ℝ) : ℝ := y 0 / (x * e)
noncomputable def jacobiB (y : BranchPoint) (x e : ℝ) : ℝ := (y 1 + y 2 * e) / x
noncomputable def jacobiC (y : BranchPoint) (x : ℝ) : ℝ := y 1 / x
noncomputable def jacobiD (y : BranchPoint) (x e : ℝ) : ℝ := (1 + y 3 * e) / x

/-- Exact outer-box arithmetic gives `A>B>C>D>0` for the paper's range
`0<e<=1/12` and every positive scale `x`. -/
theorem outerBox_jacobi_ordering
    {y : BranchPoint} (hy : InOuterParameterBox y)
    {x e : ℝ} (hx : 0 < x) (he : 0 < e) (he12 : e ≤ 1 / 12) :
    jacobiA y x e > jacobiB y x e ∧
      jacobiB y x e > jacobiC y x ∧
      jacobiC y x > jacobiD y x e ∧
      jacobiD y x e > 0 := by
  rcases hy with ⟨ha0, ha1, ht0, ht1, hw0, hw1, hd0, hd1⟩
  have hae : 30 ≤ y 0 / e := by
    rw [le_div_iff₀ he]
    nlinarith
  have hBnum : y 1 + y 2 * e ≤ 11 / 4 := by
    nlinarith
  have hABnum : y 1 + y 2 * e < y 0 / e := by
    linarith
  have hwpos : 0 < y 2 * e := mul_pos (lt_of_lt_of_le (by norm_num) hw0) he
  have hCDnum : 1 + y 3 * e < y 1 := by
    nlinarith
  have hDnum : 0 < 1 + y 3 * e := by
    nlinarith
  constructor
  · dsimp [jacobiA, jacobiB]
    have hrewrite : y 0 / (x * e) = (y 0 / e) / x := by
      field_simp
    rw [hrewrite]
    exact (div_lt_div_iff_of_pos_right hx).2 hABnum
  constructor
  · dsimp [jacobiB, jacobiC]
    exact (div_lt_div_iff_of_pos_right hx).2 (by linarith)
  constructor
  · dsimp [jacobiC, jacobiD]
    exact (div_lt_div_iff_of_pos_right hx).2 hCDnum
  · dsimp [jacobiD]
    exact div_pos hDnum hx

/-- The exact inverse matrix, cast to the real gauge coordinate space. -/
def gaugeJacobianInvReal : Matrix (Fin 4) (Fin 4) ℝ :=
  fun i j => (gaugeJacobianInv i j : ℝ)

/-- Application of the fixed inverse in the four-dimensional sup norm. -/
def gaugeInverseAction (v : BranchPoint) : BranchPoint :=
  Matrix.mulVec gaugeJacobianInvReal v

/-- The exact absolute row sums are `87,15,304/3,10/3`; hence the induced
sup-norm bound is `304/3`. -/
theorem gaugeInverse_rowSum_bound (i : Fin 4) :
    ∑ j, |gaugeJacobianInvReal i j| ≤ 304 / 3 := by
  fin_cases i <;>
    norm_num [gaugeJacobianInvReal, gaugeJacobianInv, Fin.sum_univ_succ]

theorem gaugeInverseAction_norm_le (v : BranchPoint) :
    ‖gaugeInverseAction v‖ ≤ (304 / 3) * ‖v‖ := by
  rw [pi_norm_le_iff_of_nonneg (mul_nonneg (by norm_num) (norm_nonneg v))]
  intro i
  calc
    ‖gaugeInverseAction v i‖ = |∑ j, gaugeJacobianInvReal i j * v j| := by
      simp [gaugeInverseAction, Matrix.mulVec, dotProduct, Real.norm_eq_abs]
    _ ≤ ∑ j, |gaugeJacobianInvReal i j * v j| := Finset.abs_sum_le_sum_abs _ _
    _ = ∑ j, |gaugeJacobianInvReal i j| * |v j| := by
      apply Finset.sum_congr rfl
      intro j _
      rw [abs_mul]
    _ ≤ ∑ j, |gaugeJacobianInvReal i j| * ‖v‖ := by
      apply Finset.sum_le_sum
      intro j _
      exact mul_le_mul_of_nonneg_left (norm_le_pi_norm v j) (abs_nonneg _)
    _ = (∑ j, |gaugeJacobianInvReal i j|) * ‖v‖ := by rw [Finset.sum_mul]
    _ ≤ (304 / 3) * ‖v‖ :=
      mul_le_mul_of_nonneg_right (gaugeInverse_rowSum_bound i) (norm_nonneg v)

/-- The real limiting Jacobian in analytic gauge order. -/
def gaugeJacobianReal : Matrix (Fin 4) (Fin 4) ℝ :=
  fun i j => (gaugeJacobian i j : ℝ)

theorem gaugeJacobianReal_mul_inv :
    gaugeJacobianReal * gaugeJacobianInvReal = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [gaugeJacobianReal, gaugeJacobianInvReal, gaugeJacobian,
      gaugeJacobianInv, Matrix.mul_apply, Fin.sum_univ_succ]

theorem gaugeInverseAction_injective : Function.Injective gaugeInverseAction := by
  intro u v huv
  have hmul (z : BranchPoint) :
      Matrix.mulVec gaugeJacobianReal (gaugeInverseAction z) = z := by
    rw [gaugeInverseAction, Matrix.mulVec_mulVec, gaugeJacobianReal_mul_inv]
    simp
  have hleft := congrArg (fun z => Matrix.mulVec gaugeJacobianReal z) huv
  rw [hmul u, hmul v] at hleft
  exact hleft

/-- Fixed-inverse Newton map `T(y)=y-P G(y)`. -/
def fixedInverseNewtonMap (G : BranchPoint → BranchPoint) (y : BranchPoint) : BranchPoint :=
  y - gaugeInverseAction (G y)

theorem fixedInverseNewtonMap_isFixedPt_iff
    {G : BranchPoint → BranchPoint} {y : BranchPoint} :
    Function.IsFixedPt (fixedInverseNewtonMap G) y ↔ G y = 0 := by
  constructor
  · intro h
    have hp : gaugeInverseAction (G y) = 0 := by
      have := h
      simp only [Function.IsFixedPt, fixedInverseNewtonMap] at this
      exact sub_eq_self.mp this
    have hz : gaugeInverseAction (0 : BranchPoint) = 0 := by
      simp [gaugeInverseAction]
    exact gaugeInverseAction_injective (hp.trans hz.symm)
  · intro h
    have hz : gaugeInverseAction (0 : BranchPoint) = 0 := by
      simp [gaugeInverseAction]
    simp [Function.IsFixedPt, fixedInverseNewtonMap, h, hz]

/-- The exact contraction constant one half as a nonnegative real. -/
noncomputable def halfContraction : NNReal := ⟨1 / 2, by norm_num⟩

/-- Exact center-residual interval certificate.  The factor `3/608` is the
reciprocal needed to combine the inverse bound `304/3` with a half-radius
self-map margin. -/
structure FourResidualIntervalCertificate
    (G : BranchPoint → BranchPoint) (center : BranchPoint) (radius : ℝ) : Prop where
  radius_pos : 0 < radius
  center_residual : ‖G center‖ ≤ (3 / 608) * radius

/-- Exact derivative-defect interval certificate for the fixed-inverse map.
This is the finite object an interval producer must establish on the whole
closed box; a center sample is not sufficient. -/
structure FourJacobianIntervalCertificate
    (G : BranchPoint → BranchPoint) (center : BranchPoint) (radius : ℝ) : Prop where
  differentiable : ∀ y ∈ closedBall center radius,
    DifferentiableAt ℝ (fixedInverseNewtonMap G) y
  derivative_defect : ∀ y ∈ closedBall center radius,
    nnnorm (fderiv ℝ (fixedInverseNewtonMap G) y) ≤ halfContraction

/-- The residual enclosure places the Newton image of the center within half
the box radius. -/
theorem center_newton_displacement_le_half
    {G : BranchPoint → BranchPoint} {center : BranchPoint} {radius : ℝ}
    (R : FourResidualIntervalCertificate G center radius) :
    dist (fixedInverseNewtonMap G center) center ≤ radius / 2 := by
  calc
    dist (fixedInverseNewtonMap G center) center = ‖gaugeInverseAction (G center)‖ := by
      simp [fixedInverseNewtonMap]
    _ ≤ (304 / 3) * ‖G center‖ := gaugeInverseAction_norm_le _
    _ ≤ (304 / 3) * ((3 / 608) * radius) := by
      gcongr
      norm_num
      exact R.center_residual
    _ = radius / 2 := by ring

/-- Quantitative four-dimensional contraction theorem.  Exact residual and
Jacobian interval certificates imply a unique zero in the closed sup ball. -/
theorem fourDimensionalBranch_existsUnique
    {G : BranchPoint → BranchPoint} {center : BranchPoint} {radius : ℝ}
    (R : FourResidualIntervalCertificate G center radius)
    (D : FourJacobianIntervalCertificate G center radius) :
    ∃ y ∈ closedBall center radius, G y = 0 ∧
      ∀ z ∈ closedBall center radius, G z = 0 → z = y := by
  let T := fixedInverseNewtonMap G
  let s : Set BranchPoint := closedBall center radius
  have hlip : LipschitzOnWith halfContraction T s :=
    Convex.lipschitzOnWith_of_nnnorm_fderiv_le D.differentiable
      D.derivative_defect (convex_closedBall center radius)
  have hcenter : center ∈ s := by
    simp [s, R.radius_pos.le]
  have hmaps : MapsTo T s s := by
    intro y hy
    have hfirst : dist (T y) (T center) ≤ (1 / 2 : ℝ) * dist y center := by
      have hraw := hlip.dist_le_mul y hy center hcenter
      change dist (T y) (T center) ≤ (halfContraction : ℝ) * dist y center at hraw
      have hhalf : (halfContraction : ℝ) = 1 / 2 := rfl
      simpa [hhalf] using hraw
    have hsecond : dist (T center) center ≤ radius / 2 := by
      exact center_newton_displacement_le_half R
    have htotal : dist (T y) center ≤ radius := by
      calc
        dist (T y) center ≤ dist (T y) (T center) + dist (T center) center :=
          dist_triangle _ _ _
        _ ≤ (1 / 2 : ℝ) * dist y center + radius / 2 := add_le_add hfirst hsecond
        _ ≤ (1 / 2 : ℝ) * radius + radius / 2 := by
          gcongr
          exact hy
        _ = radius := by ring
    exact htotal
  have hcontract : ContractingWith halfContraction (hmaps.restrict T s s) := by
    constructor
    · change (1 / 2 : ℝ) < 1
      norm_num
    · exact hlip.mapsToRestrict hmaps
  have hscomplete : IsComplete s := Metric.isClosed_closedBall.isComplete
  have hfinite : edist center (T center) ≠ ⊤ := edist_ne_top _ _
  rcases hcontract.exists_fixedPoint' hscomplete hmaps hcenter hfinite with
    ⟨y, hy, hTy, _⟩
  refine ⟨y, hy, fixedInverseNewtonMap_isFixedPt_iff.mp hTy, ?_⟩
  intro z hz hGz
  have hTz : Function.IsFixedPt T z :=
    fixedInverseNewtonMap_isFixedPt_iff.mpr hGz
  have hTy' : Function.IsFixedPt T y := hTy
  have hdist := hlip.dist_le_mul z hz y hy
  rw [hTz.eq, hTy'.eq] at hdist
  have hnonneg : 0 ≤ dist z y := dist_nonneg
  have : dist z y = 0 := by
    have hhalf : (halfContraction : ℝ) = 1 / 2 := rfl
    rw [hhalf] at hdist
    nlinarith
  exact dist_eq_zero.mp this

/-- A locally unique positive parameter branch, with the exact equation and
box membership retained rather than erased after applying Banach. -/
structure PositiveParameterBranch (G : BranchPoint → BranchPoint) where
  parameters : BranchPoint
  in_inner_box : parameters ∈ branchInnerBox
  equation : G parameters = 0
  locally_unique : ∀ z ∈ branchInnerBox, G z = 0 → z = parameters

theorem PositiveParameterBranch.in_outer_box
    {G : BranchPoint → BranchPoint} (B : PositiveParameterBranch G) :
    InOuterParameterBox B.parameters :=
  branchInnerBox_subset_outer B.in_inner_box

theorem PositiveParameterBranch.coordinates_positive
    {G : BranchPoint → BranchPoint} (B : PositiveParameterBranch G) :
    0 < B.parameters 0 ∧ 1 < B.parameters 1 ∧
      0 < B.parameters 2 ∧ 0 < B.parameters 3 := by
  rcases B.in_outer_box with ⟨ha0, _, ht0, _, hw0, _, hd0, _⟩
  constructor
  · linarith
  constructor
  · linarith
  constructor
  · linarith
  · linarith

theorem PositiveParameterBranch.jacobi_ordering
    {G : BranchPoint → BranchPoint} (B : PositiveParameterBranch G)
    {x e : ℝ} (hx : 0 < x) (he : 0 < e) (he12 : e ≤ 1 / 12) :
    jacobiA B.parameters x e > jacobiB B.parameters x e ∧
      jacobiB B.parameters x e > jacobiC B.parameters x ∧
      jacobiC B.parameters x > jacobiD B.parameters x e ∧
      jacobiD B.parameters x e > 0 :=
  outerBox_jacobi_ordering B.in_outer_box hx he he12

/-- Exact interval data on the fixed inner box constructs the locally unique
positive branch. -/
noncomputable def PositiveParameterBranch.ofIntervalCertificates
    (G : BranchPoint → BranchPoint)
    (R : FourResidualIntervalCertificate G branchCenter branchInnerRadius)
    (D : FourJacobianIntervalCertificate G branchCenter branchInnerRadius) :
    PositiveParameterBranch G := by
  let h := fourDimensionalBranch_existsUnique R D
  exact {
    parameters := Classical.choose h
    in_inner_box := (Classical.choose_spec h).1
    equation := (Classical.choose_spec h).2.1
    locally_unique := (Classical.choose_spec h).2.2
  }

/-! ## Non-circular localization and radius thresholds -/

/-- Ratio-free endpoint positivity is fixed before localization. -/
def preLocalizationThreshold : ℝ := 256

/-- The derived localization constant, not the transposed stale value. -/
noncomputable def localizationConstant : ℝ := 12 + 8 * Real.sqrt 6

/-- Rational upper envelope fixed only after deriving `localizationConstant`. -/
def localizationThreshold : ℝ := preLocalizationThreshold * 32 ^ 2

theorem localizationConstant_pos : 0 < localizationConstant := by
  dsimp [localizationConstant]
  positivity

theorem localizationConstant_lt_32 : localizationConstant < 32 := by
  have hsqrt : Real.sqrt 6 < 5 / 2 := by
    nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 6), Real.sqrt_nonneg 6]
  dsimp [localizationConstant]
  nlinarith

theorem localizationThreshold_eq : localizationThreshold = 262144 := by
  norm_num [localizationThreshold, preLocalizationThreshold]

theorem preLocalizationThreshold_lt_localizationThreshold :
    preLocalizationThreshold < localizationThreshold := by
  norm_num [preLocalizationThreshold, localizationThreshold]

theorem localization_controls_squared_constant :
    preLocalizationThreshold * localizationConstant ^ 2 < localizationThreshold := by
  have hpre : 0 < preLocalizationThreshold := by norm_num [preLocalizationThreshold]
  have hsq : localizationConstant ^ 2 < 32 ^ 2 := by
    nlinarith [localizationConstant_pos, localizationConstant_lt_32]
  dsimp [localizationThreshold]
  nlinarith

/-- Radius constants are chosen only after the localization threshold.  The
two nonvanishing neighbor terms are exposed individually. -/
structure RadiusThresholdStage where
  K_r : ℝ
  C₀ : ℝ
  C₁ : ℝ
  K_r_pos : 0 < K_r
  C₀_nonneg : 0 ≤ C₀
  C₁_nonneg : 0 ≤ C₁
  constant_neighbors : 8 * C₁ / K_r + 8 * C₀ / K_r ^ 2 < 1 / 4

/-- The final integer threshold is chosen after `K_r`; all vanishing and
branch-readiness requirements remain named rather than hidden in “large n”. -/
structure EventualThresholdStage (R : RadiusThresholdStage) where
  n₀ : ℕ
  n_at_least_128 : 128 ≤ n₀
  branch_ready : ℕ → Prop
  vanishing_neighbors_ready : ℕ → Prop
  radius_dominates_degree : ℕ → Prop
  analytic_domain_ready : ℕ → Prop
  branch_after : ∀ n, n₀ ≤ n → branch_ready n
  neighbors_after : ∀ n, n₀ ≤ n → vanishing_neighbors_ready n
  radius_after : ∀ n, n₀ ≤ n → radius_dominates_degree n
  domain_after : ∀ n, n₀ ≤ n → analytic_domain_ready n

/-! ## Typed final-certificate inputs -/

/-- Identification and regularity data connecting the transformed multiplier
to the target xi Jensen polynomial. -/
structure XiCoefficientEstimate
    (J transformed : ℝ → ℝ) where
  transformed_continuous : Continuous transformed
  scale : ℝ
  normalization : ℝ
  scale_pos : 0 < scale
  normalization_ne_zero : normalization ≠ 0
  identify : ∀ y, transformed y = J (-y / scale) / normalization

/-- Root-separation data for the comparison model, explicitly tied to the
four parameters that generated it. -/
structure ComparisonRootCertificate (comparison : ℝ → ℝ) (d : ℕ) where
  parameters : BranchPoint
  a : Fin d → ℝ
  b : Fin d → ℝ
  positive_left : ∀ i, 0 < a i
  ordered : ∀ i, a i < b i
  separated : ∀ i j, i < j → b i < a j
  model_change : ∀ i, comparison (a i) * comparison (b i) < 0

/-- The sixth-order analytic remainder is consumed only through the two
endpoint relative-error bounds needed by sign transfer. -/
structure SixthResidualCertificate
    (comparison transformed : ℝ → ℝ) {d : ℕ}
    (roots : ComparisonRootCertificate comparison d) where
  relative_left : ∀ i, |transformed (roots.a i) / comparison (roots.a i) - 1| < 1
  relative_right : ∀ i, |transformed (roots.b i) / comparison (roots.b i) - 1| < 1

/-- All remaining analytic inputs, split along their actual theorem seams. -/
structure JensenWedgeAnalyticInputs
    (J : ℝ → ℝ) (G : BranchPoint → BranchPoint) (d : ℕ) where
  branch : PositiveParameterBranch G
  comparison : ℝ → ℝ
  transformed : ℝ → ℝ
  comparison_roots : ComparisonRootCertificate comparison d
  parameters_match : comparison_roots.parameters = branch.parameters
  sixth_residual : SixthResidualCertificate comparison transformed comparison_roots
  xi_estimate : XiCoefficientEstimate J transformed

/-- The typed analytic inputs construct the old proof-firewall certificate;
no field is synthesized from an unnamed global premise. -/
def JensenWedgeAnalyticInputs.toJensenWedgeCertificate
    {J : ℝ → ℝ} {G : BranchPoint → BranchPoint} {d : ℕ}
    (I : JensenWedgeAnalyticInputs J G d) : JensenWedgeCertificate J d where
  comparison := I.comparison
  transformed := I.transformed
  intervals := {
    a := I.comparison_roots.a
    b := I.comparison_roots.b
    nonnegative_left := fun i => (I.comparison_roots.positive_left i).le
    ordered := I.comparison_roots.ordered
    separated := fun i j hij => (I.comparison_roots.separated i j hij).le
    model_change := I.comparison_roots.model_change
    relative_left := I.sixth_residual.relative_left
    relative_right := I.sixth_residual.relative_right
  }
  transformed_continuous := I.xi_estimate.transformed_continuous
  scale := I.xi_estimate.scale
  normalization := I.xi_estimate.normalization
  scale_pos := I.xi_estimate.scale_pos
  normalization_ne_zero := I.xi_estimate.normalization_ne_zero
  identify := I.xi_estimate.identify

theorem JensenWedgeAnalyticInputs.target_hasDistinctNegativeRoots
    {J : ℝ → ℝ} {G : BranchPoint → BranchPoint} {d : ℕ}
    (I : JensenWedgeAnalyticInputs J G d) :
    HasDistinctNegativeRoots J d :=
  I.toJensenWedgeCertificate.target_hasDistinctNegativeRoots

end Zeta23.Research.JensenWedge
