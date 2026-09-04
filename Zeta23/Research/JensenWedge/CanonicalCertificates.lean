import Zeta23.Research.JensenWedge.QuantitativeBranch
import Zeta23.Research.JensenWedge.SaddleOrderSix

/-!
# Concrete exact certificates

This module constructs the certificate records whose fields are already
finite exact algebra.  In particular it constructs the positive branch for
the limiting four-equation system and the explicit radius-constant stage.

It deliberately does not construct either xi-dependent interval input:
`FourResidualIntervalCertificate` for the perturbed xi map and
`FourJacobianIntervalCertificate` on its whole box remain analytic obligations.
-/

namespace Zeta23.Research.JensenWedge

open Metric Set

noncomputable section

/-- All finite order-six saddle facts on one concrete bidisc point. -/
structure SaddleFiniteCertificate (r sigma : ℂ) : Prop where
  r_in_box : ‖r‖ ≤ 7 / 50
  sigma_in_box : ‖sigma‖ ≤ 7 / 50
  scaled_factor_ne_zero : 1 + r - (3 / 4) * sigma ≠ 0
  reduced_denominator_ne_zero : h6ReducedDenominator r sigma ≠ 0
  order_six_bound : ‖saddleH6 r sigma‖ < 10000

/-- The exact finite bounds now construct one certificate rather than
remaining a collection of unrelated facts. -/
theorem saddleFiniteCertificate_of_mem_bidisc
    {r sigma : ℂ} (hr : ‖r‖ ≤ 7 / 50) (hsigma : ‖sigma‖ ≤ 7 / 50) :
    SaddleFiniteCertificate r sigma where
  r_in_box := hr
  sigma_in_box := hsigma
  scaled_factor_ne_zero := saddle_scaled_factor_ne_zero hr hsigma
  reduced_denominator_ne_zero := h6ReducedDenominator_ne_zero hr hsigma
  order_six_bound := saddleH6_norm_lt_tenThousand hr hsigma

/-- The four leading residuals in the analytic coordinate order
`(alpha,t,w,delta)`. -/
def leadingGaugeResidual (y : BranchPoint) : BranchPoint := ![
  y 0 * y 2 + y 0 * y 3 * (y 1) ^ 2 + (y 1) ^ 2 -
    2 * y 0 * (y 1) ^ 2,
  y 2 + y 3 * (y 1) ^ 3 - (y 1) ^ 3,
  3 * (y 2 + y 3 * (y 1) ^ 4) - 2 * (y 1) ^ 4,
  4 * (y 2 + y 3 * (y 1) ^ 5) - 2 * (y 1) ^ 5
]

theorem leadingGaugeResidual_eq_zero_iff (y : BranchPoint) :
    leadingGaugeResidual y = 0 ↔
      SixthOrderLeadingSystem (y 1) (y 2) (y 3) (y 0) := by
  constructor
  · intro h
    have h0 := congrFun h 0
    have h1 := congrFun h 1
    have h2 := congrFun h 2
    have h3 := congrFun h 3
    simp [leadingGaugeResidual] at h0 h1 h2 h3
    exact ⟨by linarith, by linarith, by linarith, by linarith⟩
  · intro h
    ext i
    fin_cases i <;> simp [leadingGaugeResidual]
    · linarith [h.orderOne]
    · linarith [h.orderTwo]
    · linarith [h.orderThree]
    · linarith [h.orderFour]

theorem leadingGaugeResidual_center :
    leadingGaugeResidual branchCenter = 0 := by
  apply (leadingGaugeResidual_eq_zero_iff branchCenter).2
  simpa [branchCenter] using sixthOrderLeadingSystem_candidate

/-- The limiting residual has no second zero in the fixed inner box. -/
theorem leadingGaugeResidual_unique_in_inner
    {y : BranchPoint} (hy : y ∈ branchInnerBox)
    (hzero : leadingGaugeResidual y = 0) :
    y = branchCenter := by
  have houter := branchInnerBox_subset_outer hy
  rcases houter with ⟨ha0, _ha1, ht0, _ht1, hw0, _hw1, _hd0, _hd1⟩
  have hsystem := (leadingGaugeResidual_eq_zero_iff y).1 hzero
  have hunique := sixthOrderLeadingSystem_unique_of_t_w_pos
    (by linarith : 0 < y 1) (by linarith : 0 < y 2) hsystem
  rcases hunique with ⟨ht, hw, hdelta, halpha⟩
  ext i
  fin_cases i <;> simp [branchCenter, ht, hw, hdelta, halpha]

/-- A concrete exact positive branch for the limiting system.  This is not
the perturbed xi branch. -/
def limitingPositiveParameterBranch :
    PositiveParameterBranch leadingGaugeResidual where
  parameters := branchCenter
  in_inner_box := branchCenter_mem_inner
  equation := leadingGaugeResidual_center
  locally_unique := fun _ hy hzero => leadingGaugeResidual_unique_in_inner hy hzero

/-- The center-residual certificate for the limiting system is constructed,
not assumed. -/
theorem leadingResidualIntervalCertificate :
    FourResidualIntervalCertificate leadingGaugeResidual branchCenter
      branchInnerRadius where
  radius_pos := branchInnerRadius_pos
  center_residual := by
    rw [leadingGaugeResidual_center, norm_zero]
    norm_num [branchInnerRadius]

/-- The exact constants used after localization.  `C1=96` is a rational
upper envelope; the paper's sharper strict estimate is not needed for this
finite inequality. -/
def canonicalRadiusThresholdStage : RadiusThresholdStage where
  K_r := 4096
  C₀ := 48
  C₁ := 96
  K_r_pos := by norm_num
  C₀_nonneg := by norm_num
  C₁_nonneg := by norm_num
  constant_neighbors := by norm_num

theorem canonicalRadiusThresholdStage_values :
    canonicalRadiusThresholdStage.K_r = 4096 ∧
      canonicalRadiusThresholdStage.C₀ = 48 ∧
      canonicalRadiusThresholdStage.C₁ = 96 := by
  norm_num [canonicalRadiusThresholdStage]

theorem limitingBranch_jacobi_ordering
    {x e : ℝ} (hx : 0 < x) (he : 0 < e) (he12 : e ≤ 1 / 12) :
    jacobiA limitingPositiveParameterBranch.parameters x e >
        jacobiB limitingPositiveParameterBranch.parameters x e ∧
      jacobiB limitingPositiveParameterBranch.parameters x e >
        jacobiC limitingPositiveParameterBranch.parameters x ∧
      jacobiC limitingPositiveParameterBranch.parameters x >
        jacobiD limitingPositiveParameterBranch.parameters x e ∧
      jacobiD limitingPositiveParameterBranch.parameters x e > 0 :=
  limitingPositiveParameterBranch.jacobi_ordering hx he he12

end

end Zeta23.Research.JensenWedge
