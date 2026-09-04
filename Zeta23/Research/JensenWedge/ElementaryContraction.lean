import Zeta23.Research.JensenWedge.LeadingJacobianVariation

/-!
# Concrete elementary contraction certificate

This module assembles the full Fréchet derivative, the fixed inverse, the
finite-scale error, and the inner-box limiting variation into the Jacobian
half of the quantitative branch certificate.
-/

namespace Zeta23.Research.JensenWedge

open Metric Set

noncomputable section

theorem gaugeJacobianInvReal_mul_real :
    gaugeJacobianInvReal * gaugeJacobianReal = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [gaugeJacobianReal, gaugeJacobianInvReal, gaugeJacobian,
      gaugeJacobianInv, Matrix.mul_apply, Fin.sum_univ_succ]

theorem gaugeInverseCLM_comp_center :
    gaugeInverseCLM.comp (branchMatrixCLM gaugeJacobianReal) =
      ContinuousLinearMap.id ℝ BranchPoint := by
  apply ContinuousLinearMap.ext
  intro v
  rw [ContinuousLinearMap.comp_apply]
  change Matrix.mulVec gaugeJacobianInvReal
      (Matrix.mulVec gaugeJacobianReal v) = v
  rw [Matrix.mulVec_mulVec, gaugeJacobianInvReal_mul_real]
  simp

def exactElementaryAffineMap
    (x e : ℝ) (saddle : BranchPoint) (y : BranchPoint) : BranchPoint :=
  exactElementaryParameterMap y x e + saddle

theorem exactElementaryAffineMap_hasFDerivAt
    {y saddle : BranchPoint} {e x : ℝ}
    (halpha : 0 < y 0) (ht : 0 < y 1) (hw : 0 ≤ y 2)
    (hdelta : 0 ≤ y 3) (he : 0 < e) (hx : 0 ≤ x) :
    HasFDerivAt (exactElementaryAffineMap x e saddle)
      (branchMatrixCLM (exactElementaryJacobian y e x)) y := by
  simpa [exactElementaryAffineMap] using
    (exactElementaryParameterMap_hasFDerivAt
      halpha ht hw hdelta he hx).add_const saddle

theorem fixedInverseNewtonMap_exactElementaryAffine_hasFDerivAt
    {y saddle : BranchPoint} {e x : ℝ}
    (halpha : 0 < y 0) (ht : 0 < y 1) (hw : 0 ≤ y 2)
    (hdelta : 0 ≤ y 3) (he : 0 < e) (hx : 0 ≤ x) :
    HasFDerivAt (fixedInverseNewtonMap (exactElementaryAffineMap x e saddle))
      (ContinuousLinearMap.id ℝ BranchPoint -
        gaugeInverseCLM.comp
          (branchMatrixCLM (exactElementaryJacobian y e x))) y := by
  have hG := exactElementaryAffineMap_hasFDerivAt
    (saddle := saddle) halpha ht hw hdelta he hx
  have hPG := gaugeInverseCLM.hasFDerivAt.comp y hG
  have hT := (hasFDerivAt_id y).sub hPG
  simpa [fixedInverseNewtonMap, gaugeInverseCLM_apply, Function.comp_def] using hT

theorem fixedInverse_derivative_defect_identity
    (J : BranchPoint →L[ℝ] BranchPoint) :
    ContinuousLinearMap.id ℝ BranchPoint - gaugeInverseCLM.comp J =
      gaugeInverseCLM.comp (branchMatrixCLM gaugeJacobianReal - J) := by
  rw [ContinuousLinearMap.comp_sub, gaugeInverseCLM_comp_center]

theorem exactElementaryJacobian_innerBox_center_operator_error
    {y : BranchPoint} (hy : y ∈ branchInnerBox)
    {e x : ℝ} (he : 0 < e) (he1 : e ≤ 1) (hx : 0 ≤ x) :
    ‖branchMatrixCLM (exactElementaryJacobian y e x) -
        branchMatrixCLM gaugeJacobianReal‖ ≤
      40000 * (e + x) + 1 / 12500 := by
  have houter := branchInnerBox_subset_outer hy
  have hfinite := exactElementaryJacobian_outerBox_operator_error
    houter he he1 hx
  have hvary := leadingElementaryJacobian_innerBox_operator_error hy
  calc
    ‖branchMatrixCLM (exactElementaryJacobian y e x) -
        branchMatrixCLM gaugeJacobianReal‖ =
      ‖(branchMatrixCLM (exactElementaryJacobian y e x) -
          branchMatrixCLM (leadingElementaryJacobian y)) +
        (branchMatrixCLM (leadingElementaryJacobian y) -
          branchMatrixCLM gaugeJacobianReal)‖ := by congr 1; abel
    _ ≤ ‖branchMatrixCLM (exactElementaryJacobian y e x) -
          branchMatrixCLM (leadingElementaryJacobian y)‖ +
        ‖branchMatrixCLM (leadingElementaryJacobian y) -
          branchMatrixCLM gaugeJacobianReal‖ := norm_add_le _ _
    _ ≤ 40000 * (e + x) + 1 / 12500 := add_le_add hfinite hvary

theorem fixedInverseNewtonMap_exactElementaryAffine_fderiv_norm_le
    {y saddle : BranchPoint} (hy : y ∈ branchInnerBox)
    {e x : ℝ} (he : 0 < e) (he1 : e ≤ 1) (hx : 0 ≤ x) :
    ‖fderiv ℝ (fixedInverseNewtonMap
        (exactElementaryAffineMap x e saddle)) y‖ ≤
      (304 / 3) * (40000 * (e + x) + 1 / 12500) := by
  have ho := branchInnerBox_subset_outer hy
  rcases ho with ⟨ha0, _ha1, ht0, _ht1, hw0, _hw1, hd0, _hd1⟩
  have hderiv := fixedInverseNewtonMap_exactElementaryAffine_hasFDerivAt
    (saddle := saddle) (by linarith) (by linarith) (by linarith)
      (by linarith) he hx
  rw [hderiv.fderiv, fixedInverse_derivative_defect_identity]
  calc
    ‖gaugeInverseCLM.comp
        (branchMatrixCLM gaugeJacobianReal -
          branchMatrixCLM (exactElementaryJacobian y e x))‖ ≤
      ‖gaugeInverseCLM‖ *
        ‖branchMatrixCLM gaugeJacobianReal -
          branchMatrixCLM (exactElementaryJacobian y e x)‖ :=
      ContinuousLinearMap.opNorm_comp_le _ _
    _ = ‖gaugeInverseCLM‖ *
        ‖branchMatrixCLM (exactElementaryJacobian y e x) -
          branchMatrixCLM gaugeJacobianReal‖ := by rw [norm_sub_rev]
    _ ≤ (304 / 3) * (40000 * (e + x) + 1 / 12500) :=
      mul_le_mul gaugeInverseCLM_norm_le
        (exactElementaryJacobian_innerBox_center_operator_error hy he he1 hx)
        (norm_nonneg _) (by norm_num)

/-- At the explicit scale `e+x <= 10^{-8}`, the full inner-box derivative
defect is strictly below the certificate's contraction constant `1/2`. -/
theorem exactElementaryAffine_jacobianIntervalCertificate
    {saddle : BranchPoint} {e x : ℝ}
    (he : 0 < e) (he1 : e ≤ 1) (hx : 0 ≤ x)
    (hscale : e + x ≤ 1 / 100000000) :
    FourJacobianIntervalCertificate (exactElementaryAffineMap x e saddle)
      branchCenter branchInnerRadius := by
  constructor
  · intro y hy
    exact (fixedInverseNewtonMap_exactElementaryAffine_hasFDerivAt
      (saddle := saddle)
      (by have ho := branchInnerBox_subset_outer hy; linarith [ho.1])
      (by have ho := branchInnerBox_subset_outer hy; linarith [ho.2.2.1])
      (by have ho := branchInnerBox_subset_outer hy; linarith [ho.2.2.2.2.1])
      (by have ho := branchInnerBox_subset_outer hy; linarith [ho.2.2.2.2.2.2.1])
      he hx).differentiableAt
  · intro y hy
    have hnorm := fixedInverseNewtonMap_exactElementaryAffine_fderiv_norm_le
      (saddle := saddle) hy he he1 hx
    have hhalf : (304 / 3 : ℝ) *
        (40000 * (e + x) + 1 / 12500) ≤ 1 / 2 := by
      nlinarith
    exact_mod_cast hnorm.trans hhalf

end

end Zeta23.Research.JensenWedge
