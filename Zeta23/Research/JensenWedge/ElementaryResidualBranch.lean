import Zeta23.Research.JensenWedge.ElementaryContraction

/-!
# Elementary center residual and positive branch

This module supplies the residual half of the concrete contraction argument.
It deliberately isolates the remaining analytic input as a norm enclosure for
the exact xi saddle vector.  Once that enclosure and the explicit scale
budget are provided, the kernel constructs the locally unique positive
four-parameter branch.
-/

namespace Zeta23.Research.JensenWedge

noncomputable section

/-- The finite elementary correction at the exact rational center is bounded
in the branch-space sup norm by the componentwise `C^0` enclosure. -/
theorem exactElementaryParameterMap_center_error_norm_le
    {e x : ℝ} (he : 0 < e) (he1 : e ≤ 1) (hx : 0 ≤ x) :
    ‖exactElementaryParameterMap branchCenter x e -
        leadingElementaryParameterMap branchCenter‖ ≤
      10000 * (e + x / e) := by
  have houter := branchInnerBox_subset_outer branchCenter_mem_inner
  have hscale : 0 ≤ 10000 * (e + x / e) := by
    positivity
  rw [pi_norm_le_iff_of_nonneg hscale]
  intro j
  simpa [Real.norm_eq_abs] using
    exactElementaryParameterMap_outerBox_value_error houter he he1 hx j

/-- The center residual separates into the independently controlled
elementary correction and exact-xi saddle correction. -/
theorem exactElementaryAffineMap_center_norm_le
    {saddle : BranchPoint} {epsilon e x : ℝ}
    (he : 0 < e) (he1 : e ≤ 1) (hx : 0 ≤ x)
    (hsaddle : ‖saddle - leadingXiSaddleVector‖ ≤ epsilon) :
    ‖exactElementaryAffineMap x e saddle branchCenter‖ ≤
      10000 * (e + x / e) + epsilon := by
  have hdecomp :
      exactElementaryAffineMap x e saddle branchCenter =
        (exactElementaryParameterMap branchCenter x e -
            leadingElementaryParameterMap branchCenter) +
          (saddle - leadingXiSaddleVector) := by
    ext j
    have hj := congrFun leadingXiParameterMap_center j
    simp only [leadingXiParameterMap, Pi.add_apply, Pi.zero_apply] at hj
    simp only [exactElementaryAffineMap, Pi.add_apply, Pi.sub_apply]
    linarith
  rw [hdecomp]
  exact (norm_add_le _ _).trans
    (add_le_add
      (exactElementaryParameterMap_center_error_norm_le he he1 hx) hsaddle)

/-- An exact saddle enclosure satisfying the displayed rational budget
produces the center-residual interval certificate consumed by Banach's
fixed-point theorem. -/
theorem exactElementaryAffine_residualIntervalCertificate
    {saddle : BranchPoint} {epsilon e x : ℝ}
    (he : 0 < e) (he1 : e ≤ 1) (hx : 0 ≤ x)
    (hsaddle : ‖saddle - leadingXiSaddleVector‖ ≤ epsilon)
    (hbudget : 10000 * (e + x / e) + epsilon ≤
      (3 / 608) * branchInnerRadius) :
    FourResidualIntervalCertificate (exactElementaryAffineMap x e saddle)
      branchCenter branchInnerRadius where
  radius_pos := branchInnerRadius_pos
  center_residual :=
    (exactElementaryAffineMap_center_norm_le he he1 hx hsaddle).trans hbudget

/-- The residual and whole-box Jacobian inequalities now construct the
locally unique positive branch.  The only uninstantiated mathematical datum
is the explicit exact-xi saddle enclosure `hsaddle`; no existence premise is
hidden in this definition. -/
noncomputable def exactElementaryAffine_positiveParameterBranch
    {saddle : BranchPoint} {epsilon e x : ℝ}
    (he : 0 < e) (he1 : e ≤ 1) (hx : 0 ≤ x)
    (hjacobianScale : e + x ≤ 1 / 100000000)
    (hsaddle : ‖saddle - leadingXiSaddleVector‖ ≤ epsilon)
    (hresidualBudget : 10000 * (e + x / e) + epsilon ≤
      (3 / 608) * branchInnerRadius) :
    PositiveParameterBranch (exactElementaryAffineMap x e saddle) :=
  PositiveParameterBranch.ofIntervalCertificates _
    (exactElementaryAffine_residualIntervalCertificate
      he he1 hx hsaddle hresidualBudget)
    (exactElementaryAffine_jacobianIntervalCertificate
      he he1 hx hjacobianScale)

end

end Zeta23.Research.JensenWedge
