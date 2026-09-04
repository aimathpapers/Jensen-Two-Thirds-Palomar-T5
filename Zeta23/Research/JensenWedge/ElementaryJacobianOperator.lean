import Zeta23.Research.JensenWedge.ElementaryFrechet

/-!
# Operator-norm elementary Jacobian certificate

Entrywise interval bounds are converted here into bounds for the actual
continuous linear maps in the branch-space sup norm.  The fixed inverse is
also packaged as a continuous linear map with its exact audited norm bound.
-/

namespace Zeta23.Research.JensenWedge

noncomputable section

/-- Four-by-four entrywise control implies the expected four-row-sum
operator bound in the branch-space sup norm. -/
theorem branchMatrixCLM_sub_norm_le_of_entrywise
    {A B : Matrix (Fin 4) (Fin 4) ℝ} {C : ℝ}
    (hC : 0 ≤ C) (hentry : ∀ i j, |A i j - B i j| ≤ C) :
    ‖branchMatrixCLM A - branchMatrixCLM B‖ ≤ 4 * C := by
  apply ContinuousLinearMap.opNorm_le_bound _ (mul_nonneg (by norm_num) hC)
  intro v
  rw [pi_norm_le_iff_of_nonneg
    (mul_nonneg (mul_nonneg (by norm_num) hC) (norm_nonneg v))]
  intro i
  calc
    ‖((branchMatrixCLM A - branchMatrixCLM B) v) i‖ =
        |∑ j : Fin 4, (A i j - B i j) * v j| := by
      change |(∑ j : Fin 4, A i j * v j) -
          ∑ j : Fin 4, B i j * v j| = _
      rw [← Finset.sum_sub_distrib]
      congr 1
      apply Finset.sum_congr rfl
      intro j _hj
      ring
    _ ≤ ∑ j : Fin 4, |(A i j - B i j) * v j| :=
      Finset.abs_sum_le_sum_abs _ _
    _ = ∑ j : Fin 4, |A i j - B i j| * |v j| := by
      apply Finset.sum_congr rfl
      intro j _hj
      rw [abs_mul]
    _ ≤ ∑ _j : Fin 4, C * ‖v‖ := by
      apply Finset.sum_le_sum
      intro j _hj
      exact (mul_le_mul (hentry i j) (norm_le_pi_norm v j)
        (abs_nonneg _) hC)
    _ = 4 * C * ‖v‖ := by
      simp
      ring

/-- The fixed inverse matrix as a continuous linear map. -/
def gaugeInverseCLM : BranchPoint →L[ℝ] BranchPoint :=
  branchMatrixCLM gaugeJacobianInvReal

theorem gaugeInverseCLM_apply (v : BranchPoint) :
    gaugeInverseCLM v = gaugeInverseAction v := rfl

/-- The exact row-sum estimate `304/3` is an operator-norm certificate. -/
theorem gaugeInverseCLM_norm_le : ‖gaugeInverseCLM‖ ≤ 304 / 3 := by
  apply ContinuousLinearMap.opNorm_le_bound _ (by norm_num)
  intro v
  simpa [gaugeInverseCLM_apply] using gaugeInverseAction_norm_le v

/-- The fixed-box entrywise `C¹` estimate controls the actual derivative in
operator norm. -/
theorem exactElementaryJacobian_outerBox_operator_error
    {y : BranchPoint} (hy : InOuterParameterBox y)
    {e x : ℝ} (he : 0 < e) (he1 : e ≤ 1) (hx : 0 ≤ x) :
    ‖branchMatrixCLM (exactElementaryJacobian y e x) -
        branchMatrixCLM (leadingElementaryJacobian y)‖ ≤
      40000 * (e + x) := by
  have hscale : 0 ≤ 10000 * (e + x) := by positivity
  have h := branchMatrixCLM_sub_norm_le_of_entrywise hscale
    (fun i j => exactElementaryJacobian_outerBox_entry_error
      hy he he1 hx i j)
  nlinarith

end

end Zeta23.Research.JensenWedge
