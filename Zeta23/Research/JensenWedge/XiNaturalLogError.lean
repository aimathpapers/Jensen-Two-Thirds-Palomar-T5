import Zeta23.Research.JensenWedge.XiNaturalAuxiliaryFactorization
import Zeta23.Research.JensenWedge.XiLogError

/-!
# Branch-fixed logarithmic error for the natural auxiliary moment

The Gamma-free factorization has a sharper moment-only relative error.  The
fixed sector is so remote that this error lies in the closed half-disc about
zero.  Consequently `1 + error` stays in the open right half-plane, and its
principal logarithm is a single holomorphic branch on the entire sector.
-/

namespace Zeta23.Research.JensenWedge

open Complex Set

noncomputable section

theorem complexXiNaturalAuxiliaryRelativeError_norm_le_half
    {M : ℂ} (hM : M ∈ leanXiCoefficientSector) :
    ‖complexXiNaturalAuxiliaryRelativeError M‖ ≤ 1 / 2 := by
  let N : ℂ := coefficientMellinParameter M
  let C : ℝ := fullThetaMomentErrorCoefficient
  have hN : N ∈ leanSaddleSector :=
    leanTwoShiftAdmissible_base (leanCoefficientSector_admissible hM.2)
  have hNpos : 0 < ‖N‖ := norm_pos_iff.mpr
    (leanSaddleSector_quantitative hN).parameter_ne_zero
  have hlognonneg : 0 ≤ Real.log ‖N‖ := by
    have hlog := leanSaddleSector_log_re_gt hN
    rw [Complex.log_re] at hlog
    linarith
  have hconstant :
      100 * C ≤ manuscriptXiCoefficientErrorCoefficient := by
    norm_num [C, manuscriptXiCoefficientErrorCoefficient,
      complexXiCoefficientErrorCoefficient,
      fullThetaMomentErrorCoefficient]
  calc
    ‖complexXiNaturalAuxiliaryRelativeError M‖ ≤
        (100 * C) * Real.log ‖N‖ / ‖N‖ := by
      simpa only [C, N] using
        complexXiNaturalAuxiliaryRelativeError_norm_le hM
    _ ≤ manuscriptXiCoefficientErrorCoefficient *
          Real.log ‖N‖ / ‖N‖ := by
      apply div_le_div_of_nonneg_right _ hNpos.le
      exact mul_le_mul_of_nonneg_right hconstant hlognonneg
    _ ≤ 1 / 2 := by
      simpa only [N] using manuscriptXiCoefficientErrorRate_le_half hM

theorem one_add_complexXiNaturalAuxiliaryRelativeError_ne_zero
    {M : ℂ} (hM : M ∈ leanXiCoefficientSector) :
    1 + complexXiNaturalAuxiliaryRelativeError M ≠ 0 := by
  intro hzero
  have herr : complexXiNaturalAuxiliaryRelativeError M = -1 := by
    linear_combination hzero
  have hhalf := complexXiNaturalAuxiliaryRelativeError_norm_le_half hM
  rw [herr] at hhalf
  norm_num at hhalf

theorem one_add_complexXiNaturalAuxiliaryRelativeError_re_pos
    {M : ℂ} (hM : M ∈ leanXiCoefficientSector) :
    0 < (1 + complexXiNaturalAuxiliaryRelativeError M).re := by
  have hhalf := complexXiNaturalAuxiliaryRelativeError_norm_le_half hM
  have habs := Complex.abs_re_le_norm
    (complexXiNaturalAuxiliaryRelativeError M)
  rw [abs_le] at habs
  norm_num
  linarith

/-- The canonical logarithmic error in the natural auxiliary factorization.
Its branch is fixed by the open-right-half-plane estimate. -/
def complexXiNaturalAuxiliaryLogError (M : ℂ) : ℂ :=
  log (1 + complexXiNaturalAuxiliaryRelativeError M)

theorem exp_complexXiNaturalAuxiliaryLogError
    {M : ℂ} (hM : M ∈ leanXiCoefficientSector) :
    exp (complexXiNaturalAuxiliaryLogError M) =
      1 + complexXiNaturalAuxiliaryRelativeError M := by
  unfold complexXiNaturalAuxiliaryLogError
  exact exp_log (one_add_complexXiNaturalAuxiliaryRelativeError_ne_zero hM)

theorem differentiableAt_complexXiNaturalAuxiliaryLogError
    {M : ℂ} (hM : M ∈ leanXiCoefficientSector) :
    DifferentiableAt ℂ complexXiNaturalAuxiliaryLogError M := by
  have hinner : DifferentiableAt ℂ
      (fun z => 1 + complexXiNaturalAuxiliaryRelativeError z) M :=
    DifferentiableAt.add (differentiableAt_const _)
      ((differentiableOn_complexXiNaturalAuxiliaryRelativeError M hM).differentiableAt
        (isOpen_leanXiCoefficientSector.mem_nhds hM))
  have hslit : 1 + complexXiNaturalAuxiliaryRelativeError M ∈ slitPlane :=
    Or.inl (one_add_complexXiNaturalAuxiliaryRelativeError_re_pos hM)
  unfold complexXiNaturalAuxiliaryLogError
  exact (Complex.differentiableAt_log hslit).comp M hinner

theorem differentiableOn_complexXiNaturalAuxiliaryLogError :
    DifferentiableOn ℂ complexXiNaturalAuxiliaryLogError
      leanXiCoefficientSector := by
  intro M hM
  exact (differentiableAt_complexXiNaturalAuxiliaryLogError hM).differentiableWithinAt

theorem complexXiNaturalAuxiliaryLogError_norm_le
    {M : ℂ} (hM : M ∈ leanXiCoefficientSector) :
    ‖complexXiNaturalAuxiliaryLogError M‖ ≤
      (3 / 2 : ℝ) * ‖complexXiNaturalAuxiliaryRelativeError M‖ := by
  unfold complexXiNaturalAuxiliaryLogError
  exact Complex.norm_log_one_add_half_le_self
    (complexXiNaturalAuxiliaryRelativeError_norm_le_half hM)

end

end Zeta23.Research.JensenWedge
