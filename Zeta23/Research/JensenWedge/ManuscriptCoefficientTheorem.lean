import Zeta23.Research.JensenWedge.ManuscriptCorrectionBounds

/-!
# Manuscript-normalized coefficient theorem

This module transfers the already checked coefficient asymptotic from its
exact factored main to the simplified main printed in manuscript Theorem 7.1.
-/

namespace Zeta23.Research.JensenWedge

open Complex Filter Set

noncomputable section

/-- Relative error when the actual coefficient is normalized by the main
printed in manuscript Theorem 7.1. -/
def manuscriptXiCoefficientRelativeError (M : ℂ) : ℂ :=
  manuscriptMainCorrection M * (1 + complexXiCoefficientRelativeError M) - 1

def manuscriptXiCoefficientErrorCoefficient : ℝ :=
  20 + 21 * complexXiCoefficientErrorCoefficient

theorem complexXiCoefficientMoment_manuscript_factorization
    {M : ℂ} (hM : M ∈ leanXiCoefficientSector) :
    complexXiCoefficientMoment M = manuscriptXiCoefficientMain M *
      (1 + manuscriptXiCoefficientRelativeError M) := by
  rw [complexXiCoefficientMoment_factorization hM,
    complexXiCoefficientMain_eq_manuscript_mul_correction hM]
  unfold manuscriptXiCoefficientRelativeError
  ring

theorem manuscriptXiCoefficientMain_ne_zero
    {M : ℂ} (hM : M ∈ leanXiCoefficientSector) :
    manuscriptXiCoefficientMain M ≠ 0 := by
  have hfactored := complexXiCoefficientMain_ne_zero hM
  intro hzero
  apply hfactored
  rw [complexXiCoefficientMain_eq_manuscript_mul_correction hM, hzero,
    zero_mul]

theorem manuscriptXiCoefficientRelativeError_norm_le
    {M : ℂ} (hM : M ∈ leanXiCoefficientSector) :
    let N := coefficientMellinParameter M
    ‖manuscriptXiCoefficientRelativeError M‖ ≤
      manuscriptXiCoefficientErrorCoefficient * Real.log ‖N‖ / ‖N‖ := by
  let N : ℂ := coefficientMellinParameter M
  let q : ℝ := Real.log ‖N‖ / ‖N‖
  let correction : ℂ := manuscriptMainCorrection M
  let error : ℂ := complexXiCoefficientRelativeError M
  let A : ℝ := complexXiCoefficientErrorCoefficient
  have hN : N ∈ leanSaddleSector :=
    leanTwoShiftAdmissible_base (leanCoefficientSector_admissible hM.2)
  have hNlarge := leanSaddleSector_parameterNorm_ge_fiveHundredBillion hN
  have hNpos : 0 < ‖N‖ := by linarith
  have hlogpos : 0 < Real.log ‖N‖ := by
    have h := leanSaddleSector_log_re_gt hN
    rw [Complex.log_re] at h
    linarith
  have hqnonneg : 0 ≤ q := div_nonneg hlogpos.le hNpos.le
  have hqone : q ≤ 1 := by
    apply (div_le_one hNpos).2
    nlinarith [Real.log_le_sub_one_of_pos hNpos]
  have hA : 0 ≤ A := by
    norm_num [A, complexXiCoefficientErrorCoefficient,
      fullThetaMomentErrorCoefficient]
  have hcorrection : ‖correction - 1‖ ≤ 20 * q := by
    dsimp only [correction, q]
    convert manuscriptMainCorrection_sub_one_norm_le hM using 1 <;> ring
  have herror : ‖error‖ ≤ A * q := by
    dsimp only [error, A, q, N]
    convert complexXiCoefficientRelativeError_norm_le hM using 1 <;> ring
  have honeError : ‖1 + error‖ ≤ 1 + A * q := by
    calc
      ‖1 + error‖ ≤ ‖(1 : ℂ)‖ + ‖error‖ := norm_add_le _ _
      _ ≤ 1 + A * q := by norm_num; gcongr
  change ‖correction * (1 + error) - 1‖ ≤
    (20 + 21 * A) * Real.log ‖N‖ / ‖N‖
  have hright : (20 + 21 * A) * Real.log ‖N‖ / ‖N‖ =
      (20 + 21 * A) * q := by dsimp only [q]; ring
  rw [hright]
  have hid : correction * (1 + error) - 1 =
      (correction - 1) * (1 + error) + error := by ring
  rw [hid]
  calc
    ‖(correction - 1) * (1 + error) + error‖ ≤
        ‖correction - 1‖ * ‖1 + error‖ + ‖error‖ := by
      rw [← norm_mul]
      exact norm_add_le _ _
    _ ≤ (20 * q) * (1 + A * q) + A * q := by gcongr
    _ ≤ (20 + 21 * A) * q := by
      have hqSq : q ^ 2 ≤ q := by nlinarith
      nlinarith [mul_le_mul_of_nonneg_left hqSq hA]

/-- The manuscript statement of the sectorial coefficient theorem: its
displayed main is nonzero, the factorization is exact, and the relative error
has a concrete logarithmic rate. -/
theorem complexXiCoefficient_manuscript_sector_asymptotic
    {M : ℂ} (hM : M ∈ leanXiCoefficientSector) :
    let N := coefficientMellinParameter M
    manuscriptXiCoefficientMain M ≠ 0 ∧
      complexXiCoefficientMoment M = manuscriptXiCoefficientMain M *
        (1 + manuscriptXiCoefficientRelativeError M) ∧
      ‖manuscriptXiCoefficientRelativeError M‖ ≤
        manuscriptXiCoefficientErrorCoefficient * Real.log ‖N‖ / ‖N‖ := by
  exact ⟨manuscriptXiCoefficientMain_ne_zero hM,
    complexXiCoefficientMoment_manuscript_factorization hM,
    manuscriptXiCoefficientRelativeError_norm_le hM⟩

theorem differentiableAt_coefficientReindexCorrection
    {N : ℂ} (hN : N ∈ leanSaddleSector) :
    DifferentiableAt ℂ coefficientReindexCorrection N := by
  have hNre : 0 < N.re := leanSaddleSector_re_pos hN
  have hN2re : 0 < (N + 2).re := by
    norm_num
    linarith
  have hlogN : DifferentiableAt ℂ log N :=
    Complex.differentiableAt_log
      (Complex.mem_slitPlane_iff.mpr (Or.inl hNre))
  have hlogN2 : DifferentiableAt ℂ (fun z : ℂ => log (z + 2)) N :=
    (Complex.differentiableAt_log
      (Complex.mem_slitPlane_iff.mpr (Or.inl hN2re))).comp N
        (differentiableAt_id.add_const 2)
  unfold coefficientReindexCorrection
  fun_prop

theorem differentiableAt_coefficientGaussianCorrection
    {N : ℂ} (hN : N ∈ leanSaddleSector) :
    DifferentiableAt ℂ coefficientGaussianCorrection N := by
  have hKdiff := (hasDerivAt_saddleCurvatureAlong hN).differentiableAt
  have hKne : saddleCurvatureAlong N ≠ 0 := by
    have hKre : 0 < (saddleCurvatureAlong N).re := by
      rw [saddleCurvatureAlong_eq hN]
      exact quantitativeSaddleBranch_curvature_re_pos hN
    intro hzero
    rw [hzero] at hKre
    simp at hKre
  have hright : DifferentiableAt ℂ
      (fun z : ℂ => exp (1 / (2 * saddleCurvatureAlong z))) N := by
    have hden : DifferentiableAt ℂ
        (fun z : ℂ => 2 * saddleCurvatureAlong z) N :=
      (differentiableAt_const (2 : ℂ)).mul hKdiff
    have hdenne : 2 * saddleCurvatureAlong N ≠ 0 :=
      mul_ne_zero (by norm_num) hKne
    exact ((differentiableAt_const (1 : ℂ)).div hden hdenne).cexp
  have heq : coefficientGaussianCorrection =ᶠ[nhds N]
      fun z : ℂ => exp (1 / (2 * saddleCurvatureAlong z)) := by
    filter_upwards [isOpen_leanSaddleSector.mem_nhds hN] with z hz
    unfold coefficientGaussianCorrection
    rw [saddleCurvatureAlong_eq hz]
  exact hright.congr_of_eventuallyEq heq

theorem differentiableAt_coefficientCancellationCorrection
    {N : ℂ} (hN : N ∈ leanSaddleSector) :
    DifferentiableAt ℂ coefficientCancellationCorrection N := by
  have hbranch := (hasDerivAt_quantitativeSaddleBranch hN).differentiableAt
  have hcoefficient : DifferentiableAt ℂ coefficientMomentMultiplier N := by
    unfold coefficientMomentMultiplier
    fun_prop
  have hcne := coefficientMomentMultiplier_ne_zero_of_sector hN
  unfold coefficientCancellationCorrection
  exact (differentiableAt_const (1 : ℂ)).sub
    ((hbranch.pow 2).div hcoefficient hcne)

theorem differentiableAt_manuscriptMainCorrection
    {M : ℂ} (hM : M ∈ leanXiCoefficientSector) :
    DifferentiableAt ℂ manuscriptMainCorrection M := by
  let N : ℂ := coefficientMellinParameter M
  have hN : N ∈ leanSaddleSector :=
    leanTwoShiftAdmissible_base (leanCoefficientSector_admissible hM.2)
  have hNdiff : DifferentiableAt ℂ coefficientMellinParameter M :=
    differentiableAt_coefficientMellinParameter M
  have hreindex : DifferentiableAt ℂ
      (fun z => coefficientReindexCorrection (coefficientMellinParameter z)) M :=
    by
      simpa only [Function.comp_def] using
        (differentiableAt_coefficientReindexCorrection hN).comp M hNdiff
  have hgaussian : DifferentiableAt ℂ
      (fun z => coefficientGaussianCorrection (coefficientMellinParameter z)) M :=
    by
      simpa only [Function.comp_def] using
        (differentiableAt_coefficientGaussianCorrection hN).comp M hNdiff
  have hcancellation : DifferentiableAt ℂ
      (fun z => coefficientCancellationCorrection
        (coefficientMellinParameter z)) M :=
    by
      simpa only [Function.comp_def] using
        (differentiableAt_coefficientCancellationCorrection hN).comp M hNdiff
  change DifferentiableAt ℂ
    (fun z => coefficientReindexCorrection (coefficientMellinParameter z) *
      coefficientGaussianCorrection (coefficientMellinParameter z) *
        coefficientCancellationCorrection (coefficientMellinParameter z)) M
  exact (hreindex.mul hgaussian).mul hcancellation

theorem manuscriptMainCorrection_ne_zero
    {M : ℂ} (hM : M ∈ leanXiCoefficientSector) :
    manuscriptMainCorrection M ≠ 0 := by
  have hfactored := complexXiCoefficientMain_ne_zero hM
  intro hzero
  apply hfactored
  rw [complexXiCoefficientMain_eq_manuscript_mul_correction hM, hzero,
    mul_zero]

theorem differentiableAt_manuscriptXiCoefficientMain
    {M : ℂ} (hM : M ∈ leanXiCoefficientSector) :
    DifferentiableAt ℂ manuscriptXiCoefficientMain M := by
  have hright : DifferentiableAt ℂ
      (fun z => complexXiCoefficientMain z / manuscriptMainCorrection z) M :=
    (differentiableAt_complexXiCoefficientMain hM).div
      (differentiableAt_manuscriptMainCorrection hM)
      (manuscriptMainCorrection_ne_zero hM)
  have heq : manuscriptXiCoefficientMain =ᶠ[nhds M]
      fun z => complexXiCoefficientMain z / manuscriptMainCorrection z := by
    filter_upwards [isOpen_leanXiCoefficientSector.mem_nhds hM] with z hz
    rw [complexXiCoefficientMain_eq_manuscript_mul_correction hz]
    field_simp [manuscriptMainCorrection_ne_zero hz]
  exact hright.congr_of_eventuallyEq heq

theorem differentiableAt_manuscriptXiCoefficientRelativeError
    {M : ℂ} (hM : M ∈ leanXiCoefficientSector) :
    DifferentiableAt ℂ manuscriptXiCoefficientRelativeError M := by
  have hgenericAt : DifferentiableAt ℂ
      (holomorphicRelativeError complexXiCoefficientMoment
        manuscriptXiCoefficientMain) M := by
    unfold holomorphicRelativeError
    exact ((differentiableAt_complexXiCoefficientMoment hM).div
      (differentiableAt_manuscriptXiCoefficientMain hM)
      (manuscriptXiCoefficientMain_ne_zero hM)).sub_const 1
  have heq : manuscriptXiCoefficientRelativeError =ᶠ[nhds M]
      holomorphicRelativeError complexXiCoefficientMoment
        manuscriptXiCoefficientMain := by
    filter_upwards [isOpen_leanXiCoefficientSector.mem_nhds hM] with z hz
    unfold holomorphicRelativeError
    rw [complexXiCoefficientMoment_manuscript_factorization hz]
    field_simp [manuscriptXiCoefficientMain_ne_zero hz]
    ring
  exact hgenericAt.congr_of_eventuallyEq heq

theorem differentiableOn_manuscriptXiCoefficientMain :
    DifferentiableOn ℂ manuscriptXiCoefficientMain
      leanXiCoefficientSector := by
  intro M hM
  exact (differentiableAt_manuscriptXiCoefficientMain hM).differentiableWithinAt

theorem differentiableOn_manuscriptXiCoefficientRelativeError :
    DifferentiableOn ℂ manuscriptXiCoefficientRelativeError
      leanXiCoefficientSector := by
  intro M hM
  exact
    (differentiableAt_manuscriptXiCoefficientRelativeError hM).differentiableWithinAt

/-- Holomorphic form of the coefficient theorem with exactly the main printed
in manuscript Theorem 7.1. -/
theorem complexXiCoefficient_manuscript_sector_holomorphic_asymptotic :
    IsOpen leanXiCoefficientSector ∧
      DifferentiableOn ℂ complexXiCoefficientMoment leanXiCoefficientSector ∧
      DifferentiableOn ℂ manuscriptXiCoefficientMain leanXiCoefficientSector ∧
      DifferentiableOn ℂ manuscriptXiCoefficientRelativeError
        leanXiCoefficientSector ∧
      ∀ M ∈ leanXiCoefficientSector,
        manuscriptXiCoefficientMain M ≠ 0 ∧
          complexXiCoefficientMoment M = manuscriptXiCoefficientMain M *
            (1 + manuscriptXiCoefficientRelativeError M) ∧
          ‖manuscriptXiCoefficientRelativeError M‖ ≤
            manuscriptXiCoefficientErrorCoefficient *
              Real.log ‖coefficientMellinParameter M‖ /
                ‖coefficientMellinParameter M‖ := by
  exact ⟨isOpen_leanXiCoefficientSector,
    differentiableOn_complexXiCoefficientMoment,
    differentiableOn_manuscriptXiCoefficientMain,
    differentiableOn_manuscriptXiCoefficientRelativeError,
    fun M hM => complexXiCoefficient_manuscript_sector_asymptotic hM⟩

end

end Zeta23.Research.JensenWedge
