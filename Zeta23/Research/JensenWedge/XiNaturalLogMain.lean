import Zeta23.Research.JensenWedge.XiNaturalLogError
import Zeta23.Research.JensenWedge.ManuscriptCorrectionBounds

/-!
# An explicit holomorphic logarithm of the natural auxiliary main

The natural auxiliary main is a product of a dyadic exponential, the saddle
moment, and the two-shift denominator.  We give each factor a branch-safe
logarithm on the fixed paired sector.  In particular the denominator is
factored as `16 (N+2) (N+1) (1-L_N^2/c_N)`; the final factor stays in the
open right half-plane.  The sum of these logarithms exponentiates exactly to
the natural main.
-/

namespace Zeta23.Research.JensenWedge

open Complex Set

noncomputable section

/-- Branch-safe logarithm of the exact two-shift denominator. -/
def complexXiNaturalTwoShiftLog (M : ℂ) : ℂ :=
  let N := coefficientMellinParameter M
  log 16 + log (N + 2) + log (N + 1) +
    log (coefficientCancellationCorrection N)

theorem coefficientCancellationCorrection_norm_sub_one_le_half
    {M : ℂ} (hM : M ∈ leanXiCoefficientSector) :
    ‖coefficientCancellationCorrection (coefficientMellinParameter M) - 1‖ ≤
      1 / 2 := by
  let N : ℂ := coefficientMellinParameter M
  have hN : N ∈ leanSaddleSector :=
    leanTwoShiftAdmissible_base (leanCoefficientSector_admissible hM.2)
  have hNpos : 0 < ‖N‖ := norm_pos_iff.mpr
    (leanSaddleSector_quantitative hN).parameter_ne_zero
  have hlognonneg : 0 ≤ Real.log ‖N‖ := by
    have hlog := leanSaddleSector_log_re_gt hN
    rw [Complex.log_re] at hlog
    linarith
  have hconstant : (1 : ℝ) ≤ manuscriptXiCoefficientErrorCoefficient := by
    norm_num [manuscriptXiCoefficientErrorCoefficient,
      complexXiCoefficientErrorCoefficient, fullThetaMomentErrorCoefficient]
  calc
    ‖coefficientCancellationCorrection N - 1‖ ≤
        Real.log ‖N‖ / ‖N‖ := coefficientCancellationCorrection_sub_one_norm_le hN
    _ = 1 * (Real.log ‖N‖ / ‖N‖) := by ring
    _ ≤ manuscriptXiCoefficientErrorCoefficient *
          (Real.log ‖N‖ / ‖N‖) := by
      gcongr
    _ = manuscriptXiCoefficientErrorCoefficient *
          Real.log ‖N‖ / ‖N‖ := by ring
    _ ≤ 1 / 2 := by
      simpa only [N] using manuscriptXiCoefficientErrorRate_le_half hM

theorem coefficientCancellationCorrection_re_pos
    {M : ℂ} (hM : M ∈ leanXiCoefficientSector) :
    0 < (coefficientCancellationCorrection
      (coefficientMellinParameter M)).re := by
  let c := coefficientCancellationCorrection (coefficientMellinParameter M)
  have hhalf := coefficientCancellationCorrection_norm_sub_one_le_half hM
  have hre := Complex.abs_re_le_norm (c - 1)
  rw [abs_le] at hre
  change 0 < c.re
  norm_num at hre
  linarith

theorem exp_complexXiNaturalTwoShiftLog
    {M : ℂ} (hM : M ∈ leanXiCoefficientSector) :
    exp (complexXiNaturalTwoShiftLog M) =
      coefficientMomentMultiplier (coefficientMellinParameter M) -
        quantitativeSaddleBranch (coefficientMellinParameter M) ^ 2 := by
  let N : ℂ := coefficientMellinParameter M
  let c : ℂ := coefficientMomentMultiplier N
  have hN : N ∈ leanSaddleSector :=
    leanTwoShiftAdmissible_base (leanCoefficientSector_admissible hM.2)
  have hNre : 0 < N.re := leanSaddleSector_re_pos hN
  have hN1 : N + 1 ≠ 0 := by
    intro hzero
    have hre := congrArg Complex.re hzero
    norm_num at hre
    linarith
  have hN2 : N + 2 ≠ 0 := by
    intro hzero
    have hre := congrArg Complex.re hzero
    norm_num at hre
    linarith
  have hcancel : coefficientCancellationCorrection N ≠ 0 := by
    have hre : 0 < (coefficientCancellationCorrection N).re := by
      simpa only [N] using coefficientCancellationCorrection_re_pos hM
    intro hzero
    rw [hzero] at hre
    simp at hre
  have hc : c ≠ 0 := coefficientMomentMultiplier_ne_zero_of_sector hN
  have hfactor : c * coefficientCancellationCorrection N =
      c - quantitativeSaddleBranch N ^ 2 := by
    unfold coefficientCancellationCorrection
    change c * (1 - quantitativeSaddleBranch N ^ 2 / c) =
      c - quantitativeSaddleBranch N ^ 2
    field_simp [hc]
  unfold complexXiNaturalTwoShiftLog
  rw [exp_add, exp_add, exp_add, exp_log (by norm_num : (16 : ℂ) ≠ 0),
    exp_log hN2, exp_log hN1, exp_log hcancel]
  simpa only [c, coefficientMomentMultiplier, N] using hfactor

theorem differentiableAt_coefficientCancellationCorrection_comp
    {M : ℂ} (hM : M ∈ leanXiCoefficientSector) :
    DifferentiableAt ℂ
      (fun z => coefficientCancellationCorrection
        (coefficientMellinParameter z)) M := by
  let N : ℂ := coefficientMellinParameter M
  have hN : N ∈ leanSaddleSector :=
    leanTwoShiftAdmissible_base (leanCoefficientSector_admissible hM.2)
  have hNdiff : DifferentiableAt ℂ coefficientMellinParameter M :=
    differentiableAt_coefficientMellinParameter M
  have hbranch : DifferentiableAt ℂ
      (fun z => quantitativeSaddleBranch (coefficientMellinParameter z)) M := by
    simpa only [Function.comp_def] using
      (hasDerivAt_quantitativeSaddleBranch hN).differentiableAt.comp M hNdiff
  have hcoefficient : DifferentiableAt ℂ
      (fun z => coefficientMomentMultiplier (coefficientMellinParameter z)) M := by
    unfold coefficientMomentMultiplier coefficientMellinParameter
    fun_prop
  have hc : coefficientMomentMultiplier N ≠ 0 :=
    coefficientMomentMultiplier_ne_zero_of_sector hN
  change DifferentiableAt ℂ
    (fun z => 1 -
      quantitativeSaddleBranch (coefficientMellinParameter z) ^ 2 /
        coefficientMomentMultiplier (coefficientMellinParameter z)) M
  exact (differentiableAt_const (c := (1 : ℂ))).sub
    ((hbranch.pow 2).div hcoefficient (by simpa only [N] using hc))

theorem differentiableAt_complexXiNaturalTwoShiftLog
    {M : ℂ} (hM : M ∈ leanXiCoefficientSector) :
    DifferentiableAt ℂ complexXiNaturalTwoShiftLog M := by
  let N : ℂ := coefficientMellinParameter M
  have hN : N ∈ leanSaddleSector :=
    leanTwoShiftAdmissible_base (leanCoefficientSector_admissible hM.2)
  have hNre : 0 < N.re := leanSaddleSector_re_pos hN
  have hNdiff : DifferentiableAt ℂ coefficientMellinParameter M :=
    differentiableAt_coefficientMellinParameter M
  have hlogN2 : DifferentiableAt ℂ
      (fun z => log (coefficientMellinParameter z + 2)) M :=
    (Complex.differentiableAt_log
      (Complex.mem_slitPlane_iff.mpr (Or.inl (by
        change 0 < (N + 2).re
        norm_num
        linarith)))).comp M (hNdiff.add_const 2)
  have hlogN1 : DifferentiableAt ℂ
      (fun z => log (coefficientMellinParameter z + 1)) M :=
    (Complex.differentiableAt_log
      (Complex.mem_slitPlane_iff.mpr (Or.inl (by
        change 0 < (N + 1).re
        norm_num
        linarith)))).comp M (hNdiff.add_const 1)
  have hcancel := differentiableAt_coefficientCancellationCorrection_comp hM
  have hlogCancel : DifferentiableAt ℂ
      (fun z => log (coefficientCancellationCorrection
        (coefficientMellinParameter z))) M := by
    simpa only [Function.comp_def] using
      (Complex.differentiableAt_log
        (Complex.mem_slitPlane_iff.mpr
          (Or.inl (coefficientCancellationCorrection_re_pos hM)))).comp M hcancel
  change DifferentiableAt ℂ
    (fun z => log 16 + log (coefficientMellinParameter z + 2) +
      log (coefficientMellinParameter z + 1) +
        log (coefficientCancellationCorrection
          (coefficientMellinParameter z))) M
  exact (((differentiableAt_const (c := log (16 : ℂ))).add hlogN2).add
    hlogN1).add hlogCancel

/-- Explicit logarithm of the natural auxiliary main. -/
def complexXiNaturalAuxiliaryLogMain (M : ℂ) : ℂ :=
  -(2 * M + 2) * log 2 +
    saddleMomentLogMain (coefficientMellinParameter M) +
    complexXiNaturalTwoShiftLog M

theorem exp_complexXiNaturalAuxiliaryLogMain
    {M : ℂ} (hM : M ∈ leanXiCoefficientSector) :
    exp (complexXiNaturalAuxiliaryLogMain M) =
      complexXiNaturalAuxiliaryMain M := by
  let N : ℂ := coefficientMellinParameter M
  have hN : N ∈ leanSaddleSector :=
    leanTwoShiftAdmissible_base (leanCoefficientSector_admissible hM.2)
  unfold complexXiNaturalAuxiliaryLogMain
  change exp (-(2 * M + 2) * log 2 + saddleMomentLogMain N +
      complexXiNaturalTwoShiftLog M) =
    coefficientDyadicScale M * saddleMomentMain N *
      (coefficientMomentMultiplier N - quantitativeSaddleBranch N ^ 2)
  rw [exp_add, exp_add, saddleMomentMain_eq_exp_logMain hN,
    exp_complexXiNaturalTwoShiftLog hM]
  unfold coefficientDyadicScale
  ring

theorem differentiableAt_complexXiNaturalAuxiliaryLogMain
    {M : ℂ} (hM : M ∈ leanXiCoefficientSector) :
    DifferentiableAt ℂ complexXiNaturalAuxiliaryLogMain M := by
  let N : ℂ := coefficientMellinParameter M
  have hN : N ∈ leanSaddleSector :=
    leanTwoShiftAdmissible_base (leanCoefficientSector_admissible hM.2)
  have hNdiff : DifferentiableAt ℂ coefficientMellinParameter M :=
    differentiableAt_coefficientMellinParameter M
  have hlinear : DifferentiableAt ℂ
      (fun z : ℂ => -(2 * z + 2) * log 2) M := by fun_prop
  have hsaddle : DifferentiableAt ℂ
      (fun z => saddleMomentLogMain (coefficientMellinParameter z)) M := by
    simpa only [Function.comp_def] using
      (hasDerivAt_saddleMomentLogMain hN).differentiableAt.comp M hNdiff
  change DifferentiableAt ℂ
    (fun z => -(2 * z + 2) * log 2 +
      saddleMomentLogMain (coefficientMellinParameter z) +
        complexXiNaturalTwoShiftLog z) M
  exact (hlinear.add hsaddle).add
    (differentiableAt_complexXiNaturalTwoShiftLog hM)

theorem differentiableOn_complexXiNaturalAuxiliaryLogMain :
    DifferentiableOn ℂ complexXiNaturalAuxiliaryLogMain
      leanXiCoefficientSector := by
  intro M hM
  exact (differentiableAt_complexXiNaturalAuxiliaryLogMain hM).differentiableWithinAt

/-- The branch-fixed analytic logarithm of the exact auxiliary moment. -/
def complexXiNaturalAuxiliaryLog (M : ℂ) : ℂ :=
  complexXiNaturalAuxiliaryLogMain M +
    complexXiNaturalAuxiliaryLogError M

theorem exp_complexXiNaturalAuxiliaryLog
    {M : ℂ} (hM : M ∈ leanXiCoefficientSector) :
    exp (complexXiNaturalAuxiliaryLog M) = complexXiAuxiliaryMoment M := by
  rw [complexXiNaturalAuxiliaryLog, exp_add,
    exp_complexXiNaturalAuxiliaryLogMain hM,
    exp_complexXiNaturalAuxiliaryLogError hM,
    complexXiNaturalAuxiliaryRelativeError_eq_momentError hM,
    complexXiAuxiliaryMoment_natural_factorization hM]

theorem differentiableOn_complexXiNaturalAuxiliaryLog :
    DifferentiableOn ℂ complexXiNaturalAuxiliaryLog
      leanXiCoefficientSector :=
  differentiableOn_complexXiNaturalAuxiliaryLogMain.add
    differentiableOn_complexXiNaturalAuxiliaryLogError

end

end Zeta23.Research.JensenWedge
