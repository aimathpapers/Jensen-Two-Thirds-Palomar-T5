import Zeta23.Research.JensenWedge.XiAuxiliaryMoment

/-!
# Natural auxiliary-moment factorization

The coefficient theorem carries a Gamma quotient because it is normalized
for the xi coefficients.  After passing to the auxiliary moment `M_z`, that
quotient cancels exactly.  This module performs the cancellation before any
logarithm is taken: the natural main contains only the dyadic factor, the
moving-saddle moment, and the two-shift polynomial.  Its relative error is
exactly the already proved moment/two-shift error.
-/

namespace Zeta23.Research.JensenWedge

open Complex Set

noncomputable section

/-- The Gamma-free main for the auxiliary moment. -/
def complexXiNaturalAuxiliaryMain (M : ℂ) : ℂ :=
  let N := coefficientMellinParameter M
  coefficientDyadicScale M * saddleMomentMain N *
    (coefficientMomentMultiplier N - quantitativeSaddleBranch N ^ 2)

/-- Relative error of the exact auxiliary moment against its Gamma-free
main.  The quotient definition makes the holomorphic trust boundary
explicit. -/
def complexXiNaturalAuxiliaryRelativeError (M : ℂ) : ℂ :=
  holomorphicRelativeError complexXiAuxiliaryMoment
    complexXiNaturalAuxiliaryMain M

theorem complexXiNaturalAuxiliaryMain_ne_zero
    {M : ℂ} (hM : M ∈ leanXiCoefficientSector) :
    complexXiNaturalAuxiliaryMain M ≠ 0 := by
  let N : ℂ := coefficientMellinParameter M
  have hN : N ∈ leanSaddleSector :=
    leanTwoShiftAdmissible_base (leanCoefficientSector_admissible hM.2)
  have hdyadic : coefficientDyadicScale M ≠ 0 := by
    unfold coefficientDyadicScale
    exact exp_ne_zero _
  exact mul_ne_zero
    (mul_ne_zero hdyadic (saddleMomentMain_ne_zero hN))
    (coefficientMomentMultiplier_sub_saddle_sq_ne_zero hN)

/-- Exact Gamma-free factorization, obtained directly from the two shifted
theta moments rather than by dividing the coefficient asymptotic. -/
theorem complexXiAuxiliaryMoment_natural_factorization
    {M : ℂ} (hM : M ∈ leanXiCoefficientSector) :
    complexXiAuxiliaryMoment M = complexXiNaturalAuxiliaryMain M *
      (1 + complexXiMomentRelativeError M) := by
  let N : ℂ := coefficientMellinParameter M
  let c : ℂ := coefficientMomentMultiplier N
  let L : ℂ := quantitativeSaddleBranch N
  have hNcoef : N ∈ leanCoefficientSector := hM.2
  have hNadm := leanCoefficientSector_admissible hNcoef
  have hN : N ∈ leanSaddleSector := leanTwoShiftAdmissible_base hNadm
  have hN2 : N + 2 ∈ leanSaddleSector := by
    simpa using (hNadm 1 (by constructor <;> norm_num)).1
  have hdenom : c - L ^ 2 ≠ 0 := by
    simpa only [c, L, N] using
      coefficientMomentMultiplier_sub_saddle_sq_ne_zero hN
  have hratio : saddleMomentMain (N + 2) =
      saddleMomentMain N * L ^ 2 *
        (1 + saddleMainTwoShiftRelativeError N) := by
    simpa only [L] using
      saddleMomentMain_fixedSector_twoShift_factorization hNcoef
  have hassembly := fullThetaTwoShiftAssembly
    (scale := coefficientDyadicScale M) (coefficient := c)
    (saddleScale := L) (ratioError := saddleMainTwoShiftRelativeError N)
    hN hN2 hdenom hratio
  simpa only [complexXiAuxiliaryMoment, complexXiNaturalAuxiliaryMain,
    complexXiMomentRelativeError, N, c, L] using hassembly

/-- The quotient-defined natural error is character-for-character the
moment/two-shift error used in the coefficient assembly. -/
theorem complexXiNaturalAuxiliaryRelativeError_eq_momentError
    {M : ℂ} (hM : M ∈ leanXiCoefficientSector) :
    complexXiNaturalAuxiliaryRelativeError M =
      complexXiMomentRelativeError M := by
  unfold complexXiNaturalAuxiliaryRelativeError holomorphicRelativeError
  rw [complexXiAuxiliaryMoment_natural_factorization hM]
  field_simp [complexXiNaturalAuxiliaryMain_ne_zero hM]
  ring

theorem differentiableAt_complexXiNaturalAuxiliaryMain
    {M : ℂ} (hM : M ∈ leanXiCoefficientSector) :
    DifferentiableAt ℂ complexXiNaturalAuxiliaryMain M := by
  let N : ℂ := coefficientMellinParameter M
  have hN : N ∈ leanSaddleSector :=
    leanTwoShiftAdmissible_base (leanCoefficientSector_admissible hM.2)
  have hNdiff : DifferentiableAt ℂ coefficientMellinParameter M :=
    differentiableAt_coefficientMellinParameter M
  have hdyadic : DifferentiableAt ℂ coefficientDyadicScale M := by
    unfold coefficientDyadicScale
    fun_prop
  have hsaddle : DifferentiableAt ℂ
      (fun z => saddleMomentMain (coefficientMellinParameter z)) M := by
    simpa only [Function.comp_def] using
      (hasDerivAt_saddleMomentMain hN).differentiableAt.comp M hNdiff
  have hcoefficient : DifferentiableAt ℂ
      (fun z => coefficientMomentMultiplier (coefficientMellinParameter z)) M := by
    unfold coefficientMomentMultiplier coefficientMellinParameter
    fun_prop
  have hbranch : DifferentiableAt ℂ
      (fun z => quantitativeSaddleBranch (coefficientMellinParameter z)) M := by
    simpa only [Function.comp_def] using
      (hasDerivAt_quantitativeSaddleBranch hN).differentiableAt.comp M hNdiff
  change DifferentiableAt ℂ
    (fun z => coefficientDyadicScale z *
      saddleMomentMain (coefficientMellinParameter z) *
        (coefficientMomentMultiplier (coefficientMellinParameter z) -
          quantitativeSaddleBranch (coefficientMellinParameter z) ^ 2)) M
  exact (hdyadic.mul hsaddle).mul (hcoefficient.sub (hbranch.pow 2))

theorem differentiableOn_complexXiNaturalAuxiliaryMain :
    DifferentiableOn ℂ complexXiNaturalAuxiliaryMain
      leanXiCoefficientSector := by
  intro M hM
  exact (differentiableAt_complexXiNaturalAuxiliaryMain hM).differentiableWithinAt

theorem differentiableOn_complexXiNaturalAuxiliaryRelativeError :
    DifferentiableOn ℂ complexXiNaturalAuxiliaryRelativeError
      leanXiCoefficientSector := by
  intro M hM
  unfold complexXiNaturalAuxiliaryRelativeError holomorphicRelativeError
  exact (((differentiableAt_complexXiAuxiliaryMoment hM).div
    (differentiableAt_complexXiNaturalAuxiliaryMain hM)
    (complexXiNaturalAuxiliaryMain_ne_zero hM)).sub_const 1).differentiableWithinAt

/-- The Gamma-free error inherits the sharper moment-only rate. -/
theorem complexXiNaturalAuxiliaryRelativeError_norm_le
    {M : ℂ} (hM : M ∈ leanXiCoefficientSector) :
    ‖complexXiNaturalAuxiliaryRelativeError M‖ ≤
      (100 * fullThetaMomentErrorCoefficient) *
        Real.log ‖coefficientMellinParameter M‖ /
          ‖coefficientMellinParameter M‖ := by
  rw [complexXiNaturalAuxiliaryRelativeError_eq_momentError hM]
  exact complexXiMomentRelativeError_norm_le hM

end

end Zeta23.Research.JensenWedge
