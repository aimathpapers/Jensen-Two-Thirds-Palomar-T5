import Zeta23.Research.JensenWedge.ManuscriptCauchyTransport

/-!
# Exact xi auxiliary-moment bridge

The manuscript performs its logarithmic-derivative analysis on the auxiliary
moment `M_z`, after removing the exact Gamma quotient from the centered-xi
coefficient.  This module defines that object directly, proves the exact
Gamma bridge, and transfers the manuscript-normalized sector theorem and its
order-six Cauchy error transport without changing the relative error.
-/

namespace Zeta23.Research.JensenWedge

open Complex Set

noncomputable section

/-- The manuscript auxiliary moment `M_z`, continued holomorphically in the
coefficient parameter.  This is the exact coefficient moment with the Gamma
quotient removed. -/
def complexXiAuxiliaryMoment (M : ℂ) : ℂ :=
  let N := coefficientMellinParameter M
  coefficientDyadicScale M *
    (coefficientMomentMultiplier N * fullThetaMoment N -
      fullThetaMoment (N + 2))

/-- The displayed coefficient main with the exact Gamma quotient removed.
This is the main term paired with `complexXiAuxiliaryMoment`. -/
def manuscriptXiAuxiliaryMain (M : ℂ) : ℂ :=
  manuscriptXiCoefficientMain M / complexFactorialRatio M

/-- Gamma has no zero or pole at either argument of the factorial ratio in
the open right half-plane. -/
theorem complexFactorialRatio_ne_zero_of_re_pos
    {M : ℂ} (hM : 0 < M.re) :
    complexFactorialRatio M ≠ 0 := by
  have hnum : ∀ m : ℕ, M + 1 ≠ -(m : ℂ) := by
    intro m h
    have hre := congrArg Complex.re h
    norm_num at hre
    nlinarith [Nat.cast_nonneg (α := ℝ) m]
  have hden : ∀ m : ℕ, 2 * M + 1 ≠ -(m : ℂ) := by
    intro m h
    have hre := congrArg Complex.re h
    norm_num at hre
    nlinarith [Nat.cast_nonneg (α := ℝ) m]
  exact div_ne_zero (Complex.Gamma_ne_zero hnum)
    (Complex.Gamma_ne_zero hden)

theorem complexFactorialRatio_ne_zero_of_mem_leanXiCoefficientSector
    {M : ℂ} (hM : M ∈ leanXiCoefficientSector) :
    complexFactorialRatio M ≠ 0 := by
  apply complexFactorialRatio_ne_zero_of_re_pos
  exact leanSaddleSector_re_pos
    (leanTwoShiftAdmissible_base (leanCoefficientSector_admissible hM.1))

/-- Character-level identity relating the auxiliary moment to the complete
coefficient continuation. -/
theorem complexXiCoefficientMoment_eq_factorialRatio_mul_auxiliary
    (M : ℂ) :
    complexXiCoefficientMoment M =
      complexFactorialRatio M * complexXiAuxiliaryMoment M := by
  unfold complexXiCoefficientMoment complexXiAuxiliaryMoment
  ring

/-- At positive integers, the exact Gamma ratio times the auxiliary moment is
the centered-xi coefficient already identified in T1. -/
theorem complexFactorialRatio_mul_auxiliary_nat_succ (n : ℕ) :
    complexFactorialRatio ((n + 1 : ℕ) : ℂ) *
        complexXiAuxiliaryMoment ((n + 1 : ℕ) : ℂ) =
      centeredXiCoefficient (n + 1) := by
  rw [← complexXiCoefficientMoment_eq_factorialRatio_mul_auxiliary,
    complexXiCoefficientMoment_nat_succ]

/-- Removing the exact Gamma quotient does not change the relative error in
the manuscript-normalized coefficient theorem. -/
theorem complexXiAuxiliaryMoment_manuscript_factorization
    {M : ℂ} (hM : M ∈ leanXiCoefficientSector) :
    complexXiAuxiliaryMoment M = manuscriptXiAuxiliaryMain M *
      (1 + manuscriptXiCoefficientRelativeError M) := by
  have hratio := complexFactorialRatio_ne_zero_of_mem_leanXiCoefficientSector hM
  have hcoefficient := complexXiCoefficientMoment_manuscript_factorization hM
  rw [complexXiCoefficientMoment_eq_factorialRatio_mul_auxiliary] at hcoefficient
  unfold manuscriptXiAuxiliaryMain
  field_simp [hratio] at hcoefficient ⊢
  exact hcoefficient

theorem manuscriptXiAuxiliaryMain_ne_zero
    {M : ℂ} (hM : M ∈ leanXiCoefficientSector) :
    manuscriptXiAuxiliaryMain M ≠ 0 := by
  exact div_ne_zero (manuscriptXiCoefficientMain_ne_zero hM)
    (complexFactorialRatio_ne_zero_of_mem_leanXiCoefficientSector hM)

theorem differentiableAt_complexXiAuxiliaryMoment
    {M : ℂ} (hM : M ∈ leanXiCoefficientSector) :
    DifferentiableAt ℂ complexXiAuxiliaryMoment M := by
  let N : ℂ := coefficientMellinParameter M
  have hNouter : N ∈ leanSaddleSector :=
    leanTwoShiftAdmissible_base (leanCoefficientSector_admissible hM.2)
  have hNre : 0 < N.re := leanSaddleSector_re_pos hNouter
  have hNdiff : DifferentiableAt ℂ coefficientMellinParameter M :=
    differentiableAt_coefficientMellinParameter M
  have hfullN : DifferentiableAt ℂ
      (fun z => fullThetaMoment (coefficientMellinParameter z)) M :=
    (differentiableAt_fullThetaMoment (by linarith)).comp M hNdiff
  have hN2re : -1 < (N + 2).re := by
    norm_num
    linarith
  have hfullN2 : DifferentiableAt ℂ
      (fun z => fullThetaMoment (coefficientMellinParameter z + 2)) M := by
    have hcomp := (differentiableAt_fullThetaMoment hN2re).comp M
      (hNdiff.add_const 2)
    simpa only [Function.comp_def] using hcomp
  have hcoefficient : DifferentiableAt ℂ
      (fun z => coefficientMomentMultiplier (coefficientMellinParameter z)) M := by
    unfold coefficientMomentMultiplier coefficientMellinParameter
    fun_prop
  have hdyadic : DifferentiableAt ℂ coefficientDyadicScale M := by
    unfold coefficientDyadicScale
    fun_prop
  change DifferentiableAt ℂ
    (fun z => coefficientDyadicScale z *
      (coefficientMomentMultiplier (coefficientMellinParameter z) *
          fullThetaMoment (coefficientMellinParameter z) -
        fullThetaMoment (coefficientMellinParameter z + 2))) M
  exact hdyadic.mul ((hcoefficient.mul hfullN).sub hfullN2)

theorem differentiableAt_manuscriptXiAuxiliaryMain
    {M : ℂ} (hM : M ∈ leanXiCoefficientSector) :
    DifferentiableAt ℂ manuscriptXiAuxiliaryMain M := by
  have hMre : 0 < M.re := leanSaddleSector_re_pos
    (leanTwoShiftAdmissible_base (leanCoefficientSector_admissible hM.1))
  unfold manuscriptXiAuxiliaryMain
  exact (differentiableAt_manuscriptXiCoefficientMain hM).div
    (hasDerivAt_complexFactorialRatio hMre).differentiableAt
    (complexFactorialRatio_ne_zero_of_re_pos hMre)

theorem differentiableOn_complexXiAuxiliaryMoment :
    DifferentiableOn ℂ complexXiAuxiliaryMoment leanXiCoefficientSector := by
  intro M hM
  exact (differentiableAt_complexXiAuxiliaryMoment hM).differentiableWithinAt

theorem differentiableOn_manuscriptXiAuxiliaryMain :
    DifferentiableOn ℂ manuscriptXiAuxiliaryMain leanXiCoefficientSector := by
  intro M hM
  exact (differentiableAt_manuscriptXiAuxiliaryMain hM).differentiableWithinAt

/-- Holomorphic auxiliary-moment form of manuscript Theorem 7.1.  The error
function and its explicit bound are exactly the already-audited coefficient
error, not a newly introduced witness. -/
theorem complexXiAuxiliaryMoment_manuscript_sector_holomorphic_asymptotic :
    IsOpen leanXiCoefficientSector ∧
      DifferentiableOn ℂ complexXiAuxiliaryMoment leanXiCoefficientSector ∧
      DifferentiableOn ℂ manuscriptXiAuxiliaryMain leanXiCoefficientSector ∧
      DifferentiableOn ℂ manuscriptXiCoefficientRelativeError
        leanXiCoefficientSector ∧
      ∀ M ∈ leanXiCoefficientSector,
        manuscriptXiAuxiliaryMain M ≠ 0 ∧
          complexXiAuxiliaryMoment M = manuscriptXiAuxiliaryMain M *
            (1 + manuscriptXiCoefficientRelativeError M) ∧
          ‖manuscriptXiCoefficientRelativeError M‖ ≤
            manuscriptXiCoefficientErrorCoefficient *
              Real.log ‖coefficientMellinParameter M‖ /
                ‖coefficientMellinParameter M‖ := by
  exact ⟨isOpen_leanXiCoefficientSector,
    differentiableOn_complexXiAuxiliaryMoment,
    differentiableOn_manuscriptXiAuxiliaryMain,
    differentiableOn_manuscriptXiCoefficientRelativeError,
    fun M hM => ⟨manuscriptXiAuxiliaryMain_ne_zero hM,
      complexXiAuxiliaryMoment_manuscript_factorization hM,
      manuscriptXiCoefficientRelativeError_norm_le hM⟩⟩

/-- The auxiliary-moment theorem inherits the same concrete order-six error
transport because its relative error is definitionally the coefficient
relative error. -/
theorem complexXiAuxiliaryMoment_relativeError_derivatives_through_six
    {x : ℝ} (hx : Real.exp (leanSaddleCutoff + 2) < x) :
    ∀ j ≤ 6,
      ‖iteratedDeriv j manuscriptXiCoefficientRelativeError (x : ℂ)‖ ≤
        j.factorial * manuscriptCauchyEpsilon x /
          manuscriptCauchyRadius x ^ j :=
  manuscriptXiCoefficientRelativeError_derivatives_through_six hx

end

end Zeta23.Research.JensenWedge
