/-
Copyright (c) 2026 John Savva. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
import Zeta23.Research.JensenWedge.ManuscriptTheoremSevenOne

/-!
# Comparator solution for manuscript Theorem 7.1

The trusted statement layer uses only Mathlib definitions.  This untrusted
file proves that its theta Mellin moment and coefficient continuation are
definitionally the production objects, then delegates the substantive
analytic estimates to the Phase-28 theorem.
-/

/- BEGIN PALOMAR TRUSTED DEFINITIONS -/

namespace JensenT5Public

open Complex Function MeasureTheory Set

noncomputable section

def thetaTail (t : ℝ) : ℝ :=
  (HurwitzZeta.evenKernel 0 t - 1) / 2

def thetaMellinKernelReal (u : ℝ) : ℝ :=
  Real.exp (u / 4) * thetaTail (Real.exp u)

def thetaMellinKernel (u : ℝ) : ℂ :=
  (thetaMellinKernelReal u : ℂ)

def thetaMoment (s : ℂ) : ℂ :=
  mellin thetaMellinKernel (s + 1)

def coefficientMellinParameter (M : ℂ) : ℂ :=
  2 * M - 2

def coefficientMomentMultiplier (N : ℂ) : ℂ :=
  16 * (N + 2) * (N + 1)

def coefficientDyadicScale (M : ℂ) : ℂ :=
  exp (-(2 * M + 2) * log 2)

def factorialRatio (M : ℂ) : ℂ :=
  Gamma (M + 1) / Gamma (2 * M + 1)

def xiCoefficientMoment (M : ℂ) : ℂ :=
  let N := coefficientMellinParameter M
  factorialRatio M * coefficientDyadicScale M *
    (coefficientMomentMultiplier N * thetaMoment N - thetaMoment (N + 2))

def centeredRiemannXi (w : ℂ) : ℂ :=
  let s : ℂ := 1 / 2 + w
  s * (s - 1) / 2 * completedRiemannZeta₀ s + 1 / 2

def centeredXiCoefficient (n : ℕ) : ℂ :=
  (n.factorial : ℂ) / ((2 * n).factorial : ℂ) *
    iteratedDeriv (2 * n) centeredRiemannXi 0

def saddleEquation (s L : ℂ) : ℂ :=
  L * ((Real.pi : ℂ) * exp L + 3 / 4) - s

def saddleCurvature (s L : ℂ) : ℂ :=
  ((1 + L) * s - (3 / 4) * L ^ 2) / L ^ 2

def saddleMain (L : ℂ → ℂ) (s : ℂ) : ℂ :=
  exp (s * log (L s) + L s / 4 - s / L s + 3 / 4) *
    ((2 * Real.pi : ℂ) / saddleCurvature s (L s)) ^ (1 / 2 : ℂ)

def coefficientElementaryMain (M : ℂ) : ℂ :=
  let N := coefficientMellinParameter M
  exp (M - 2 + (M + 1 / 2) * log M -
    N * log 2 - (N + 1 / 2) * log N)

def xiCoefficientMain (L : ℂ → ℂ) (M : ℂ) : ℂ :=
  coefficientElementaryMain M *
    saddleMain L (coefficientMellinParameter M)

def proofSectorAt (R : ℝ) : Set ℂ :=
  {s | R < ‖s‖ ∧ |s.arg| < 1 / 100}

def outerSectorAt (R : ℝ) : Set ℂ :=
  {M | R < ‖M‖ ∧ |M.arg| < 1 / 200}

def innerSectorAt (R : ℝ) : Set ℂ :=
  {M | R < ‖M‖ ∧ |M.arg| ≤ 1 / 400}

def cauchyRadius (x : ℝ) : ℝ := x / 1000

end

end JensenT5Public

/- END PALOMAR TRUSTED DEFINITIONS -/

open Complex Set
open JensenT5Public

noncomputable section

namespace JensenT5Bridge

namespace Z

export Zeta23.Research.JensenWedge
  (fullThetaMoment fullThetaMoment_eq_mellin complexXiCoefficientMoment
   complexFactorialRatio coefficientDyadicScale coefficientMomentMultiplier
   coefficientMellinParameter sectorialSaddleEquation leadingCurvature
   quantitativeSaddleBranch manuscriptXiCoefficientMain
   manuscriptTheoremRadius manuscriptOuterSector manuscriptInnerSector
   leanSaddleSector leanSaddleCutoff saddleProofAngle saddleSector
   isOpen_leanSaddleSector manuscriptPaperRelativeError
   manuscriptPaperErrorCoefficient manuscriptXiCoefficientErrorCoefficient
   complexXiCoefficientErrorCoefficient fullThetaMomentErrorCoefficient
   quantitativeSaddleBranch_differentiableOn_leanSector
   quantitativeSaddleBranch_spec leanSaddleSector_quantitative
   centeredXi centeredXiCoefficient complexXiCoefficientMoment_nat_succ
   manuscriptTheoremSevenOne_effective
   manuscriptXiCoefficientMain_ne_zero_of_outer
   manuscriptPaperRelativeError_derivatives_through_six
   manuscriptCauchyRadius manuscriptCauchyEpsilon)

end Z

theorem thetaMoment_eq (s : ℂ) :
    thetaMoment s = Z.fullThetaMoment s := by
  rw [Z.fullThetaMoment_eq_mellin]
  rfl

theorem xiCoefficientMoment_eq (M : ℂ) :
    xiCoefficientMoment M = Z.complexXiCoefficientMoment M := by
  unfold xiCoefficientMoment Z.complexXiCoefficientMoment
  unfold factorialRatio Z.complexFactorialRatio
  unfold coefficientDyadicScale Z.coefficientDyadicScale
  unfold coefficientMomentMultiplier Z.coefficientMomentMultiplier
  unfold coefficientMellinParameter Z.coefficientMellinParameter
  simp only [thetaMoment_eq]

theorem centeredRiemannXi_eq (w : ℂ) :
    centeredRiemannXi w = Z.centeredXi w := by
  rfl

theorem centeredXiCoefficient_eq (n : ℕ) :
    centeredXiCoefficient n = Z.centeredXiCoefficient n := by
  rfl

theorem saddleEquation_eq (s L : ℂ) :
    saddleEquation s L = Z.sectorialSaddleEquation s L := by
  rfl

theorem saddleCurvature_eq (s L : ℂ) :
    saddleCurvature s L = Z.leadingCurvature s L := by
  rfl

theorem xiCoefficientMain_eq (M : ℂ) :
    xiCoefficientMain Z.quantitativeSaddleBranch M =
      Z.manuscriptXiCoefficientMain M := by
  rfl

theorem outerSector_eq :
    outerSectorAt Z.manuscriptTheoremRadius = Z.manuscriptOuterSector := by
  ext M
  rfl

theorem innerSector_eq :
    innerSectorAt Z.manuscriptTheoremRadius = Z.manuscriptInnerSector := by
  ext M
  rfl

theorem proofSector_subset :
    proofSectorAt Z.manuscriptTheoremRadius ⊆ Z.leanSaddleSector := by
  intro s hs
  change Z.manuscriptTheoremRadius < ‖s‖ ∧ |s.arg| < 1 / 100 at hs
  change Real.exp Z.leanSaddleCutoff < ‖s‖ ∧
    |s.arg| < Z.saddleProofAngle
  exact ⟨(Real.exp_lt_exp.mpr (by norm_num)).trans hs.1,
    by simpa only [Z.saddleProofAngle] using hs.2⟩

theorem isOpen_proofSector :
    IsOpen (proofSectorAt Z.manuscriptTheoremRadius) := by
  have hopenRadial : IsOpen {s : ℂ | Z.manuscriptTheoremRadius < ‖s‖} :=
    isOpen_lt continuous_const continuous_norm
  have heq : proofSectorAt Z.manuscriptTheoremRadius =
      Z.leanSaddleSector ∩ {s : ℂ | Z.manuscriptTheoremRadius < ‖s‖} := by
    ext s
    constructor
    · intro hs
      exact ⟨proofSector_subset hs, hs.1⟩
    · intro hs
      exact ⟨hs.2, by
        change |s.arg| < 1 / 100
        simpa only [Z.leanSaddleSector, Z.saddleSector,
          Z.saddleProofAngle] using hs.1.2⟩
  rw [heq]
  exact Z.isOpen_leanSaddleSector.inter hopenRadial

theorem publicError_eq (M : ℂ) :
    Z.manuscriptPaperRelativeError M =
      xiCoefficientMoment M /
        xiCoefficientMain Z.quantitativeSaddleBranch M - 1 := by
  rw [xiCoefficientMoment_eq, xiCoefficientMain_eq]
  rfl

end JensenT5Bridge

open JensenT5Bridge

/-- Proved normalization seam between the continuation and actual xi. -/
theorem centered_xi_continuation_agrees_at_positive_integers :
    ∀ n : ℕ, xiCoefficientMoment ((n + 1 : ℕ) : ℂ) =
      centeredXiCoefficient (n + 1) := by
  intro n
  rw [xiCoefficientMoment_eq, Z.complexXiCoefficientMoment_nat_succ,
    centeredXiCoefficient_eq]

/-- Proved solution of the literal three-sector manuscript theorem. -/
theorem sectorial_centered_xi_coefficient_asymptotic :
    ∃ R C : ℝ, ∃ L E : ℂ → ℂ,
      0 < R ∧ 0 < C ∧
      IsOpen (proofSectorAt R) ∧
      DifferentiableOn ℂ L (proofSectorAt R) ∧
      (∀ s ∈ proofSectorAt R, saddleEquation s (L s) = 0) ∧
      IsOpen (outerSectorAt R) ∧
      DifferentiableOn ℂ xiCoefficientMoment (outerSectorAt R) ∧
      DifferentiableOn ℂ (xiCoefficientMain L) (outerSectorAt R) ∧
      DifferentiableOn ℂ E (outerSectorAt R) ∧
      (∀ M ∈ outerSectorAt R,
        xiCoefficientMain L M ≠ 0 ∧
        E M = xiCoefficientMoment M / xiCoefficientMain L M - 1) ∧
      ∀ M ∈ innerSectorAt R,
        xiCoefficientMoment M = xiCoefficientMain L M * (1 + E M) ∧
        ‖E M‖ ≤ C * Real.log ‖M‖ / ‖M‖ := by
  refine ⟨Z.manuscriptTheoremRadius, Z.manuscriptPaperErrorCoefficient,
    Z.quantitativeSaddleBranch, Z.manuscriptPaperRelativeError,
    Real.exp_pos _, ?_, isOpen_proofSector, ?_, ?_, ?_⟩
  · norm_num [Z.manuscriptPaperErrorCoefficient,
      Z.manuscriptXiCoefficientErrorCoefficient,
      Z.complexXiCoefficientErrorCoefficient,
      Z.fullThetaMomentErrorCoefficient]
  · exact Z.quantitativeSaddleBranch_differentiableOn_leanSector.mono
      proofSector_subset
  · intro s hs
    rw [saddleEquation_eq]
    exact (Z.quantitativeSaddleBranch_spec
      (Z.leanSaddleSector_quantitative (proofSector_subset hs))).2.1
  · rcases Z.manuscriptTheoremSevenOne_effective with
      ⟨hopen, hactual, hmain, herror, hne, hinner⟩
    have hactualEq : xiCoefficientMoment = Z.complexXiCoefficientMoment :=
      funext xiCoefficientMoment_eq
    have hmainEq : xiCoefficientMain Z.quantitativeSaddleBranch =
        Z.manuscriptXiCoefficientMain := funext xiCoefficientMain_eq
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
    · simpa only [outerSector_eq] using hopen
    · rw [outerSector_eq, hactualEq]
      exact hactual
    · rw [outerSector_eq, hmainEq]
      exact hmain
    · simpa only [outerSector_eq] using herror
    · intro M hM
      have hM' : M ∈ Z.manuscriptOuterSector := by
        simpa only [outerSector_eq] using hM
      exact ⟨by simpa only [xiCoefficientMain_eq] using hne M hM',
        publicError_eq M⟩
    · intro M hM
      have hM' : M ∈ Z.manuscriptInnerSector := by
        simpa only [innerSector_eq] using hM
      have h := hinner M hM'
      simpa only [xiCoefficientMoment_eq, xiCoefficientMain_eq] using h

/-- Proved Cauchy derivative consequence through order six. -/
theorem sectorial_centered_xi_error_derivatives_through_six :
    ∃ R D : ℝ, ∃ L E : ℂ → ℂ,
      0 < R ∧ 0 < D ∧
      IsOpen (proofSectorAt R) ∧
      DifferentiableOn ℂ L (proofSectorAt R) ∧
      (∀ s ∈ proofSectorAt R, saddleEquation s (L s) = 0) ∧
      IsOpen (outerSectorAt R) ∧
      DifferentiableOn ℂ xiCoefficientMoment (outerSectorAt R) ∧
      DifferentiableOn ℂ (xiCoefficientMain L) (outerSectorAt R) ∧
      DifferentiableOn ℂ E (outerSectorAt R) ∧
      (∀ M ∈ outerSectorAt R,
        xiCoefficientMain L M ≠ 0 ∧
        E M = xiCoefficientMoment M / xiCoefficientMain L M - 1) ∧
      ∀ x : ℝ, R < x → ∀ j ≤ 6,
        ‖iteratedDeriv j E (x : ℂ)‖ ≤
          j.factorial * (D * Real.log (3 * x) / x) /
            cauchyRadius x ^ j := by
  refine ⟨Z.manuscriptTheoremRadius,
    Z.manuscriptXiCoefficientErrorCoefficient,
    Z.quantitativeSaddleBranch, Z.manuscriptPaperRelativeError,
    Real.exp_pos _, ?_, isOpen_proofSector, ?_, ?_, ?_⟩
  · norm_num [Z.manuscriptXiCoefficientErrorCoefficient,
      Z.complexXiCoefficientErrorCoefficient,
      Z.fullThetaMomentErrorCoefficient]
  · exact Z.quantitativeSaddleBranch_differentiableOn_leanSector.mono
      proofSector_subset
  · intro s hs
    rw [saddleEquation_eq]
    exact (Z.quantitativeSaddleBranch_spec
      (Z.leanSaddleSector_quantitative (proofSector_subset hs))).2.1
  · rcases Z.manuscriptTheoremSevenOne_effective with
      ⟨hopen, hactual, hmain, herror, hne, _hinner⟩
    have hactualEq : xiCoefficientMoment = Z.complexXiCoefficientMoment :=
      funext xiCoefficientMoment_eq
    have hmainEq : xiCoefficientMain Z.quantitativeSaddleBranch =
        Z.manuscriptXiCoefficientMain := funext xiCoefficientMain_eq
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
    · simpa only [outerSector_eq] using hopen
    · rw [outerSector_eq, hactualEq]
      exact hactual
    · rw [outerSector_eq, hmainEq]
      exact hmain
    · simpa only [outerSector_eq] using herror
    · intro M hM
      have hM' : M ∈ Z.manuscriptOuterSector := by
        simpa only [outerSector_eq] using hM
      exact ⟨by simpa only [xiCoefficientMain_eq] using hne M hM',
        publicError_eq M⟩
    · intro x hx j hj
      have h := Z.manuscriptPaperRelativeError_derivatives_through_six hx j hj
      simpa only [cauchyRadius, Z.manuscriptCauchyRadius,
        Z.manuscriptCauchyEpsilon] using h

end
