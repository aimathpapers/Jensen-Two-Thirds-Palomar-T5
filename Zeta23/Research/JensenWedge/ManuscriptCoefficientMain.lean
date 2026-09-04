import Zeta23.Research.JensenWedge.FullThetaHolomorphic

/-!
# Exact bridge to the manuscript coefficient main

The coefficient theorem is first proved with an exact factored main.  The
manuscript displays the traditional simplified main and absorbs three
explicit near-one factors: the elementary reindexing factor, the Gaussian
linear-amplitude correction, and the two-shift cancellation factor.  This
module defines both sides and checks their exact relationship in the kernel.
-/

namespace Zeta23.Research.JensenWedge

open Complex Set

noncomputable section

/-- The saddle factor printed in equation `A-main`, before the exact
Gaussian linear-amplitude correction `exp (1/(2K))`. -/
def manuscriptSaddleMain (s : ℂ) : ℂ :=
  let L := quantitativeSaddleBranch s
  let K := leadingCurvature s L
  exp (s * log L + L / 4 - s / L + 3 / 4) *
    ((2 * Real.pi : ℂ) / K) ^ (1 / 2 : ℂ)

/-- The elementary coefficient prefactor printed in equation `G-main`.
Powers are represented by the same principal-log continuation used in the
manuscript. -/
def manuscriptCoefficientElementaryMain (M : ℂ) : ℂ :=
  let N := coefficientMellinParameter M
  exp (M - 2 + (M + 1 / 2) * log M -
    N * log 2 - (N + 1 / 2) * log N)

/-- The complete main displayed in manuscript Theorem 7.1. -/
def manuscriptXiCoefficientMain (M : ℂ) : ℂ :=
  let N := coefficientMellinParameter M
  manuscriptCoefficientElementaryMain M * manuscriptSaddleMain N

/-- The exact elementary factor called `R_N` in the paper proof. -/
def coefficientReindexCorrection (N : ℂ) : ℂ :=
  exp 2 * (N + 1) *
    exp ((N + 1 / 2) * log N - (N + 3 / 2) * log (N + 2))

/-- The exact correction caused by retaining the Jacobian-induced linear
term in the comparison Gaussian. -/
def coefficientGaussianCorrection (N : ℂ) : ℂ :=
  let L := quantitativeSaddleBranch N
  let K := leadingCurvature N L
  exp (1 / (2 * K))

/-- The exact cancellation factor from the shifted theta moment. -/
def coefficientCancellationCorrection (N : ℂ) : ℂ :=
  1 - quantitativeSaddleBranch N ^ 2 / coefficientMomentMultiplier N

/-- Product of the three factors suppressed in the displayed main. -/
def manuscriptMainCorrection (M : ℂ) : ℂ :=
  let N := coefficientMellinParameter M
  coefficientReindexCorrection N * coefficientGaussianCorrection N *
    coefficientCancellationCorrection N

theorem saddleMomentMain_eq_manuscriptSaddleMain_mul_correction
    {s : ℂ} (hs : s ∈ leanSaddleSector) :
    saddleMomentMain s = manuscriptSaddleMain s *
      coefficientGaussianCorrection s := by
  let L : ℂ := quantitativeSaddleBranch s
  let K : ℂ := leadingCurvature s L
  have hKre : 0 < K.re := quantitativeSaddleBranch_curvature_re_pos hs
  have hLne : L ≠ 0 :=
    (quantitativeSaddleBranch_scaled_bounds
      (leanSaddleSector_quantitative hs)).1
  have hroot : sectorialSaddleEquation s L = 0 :=
    (quantitativeSaddleBranch_spec
      (leanSaddleSector_quantitative hs)).2.1
  rw [saddleMomentMain, integral_leadingGaussian hKre,
    leadingIntegrand_eq_exp_logIntegrand,
    leadingLogIntegrand_at_saddle hLne hroot]
  simp only [manuscriptSaddleMain, coefficientGaussianCorrection, L, K]
  ring

theorem coefficientMomentMultiplier_ne_zero_of_sector
    {s : ℂ} (hs : s ∈ leanSaddleSector) :
    coefficientMomentMultiplier s ≠ 0 := by
  have hsre : 0 < s.re := leanSaddleSector_re_pos hs
  unfold coefficientMomentMultiplier
  apply mul_ne_zero (mul_ne_zero (by norm_num) ?_) ?_
  · intro h
    have := congrArg Complex.re h
    norm_num at this
    linarith
  · intro h
    have := congrArg Complex.re h
    norm_num at this
    linarith

theorem complexFactorialMain_mul_dyadic_mul_multiplier_eq_manuscript
    {M : ℂ} (hM : M ∈ leanXiCoefficientSector) :
    complexFactorialRatioMain M * coefficientDyadicScale M *
        coefficientMomentMultiplier (coefficientMellinParameter M) =
      manuscriptCoefficientElementaryMain M *
        coefficientReindexCorrection (coefficientMellinParameter M) := by
  have hMre : 0 < M.re := leanSaddleSector_re_pos
    (leanTwoShiftAdmissible_base (leanCoefficientSector_admissible hM.1))
  let N : ℂ := coefficientMellinParameter M
  have hNre : 0 < N.re := leanSaddleSector_re_pos
    (leanTwoShiftAdmissible_base (leanCoefficientSector_admissible hM.2))
  have hNne : N ≠ 0 := by
    intro h
    rw [h] at hNre
    simp at hNre
  have hN2ne : N + 2 ≠ 0 := by
    intro h
    have hre := congrArg Complex.re h
    norm_num at hre
    linarith
  have htwo : (2 : ℂ) ≠ 0 := by norm_num
  have hexpTwo : exp (log (2 : ℂ)) = 2 := exp_log htwo
  have hsixteen : (16 : ℂ) = exp (4 * log (2 : ℂ)) := by
    rw [show 4 * log (2 : ℂ) = (4 : ℕ) * log (2 : ℂ) by norm_num]
    rw [Complex.exp_nat_mul, hexpTwo]
    norm_num
  have hN2 : N + 2 = 2 * M := by
    dsimp only [N, coefficientMellinParameter]
    ring
  have hmult : (16 : ℂ) * (N + 2) * (N + 1) =
      exp (4 * log (2 : ℂ) + log (N + 2)) * (N + 1) := by
    rw [Complex.exp_add, ← hsixteen, exp_log hN2ne]
  change complexFactorialRatioMain M * coefficientDyadicScale M *
      coefficientMomentMultiplier N =
    manuscriptCoefficientElementaryMain M * coefficientReindexCorrection N
  rw [complexFactorialRatioMain, complexFactorialRatioLogMain,
    coefficientDyadicScale, coefficientMomentMultiplier,
    manuscriptCoefficientElementaryMain, coefficientReindexCorrection]
  rw [hmult]
  calc
    exp (M + (M + 1 / 2) * log M -
          (2 * M + 1 / 2) * log (2 * M)) *
        exp (-(2 * M + 2) * log 2) *
          (exp (4 * log 2 + log (N + 2)) * (N + 1)) =
      exp ((M + (M + 1 / 2) * log M -
          (2 * M + 1 / 2) * log (2 * M)) +
        (-(2 * M + 2) * log 2) +
          (4 * log 2 + log (N + 2))) * (N + 1) := by
            rw [← Complex.exp_add]
            rw [← mul_assoc, ← Complex.exp_add]
    _ = exp ((M - 2 + (M + 1 / 2) * log M -
          N * log 2 - (N + 1 / 2) * log N) + 2 +
        ((N + 1 / 2) * log N -
          (N + 3 / 2) * log (N + 2))) * (N + 1) := by
            congr 2
            rw [hN2]
            dsimp only [N, coefficientMellinParameter]
            ring
    _ = exp (M - 2 + (M + 1 / 2) * log M -
          N * log 2 - (N + 1 / 2) * log N) *
        (exp 2 * (N + 1) *
          exp ((N + 1 / 2) * log N -
            (N + 3 / 2) * log (N + 2))) := by
              rw [Complex.exp_add, Complex.exp_add]
              ring

/-- Exact character-level bridge between the factored Lean main and the
main printed in manuscript Theorem 7.1. -/
theorem complexXiCoefficientMain_eq_manuscript_mul_correction
    {M : ℂ} (hM : M ∈ leanXiCoefficientSector) :
    complexXiCoefficientMain M = manuscriptXiCoefficientMain M *
      manuscriptMainCorrection M := by
  let N : ℂ := coefficientMellinParameter M
  let c : ℂ := coefficientMomentMultiplier N
  let L : ℂ := quantitativeSaddleBranch N
  have hN : N ∈ leanSaddleSector :=
    leanTwoShiftAdmissible_base (leanCoefficientSector_admissible hM.2)
  have hc : c ≠ 0 := by
    simpa only [c, N] using coefficientMomentMultiplier_ne_zero_of_sector hN
  have hpref :=
    complexFactorialMain_mul_dyadic_mul_multiplier_eq_manuscript hM
  have hsaddle := saddleMomentMain_eq_manuscriptSaddleMain_mul_correction hN
  have hcancel : c - L ^ 2 = c * (1 - L ^ 2 / c) := by
    field_simp [hc]
  change complexFactorialRatioMain M * coefficientDyadicScale M *
      saddleMomentMain N * (c - L ^ 2) =
    (manuscriptCoefficientElementaryMain M * manuscriptSaddleMain N) *
      (coefficientReindexCorrection N * coefficientGaussianCorrection N *
        (1 - L ^ 2 / c))
  rw [hcancel, hsaddle]
  have hpref' : complexFactorialRatioMain M * coefficientDyadicScale M * c =
      manuscriptCoefficientElementaryMain M * coefficientReindexCorrection N := by
    simpa only [N, c] using hpref
  calc
    complexFactorialRatioMain M * coefficientDyadicScale M *
        (manuscriptSaddleMain N * coefficientGaussianCorrection N) *
          (c * (1 - L ^ 2 / c)) =
      (complexFactorialRatioMain M * coefficientDyadicScale M * c) *
        manuscriptSaddleMain N * coefficientGaussianCorrection N *
          (1 - L ^ 2 / c) := by ring
    _ = _ := by rw [hpref']; ring

end

end Zeta23.Research.JensenWedge
