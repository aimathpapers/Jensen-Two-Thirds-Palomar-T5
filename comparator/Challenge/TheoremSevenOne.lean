/-
Copyright (c) 2026 John Savva. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
import Mathlib

/-!
# Challenge: sectorial asymptotics for centered-xi coefficients

Let `M(s)` be the theta Mellin moment and continue the centered Riemann-xi
coefficient to a complex variable `M` by the exact Gamma/two-shift formula in
`JensenT5Public.xiCoefficientMoment`.  The theorem asserts the existence of a
holomorphic saddle branch solving

`L (pi exp L + 3/4) = s`

on a `1/100` proof sector.  On the `1/200` outer coefficient sector, the
coefficient, the displayed saddle main, and their relative error are
holomorphic and the main is nonzero.  On the closed `1/400` inner sector the
exact factorization has relative error `O(log |M| / |M|)`.  A second theorem
records the proportional-disc Cauchy estimates for the first six derivatives
of that same relative error.

The first compared theorem below checks the normalization seam: at every
positive integer, the complex theta/Gamma continuation is exactly the even
Taylor coefficient of Riemann's xi function centered at `1/2`.

These are the analytic statements called T5 and Theorem 7.1 in the paper.
They do not assert the final Jensen-hyperbolicity theorem by themselves.  The
proofs below are deliberate Comparator holes; `Solution.TheoremSevenOne`
contains the checked proofs.
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

/-- The theta/Gamma continuation is the actual centered-xi coefficient at
every positive integer. -/
theorem centered_xi_continuation_agrees_at_positive_integers :
    ∀ n : ℕ, xiCoefficientMoment ((n + 1 : ℕ) : ℂ) =
      centeredXiCoefficient (n + 1) := by
  sorry

/-- Literal three-sector form of manuscript Theorem 7.1. -/
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
  sorry

/-- Cauchy transport through order six for the exact relative error appearing
in the sectorial theorem. -/
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
  sorry

end
