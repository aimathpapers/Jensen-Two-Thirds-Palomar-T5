/-
# Provisional frozen-main coefficients for xi''

Let `A`, `B`, and `C` denote the Dirichlet series with coefficients
`Lambda`, `Lambda log`, and `Lambda log^2`.  Freezing the slowly varying
archimedean logarithmic derivative at `Ls` gives

  Q = Ls - A,
  F = Q^2 + B,
  xi''' / xi'' = Q + (2 Q B - C) / F.

This module records the resulting locally finite convolution-Neumann formula.
It does not prove that the omitted derivatives of the archimedean factor are
small in the contour argument; that analytic adapter remains a separate gate.
-/
import Zeta23.XiPrime.Coeff.LSeries

open scoped BigOperators ArithmeticFunction ArithmeticFunction.Omega LSeries.notation
open Finset

noncomputable section

namespace Zeta23.Research.XiDerivK

open Zeta23.XiPrime

/-- Coefficients of the series provisionally denoted `C`. -/
def lamLog2C (n : ℕ) : ℂ :=
  ((Λ n * (Real.log n) ^ 2 : ℝ) : ℂ)

/-- The nonconstant part of `F = Ls^2 + d0`. -/
def xiDeriv2DenCore (Ls : ℂ) (n : ℕ) : ℂ :=
  -2 * Ls * lamC n + (lamC ⍟ lamC) n + lamLogC n

/-- Coefficients of `2 (Ls-A) B - C`. -/
def xiDeriv2Numer (Ls : ℂ) (n : ℕ) : ℂ :=
  2 * Ls * lamLogC n - 2 * (lamC ⍟ lamLogC) n - lamLog2C n

/-- Dirichlet-convolution powers for ordinary coefficient sequences. -/
def convolutionPow (f : ℕ → ℂ) : ℕ → ℕ → ℂ
  | 0 => fun n => if n = 1 then 1 else 0
  | j + 1 => convolutionPow f j ⍟ f

/-- The finite Neumann correction `(2QB-C)/(Q^2+B)` at `N`.  Local
finiteness is made explicit by the `Omega(N)` cutoff. -/
def xiDeriv2Correction (Ls : ℂ) (N : ℕ) : ℂ :=
  ∑ j ∈ range (Ω N),
    (Ls⁻¹) ^ 2 * (-((Ls⁻¹) ^ 2)) ^ j *
      ((convolutionPow (xiDeriv2DenCore Ls) j ⍟ xiDeriv2Numer Ls) N)

/-- Provisional frozen coefficient for the prime part of `xi'''/xi''`. -/
def xiDeriv2Coeff (Ls : ℂ) (N : ℕ) : ℂ :=
  -lamC N + xiDeriv2Correction Ls N

/-- The finite convolution-Neumann formula displayed by the definition. -/
theorem xiDeriv2_coeff_neumann (Ls : ℂ) (N : ℕ) :
    xiDeriv2Coeff Ls N = -lamC N +
      ∑ j ∈ range (Ω N),
        (Ls⁻¹) ^ 2 * (-((Ls⁻¹) ^ 2)) ^ j *
          ((convolutionPow (xiDeriv2DenCore Ls) j ⍟ xiDeriv2Numer Ls) N) :=
  rfl

/-- The exact convolution equation that the correction coefficients must
satisfy.  Connecting the finite Neumann candidate to this equation for every
`N` is intentionally a later proof obligation. -/
def XiDeriv2CorrectionEquation (Ls : ℂ) (jCoeff : ℕ → ℂ) : Prop :=
  ∀ N, Ls ^ 2 * jCoeff N + (xiDeriv2DenCore Ls ⍟ jCoeff) N =
    xiDeriv2Numer Ls N

/-- Pointwise recurrence obtained from the convolution equation. -/
theorem xiDeriv2_coeff_recurrence_of_equation {Ls : ℂ} {jCoeff : ℕ → ℂ}
    (hEq : XiDeriv2CorrectionEquation Ls jCoeff) (N : ℕ) :
    Ls ^ 2 * jCoeff N =
      xiDeriv2Numer Ls N - (xiDeriv2DenCore Ls ⍟ jCoeff) N := by
  have h := hEq N
  linear_combination h

@[simp] theorem xiDeriv2Coeff_zero (Ls : ℂ) : xiDeriv2Coeff Ls 0 = 0 := by
  simp [xiDeriv2Coeff, xiDeriv2Correction, lamC]

@[simp] theorem xiDeriv2Coeff_one (Ls : ℂ) : xiDeriv2Coeff Ls 1 = 0 := by
  simp [xiDeriv2Coeff, xiDeriv2Correction, xiDeriv2Numer, lamLog2C,
    LSeries.convolution_def, lamC, lamLogC]

end Zeta23.Research.XiDerivK
