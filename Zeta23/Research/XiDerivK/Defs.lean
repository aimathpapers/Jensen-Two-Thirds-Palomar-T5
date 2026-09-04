/-
# Stable definitions for the xi-second-derivative experiment

Only entire-function algebra belongs in this module.  Zero-strip, zero-count,
and explicit-formula assertions are deliberately not bundled into the
interface.
-/
import Zeta23.XiPrime.Seam

noncomputable section

namespace Zeta23.Research.XiDerivK

open Complex
open Zeta23.XiPrime

/-- The second complex derivative of Riemann's xi function. -/
def xiDeriv2 : ℂ → ℂ := deriv xiDeriv

/-- Analytic multiplicity of a zero of `xiDeriv2`. -/
def xiDeriv2Mult (rho : ℂ) : ℕ := (analyticOrderAt xiDeriv2 rho).toNat

theorem xiDeriv2_analyticAt (s : ℂ) : AnalyticAt ℂ xiDeriv2 s := by
  exact (xiDeriv_analyticAt s).deriv

theorem xiDeriv2_differentiable : Differentiable ℂ xiDeriv2 :=
  fun s => (xiDeriv2_analyticAt s).differentiableAt

end Zeta23.Research.XiDerivK
