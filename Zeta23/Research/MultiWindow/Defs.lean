/-
# Multi-window sampling maps

Finite-dimensional definitions for the C01 structural kill test.  Every window
acts on the same input coordinates and the product index retains the window
label.  These definitions deliberately make no analytic or zeta-specific
claim; the Poisson, reflection, tail, and prime-side bridges are separate
obligations.
-/
import Mathlib.Analysis.Complex.Order
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.LinearAlgebra.Matrix.Kronecker

noncomputable section
set_option linter.unusedSectionVars false

open Matrix Finset
open scoped BigOperators ComplexOrder Kronecker

namespace Zeta23.Research.MultiWindow

variable {A K I : Type*}
variable [Fintype A] [Fintype K] [Fintype I]
variable [DecidableEq A] [DecidableEq K] [DecidableEq I]

/-- Stack a family of sampling maps while retaining the window label. -/
def stack (U : A → Matrix K I ℂ) : Matrix (A × K) I ℂ :=
  fun ak i => U ak.1 ak.2 i

/-- The unlabeled Gram operator seen from the common input space. -/
def aggregateGram (U : A → Matrix K I ℂ) : Matrix I I ℂ :=
  Matrix.conjTranspose (stack U) * stack U

/-- The Gram contribution of one labeled window. -/
def marginalGram (U : A → Matrix K I ℂ) (a : A) : Matrix I I ℂ :=
  Matrix.conjTranspose (U a) * U a

/-- A labeled cross-Gram contribution. -/
def crossGram (U : A → Matrix K I ℂ) (a b : A) : Matrix I I ℂ :=
  Matrix.conjTranspose (U a) * U b

/-- Mix window labels by a matrix, leaving the sample coordinate untouched. -/
def mix (C : Matrix A A ℂ) (U : A → Matrix K I ℂ) : A → Matrix K I ℂ :=
  fun a k i => ∑ b, C a b * U b k i

/-- The induced action on the labeled sample space. -/
def windowAction (C : Matrix A A ℂ) : Matrix (A × K) (A × K) ℂ :=
  C ⊗ₖ (1 : Matrix K K ℂ)

/-- The labeled Gram operator on window/sample space. -/
def jointGram (U : A → Matrix K I ℂ) : Matrix (A × K) (A × K) ℂ :=
  stack U * Matrix.conjTranspose (stack U)

/-- Regard one ordinary sampling map as a singleton window family. -/
def singletonWindow (V : Matrix K I ℂ) : PUnit → Matrix K I ℂ := fun _ => V

end Zeta23.Research.MultiWindow
