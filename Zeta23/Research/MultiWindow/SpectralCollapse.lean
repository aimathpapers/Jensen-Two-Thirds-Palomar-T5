/-
# Spectral collapse of the naive labeled Gram

For a stacked sampling matrix `U`, the labeled Gram `U Uᴴ` and the unlabeled
Gram `Uᴴ U` have the same nonzero singular spectrum.  This file records the
exact consequences used by the C01 structural kill test: total trace, squared
Frobenius norm, rank, and positive inertia cannot recover the window labels.
-/
import Zeta23.Research.MultiWindow.ChangeBasis
import Zeta23.LinAlg.PosIndex
import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.LinearAlgebra.Matrix.Trace

noncomputable section
set_option linter.unusedSectionVars false

open Matrix RHLinalg
open scoped BigOperators ComplexOrder

namespace Zeta23.Research.MultiWindow

variable {A K I : Type*}
variable [Fintype A] [Fintype K] [Fintype I]
variable [DecidableEq A] [DecidableEq K] [DecidableEq I]

/-- The unlabeled input-space Gram is positive semidefinite. -/
theorem aggregateGram_posSemidef (U : A → Matrix K I ℂ) :
    (aggregateGram U).PosSemidef := by
  exact Matrix.posSemidef_conjTranspose_mul_self _

/-- The labeled and unlabeled Grams have the same trace. -/
theorem trace_jointGram_eq_trace_aggregateGram (U : A → Matrix K I ℂ) :
    (jointGram U).trace = (aggregateGram U).trace := by
  exact Matrix.trace_mul_comm (stack U) (Matrix.conjTranspose (stack U))

/-- Real traces therefore agree as well. -/
theorem rtrace_jointGram_eq_rtrace_aggregateGram (U : A → Matrix K I ℂ) :
    rtrace (jointGram U) = rtrace (aggregateGram U) := by
  unfold rtrace
  rw [trace_jointGram_eq_trace_aggregateGram]

/-- The labeled and unlabeled Grams have the same rank. -/
theorem rank_jointGram_eq_rank_aggregateGram (U : A → Matrix K I ℂ) :
    (jointGram U).rank = (aggregateGram U).rank := by
  unfold jointGram aggregateGram
  rw [Matrix.rank_self_mul_conjTranspose, Matrix.rank_conjTranspose_mul_self]

private theorem trace_jointGram_sq_eq_trace_aggregateGram_sq
    (U : A → Matrix K I ℂ) :
    ((jointGram U) * (jointGram U)).trace =
      ((aggregateGram U) * (aggregateGram U)).trace := by
  let S : Matrix (A × K) I ℂ := stack U
  change ((S * Sᴴ) * (S * Sᴴ)).trace = ((Sᴴ * S) * (Sᴴ * S)).trace
  calc
    ((S * Sᴴ) * (S * Sᴴ)).trace =
        (S * ((Sᴴ * S) * Sᴴ)).trace := by simp only [Matrix.mul_assoc]
    _ = (((Sᴴ * S) * Sᴴ) * S).trace :=
      Matrix.trace_mul_comm S ((Sᴴ * S) * Sᴴ)
    _ = ((Sᴴ * S) * (Sᴴ * S)).trace := by simp only [Matrix.mul_assoc]

/-- Squared Frobenius norms agree; a Frobenius-only certificate sees no more
than the aggregate input-space Gram. -/
theorem frobSq_jointGram_eq_frobSq_aggregateGram (U : A → Matrix K I ℂ) :
    frobSq (jointGram U) = frobSq (aggregateGram U) := by
  unfold frobSq
  rw [(jointGram_isHermitian U).eq, (aggregateGram_posSemidef U).isHermitian.eq]
  exact congrArg RCLike.re (trace_jointGram_sq_eq_trace_aggregateGram_sq U)

/-- Since both Grams are positive semidefinite, their positive inertia also
agrees and equals their common rank. -/
theorem posIndex_jointGram_eq_posIndex_aggregateGram (U : A → Matrix K I ℂ) :
    posIndex (jointGram_posSemidef U).isHermitian =
      posIndex (aggregateGram_posSemidef U).isHermitian := by
  rw [posIndex_eq_rank_of_posSemidef (jointGram_posSemidef U),
    posIndex_eq_rank_of_posSemidef (aggregateGram_posSemidef U),
    rank_jointGram_eq_rank_aggregateGram]

end Zeta23.Research.MultiWindow
