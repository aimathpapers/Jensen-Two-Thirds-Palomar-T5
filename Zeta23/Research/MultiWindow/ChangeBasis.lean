/-
# Exact algebra for the C01 multi-window collapse test

The aggregate input-space Gram matrix is exactly the sum of the marginal
Grams.  By contrast, the labeled output-space Gram retains cross blocks and
transforms by window-space congruence.  This file records those statements
entrywise so that complex conjugation and index orientation are explicit.
-/
import Zeta23.Research.MultiWindow.Defs

noncomputable section
set_option linter.unusedSectionVars false

open Matrix Finset
open scoped BigOperators ComplexOrder Kronecker

namespace Zeta23.Research.MultiWindow

variable {A K I : Type*}
variable [Fintype A] [Fintype K] [Fintype I]
variable [DecidableEq A] [DecidableEq K] [DecidableEq I]

/-- Naive stacking forgets labels on the input side: `UᴴU` is the sum of the
individual window Grams. -/
theorem aggregateGram_eq_sum_marginal (U : A → Matrix K I ℂ) :
    aggregateGram U = ∑ a, marginalGram U a := by
  ext i j
  rw [Matrix.sum_apply]
  simp [aggregateGram, marginalGram, stack, Matrix.mul_apply, Fintype.sum_prod_type]

/-- Window mixing is the Kronecker action `C ⊗ I` on the stacked feature map. -/
theorem stack_mix (C : Matrix A A ℂ) (U : A → Matrix K I ℂ) :
    stack (mix C U) = windowAction C * stack U := by
  ext ⟨a, k⟩ i
  change (∑ b, C a b * U b k i) =
    ∑ x : A × K, (C a x.1 * (1 : Matrix K K ℂ) k x.2) * U x.1 x.2 i
  rw [Fintype.sum_prod_type]
  simp [Matrix.one_apply]

/-- Entry formula for the labeled joint Gram. -/
theorem jointGram_apply (U : A → Matrix K I ℂ) (a b : A) (k l : K) :
    jointGram U (a, k) (b, l) =
      ∑ i, U a k i * (starRingEnd ℂ) (U b l i) := by
  simp [jointGram, stack, Matrix.mul_apply, Matrix.conjTranspose_apply]

/-- The labeled joint Gram is positive semidefinite. -/
theorem jointGram_posSemidef (U : A → Matrix K I ℂ) : (jointGram U).PosSemidef := by
  exact Matrix.posSemidef_self_mul_conjTranspose _

/-- In particular, the labeled joint Gram is Hermitian. -/
theorem jointGram_isHermitian (U : A → Matrix K I ℂ) : (jointGram U).IsHermitian :=
  (jointGram_posSemidef U).1

/-- A singleton family recovers the ordinary input-space Gram exactly. -/
theorem aggregateGram_singleton (V : Matrix K I ℂ) :
    aggregateGram (singletonWindow V) = Matrix.conjTranspose V * V := by
  rw [aggregateGram_eq_sum_marginal]
  simp [singletonWindow, marginalGram]

/-- A singleton family also recovers the ordinary output-space Gram entrywise. -/
theorem jointGram_singleton_apply (V : Matrix K I ℂ) (k l : K) :
    jointGram (singletonWindow V) (PUnit.unit, k) (PUnit.unit, l) =
      (V * Matrix.conjTranspose V) k l := by
  simp [jointGram_apply, singletonWindow, Matrix.mul_apply, Matrix.conjTranspose_apply]

/-- Exact change-of-window-basis law, with the conjugation orientation shown
explicitly.  This is the entrywise form of
`G ↦ (C ⊗ I) G (C ⊗ I)ᴴ`. -/
theorem jointGram_changeBasis_apply (C : Matrix A A ℂ) (U : A → Matrix K I ℂ)
    (a b : A) (k l : K) :
    jointGram (mix C U) (a, k) (b, l) =
      ∑ c, ∑ d, C a c * jointGram U (c, k) (d, l) *
        (starRingEnd ℂ) (C b d) := by
  simp only [jointGram_apply, mix]
  simp_rw [map_sum, map_mul, Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  congr 1 with c
  rw [Finset.sum_comm]
  congr 1 with d
  rw [Finset.sum_mul]
  congr 1 with i
  ring

end Zeta23.Research.MultiWindow
