/-
# Exact symmetries of xi''
-/
import Zeta23.Research.XiDerivK.Defs

noncomputable section
open scoped ComplexConjugate

namespace Zeta23.Research.XiDerivK

open Complex
open Zeta23 XiPrime

/-- Even functional-equation sign for the second derivative. -/
theorem xiDeriv2_one_sub (s : ℂ) : xiDeriv2 (1 - s) = xiDeriv2 s := by
  exact XiPrime.deriv_xiDeriv_one_sub s

/-- Schwarz reflection for the second derivative. -/
theorem xiDeriv2_conj (s : ℂ) :
    xiDeriv2 (conj s) = conj (xiDeriv2 s) := by
  exact XiPrime.deriv_xiDeriv_conj s

/-- Reflection through the critical line preserves the value up to complex
conjugation; unlike xi', the sign is positive. -/
theorem xiDeriv2_reflect (s : ℂ) :
    xiDeriv2 (reflect s) = conj (xiDeriv2 s) := by
  unfold reflect
  rw [xiDeriv2_one_sub, xiDeriv2_conj]

theorem xiDeriv2_reflect_eq_zero_iff (s : ℂ) :
    xiDeriv2 (reflect s) = 0 ↔ xiDeriv2 s = 0 := by
  rw [xiDeriv2_reflect, map_eq_zero]

end Zeta23.Research.XiDerivK
