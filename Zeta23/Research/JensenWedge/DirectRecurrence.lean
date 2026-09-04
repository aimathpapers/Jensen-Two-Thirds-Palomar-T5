import Mathlib

/-!
# Algebraic elimination for the non-perturbative Jensen recurrence

This module checks the finite algebra used to eliminate Holland's auxiliary
Jacobi-error sequence.  It assumes the three displayed recurrence identities;
it does not prove that a hypergeometric polynomial satisfies them and contains
no asymptotic estimate.  The paper proof now derives the same four coefficients
directly from the shifted `_3F_2` differential equation; the exact symbolic
producer checks that the ODE and eliminated coefficients agree.
-/

namespace Zeta23.Research.JensenWedge

noncomputable def recurrenceEpsilon (C D : ℝ) : ℝ := (C - D) / C

noncomputable def recurrenceA (A y : ℝ) : ℝ := 1 - y / A

noncomputable def recurrenceB (A B y d m : ℝ) : ℝ :=
  B + m - y + (d - 1 - 2 * m) * y / A

noncomputable def recurrenceC (A y d m : ℝ) : ℝ :=
  (d - m) * (1 + m / A) * y

noncomputable def recurrenceBeta (A d m : ℝ) : ℝ :=
  A * (2 * m + 1 - d) - d * (2 * m + 1) + 3 * m ^ 2 + 3 * m + 1

noncomputable def recurrenceGamma (A d m : ℝ) : ℝ :=
  m * (m - d) * (m + A)

noncomputable def recurrenceP3 (A C D y : ℝ) : ℝ :=
  recurrenceA A y + recurrenceEpsilon C D * y / A

noncomputable def recurrenceP2 (A B C D y d m : ℝ) : ℝ :=
  recurrenceB A B y d (m + 1) + (D + m) * recurrenceA A y +
    recurrenceEpsilon C D * y / A * (A - d + 3 + 3 * m)

noncomputable def recurrenceP1 (A B C D y d m : ℝ) : ℝ :=
  recurrenceC A y d (m + 1) + (D + m) * recurrenceB A B y d m +
    recurrenceEpsilon C D * y / A * recurrenceBeta A d m

noncomputable def recurrenceP0 (A C D y d m : ℝ) : ℝ :=
  (D + m) * recurrenceC A y d m +
    recurrenceEpsilon C D * y / A * recurrenceGamma A d m

/-- Legacy/superseded adapter: eliminating `U_m`, `U_(m+1)`, and `V_m` from
the three supplied auxiliary identities gives the direct four-term recurrence.
The paper's provenance is now the displayed shifted `_3F_2` ODE, not this
conditional elimination theorem. -/
theorem directRecurrence_elimination
    {A B C D y d m T0 T1 T2 T3 U0 U1 V : ℝ}
    (hU0 : y * U0 = recurrenceA A y * T2 + recurrenceB A B y d m * T1 +
      recurrenceC A y d m * T0)
    (hU1 : y * U1 = recurrenceA A y * T3 + recurrenceB A B y d (m + 1) * T2 +
      recurrenceC A y d (m + 1) * T1)
    (hV : y * V = y / A *
      (T3 + (A - d + 3 + 3 * m) * T2 + recurrenceBeta A d m * T1 +
        recurrenceGamma A d m * T0))
    (hAux : U1 + (D + m) * U0 = -recurrenceEpsilon C D * V) :
    recurrenceP3 A C D y * T3 + recurrenceP2 A B C D y d m * T2 +
      recurrenceP1 A B C D y d m * T1 + recurrenceP0 A C D y d m * T0 = 0 := by
  have hcombined :
      y * U1 + (D + m) * (y * U0) + recurrenceEpsilon C D * (y * V) = 0 := by
    calc
      y * U1 + (D + m) * (y * U0) + recurrenceEpsilon C D * (y * V) =
          y * (U1 + (D + m) * U0 + recurrenceEpsilon C D * V) := by ring
      _ = 0 := by rw [hAux]; ring
  rw [hU0, hU1, hV] at hcombined
  simpa only [recurrenceP3, recurrenceP2, recurrenceP1, recurrenceP0] using
    (show recurrenceP3 A C D y * T3 + recurrenceP2 A B C D y d m * T2 +
      recurrenceP1 A B C D y d m * T1 + recurrenceP0 A C D y d m * T0 = 0 by
      simp only [recurrenceP3, recurrenceP2, recurrenceP1, recurrenceP0]
      ring_nf at hcombined ⊢
      exact hcombined)

/-! The following closed forms expose the coefficients used in the analytic
dominance argument.  They are consequences only of the definitions above;
they do not assert the parameter inequalities needed later. -/

theorem recurrenceP3_closed
    {A C D y : ℝ} (hA : A ≠ 0) (hC : C ≠ 0) :
    recurrenceP3 A C D y = (A * C - D * y) / (A * C) := by
  simp only [recurrenceP3, recurrenceA, recurrenceEpsilon]
  field_simp [hA, hC]
  all_goals ring

theorem recurrenceP2_closed
    {A B C D y d m : ℝ} (hA : A ≠ 0) (hC : C ≠ 0) :
    recurrenceP2 A B C D y d m =
      (A * C * (B + D + 2 * m + 1) - A * D * y - C * D * y +
        D * d * y - 3 * D * m * y - 3 * D * y) / (A * C) := by
  simp only [recurrenceP2, recurrenceA, recurrenceB, recurrenceEpsilon]
  field_simp [hA, hC]
  all_goals ring

theorem recurrenceP1_closed
    {A B C D y d m : ℝ} (hA : A ≠ 0) (hC : C ≠ 0) :
    recurrenceP1 A B C D y d m =
      (A * B * C * D + A * B * C * m + A * C * D * m -
        A * C * D * y + A * C * m ^ 2 + A * D * d * y -
        2 * A * D * m * y - A * D * y + C * D * d * y -
        2 * C * D * m * y - C * D * y + 2 * D * d * m * y +
        D * d * y - 3 * D * m ^ 2 * y - 3 * D * m * y - D * y) /
        (A * C) := by
  simp only [recurrenceP1, recurrenceB, recurrenceC, recurrenceBeta,
    recurrenceEpsilon]
  field_simp [hA, hC]
  all_goals ring

theorem recurrenceP0_closed
    {A C D y d m : ℝ} (hA : A ≠ 0) (hC : C ≠ 0) :
    recurrenceP0 A C D y d m =
      D * y * (A + m) * (C + m) * (d - m) / (A * C) := by
  simp only [recurrenceP0, recurrenceC, recurrenceGamma, recurrenceEpsilon]
  field_simp [hA, hC]
  all_goals ring

end Zeta23.Research.JensenWedge
