/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
/-
Solution/Multiplicity.lean — UNTRUSTED solution module for Challenge/Multiplicity.lean: the same twelve
statements, proved by delegating to Zeta23/FinalMult.lean (ζ: thmB₀_mult, thmC₀_mult + cumulative),
Zeta23/ThmD/Mult.lean (optimal window: thmD₀_simple_mult, thmD₀_dist_mult + cumulative; constants
HD 1 = 2 − 1/cStar 1 and GD 1 = 3/2 − (cStar 1)⁻¹/2), Zeta23/ThmE/Mult.lean and Zeta23/ThmDE/Mult.lean (χ).
Reuses `cStar_one_eq_cMT` from module Solution.
-/
import ChallengeDeps
import Solution
import Zeta23.FinalMult
import Zeta23.ThmD.Mult
import Zeta23.ThmE.Mult
import Zeta23.ThmDE.Mult

noncomputable section

theorem two_thirds_simple_on_critical_line :
    ∀ ε > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀, (2 / 3 - ε) * (Ncount T (2 * T) : ℝ) ≤ N0simple T (2 * T) :=
  Zeta23.thmB₀_mult

theorem two_thirds_simple_on_critical_line_cumulative :
    ∀ ε > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀, (2 / 3 - ε) * (Ncount 0 T : ℝ) ≤ N0simple 0 T :=
  Zeta23.thmB₀_mult_cumulative

theorem five_sixths_distinct :
    ∀ ε > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀, (5 / 6 - ε) * (Ncount T (2 * T) : ℝ) ≤ Ndist T (2 * T) :=
  Zeta23.thmC₀_mult

theorem five_sixths_distinct_cumulative :
    ∀ ε > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀, (5 / 6 - ε) * (Ncount 0 T : ℝ) ≤ Ndist 0 T :=
  Zeta23.thmC₀_mult_cumulative

theorem montgomery_taylor_simple_on_critical_line_mult :
    ∀ ε > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀, (2 - 1 / cMT - ε) * (Ncount T (2 * T) : ℝ) ≤ N0simple T (2 * T) := by
  have h := @Zeta23.ThmD.thmD₀_simple_mult
  simp only [Zeta23.ThmD.HD, cStar_one_eq_cMT] at h
  exact h

theorem montgomery_taylor_simple_on_critical_line_mult_cumulative :
    ∀ ε > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀, (2 - 1 / cMT - ε) * (Ncount 0 T : ℝ) ≤ N0simple 0 T := by
  have h := @Zeta23.ThmD.thmD₀_simple_mult_cumulative
  simp only [Zeta23.ThmD.HD, cStar_one_eq_cMT] at h
  exact h

theorem montgomery_taylor_distinct_mult :
    ∀ ε > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀, (3 / 2 - cMT⁻¹ / 2 - ε) * (Ncount T (2 * T) : ℝ) ≤ Ndist T (2 * T) := by
  have h := @Zeta23.ThmD.thmD₀_dist_mult
  simp only [Zeta23.ThmD.GD, cStar_one_eq_cMT] at h
  exact h

theorem montgomery_taylor_distinct_mult_cumulative :
    ∀ ε > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀, (3 / 2 - cMT⁻¹ / 2 - ε) * (Ncount 0 T : ℝ) ≤ Ndist 0 T := by
  have h := @Zeta23.ThmD.thmD₀_dist_mult_cumulative
  simp only [Zeta23.ThmD.GD, cStar_one_eq_cMT] at h
  exact h

theorem dirichlet_two_thirds_simple_on_critical_line
    {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (hq : 1 < q) (hχ : χ.IsPrimitive) :
    ∀ ε > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀, (2 / 3 - ε) * (NcountL χ T (2 * T) : ℝ) ≤ N0simpleL χ T (2 * T) :=
  Zeta23.ThmE.thmE_B₀_mult hq hχ

theorem dirichlet_five_sixths_distinct
    {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (hq : 1 < q) (hχ : χ.IsPrimitive) :
    ∀ ε > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀, (5 / 6 - ε) * (NcountL χ T (2 * T) : ℝ) ≤ NdistL χ T (2 * T) :=
  Zeta23.ThmE.thmE_C₀_mult hq hχ

theorem dirichlet_montgomery_taylor_simple_on_critical_line_mult
    {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (hq : 1 < q) (hχ : χ.IsPrimitive) :
    ∀ ε > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀, (2 - 1 / cMT - ε) * (NcountL χ T (2 * T) : ℝ) ≤ N0simpleL χ T (2 * T) := by
  have h := Zeta23.ThmDE.thmE_D₀_simple_mult (χ := χ) hq hχ
  simp only [Zeta23.ThmD.HD, cStar_one_eq_cMT] at h
  exact h

theorem dirichlet_montgomery_taylor_distinct_mult
    {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (hq : 1 < q) (hχ : χ.IsPrimitive) :
    ∀ ε > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀, (3 / 2 - cMT⁻¹ / 2 - ε) * (NcountL χ T (2 * T) : ℝ) ≤ NdistL χ T (2 * T) := by
  have h := Zeta23.ThmDE.thmE_D₀_dist_mult (χ := χ) hq hχ
  simp only [Zeta23.ThmD.GD, cStar_one_eq_cMT] at h
  exact h

end
