/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
/-
Solution.lean — the UNTRUSTED comparator solution module: the fifteen statements of Challenge.lean,
byte-identical, each PROVED by delegating to the Zeta23 library:

  A, B, C  →  Zeta23.thmA₀ / thmA₀_cumulative / thmB₀ / thmB₀_cumulative / thmC₀ / thmC₀_cumulative
              (Zeta23/Final.lean, re-exported with English names by Zeta23/Unconditional.lean);
  D        →  Zeta23.ThmD.thmD₀ / thmD₀_simple / thmD₀_dist            (Zeta23/ThmD/Final.lean);
  E        →  Zeta23.ThmE.thmE_A₀ / thmE_B₀ / thmE_C₀                  (Zeta23/ThmE/Final.lean);
  D for χ  →  Zeta23.ThmDE.thmE_D₀ / thmE_D₀_simple / thmE_D₀_dist      (Zeta23/ThmDE/Final.lean).

The challenge's counting functions (ChallengeDeps.lean) are character-for-character the Zeta23 ones
(Zeta23/Statement.lean §1, Zeta23/ThmE/Statement.lean §1) in a different namespace, so each delegation
typechecks by definitional unfolding in the kernel. The only mathematics proved HERE is the identity
`cStar_one_eq_cMT`: Zeta23 carries the Theorem-D constant as `Zeta23.ThmD.cStar 1`
(= √2·sin ϑ/(cos ϑ + ϑ·sin ϑ) at ϑ = 1/√2, a division-safe form) and `Zeta23.ThmD.HD 1 = 2 − 1/cStar 1`,
while the challenge states the paper's displayed closed form c₁* = √2·tan ϑ/(1 + ϑ·tan ϑ), ϑ = 1/√2.

Nothing in this file is part of the trusted base: comparator re-checks that every theorem below has
exactly the statement of its Challenge namesake and uses only the permitted axioms.
-/
import ChallengeDeps
import Zeta23.Unconditional
import Zeta23.ThmD.Final
import Zeta23.ThmE.Final
import Zeta23.ThmDE.Final

noncomputable section

/-- The Zeta23 library's Theorem-D constant `cStar 1` (division-safe sin/cos form) equals the
challenge's `cMT` (the paper's tan form at ϑ = 1/√2): by Zeta23's own `cStar_eq_tan_form` and
unfolding `Zeta23.ThmD.theta 1 = 1 / Real.sqrt 2`. -/
theorem cStar_one_eq_cMT : Zeta23.ThmD.cStar 1 = cMT := by
  rw [Zeta23.ThmD.cStar_eq_tan_form zero_le_one le_rfl]
  unfold cMT Zeta23.ThmD.theta
  rfl

theorem two_thirds_on_critical_line :
    ∀ ε > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀, (2 / 3 - ε) * (Ncount T (2 * T) : ℝ) ≤ N0star T (2 * T) :=
  Zeta23.thmA₀

theorem two_thirds_on_critical_line_cumulative :
    ∀ ε > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀, (2 / 3 - ε) * (Ncount 0 T : ℝ) ≤ N0star 0 T :=
  Zeta23.thmA₀_cumulative

theorem half_simple_on_critical_line :
    ∀ ε > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀, (1 / 2 - ε) * (Ncount T (2 * T) : ℝ) ≤ N0simple T (2 * T) :=
  Zeta23.thmB₀

theorem half_simple_on_critical_line_cumulative :
    ∀ ε > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀, (1 / 2 - ε) * (Ncount 0 T : ℝ) ≤ N0simple 0 T :=
  Zeta23.thmB₀_cumulative

theorem three_quarters_distinct :
    ∀ ε > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀, (3 / 4 - ε) * (Ncount T (2 * T) : ℝ) ≤ Ndist T (2 * T) :=
  Zeta23.thmC₀

theorem three_quarters_distinct_cumulative :
    ∀ ε > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀, (3 / 4 - ε) * (Ncount 0 T : ℝ) ≤ Ndist 0 T :=
  Zeta23.thmC₀_cumulative

theorem montgomery_taylor_on_critical_line :
    ∀ ε > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀, (2 - 1 / cMT - ε) * (Ncount T (2 * T) : ℝ) ≤ N0star T (2 * T) := by
  have h := @Zeta23.ThmD.thmD₀
  simp only [Zeta23.ThmD.HD, cStar_one_eq_cMT] at h
  exact h

theorem montgomery_taylor_simple_on_critical_line :
    ∀ ε > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀, (2 * cMT - 1 - ε) * (Ncount T (2 * T) : ℝ) ≤ N0simple T (2 * T) := by
  have h := @Zeta23.ThmD.thmD₀_simple
  simp only [cStar_one_eq_cMT] at h
  exact h

theorem montgomery_taylor_distinct :
    ∀ ε > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀, (cMT - ε) * (Ncount T (2 * T) : ℝ) ≤ Ndist T (2 * T) := by
  have h := @Zeta23.ThmD.thmD₀_dist
  simp only [cStar_one_eq_cMT] at h
  exact h

theorem dirichlet_two_thirds_on_critical_line
    {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (hq : 1 < q) (hχ : χ.IsPrimitive) :
    ∀ ε > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀, (2 / 3 - ε) * (NcountL χ T (2 * T) : ℝ) ≤ N0starL χ T (2 * T) :=
  Zeta23.ThmE.thmE_A₀ hq hχ

theorem dirichlet_half_simple_on_critical_line
    {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (hq : 1 < q) (hχ : χ.IsPrimitive) :
    ∀ ε > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀, (1 / 2 - ε) * (NcountL χ T (2 * T) : ℝ) ≤ N0simpleL χ T (2 * T) :=
  Zeta23.ThmE.thmE_B₀ hq hχ

theorem dirichlet_three_quarters_distinct
    {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (hq : 1 < q) (hχ : χ.IsPrimitive) :
    ∀ ε > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀, (3 / 4 - ε) * (NcountL χ T (2 * T) : ℝ) ≤ NdistL χ T (2 * T) :=
  Zeta23.ThmE.thmE_C₀ hq hχ

theorem dirichlet_montgomery_taylor_on_critical_line
    {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (hq : 1 < q) (hχ : χ.IsPrimitive) :
    ∀ ε > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀, (2 - 1 / cMT - ε) * (NcountL χ T (2 * T) : ℝ) ≤ N0starL χ T (2 * T) := by
  have h := Zeta23.ThmDE.thmE_D₀ (χ := χ) hq hχ
  simp only [Zeta23.ThmD.HD, cStar_one_eq_cMT] at h
  exact h

theorem dirichlet_montgomery_taylor_simple_on_critical_line
    {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (hq : 1 < q) (hχ : χ.IsPrimitive) :
    ∀ ε > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀, (2 * cMT - 1 - ε) * (NcountL χ T (2 * T) : ℝ) ≤ N0simpleL χ T (2 * T) := by
  have h := Zeta23.ThmDE.thmE_D₀_simple (χ := χ) hq hχ
  simp only [cStar_one_eq_cMT] at h
  exact h

theorem dirichlet_montgomery_taylor_distinct
    {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (hq : 1 < q) (hχ : χ.IsPrimitive) :
    ∀ ε > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀, (cMT - ε) * (NcountL χ T (2 * T) : ℝ) ≤ NdistL χ T (2 * T) := by
  have h := Zeta23.ThmDE.thmE_D₀_dist (χ := χ) hq hχ
  simp only [cStar_one_eq_cMT] at h
  exact h

end
