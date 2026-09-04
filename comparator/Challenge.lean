/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
/-
Challenge.lean — the TRUSTED comparator challenge module: WHAT IS CLAIMED.

Fifteen theorem statements about the zeros of Mathlib's `riemannZeta` and of Mathlib's
`DirichletCharacter.LFunction`, each with proof `sorry`. They are the ε-forms of the headline
("in particular") assertions of Theorems A–E of the paper "More than two thirds of the zeros of the
Riemann zeta function lie on the critical line", with Theorems B–E in their Cauchy–Schwarz forms (1/2
simple, 3/4 distinct, 2c₁* − 1 and c₁* with the optimal window; the paper states the multiplicity-aware
constants 2/3, 5/6, 2 − 1/c₁*, (3 − 1/c₁*)/2, which are the subject of Challenge/Multiplicity.lean):
writing N(T₁,T₂) for the number of nontrivial zeros
with T₁ < Im ρ ≤ T₂ counted with multiplicity, N₀* / N₀ˢ / N_d for the distinct on-line / simple
on-line / distinct counts (all defined from Mathlib alone in ChallengeDeps.lean), and
"liminf_{T→∞} X(T)/N(T) ≥ c" as "∀ ε > 0, ∃ T₀, ∀ T ≥ T₀, (c − ε)·N(T) ≤ X(T)":
  * Theorem A: N₀*/N ≥ 2/3 (dyadic windows (T,2T] and cumulative windows (0,T]);
  * Theorem B (Cauchy–Schwarz form): N₀ˢ/N ≥ 1/2 (both forms);   * Theorem C (Cauchy–Schwarz form): N_d/N ≥ 3/4;
  * Theorem D: with the Montgomery–Taylor constant c₁* = `cMT` (ChallengeDeps §3), on dyadic windows
    N₀*/N ≥ 2 − 1/c₁*,  N₀ˢ/N ≥ 2c₁* − 1,  N_d/N ≥ c₁*;
  * Theorem E: for every primitive Dirichlet character χ mod q > 1, the analogues of A, B, C (dyadic)
    for the zeros of L(s,χ), and ("Theorem D holds likewise") the three Theorem-D bounds for L(s,χ).
Solution.lean (untrusted) proves exactly these statements by delegating to the Zeta23 library;
github.com/leanprover/comparator checks statement equality, that only the axioms propext,
Classical.choice, Quot.sound are used, and replays the proofs through the kernel. See README.md here.

The `sorry`s below are deliberate (this is the challenge side); expect "declaration uses 'sorry'"
warnings when building this module.
-/
import ChallengeDeps

noncomputable section

/-- **Theorem A — at least 2/3 of the nontrivial zeros of ζ lie on the critical line** (dyadic
windows): for every ε > 0 and all sufficiently large T, (2/3 − ε)·N(T,2T) ≤ N₀*(T,2T), i.e.
liminf_{T→∞} N₀*(T,2T)/N(T,2T) ≥ 2/3. The zeros with T < Im ρ ≤ 2T are counted WITH multiplicity on
the left and as DISTINCT points of the critical line on the right. -/
theorem two_thirds_on_critical_line :
    ∀ ε > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀, (2 / 3 - ε) * (Ncount T (2 * T) : ℝ) ≤ N0star T (2 * T) := by
  sorry

/-- **Theorem A**, cumulative form: liminf_{T→∞} N₀*(T)/N(T) ≥ 2/3 (windows (0,T]). -/
theorem two_thirds_on_critical_line_cumulative :
    ∀ ε > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀, (2 / 3 - ε) * (Ncount 0 T : ℝ) ≤ N0star 0 T := by
  sorry

/-- **Theorem B — at least 1/2 of the zeros are simple and on the critical line** (dyadic windows).
-/
theorem half_simple_on_critical_line :
    ∀ ε > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀, (1 / 2 - ε) * (Ncount T (2 * T) : ℝ) ≤ N0simple T (2 * T) := by
  sorry

/-- **Theorem B**, cumulative form: liminf_{T→∞} N₀ˢ(T)/N(T) ≥ 1/2. -/
theorem half_simple_on_critical_line_cumulative :
    ∀ ε > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀, (1 / 2 - ε) * (Ncount 0 T : ℝ) ≤ N0simple 0 T := by
  sorry

/-- **Theorem C — at least 3/4 of the zeros are distinct** (dyadic windows). -/
theorem three_quarters_distinct :
    ∀ ε > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀, (3 / 4 - ε) * (Ncount T (2 * T) : ℝ) ≤ Ndist T (2 * T) := by
  sorry

/-- **Theorem C**, cumulative form: liminf_{T→∞} N_d(T)/N(T) ≥ 3/4. -/
theorem three_quarters_distinct_cumulative :
    ∀ ε > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀, (3 / 4 - ε) * (Ncount 0 T : ℝ) ≤ Ndist 0 T := by
  sorry

/-- **Theorem D — the optimal (Montgomery–Taylor) window**: liminf_{T→∞} N₀*(T,2T)/N(T,2T) ≥ 2 −
1/c₁* (= 3/2 − cot(1/√2)/√2 = 0.67250…), with c₁* = `cMT`. -/
theorem montgomery_taylor_on_critical_line :
    ∀ ε > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀, (2 - 1 / cMT - ε) * (Ncount T (2 * T) : ℝ) ≤ N0star T (2 * T) := by
  sorry

/-- **Theorem D**, simple zeros on the line: liminf_{T→∞} N₀ˢ(T,2T)/N(T,2T) ≥ 2c₁* − 1 (= 0.50659…).
-/
theorem montgomery_taylor_simple_on_critical_line :
    ∀ ε > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀, (2 * cMT - 1 - ε) * (Ncount T (2 * T) : ℝ) ≤ N0simple T (2 * T) := by
  sorry

/-- **Theorem D**, distinct zeros: liminf_{T→∞} N_d(T,2T)/N(T,2T) ≥ c₁* (= 0.75329…). -/
theorem montgomery_taylor_distinct :
    ∀ ε > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀, (cMT - ε) * (Ncount T (2 * T) : ℝ) ≤ Ndist T (2 * T) := by
  sorry

/-- **Theorem E — Dirichlet L-functions**: for every primitive Dirichlet character χ modulo q > 1,
at least 2/3 of the nontrivial zeros of L(s,χ) with T < Im ρ ≤ 2T (counted with multiplicity) are
matched by distinct zeros on the critical line, for all large T. -/
theorem dirichlet_two_thirds_on_critical_line
    {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (hq : 1 < q) (hχ : χ.IsPrimitive) :
    ∀ ε > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀, (2 / 3 - ε) * (NcountL χ T (2 * T) : ℝ) ≤ N0starL χ T (2 * T) := by
  sorry

/-- **Theorem E**: at least 1/2 of the nontrivial zeros of L(s,χ) are simple and on the critical
line (χ primitive mod q > 1; dyadic windows). -/
theorem dirichlet_half_simple_on_critical_line
    {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (hq : 1 < q) (hχ : χ.IsPrimitive) :
    ∀ ε > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀, (1 / 2 - ε) * (NcountL χ T (2 * T) : ℝ) ≤ N0simpleL χ T (2 * T) := by
  sorry

/-- **Theorem E**: at least 3/4 of the nontrivial zeros of L(s,χ) are distinct (χ primitive mod q >
1; dyadic windows). -/
theorem dirichlet_three_quarters_distinct
    {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (hq : 1 < q) (hχ : χ.IsPrimitive) :
    ∀ ε > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀, (3 / 4 - ε) * (NcountL χ T (2 * T) : ℝ) ≤ NdistL χ T (2 * T) := by
  sorry

/-- **Theorem E, "Theorem D holds likewise"**: for χ primitive mod q > 1, liminf_{T→∞}
N*_{0,χ}(T,2T)/N_χ(T,2T) ≥ 2 − 1/c₁* (= 0.67250…). -/
theorem dirichlet_montgomery_taylor_on_critical_line
    {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (hq : 1 < q) (hχ : χ.IsPrimitive) :
    ∀ ε > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀, (2 - 1 / cMT - ε) * (NcountL χ T (2 * T) : ℝ) ≤ N0starL χ T (2 * T) := by
  sorry

/-- **Theorem E, "Theorem D holds likewise"**, simple zeros on the line: ≥ 2c₁* − 1 (= 0.50659…). -/
theorem dirichlet_montgomery_taylor_simple_on_critical_line
    {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (hq : 1 < q) (hχ : χ.IsPrimitive) :
    ∀ ε > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀, (2 * cMT - 1 - ε) * (NcountL χ T (2 * T) : ℝ) ≤ N0simpleL χ T (2 * T) := by
  sorry

/-- **Theorem E, "Theorem D holds likewise"**, distinct zeros: ≥ c₁* (= 0.75329…). -/
theorem dirichlet_montgomery_taylor_distinct
    {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (hq : 1 < q) (hχ : χ.IsPrimitive) :
    ∀ ε > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀, (cMT - ε) * (NcountL χ T (2 * T) : ℝ) ≤ NdistL χ T (2 * T) := by
  sorry

end
