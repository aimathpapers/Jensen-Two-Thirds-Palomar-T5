/-
# Marginal-only hybrid bounds

This module isolates the first semantic obstruction in a proposed hybrid of
the Gram detector and a Levinson detector.  Two lower bounds for the same
target combine only by taking their maximum.  More importantly, a lower bound
for all critical-line zeros cannot improve a lower bound for simple critical-
line zeros when the latter form a nested subpopulation.

No analytic interpretation of either detector is assumed here.
-/
import Mathlib.Order.Lattice.Nat

namespace Zeta23.Research.Hybrid

/-- Two marginal lower bounds for one target imply their maximum, and nothing
stronger is used in this implication. -/
theorem sameTarget_lower_of_marginals {pair levinson target : ℕ}
    (hpair : pair ≤ target) (hlevinson : levinson ≤ target) :
    max pair levinson ≤ target :=
  max_le hpair hlevinson

/-- The maximum bound is sharp given only two same-target marginals. -/
theorem sameTarget_marginals_sharp (pair levinson : ℕ) :
    ∃ target, pair ≤ target ∧ levinson ≤ target ∧
      target = max pair levinson := by
  exact ⟨max pair levinson, le_max_left _ _, le_max_right _ _, rfl⟩

/-- The three populations needed to compare a simple-critical detector with a
critical-line detector. -/
structure NestedCounts where
  total : ℕ
  simpleCritical : ℕ
  criticalLine : ℕ
  simple_le_line : simpleCritical ≤ criticalLine
  line_le_total : criticalLine ≤ total

/-- An extremal configuration satisfying arbitrary compatible marginal lower
bounds while keeping the simple-critical population exactly at its own lower
bound. -/
def nestedMarginalWitness (simpleLower lineLower total : ℕ)
    (hs : simpleLower ≤ total) (hl : lineLower ≤ total) : NestedCounts where
  total := total
  simpleCritical := simpleLower
  criticalLine := max simpleLower lineLower
  simple_le_line := le_max_left _ _
  line_le_total := max_le hs hl

theorem nestedMarginalWitness_simple (simpleLower lineLower total : ℕ)
    (hs : simpleLower ≤ total) (hl : lineLower ≤ total) :
    (nestedMarginalWitness simpleLower lineLower total hs hl).simpleCritical =
      simpleLower :=
  rfl

theorem nestedMarginalWitness_marginals (simpleLower lineLower total : ℕ)
    (hs : simpleLower ≤ total) (hl : lineLower ≤ total) :
    simpleLower ≤
        (nestedMarginalWitness simpleLower lineLower total hs hl).simpleCritical ∧
      lineLower ≤
        (nestedMarginalWitness simpleLower lineLower total hs hl).criticalLine := by
  constructor
  · exact le_rfl
  · exact le_max_right _ _

/-- Sharp no-gain theorem: every universal simple-critical lower bound derived
only from compatible lower marginals for `simpleCritical` and `criticalLine`
is at most the original simple-critical marginal. -/
theorem no_simple_gain_from_nested_marginals
    {simpleLower lineLower total claimed : ℕ}
    (hs : simpleLower ≤ total) (hl : lineLower ≤ total)
    (hclaimed : ∀ counts : NestedCounts,
      counts.total = total →
      simpleLower ≤ counts.simpleCritical →
      lineLower ≤ counts.criticalLine →
      claimed ≤ counts.simpleCritical) :
    claimed ≤ simpleLower := by
  let counts := nestedMarginalWitness simpleLower lineLower total hs hl
  have hm := nestedMarginalWitness_marginals simpleLower lineLower total hs hl
  have h := hclaimed counts rfl hm.1 hm.2
  simpa [counts, nestedMarginalWitness] using h

end Zeta23.Research.Hybrid
