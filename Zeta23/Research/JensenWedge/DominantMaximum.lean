import Mathlib

/-!
# Abstract maximum step for the direct Jensen recurrence

This module checks the finite contradiction used after the analytic
coefficient bounds have reduced every interior normalized term to `q * M`
with `q < 1`.  It does not establish those coefficient bounds.
-/

namespace Zeta23.Research.JensenWedge

/-- If a finite normalized sequence attains its upper bound `M`, the first two
entries are at most one, and every later entry is at most `q*M` for `q<1`,
then `M` itself is at most one. -/
theorem dominantMaximum_le_one
    {d : ℕ} {u : ℕ → ℝ} {M q : ℝ}
    (hq_lt_one : q < 1)
    (hattain : ∃ k, k ≤ d ∧ u k = M)
    (hzero : u 0 ≤ 1)
    (hone : u 1 ≤ 1)
    (hrec : ∀ k, 2 ≤ k → k ≤ d → u k ≤ q * M) :
    M ≤ 1 := by
  by_contra hM
  have hM_gt_one : 1 < M := lt_of_not_ge hM
  obtain ⟨k, hkd, huk⟩ := hattain
  have hk0 : k ≠ 0 := by
    intro hk
    subst k
    linarith
  have hk1 : k ≠ 1 := by
    intro hk
    subst k
    linarith
  have hk2 : 2 ≤ k := by omega
  have hcontract := hrec k hk2 hkd
  rw [huk] at hcontract
  nlinarith

end Zeta23.Research.JensenWedge
