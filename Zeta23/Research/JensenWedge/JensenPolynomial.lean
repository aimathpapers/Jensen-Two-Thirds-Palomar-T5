import Zeta23.Research.JensenWedge.ConditionalAssembly

/-!
# Concrete Jensen-polynomial interface

This module connects the abstract conditional assembly to the standard
Jensen polynomial attached to a real sequence.  It intentionally makes no
claim that a particular sequence supplies the analytic certificate: that is
the remaining paper-level construction.
-/

namespace Zeta23.Research.JensenWedge

/-- The degree-`d` Jensen polynomial attached to `γ`, based at `n`. -/
noncomputable def jensenPolynomial
    (γ : ℕ → ℝ) (n d : ℕ) (X : ℝ) : ℝ :=
  ∑ j ∈ Finset.range (d + 1),
    (Nat.choose d j : ℝ) * γ (n + j) * X ^ j

/-- The conditional wedge theorem specialized to the actual Jensen
polynomial formula.  All analytic content is still isolated in
`certificate`; this theorem only closes the definition/interface gap. -/
theorem conditionalTwoThirdsWedge_jensenPolynomial
    (γ : ℕ → ℝ) (K : ℝ)
    (certificate : ∀ n d, TwoThirdsWedge K n d →
      JensenWedgeCertificate (jensenPolynomial γ n d) d) :
    ∀ n d, TwoThirdsWedge K n d →
      HasDistinctNegativeRoots (jensenPolynomial γ n d) d := by
  exact conditionalTwoThirdsWedge (fun n d => jensenPolynomial γ n d) K certificate

end Zeta23.Research.JensenWedge
