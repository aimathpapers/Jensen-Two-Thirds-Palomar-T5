import Zeta23.Research.JensenWedge.XiAuxiliaryMoment
import Zeta23.Research.JensenWedge.JensenPolynomial
import Zeta23.Research.JensenWedge.QuantitativeBranch

/-!
# The concrete Riemann-xi Jensen target

This module fixes the real coefficient sequence and polynomial to which the
conditional two-thirds root theorem applies.  The coefficients are defined
from the manuscript's real omega integral, and their complexifications are
proved equal to the even Taylor coefficients of Mathlib's centered xi.

The final theorems do not manufacture the remaining Jacobi/MMP/MSS or
sixth-residual inputs.  They state those dependencies through the existing
typed certificate interfaces while removing all ambiguity about the target
sequence and Jensen polynomial.
-/

namespace Zeta23.Research.JensenWedge

open Complex MeasureTheory Set
open Finset Polynomial

noncomputable section

/-- The real manuscript coefficient sequence
`gamma(n) = 8 n!/(2n)! integral_0^infinity u^(2n) omega(e^(2u))e^(u/2) du`.
-/
def riemannXiCoefficientReal (n : ℕ) : ℝ :=
  8 * (n.factorial : ℝ) / ((2 * n).factorial : ℝ) *
    ∫ u in Ioi (0 : ℝ), u ^ (2 * n) * omegaLogAmplitude u

/-- Exact identification of the real omega coefficient with the complex
centered-xi Taylor coefficient proved in T1. -/
theorem ofReal_riemannXiCoefficientReal (n : ℕ) :
    (riemannXiCoefficientReal n : ℂ) = centeredXiCoefficient n := by
  rw [centeredXiCoefficient_eq_omegaMoment,
    halfLineMoment_omegaLogAmplitude_eq_ofReal]
  unfold riemannXiCoefficientReal
  push_cast
  ring

/-- The real sequence has exactly the Taylor normalization printed in the
manuscript. -/
theorem riemannXiCoefficientReal_taylor_normalization (n : ℕ) :
    ((riemannXiCoefficientReal n / (n.factorial : ℝ) : ℝ) : ℂ) =
      iteratedDeriv (2 * n) centeredXi 0 / ((2 * n).factorial : ℂ) := by
  push_cast
  rw [ofReal_riemannXiCoefficientReal]
  exact centeredXiCoefficient_taylor_normalization n

theorem centeredXiCoefficient_im_eq_zero (n : ℕ) :
    (centeredXiCoefficient n).im = 0 := by
  rw [← ofReal_riemannXiCoefficientReal]
  simp

/-- The integer auxiliary-moment specialization lands in the concrete real
coefficient sequence, not merely an abstract complex coefficient. -/
theorem complexFactorialRatio_mul_auxiliary_nat_succ_eq_real (n : ℕ) :
    complexFactorialRatio ((n + 1 : ℕ) : ℂ) *
        complexXiAuxiliaryMoment ((n + 1 : ℕ) : ℂ) =
      (riemannXiCoefficientReal (n + 1) : ℂ) := by
  rw [complexFactorialRatio_mul_auxiliary_nat_succ,
    ofReal_riemannXiCoefficientReal]

/-- The actual Riemann-xi Jensen polynomial in the convention of the paper.
-/
def riemannXiJensenPolynomial (n d : ℕ) (X : ℝ) : ℝ :=
  jensenPolynomial riemannXiCoefficientReal n d X

theorem riemannXiJensenPolynomial_eq_sum (n d : ℕ) (X : ℝ) :
    riemannXiJensenPolynomial n d X =
      ∑ j ∈ Finset.range (d + 1),
        (Nat.choose d j : ℝ) * riemannXiCoefficientReal (n + j) * X ^ j := by
  rfl

/-- Polynomial object whose evaluation is the paper's Jensen function. -/
noncomputable def riemannXiJensenPolynomialObject (n d : ℕ) : ℝ[X] :=
  ∑ j ∈ Finset.range (d + 1),
    Polynomial.C ((Nat.choose d j : ℝ) * riemannXiCoefficientReal (n + j)) *
      Polynomial.X ^ j

theorem eval_riemannXiJensenPolynomialObject (n d : ℕ) (X : ℝ) :
    Polynomial.eval X (riemannXiJensenPolynomialObject n d) =
      riemannXiJensenPolynomial n d X := by
  unfold riemannXiJensenPolynomialObject riemannXiJensenPolynomial jensenPolynomial
  simp only [Polynomial.eval_finsetSum, Polynomial.eval_mul,
    Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]

theorem riemannXiJensenPolynomialObject_natDegree_le (n d : ℕ) :
    (riemannXiJensenPolynomialObject n d).natDegree ≤ d := by
  unfold riemannXiJensenPolynomialObject
  apply natDegree_sum_le_of_forall_le
  intro j hj
  rw [Finset.mem_range] at hj
  exact (natDegree_C_mul_X_pow_le _ _).trans (Nat.le_of_lt_succ hj)

theorem riemannXiJensenPolynomialObject_coeff_degree (n d : ℕ) :
    (riemannXiJensenPolynomialObject n d).coeff d =
      riemannXiCoefficientReal (n + d) := by
  unfold riemannXiJensenPolynomialObject
  rw [Polynomial.finsetSum_coeff]
  simp_rw [Polynomial.coeff_C_mul_X_pow]
  simp

/-- Concrete-target form of the conditional root theorem.  The target is no
longer a caller-chosen sequence. -/
theorem conditionalTwoThirdsWedge_riemannXi
    (K : ℝ)
    (certificate : ∀ n d, TwoThirdsWedge K n d →
      JensenWedgeCertificate (riemannXiJensenPolynomial n d) d) :
    ∀ n d, TwoThirdsWedge K n d →
      HasDistinctNegativeRoots (riemannXiJensenPolynomial n d) d := by
  exact conditionalTwoThirdsWedge
    (fun n d => riemannXiJensenPolynomial n d) K certificate

/-- The same concrete-target theorem expressed through the fully split typed
analytic inputs.  This makes the remaining parameter-branch, comparison-root,
sixth-residual, and xi-identification obligations visible in the theorem
signature. -/
theorem conditionalTwoThirdsWedge_riemannXi_of_analyticInputs
    (K : ℝ) (G : ℕ → ℕ → BranchPoint → BranchPoint)
    (inputs : ∀ n d, TwoThirdsWedge K n d →
      JensenWedgeAnalyticInputs (riemannXiJensenPolynomial n d) (G n d) d) :
    ∀ n d, TwoThirdsWedge K n d →
      HasDistinctNegativeRoots (riemannXiJensenPolynomial n d) d := by
  intro n d hnd
  exact (inputs n d hnd).target_hasDistinctNegativeRoots

end

end Zeta23.Research.JensenWedge
