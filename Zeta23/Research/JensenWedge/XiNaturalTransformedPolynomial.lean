import Zeta23.Research.JensenWedge.XiNaturalExplicitBranch
import Zeta23.Research.JensenWedge.XiCoefficientPositivity
import Zeta23.Research.JensenWedge.TerminatingHypergeometric

/-!
# Exact transformed xi Jensen polynomial and comparison model

This module fixes the normalization used in the final sign-transfer argument.
The transformed polynomial is defined literally from the Riemann-xi Jensen
polynomial, so its identification, continuity, positive scale, and nonzero
normalization are kernel consequences rather than fields supplied by a final
certificate.  The terminating hypergeometric comparison polynomial is fixed
from the same branch parameters.
-/

namespace Zeta23.Research.JensenWedge

open Finset Polynomial

noncomputable section

/-- Positive first coefficient ratio at the Jensen base point. -/
def xiNaturalFirstCoefficientRatio (n : ℕ) : ℝ :=
  riemannXiCoefficientReal (n + 1) / riemannXiCoefficientReal n

theorem xiNaturalFirstCoefficientRatio_pos (n : ℕ) :
    0 < xiNaturalFirstCoefficientRatio n := by
  exact div_pos (riemannXiCoefficientReal_pos (n + 1))
    (riemannXiCoefficientReal_pos n)

/-- The second Jacobi parameter in the natural branch normalization. -/
def xiNaturalComparisonB (n : ℕ) (L : ℝ) (y : BranchPoint) : ℝ :=
  residualParameterB y n (1 / L)

theorem xiNaturalComparisonB_pos
    {n : ℕ} (hn : 0 < n) {L : ℝ} (hL : 0 < L)
    {y : BranchPoint} (hy : InOuterParameterBox y) :
    0 < xiNaturalComparisonB n L y := by
  rcases hy with ⟨_, _, ht, _, hw, _, _, _⟩
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have he : 0 < (1 / L : ℝ) := one_div_pos.mpr hL
  have hsum : 0 < y 1 + y 2 * (1 / L) := by
    have hwy : 0 < y 2 := lt_of_lt_of_le (by norm_num) hw
    nlinarith [mul_pos hwy he]
  unfold xiNaturalComparisonB residualParameterB
  exact mul_pos hnR hsum

/-- Positive change-of-variable scale `S=B R_1`. -/
def xiNaturalJensenScale (n : ℕ) (L : ℝ) (y : BranchPoint) : ℝ :=
  xiNaturalComparisonB n L y * xiNaturalFirstCoefficientRatio n

theorem xiNaturalJensenScale_pos
    {n : ℕ} (hn : 0 < n) {L : ℝ} (hL : 0 < L)
    {y : BranchPoint} (hy : InOuterParameterBox y) :
    0 < xiNaturalJensenScale n L y :=
  mul_pos (xiNaturalComparisonB_pos hn hL hy)
    (xiNaturalFirstCoefficientRatio_pos n)

/-- The actual xi multiplier polynomial after the paper's positive-to-negative
change of variables and coefficient normalization. -/
def xiNaturalTransformedPolynomial
    (n d : ℕ) (L : ℝ) (y : BranchPoint) (X : ℝ) : ℝ :=
  riemannXiJensenPolynomial n d
      (-X / xiNaturalJensenScale n L y) /
    riemannXiCoefficientReal n

theorem continuous_xiNaturalTransformedPolynomial
    (n d : ℕ) (L : ℝ) (y : BranchPoint) :
    Continuous (xiNaturalTransformedPolynomial n d L y) := by
  unfold xiNaturalTransformedPolynomial riemannXiJensenPolynomial jensenPolynomial
  fun_prop

/-- The complete `XiCoefficientEstimate` record is produced without an
analytic assumption: it is the defining normalization of the transformed
polynomial. -/
def xiNaturalCoefficientEstimate
    {n d : ℕ} (hn : 0 < n) {L : ℝ} (hL : 0 < L)
    {y : BranchPoint} (hy : InOuterParameterBox y) :
    XiCoefficientEstimate (riemannXiJensenPolynomial n d)
      (xiNaturalTransformedPolynomial n d L y) where
  transformed_continuous := continuous_xiNaturalTransformedPolynomial n d L y
  scale := xiNaturalJensenScale n L y
  normalization := riemannXiCoefficientReal n
  scale_pos := xiNaturalJensenScale_pos hn hL hy
  normalization_ne_zero := (riemannXiCoefficientReal_pos n).ne'
  identify := by intro X; rfl

/-- The terminating hypergeometric comparison fixed by the exact positive
branch. -/
def xiNaturalComparisonPolynomial
    (n d : ℕ) (L : ℝ) (y : BranchPoint) : ℝ[X] :=
  let A := residualParameterA y n (1 / L)
  let B := residualParameterB y n (1 / L)
  let C := residualParameterC y n
  let D := residualParameterD y n (1 / L)
  terminating3F2Polynomial d A B C D (D / (A * C))

/-- Evaluation form consumed by the final sign-transfer structures. -/
def xiNaturalComparisonFunction
    (n d : ℕ) (L : ℝ) (y : BranchPoint) (X : ℝ) : ℝ :=
  Polynomial.eval X (xiNaturalComparisonPolynomial n d L y)

theorem continuous_xiNaturalComparisonFunction
    (n d : ℕ) (L : ℝ) (y : BranchPoint) :
    Continuous (xiNaturalComparisonFunction n d L y) := by
  exact (xiNaturalComparisonPolynomial n d L y).continuous

end

end Zeta23.Research.JensenWedge
