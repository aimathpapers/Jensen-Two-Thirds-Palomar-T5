import Zeta23.Research.JensenWedge.XiNaturalTransformedPolynomial

/-!
# Six exact xi/comparison coefficient matches

The exact four quotient equations are second-difference identities.  This
module defines the actual and hypergeometric logarithmic coefficient
coordinates, proves that the quotient residual is their difference, fixes
the two initial normalizations from `S=B R₁`, and obtains all six matches
from the kernel quotient adapter.
-/

namespace Zeta23.Research.JensenWedge

open Finset Polynomial

noncomputable section

/-- Logarithm of the positive coefficient multiplier in the transformed xi
polynomial, with the common binomial coefficient omitted. -/
def xiNaturalActualLogCoordinate
    (n : ℕ) (L : ℝ) (y : BranchPoint) (j : ℕ) : ℝ :=
  Real.log (riemannXiCoefficientReal (n + j)) -
    Real.log (riemannXiCoefficientReal n) -
    (j : ℝ) * Real.log (xiNaturalJensenScale n L y)

/-- One positive-coefficient logarithmic increment of the terminating
hypergeometric comparison, again omitting the common binomial factor. -/
def xiNaturalModelLogIncrement
    (n : ℕ) (L : ℝ) (y : BranchPoint) (k : ℕ) : ℝ :=
  let A := residualParameterA y n (1 / L)
  let B := residualParameterB y n (1 / L)
  let C := residualParameterC y n
  let D := residualParameterD y n (1 / L)
  Real.log D - Real.log A - Real.log C +
    Real.log (A + k) + Real.log (C + k) -
    Real.log (B + k) - Real.log (D + k)

/-- Logarithmic comparison coordinate as the exact finite product sum. -/
def xiNaturalModelLogCoordinate
    (n : ℕ) (L : ℝ) (y : BranchPoint) (j : ℕ) : ℝ :=
  ∑ k ∈ range j, xiNaturalModelLogIncrement n L y k

theorem secondDiff_sum_range (g : ℕ → ℝ) (k : ℕ) :
    secondDiff (fun j => ∑ r ∈ range j, g r) k = g (k + 1) - g k := by
  simp only [secondDiff, sum_range_succ]
  ring

theorem secondDiff_xiNaturalActualLogCoordinate
    (n : ℕ) (L : ℝ) (y : BranchPoint) (k : ℕ) :
    secondDiff (xiNaturalActualLogCoordinate n L y) k =
      secondDiff exactXiCoefficientLog (n + k) := by
  simp only [secondDiff, xiNaturalActualLogCoordinate, exactXiCoefficientLog]
  push_cast
  ring

theorem secondDiff_xiNaturalModelLogCoordinate
    (n : ℕ) (L : ℝ) (y : BranchPoint) (k : ℕ) :
    secondDiff (xiNaturalModelLogCoordinate n L y) k =
      -exactJacobiLogQuotient y n L k := by
  rw [show xiNaturalModelLogCoordinate n L y =
      fun j => ∑ r ∈ range j, xiNaturalModelLogIncrement n L y r by rfl,
    secondDiff_sum_range]
  unfold xiNaturalModelLogIncrement exactJacobiLogQuotient logRatio
  push_cast
  ring

/-- The exact quotient residual is literally actual minus comparison second
difference. -/
theorem exactXiQuotientResidual_eq_logCoordinate_difference
    (n : ℕ) (L : ℝ) (y : BranchPoint) (k : ℕ) :
    exactXiQuotientResidual y n L k =
      secondDiff (xiNaturalActualLogCoordinate n L y) k -
        secondDiff (xiNaturalModelLogCoordinate n L y) k := by
  rw [secondDiff_xiNaturalActualLogCoordinate,
    secondDiff_xiNaturalModelLogCoordinate]
  unfold exactXiQuotientResidual
  ring

theorem xiNaturalActualLogCoordinate_zero
    (n : ℕ) (L : ℝ) (y : BranchPoint) :
    xiNaturalActualLogCoordinate n L y 0 = 0 := by
  simp [xiNaturalActualLogCoordinate]

theorem xiNaturalModelLogCoordinate_zero
    (n : ℕ) (L : ℝ) (y : BranchPoint) :
    xiNaturalModelLogCoordinate n L y 0 = 0 := by
  simp [xiNaturalModelLogCoordinate]

theorem xiNaturalModelLogCoordinate_one
    (n : ℕ) (L : ℝ) (y : BranchPoint) :
    xiNaturalModelLogCoordinate n L y 1 =
      -Real.log (xiNaturalComparisonB n L y) := by
  simp [xiNaturalModelLogCoordinate, xiNaturalModelLogIncrement,
    xiNaturalComparisonB]
  ring

/-- The four residual parameters are strictly positive throughout the paper's
outer box and logarithmic range.  This is the exact domain needed to turn the
model logarithms back into the positive hypergeometric coefficient ratios. -/
theorem xiNaturalResidualParameters_pos
    {n : ℕ} (hn : 0 < n) {L : ℝ} (hL : 0 < L)
    (hL12 : 1 / L ≤ (1 : ℝ) / 12)
    {y : BranchPoint} (hy : InOuterParameterBox y) :
    0 < residualParameterA y n (1 / L) ∧
      0 < residualParameterB y n (1 / L) ∧
      0 < residualParameterC y n ∧
      0 < residualParameterD y n (1 / L) := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have he : 0 < (1 / L : ℝ) := one_div_pos.mpr hL
  rcases residualParameters_eq_jacobiParameters hn he with
    ⟨hA, hB, hC, hD⟩
  rcases outerBox_jacobi_ordering hy (one_div_pos.mpr hnR) he hL12 with
    ⟨hAB, hBC, hCD, hDpos⟩
  rw [hA, hB, hC, hD]
  exact ⟨lt_trans hDpos (lt_trans hCD (lt_trans hBC hAB)),
    lt_trans hDpos (lt_trans hCD hBC), lt_trans hDpos hCD, hDpos⟩

/-- Exponentiating one model-log increment gives exactly the positive part of
the terminating `_3F_2` coefficient ratio. -/
theorem exp_xiNaturalModelLogIncrement
    {n : ℕ} (hn : 0 < n) {L : ℝ} (hL : 0 < L)
    (hL12 : 1 / L ≤ (1 : ℝ) / 12)
    {y : BranchPoint} (hy : InOuterParameterBox y) (k : ℕ) :
    Real.exp (xiNaturalModelLogIncrement n L y k) =
      let A := residualParameterA y n (1 / L)
      let B := residualParameterB y n (1 / L)
      let C := residualParameterC y n
      let D := residualParameterD y n (1 / L)
      D * (A + k) * (C + k) / (A * C * (B + k) * (D + k)) := by
  rcases xiNaturalResidualParameters_pos hn hL hL12 hy with
    ⟨hA, _, hC, hD⟩
  have hAk : 0 < residualParameterA y n (1 / L) + (k : ℝ) := by positivity
  have hBk : 0 < residualParameterB y n (1 / L) + (k : ℝ) := by positivity
  have hCk : 0 < residualParameterC y n + (k : ℝ) := by positivity
  have hDk : 0 < residualParameterD y n (1 / L) + (k : ℝ) := by positivity
  unfold xiNaturalModelLogIncrement
  dsimp only
  rw [show
      Real.log (residualParameterD y n (1 / L)) -
          Real.log (residualParameterA y n (1 / L)) -
          Real.log (residualParameterC y n) +
          Real.log (residualParameterA y n (1 / L) + (k : ℝ)) +
          Real.log (residualParameterC y n + (k : ℝ)) -
          Real.log (residualParameterB y n (1 / L) + (k : ℝ)) -
          Real.log (residualParameterD y n (1 / L) + (k : ℝ)) =
        ((Real.log (residualParameterD y n (1 / L)) +
            Real.log (residualParameterA y n (1 / L) + (k : ℝ))) +
            Real.log (residualParameterC y n + (k : ℝ))) -
          (((Real.log (residualParameterA y n (1 / L)) +
              Real.log (residualParameterC y n)) +
              Real.log (residualParameterB y n (1 / L) + (k : ℝ))) +
              Real.log (residualParameterD y n (1 / L) + (k : ℝ))) by ring]
  rw [Real.exp_sub]
  simp only [Real.exp_add, Real.exp_log hA, Real.exp_log hC,
    Real.exp_log hD, Real.exp_log hAk,
    Real.exp_log hBk, Real.exp_log hCk, Real.exp_log hDk]

/-- The alternating binomial factor supplies exactly the terminating
parameter `-d` in the hypergeometric coefficient recursion. -/
theorem alternatingChoose_step
    {d k : ℕ} (hk : k < d) :
    (-1 : ℝ) ^ k * (Nat.choose d k : ℝ) * ((k : ℝ) - d) / (k + 1) =
      (-1 : ℝ) ^ (k + 1) * (Nat.choose d (k + 1) : ℝ) := by
  have hchooseNat := Nat.choose_succ_right_eq d k
  have hchoose :
      (Nat.choose d (k + 1) : ℝ) * (k + 1) =
        (Nat.choose d k : ℝ) * ((d : ℝ) - k) := by
    have hchooseCast := congrArg (fun m : ℕ => (m : ℝ)) hchooseNat
    simpa only [Nat.cast_mul, Nat.cast_add, Nat.cast_one,
      Nat.cast_sub hk.le] using hchooseCast
  rw [div_eq_iff (by positivity : (k : ℝ) + 1 ≠ 0), pow_succ]
  calc
    (-1 : ℝ) ^ k * (Nat.choose d k : ℝ) * ((k : ℝ) - d) =
        (-1 : ℝ) ^ k * (-1) *
          ((Nat.choose d k : ℝ) * ((d : ℝ) - k)) := by ring
    _ = (-1 : ℝ) ^ k * (-1) *
          ((Nat.choose d (k + 1) : ℝ) * (k + 1)) := by rw [hchoose]
    _ = (-1 : ℝ) ^ k * (-1) *
          (Nat.choose d (k + 1) : ℝ) * (k + 1) := by ring

/-- Every model log-coordinate coefficient is the corresponding coefficient
of the terminating `_3F_2` polynomial. -/
theorem terminating3F2Coefficient_eq_xiNaturalModel
    {n : ℕ} (hn : 0 < n) {d : ℕ} {L : ℝ} (hL : 0 < L)
    (hL12 : 1 / L ≤ (1 : ℝ) / 12)
    {y : BranchPoint} (hy : InOuterParameterBox y) :
    ∀ j : ℕ, j ≤ d →
      terminating3F2Coefficient d
          (residualParameterA y n (1 / L))
          (residualParameterB y n (1 / L))
          (residualParameterC y n)
          (residualParameterD y n (1 / L))
          (residualParameterD y n (1 / L) /
            (residualParameterA y n (1 / L) * residualParameterC y n)) j =
        (-1 : ℝ) ^ j * (Nat.choose d j : ℝ) *
          Real.exp (xiNaturalModelLogCoordinate n L y j) := by
  intro j hjd
  induction j with
  | zero =>
      simp [terminating3F2Coefficient_zero, xiNaturalModelLogCoordinate]
  | succ k ih =>
      have hk : k < d := by omega
      rcases xiNaturalResidualParameters_pos hn hL hL12 hy with
        ⟨hA, hB, hC, hD⟩
      have hAk : 0 < residualParameterA y n (1 / L) + (k : ℝ) := by positivity
      have hBk : 0 < residualParameterB y n (1 / L) + (k : ℝ) := by positivity
      have hCk : 0 < residualParameterC y n + (k : ℝ) := by positivity
      have hDk : 0 < residualParameterD y n (1 / L) + (k : ℝ) := by positivity
      have hcoord :
          Real.exp (xiNaturalModelLogCoordinate n L y (k + 1)) =
            Real.exp (xiNaturalModelLogCoordinate n L y k) *
              Real.exp (xiNaturalModelLogIncrement n L y k) := by
        unfold xiNaturalModelLogCoordinate
        rw [sum_range_succ, Real.exp_add]
      have hstep := alternatingChoose_step hk
      rw [terminating3F2Coefficient_succ, ih (by omega), hcoord,
        exp_xiNaturalModelLogIncrement hn hL hL12 hy]
      dsimp only
      calc
        ((-1 : ℝ) ^ k * (Nat.choose d k : ℝ) *
                Real.exp (xiNaturalModelLogCoordinate n L y k)) *
              ((residualParameterD y n (1 / L) /
                    (residualParameterA y n (1 / L) *
                      residualParameterC y n)) *
                ((k : ℝ) - d) *
                (residualParameterA y n (1 / L) + k) *
                (residualParameterC y n + k)) /
                ((residualParameterB y n (1 / L) + k) *
                  (residualParameterD y n (1 / L) + k) * (k + 1)) =
            (((-1 : ℝ) ^ k * (Nat.choose d k : ℝ) *
                ((k : ℝ) - d) / (k + 1)) *
              Real.exp (xiNaturalModelLogCoordinate n L y k)) *
              (residualParameterD y n (1 / L) *
                (residualParameterA y n (1 / L) + k) *
                (residualParameterC y n + k) /
                (residualParameterA y n (1 / L) *
                  residualParameterC y n *
                  (residualParameterB y n (1 / L) + k) *
                  (residualParameterD y n (1 / L) + k))) := by
                    field_simp [hA.ne', hC.ne', hBk.ne', hDk.ne']
        _ = ((-1 : ℝ) ^ (k + 1) * (Nat.choose d (k + 1) : ℝ) *
              Real.exp (xiNaturalModelLogCoordinate n L y k)) *
              (residualParameterD y n (1 / L) *
                (residualParameterA y n (1 / L) + k) *
                (residualParameterC y n + k) /
                (residualParameterA y n (1 / L) *
                  residualParameterC y n *
                  (residualParameterB y n (1 / L) + k) *
                  (residualParameterD y n (1 / L) + k))) := by rw [hstep]
        _ = (-1 : ℝ) ^ (k + 1) * (Nat.choose d (k + 1) : ℝ) *
              (Real.exp (xiNaturalModelLogCoordinate n L y k) *
                (residualParameterD y n (1 / L) *
                  (residualParameterA y n (1 / L) + k) *
                  (residualParameterC y n + k) /
                  (residualParameterA y n (1 / L) *
                    residualParameterC y n *
                    (residualParameterB y n (1 / L) + k) *
                    (residualParameterD y n (1 / L) + k)))) := by ring

/-- The scale `S=B R₁` supplies the second normalization exactly. -/
theorem xiNaturalActualLogCoordinate_one
    {n : ℕ} (hn : 0 < n) {L : ℝ} (hL : 0 < L)
    {y : BranchPoint} (hy : InOuterParameterBox y) :
    xiNaturalActualLogCoordinate n L y 1 =
      -Real.log (xiNaturalComparisonB n L y) := by
  have hg0 := riemannXiCoefficientReal_pos n
  have hg1 := riemannXiCoefficientReal_pos (n + 1)
  have hB := xiNaturalComparisonB_pos hn hL hy
  have hratio := xiNaturalFirstCoefficientRatio_pos n
  unfold xiNaturalActualLogCoordinate xiNaturalJensenScale
    xiNaturalFirstCoefficientRatio
  norm_num
  rw [Real.log_mul hB.ne' (div_ne_zero hg1.ne' hg0.ne'),
    Real.log_div hg1.ne' hg0.ne']
  ring

/-- A zero of the exact four-coordinate map forces all six logarithmic
coefficient coordinates to match. -/
theorem xiNaturalSixLogCoordinates_match
    {n : ℕ} (hn : 0 < n) {L : ℝ} (hL : 0 < L)
    {y : BranchPoint} (hy : InOuterParameterBox y)
    (hmap : exactXiParameterMap n L y = 0) :
    ∀ j : Fin 6,
      xiNaturalActualLogCoordinate n L y j =
        xiNaturalModelLogCoordinate n L y j := by
  apply exactXiParameterMap_six_log_coefficients hn.ne' hL.ne'
  · intro k
    exact exactXiQuotientResidual_eq_logCoordinate_difference n L y k
  · rw [xiNaturalActualLogCoordinate_zero, xiNaturalModelLogCoordinate_zero]
  · rw [xiNaturalActualLogCoordinate_one hn hL hy,
      xiNaturalModelLogCoordinate_one]
  · exact hmap

theorem xiNaturalSixMultipliers_match
    {n : ℕ} (hn : 0 < n) {L : ℝ} (hL : 0 < L)
    {y : BranchPoint} (hy : InOuterParameterBox y)
    (hmap : exactXiParameterMap n L y = 0) :
    ∀ j : Fin 6,
      Real.exp (xiNaturalActualLogCoordinate n L y j) =
        Real.exp (xiNaturalModelLogCoordinate n L y j) :=
  exp_sixCoefficients_of_log_sixCoefficients _ _
    (xiNaturalSixLogCoordinates_match hn hL hy hmap)

/-- Finite polynomial carrying the exact transformed-xi logarithmic
multipliers. -/
def xiNaturalActualLogPolynomial
    (n d : ℕ) (L : ℝ) (y : BranchPoint) : ℝ[X] :=
  ∑ j ∈ range (d + 1), Polynomial.monomial j
    ((-1 : ℝ) ^ j * (Nat.choose d j : ℝ) *
      Real.exp (xiNaturalActualLogCoordinate n L y j))

/-- Finite polynomial carrying the hypergeometric-model logarithmic
multipliers. -/
def xiNaturalModelLogPolynomial
    (n d : ℕ) (L : ℝ) (y : BranchPoint) : ℝ[X] :=
  ∑ j ∈ range (d + 1), Polynomial.monomial j
    ((-1 : ℝ) ^ j * (Nat.choose d j : ℝ) *
      Real.exp (xiNaturalModelLogCoordinate n L y j))

theorem coeff_xiNaturalActualLogPolynomial
    (n d : ℕ) (L : ℝ) (y : BranchPoint) (j : ℕ) :
    (xiNaturalActualLogPolynomial n d L y).coeff j =
      if j ≤ d then
        (-1 : ℝ) ^ j * (Nat.choose d j : ℝ) *
          Real.exp (xiNaturalActualLogCoordinate n L y j)
      else 0 := by
  simp [xiNaturalActualLogPolynomial, Polynomial.coeff_monomial]

theorem coeff_xiNaturalModelLogPolynomial
    (n d : ℕ) (L : ℝ) (y : BranchPoint) (j : ℕ) :
    (xiNaturalModelLogPolynomial n d L y).coeff j =
      if j ≤ d then
        (-1 : ℝ) ^ j * (Nat.choose d j : ℝ) *
          Real.exp (xiNaturalModelLogCoordinate n L y j)
      else 0 := by
  simp [xiNaturalModelLogPolynomial, Polynomial.coeff_monomial]

/-- The log-coordinate model is not merely analogous to the terminating
hypergeometric comparison: the two finite polynomials are definitionally
connected by the kernel-checked coefficient recursion. -/
theorem xiNaturalModelLogPolynomial_eq_comparison
    {n : ℕ} (hn : 0 < n) {d : ℕ} {L : ℝ} (hL : 0 < L)
    (hL12 : 1 / L ≤ (1 : ℝ) / 12)
    {y : BranchPoint} (hy : InOuterParameterBox y) :
    xiNaturalModelLogPolynomial n d L y =
      xiNaturalComparisonPolynomial n d L y := by
  ext j
  rw [coeff_xiNaturalModelLogPolynomial]
  simp only [xiNaturalComparisonPolynomial,
    coeff_terminating3F2Polynomial]
  by_cases hjd : j ≤ d
  · rw [if_pos hjd, if_pos hjd]
    exact (terminating3F2Coefficient_eq_xiNaturalModel
      hn hL hL12 hy j hjd).symm
  · rw [if_neg hjd, if_neg hjd]

theorem eval_xiNaturalModelLogPolynomial
    {n : ℕ} (hn : 0 < n) {d : ℕ} {L : ℝ} (hL : 0 < L)
    (hL12 : 1 / L ≤ (1 : ℝ) / 12)
    {y : BranchPoint} (hy : InOuterParameterBox y) (X : ℝ) :
    Polynomial.eval X (xiNaturalModelLogPolynomial n d L y) =
      xiNaturalComparisonFunction n d L y X := by
  rw [xiNaturalModelLogPolynomial_eq_comparison hn hL hL12 hy]
  rfl

theorem exp_xiNaturalActualLogCoordinate
    {n : ℕ} {d : ℕ} {L : ℝ} {y : BranchPoint}
    (hscale : 0 < xiNaturalJensenScale n L y) :
    Real.exp (xiNaturalActualLogCoordinate n L y d) =
      riemannXiCoefficientReal (n + d) / riemannXiCoefficientReal n /
        xiNaturalJensenScale n L y ^ d := by
  have hgd := riemannXiCoefficientReal_pos (n + d)
  have hg0 := riemannXiCoefficientReal_pos n
  unfold xiNaturalActualLogCoordinate
  rw [Real.exp_sub, Real.exp_sub, Real.exp_log hgd, Real.exp_log hg0,
    Real.exp_nat_mul, Real.exp_log hscale]

/-- Evaluation of the log-coordinate polynomial is exactly the normalized
transformed Riemann-xi Jensen polynomial. -/
theorem eval_xiNaturalActualLogPolynomial
    {n : ℕ} (hn : 0 < n) (d : ℕ) {L : ℝ} (hL : 0 < L)
    {y : BranchPoint} (hy : InOuterParameterBox y) (X : ℝ) :
    Polynomial.eval X (xiNaturalActualLogPolynomial n d L y) =
      xiNaturalTransformedPolynomial n d L y X := by
  have hscale := xiNaturalJensenScale_pos hn hL hy
  have hg0 := riemannXiCoefficientReal_pos n
  unfold xiNaturalActualLogPolynomial xiNaturalTransformedPolynomial
    riemannXiJensenPolynomial jensenPolynomial
  simp only [Polynomial.eval_finsetSum, Polynomial.eval_monomial]
  rw [Finset.sum_div]
  apply Finset.sum_congr rfl
  intro j hj
  rw [exp_xiNaturalActualLogCoordinate hscale]
  rw [div_pow, neg_pow]
  field_simp [hg0.ne', hscale.ne']
  ring

/-- The exact branch equation matches polynomial coefficients zero through
five, including their alternating signs and binomial factors. -/
theorem xiNaturalSixPolynomialCoefficients_match
    {n : ℕ} (hn : 0 < n) {d : ℕ} {L : ℝ} (hL : 0 < L)
    {y : BranchPoint} (hy : InOuterParameterBox y)
    (hmap : exactXiParameterMap n L y = 0)
    (j : Fin 6) (hjd : (j : ℕ) ≤ d) :
    (xiNaturalActualLogPolynomial n d L y).coeff j =
      (xiNaturalModelLogPolynomial n d L y).coeff j := by
  rw [coeff_xiNaturalActualLogPolynomial, if_pos hjd,
    coeff_xiNaturalModelLogPolynomial, if_pos hjd,
    xiNaturalSixMultipliers_match hn hL hy hmap j]

/-- The exact branch equation identifies the first six coefficients of the
actual transformed xi polynomial directly with the published terminating
`_3F_2` comparison polynomial. -/
theorem xiNaturalSixPolynomialCoefficients_match_comparison
    {n : ℕ} (hn : 0 < n) {d : ℕ} {L : ℝ} (hL : 0 < L)
    (hL12 : 1 / L ≤ (1 : ℝ) / 12)
    {y : BranchPoint} (hy : InOuterParameterBox y)
    (hmap : exactXiParameterMap n L y = 0)
    (j : Fin 6) (hjd : (j : ℕ) ≤ d) :
    (xiNaturalActualLogPolynomial n d L y).coeff j =
      (xiNaturalComparisonPolynomial n d L y).coeff j := by
  rw [← xiNaturalModelLogPolynomial_eq_comparison hn hL hL12 hy]
  exact xiNaturalSixPolynomialCoefficients_match hn hL hy hmap j hjd

/-- For degrees at most five, the six exact matches identify the complete
finite polynomials. -/
theorem xiNaturalLogPolynomials_eq_of_degree_le_five
    {n : ℕ} (hn : 0 < n) {d : ℕ} (hd : d ≤ 5)
    {L : ℝ} (hL : 0 < L) {y : BranchPoint} (hy : InOuterParameterBox y)
    (hmap : exactXiParameterMap n L y = 0) :
    xiNaturalActualLogPolynomial n d L y =
      xiNaturalModelLogPolynomial n d L y := by
  ext j
  by_cases hjd : j ≤ d
  · let j6 : Fin 6 := ⟨j, by omega⟩
    exact xiNaturalSixPolynomialCoefficients_match hn hL hy hmap j6 hjd
  · rw [coeff_xiNaturalActualLogPolynomial, if_neg hjd,
      coeff_xiNaturalModelLogPolynomial, if_neg hjd]

/-- Explicit-cutoff specialization using the kernel-produced positive branch.
-/
theorem xiNaturalSixLogCoordinates_match_of_explicitCutoff
    {n : ℕ} (hn : xiNaturalExplicitCutoffIndex ≤ n) :
    ∀ j : Fin 6,
      xiNaturalActualLogCoordinate n (xiNaturalSaddleScale n)
          (exactXiPositiveParameterBranch_of_explicitCutoff hn).parameters j =
        xiNaturalModelLogCoordinate n (xiNaturalSaddleScale n)
          (exactXiPositiveParameterBranch_of_explicitCutoff hn).parameters j := by
  let B := exactXiPositiveParameterBranch_of_explicitCutoff hn
  let C := xiNaturalSaddleIntervalConditions_of_explicitCutoff hn
  exact xiNaturalSixLogCoordinates_match C.n_pos C.saddleScale_pos
    B.in_outer_box B.equation

theorem explicitCutoff_inverse_xiNaturalSaddleScale_le_twelve
    {n : ℕ} (hn : xiNaturalExplicitCutoffIndex ≤ n) :
    1 / xiNaturalSaddleScale n ≤ (1 : ℝ) / 12 := by
  exact (explicitCutoff_xiNatural_branch_scales hn).1.trans (by norm_num)

theorem xiNaturalModelLogPolynomial_eq_comparison_of_explicitCutoff
    {n : ℕ} (hn : xiNaturalExplicitCutoffIndex ≤ n) (d : ℕ) :
    xiNaturalModelLogPolynomial n d (xiNaturalSaddleScale n)
        (exactXiPositiveParameterBranch_of_explicitCutoff hn).parameters =
      xiNaturalComparisonPolynomial n d (xiNaturalSaddleScale n)
        (exactXiPositiveParameterBranch_of_explicitCutoff hn).parameters := by
  let B := exactXiPositiveParameterBranch_of_explicitCutoff hn
  let C := xiNaturalSaddleIntervalConditions_of_explicitCutoff hn
  exact xiNaturalModelLogPolynomial_eq_comparison C.n_pos C.saddleScale_pos
    (explicitCutoff_inverse_xiNaturalSaddleScale_le_twelve hn) B.in_outer_box

theorem xiNaturalSixPolynomialCoefficients_match_comparison_of_explicitCutoff
    {n : ℕ} (hn : xiNaturalExplicitCutoffIndex ≤ n) {d : ℕ}
    (j : Fin 6) (hjd : (j : ℕ) ≤ d) :
    (xiNaturalActualLogPolynomial n d (xiNaturalSaddleScale n)
        (exactXiPositiveParameterBranch_of_explicitCutoff hn).parameters).coeff j =
      (xiNaturalComparisonPolynomial n d (xiNaturalSaddleScale n)
        (exactXiPositiveParameterBranch_of_explicitCutoff hn).parameters).coeff j := by
  let B := exactXiPositiveParameterBranch_of_explicitCutoff hn
  let C := xiNaturalSaddleIntervalConditions_of_explicitCutoff hn
  exact xiNaturalSixPolynomialCoefficients_match_comparison
    C.n_pos C.saddleScale_pos
    (explicitCutoff_inverse_xiNaturalSaddleScale_le_twelve hn)
    B.in_outer_box B.equation j hjd

end

end Zeta23.Research.JensenWedge
