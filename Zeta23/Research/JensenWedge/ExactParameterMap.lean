import Zeta23.Research.JensenWedge.RiemannXiJensen
import Zeta23.Research.JensenWedge.ResidualParameterGeometry
import Zeta23.Research.JensenWedge.ElementaryMap
import Zeta23.Research.JensenWedge.QuotientAdapter

/-!
# The exact xi/Jacobi parameter map

This module defines the four-parameter residual map used by the manuscript.
It contains the true Riemann-xi coefficient logarithms and the exact four
Jacobi logarithmic quotients; no truncated expansion or limiting surrogate is
substituted.  The differently scaled triangular coordinates are then proved
to vanish exactly when all four quotient residuals vanish.

Positivity of the xi coefficients and the uniform `C^1` estimates are kept as
separate downstream obligations.  `Real.log` therefore belongs to the exact
definition here, while later coefficient-identification theorems must supply
the positivity hypotheses needed to invert it.
-/

namespace Zeta23.Research.JensenWedge

noncomputable section

/-- The exact real logarithm of the manuscript's Riemann-xi coefficient. -/
def exactXiCoefficientLog (m : ℕ) : ℝ :=
  Real.log (riemannXiCoefficientReal m)

/-- The exact half-shift term in the xi quotient coordinate. -/
def exactXiHalfShiftLog (n k : ℕ) : ℝ :=
  Real.log (1 + 1 / (((n + k : ℕ) : ℝ) + 1 / 2))

/-- The exact Jacobi-side logarithmic quotient at offset `k`.  The branch
scale is `e = 1/L`, exactly as in the manuscript. -/
def exactJacobiLogQuotient
    (y : BranchPoint) (n : ℕ) (L : ℝ) (k : ℕ) : ℝ :=
  logRatio (residualParameterA y n (1 / L)) k -
    logRatio (residualParameterB y n (1 / L)) k +
    logRatio (residualParameterC y n) k -
    logRatio (residualParameterD y n (1 / L)) k

/-- The true xi/model quotient residual `E_{n,k}=M_{n,k}-Q_{n,k}`.
Since `Q_{n,k} = -Delta^2 log gamma(n+k)`, this is the Jacobi
log quotient plus the exact coefficient second difference.  The half-shift
appears only after the exact Gamma duplication bridge rewrites this
coefficient difference as an auxiliary-moment difference. -/
def exactXiQuotientResidual
    (y : BranchPoint) (n : ℕ) (L : ℝ) (k : ℕ) : ℝ :=
  exactJacobiLogQuotient y n L k +
    secondDiff exactXiCoefficientLog (n + k)

/-- Zeroth through third forward differences for a naturally indexed
sequence. -/
def natForwardDiff0 (f : ℕ → ℝ) : ℝ := f 0
def natForwardDiff1 (f : ℕ → ℝ) : ℝ := f 1 - f 0
def natForwardDiff2 (f : ℕ → ℝ) : ℝ := f 2 - 2 * f 1 + f 0
def natForwardDiff3 (f : ℕ → ℝ) : ℝ := f 3 - 3 * f 2 + 3 * f 1 - f 0

theorem natForwardDiffs_zero_iff_values_zero (f : ℕ → ℝ) :
    (natForwardDiff0 f = 0 ∧ natForwardDiff1 f = 0 ∧
      natForwardDiff2 f = 0 ∧ natForwardDiff3 f = 0) ↔
    (f 0 = 0 ∧ f 1 = 0 ∧ f 2 = 0 ∧ f 3 = 0) := by
  simp only [natForwardDiff0, natForwardDiff1, natForwardDiff2, natForwardDiff3]
  constructor <;> rintro ⟨h0, h1, h2, h3⟩
  · exact ⟨h0, by linarith, by linarith, by linarith⟩
  · exact ⟨h0, by linarith, by linarith, by linarith⟩

/-- The four exact normalized residual coordinates in the fixed order
`(alpha,t,w,delta)`. -/
def exactXiParameterMap (n : ℕ) (L : ℝ) (y : BranchPoint) : BranchPoint := ![
  -((n : ℝ) * L) * natForwardDiff0 (exactXiQuotientResidual y n L),
  ((n : ℝ) ^ 2 * L / 2) * natForwardDiff1 (exactXiQuotientResidual y n L),
  -((n : ℝ) ^ 3 * L / 2) * natForwardDiff2 (exactXiQuotientResidual y n L),
  ((n : ℝ) ^ 4 * L / 6) * natForwardDiff3 (exactXiQuotientResidual y n L)
]

/-- Nonzero integer and saddle scales make the triangular normalization
faithful: no quotient equation is lost by scaling. -/
theorem exactXiParameterMap_eq_zero_iff_forwardDiffs
    {n : ℕ} {L : ℝ} {y : BranchPoint}
    (hn : n ≠ 0) (hL : L ≠ 0) :
    exactXiParameterMap n L y = 0 ↔
      natForwardDiff0 (exactXiQuotientResidual y n L) = 0 ∧
      natForwardDiff1 (exactXiQuotientResidual y n L) = 0 ∧
      natForwardDiff2 (exactXiQuotientResidual y n L) = 0 ∧
      natForwardDiff3 (exactXiQuotientResidual y n L) = 0 := by
  have hnR : (n : ℝ) ≠ 0 := by exact_mod_cast hn
  constructor
  · intro h
    have h0 := congrFun h 0
    have h1 := congrFun h 1
    have h2 := congrFun h 2
    have h3 := congrFun h 3
    simp only [exactXiParameterMap, Matrix.cons_val_zero, Pi.zero_apply] at h0
    simp only [exactXiParameterMap, Matrix.cons_val_one, Pi.zero_apply] at h1
    simp only [exactXiParameterMap, Matrix.cons_val_two, Pi.zero_apply] at h2
    simp only [exactXiParameterMap, Matrix.cons_val_three, Pi.zero_apply] at h3
    constructor
    · apply (mul_eq_zero.mp h0).resolve_left
      exact neg_ne_zero.mpr (mul_ne_zero hnR hL)
    constructor
    · apply (mul_eq_zero.mp h1).resolve_left
      exact div_ne_zero (mul_ne_zero (pow_ne_zero 2 hnR) hL) (by norm_num)
    constructor
    · apply (mul_eq_zero.mp h2).resolve_left
      exact neg_ne_zero.mpr
        (div_ne_zero (mul_ne_zero (pow_ne_zero 3 hnR) hL) (by norm_num))
    · apply (mul_eq_zero.mp h3).resolve_left
      exact div_ne_zero (mul_ne_zero (pow_ne_zero 4 hnR) hL) (by norm_num)
  · rintro ⟨h0, h1, h2, h3⟩
    ext i
    fin_cases i <;> simp [exactXiParameterMap, h0, h1, h2, h3]

/-- The exact normalized map vanishes precisely when the four original
quotient residual values vanish. -/
theorem exactXiParameterMap_eq_zero_iff_values
    {n : ℕ} {L : ℝ} {y : BranchPoint}
    (hn : n ≠ 0) (hL : L ≠ 0) :
    exactXiParameterMap n L y = 0 ↔
      exactXiQuotientResidual y n L 0 = 0 ∧
      exactXiQuotientResidual y n L 1 = 0 ∧
      exactXiQuotientResidual y n L 2 = 0 ∧
      exactXiQuotientResidual y n L 3 = 0 := by
  rw [exactXiParameterMap_eq_zero_iff_forwardDiffs hn hL]
  exact natForwardDiffs_zero_iff_values_zero (exactXiQuotientResidual y n L)

/-- Finite-index form of the same exact quotient hinge. -/
theorem exactXiParameterMap_eq_zero_iff_fin
    {n : ℕ} {L : ℝ} {y : BranchPoint}
    (hn : n ≠ 0) (hL : L ≠ 0) :
    exactXiParameterMap n L y = 0 ↔
      ∀ k : Fin 4, exactXiQuotientResidual y n L k = 0 := by
  rw [exactXiParameterMap_eq_zero_iff_values hn hL]
  constructor
  · rintro ⟨h0, h1, h2, h3⟩ k
    fin_cases k <;> assumption
  · intro h
    exact ⟨h 0, h 1, h 2, h 3⟩

/-- If the exact quotient residual is identified with the difference of two
second-difference sequences, the concrete parameter equation plus two
normalizations recovers all six logarithmic coefficient coordinates. -/
theorem exactXiParameterMap_six_log_coefficients
    {n : ℕ} {L : ℝ} {y : BranchPoint}
    (hn : n ≠ 0) (hL : L ≠ 0)
    (a b : ℕ → ℝ)
    (hresidual : ∀ k : Fin 4,
      exactXiQuotientResidual y n L k = secondDiff a k - secondDiff b k)
    (h0 : a 0 = b 0) (h1 : a 1 = b 1)
    (hmap : exactXiParameterMap n L y = 0) :
    ∀ j : Fin 6, a j = b j := by
  apply fourQuotients_twoNormalizations_sixCoefficients a b h0 h1
  intro k hk
  have hk4 : k < 4 := Nat.lt_succ_iff.mpr hk
  let k4 : Fin 4 := ⟨k, hk4⟩
  have hz := (exactXiParameterMap_eq_zero_iff_fin hn hL).mp hmap k4
  have hr := hresidual k4
  change exactXiQuotientResidual y n L k = 0 at hz
  change exactXiQuotientResidual y n L k =
    secondDiff a k - secondDiff b k at hr
  linarith

end

end Zeta23.Research.JensenWedge
