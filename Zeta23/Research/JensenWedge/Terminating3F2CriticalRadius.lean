import Zeta23.Research.JensenWedge.CriticalRadiusRecurrence
import Zeta23.Research.JensenWedge.TerminatingHypergeometric

/-!
# Genuine terminating hypergeometric critical-radius adapter

This module connects the finite `_3F_2` coefficient producer and shifted
Euler ODE to the complete critical-radius maximum theorem. It proves the
four-term recurrence for the actual normalized derivative ratios, rather
than for an unrelated abstract sequence. Only the displayed coefficient
inequalities remain to be instantiated by the xi parameter geometry.
-/

namespace Zeta23.Research.JensenWedge

open Polynomial

noncomputable section

/-- The derivative ratio used literally in the paper's critical-radius
estimate, including the factor `y^k` and excluding `1/k!`. -/
def polynomialDerivativeRatio (p : ℝ[X]) (y : ℝ) (k : ℕ) : ℝ :=
  polynomialEulerJet p y k / p.eval y

/-- Exact conversion of the shifted terminating polynomial back to the
derivative jet of the original polynomial. -/
theorem polynomialEulerJet_derivative_shift
    {d m r : ℕ} {A B C D lambda y : ℝ}
    (hmd : m ≤ d)
    (hB : ∀ k ≤ d, B + k ≠ 0)
    (hD : ∀ k ≤ d, D + k ≠ 0) :
    let p := terminating3F2Polynomial d A B C D lambda
    let shifted := terminating3F2Polynomial (d - m) (A + m) (B + m)
      (C + m) (D + m) lambda
    polynomialEulerJet p y (m + r) =
      y ^ m * terminating3F2DerivativePrefactor d m A B C D lambda *
        polynomialEulerJet shifted y r := by
  dsimp
  have hshift := iterate_derivative_terminating3F2Polynomial
    (d := d) (m := m) (A := A) (B := B) (C := C) (D := D)
    (lambda := lambda) hmd hB hD
  unfold polynomialEulerJet
  rw [show m + r = r + m by omega, Function.iterate_add_apply, hshift,
    Polynomial.iterate_derivative_C_mul, Polynomial.eval_mul,
    Polynomial.eval_C]
  ring

/-- The shifted Euler ODE produces the paper's genuine four-term recurrence
for normalized derivative ratios at every legal index. -/
theorem terminating3F2_polynomialDerivativeRatio_fourTerm
    {d m : ℕ} {A B C D y : ℝ}
    (hmd : m + 2 ≤ d) (hA : A ≠ 0) (hC : C ≠ 0)
    (hB : ∀ k ≤ d, B + k ≠ 0)
    (hD : ∀ k ≤ d, D + k ≠ 0) :
    let p := terminating3F2Polynomial d A B C D (D / (A * C))
    recurrenceP3 A C D y * polynomialDerivativeRatio p y (m + 3) +
      recurrenceP2 A B C D y d m * polynomialDerivativeRatio p y (m + 2) +
      recurrenceP1 A B C D y d m * polynomialDerivativeRatio p y (m + 1) +
      recurrenceP0 A C D y d m * polynomialDerivativeRatio p y m = 0 := by
  dsimp
  have hmd' : m ≤ d := by omega
  have hBshift : ∀ k ≤ d - m, B + (m : ℝ) + k ≠ 0 := by
    intro k hk
    have hmk : m + k ≤ d := by omega
    simpa [Nat.cast_add, add_assoc] using hB (m + k) hmk
  have hDshift : ∀ k ≤ d - m, D + (m : ℝ) + k ≠ 0 := by
    intro k hk
    have hmk : m + k ≤ d := by omega
    simpa [Nat.cast_add, add_assoc] using hD (m + k) hmk
  have hrec := terminating3F2_shifted_fourTerm_recurrence
    (d := d) (m := m) (A := A) (B := B) (C := C) (D := D)
    (lambda := D / (A * C)) (y := y) hmd' hBshift hDshift
  rcases hypergeometricOdeCoefficients_match_directRecurrence
      (A := A) (B := B) (C := C) (D := D) (y := y)
      (d := d) (m := m) hA hC with ⟨h3, h2, h1, h0⟩
  rw [h3, h2, h1, h0] at hrec
  let p := terminating3F2Polynomial d A B C D (D / (A * C))
  let shifted := terminating3F2Polynomial (d - m) (A + m) (B + m)
    (C + m) (D + m) (D / (A * C))
  let pref := terminating3F2DerivativePrefactor d m A B C D (D / (A * C))
  have hratio (r : ℕ) :
      polynomialDerivativeRatio p y (m + r) =
        (y ^ m * pref / p.eval y) * polynomialEulerJet shifted y r := by
    unfold polynomialDerivativeRatio
    rw [polynomialEulerJet_derivative_shift hmd' hB hD]
    dsimp [p, pref, shifted]
    ring
  have hratio0 : polynomialDerivativeRatio p y m =
      (y ^ m * pref / p.eval y) * polynomialEulerJet shifted y 0 := by
    simpa using hratio 0
  rw [hratio 3, hratio 2, hratio 1, hratio0]
  dsimp [shifted] at hrec
  linear_combination (y ^ m * pref / p.eval y) * hrec

theorem terminating3F2Polynomial_natDegree_le
    (d : ℕ) (A B C D lambda : ℝ) :
    (terminating3F2Polynomial d A B C D lambda).natDegree ≤ d := by
  rw [Polynomial.natDegree_le_iff_coeff_eq_zero]
  intro k hdk
  rw [coeff_terminating3F2Polynomial, if_neg (by omega)]

theorem polynomialDerivativeRatio_zero
    {p : ℝ[X]} {y : ℝ} (hp : p.eval y ≠ 0) :
    polynomialDerivativeRatio p y 0 = 1 := by
  simp [polynomialDerivativeRatio, polynomialEulerJet, hp]

theorem polynomialDerivativeRatio_one_of_critical
    {p : ℝ[X]} {y : ℝ} (hcritical : p.derivative.eval y = 0) :
    polynomialDerivativeRatio p y 1 = 0 := by
  simp [polynomialDerivativeRatio, polynomialEulerJet, hcritical]

theorem polynomialDerivativeRatio_succ_degree_eq_zero
    {p : ℝ[X]} {y : ℝ} {d : ℕ} (hdegree : p.natDegree ≤ d) :
    polynomialDerivativeRatio p y (d + 1) = 0 := by
  have hderivative : Polynomial.derivative^[d + 1] p = 0 :=
    Polynomial.iterate_derivative_eq_zero (by omega)
  simp [polynomialDerivativeRatio, polynomialEulerJet, hderivative]

/-- The genuine terminating polynomial and its ODE instantiate every
algebraic field of the critical-radius certificate. Only the displayed
coefficient inequalities remain hypotheses. -/
noncomputable def terminating3F2CriticalRadiusCertificate
    {d : ℕ} {A B C D y R q : ℝ}
    (hp : (terminating3F2Polynomial d A B C D (D / (A * C))).eval y ≠ 0)
    (hcritical : (terminating3F2Polynomial d A B C D
      (D / (A * C))).derivative.eval y = 0)
    (hA : A ≠ 0) (hC : C ≠ 0)
    (hB : ∀ k ≤ d, B + k ≠ 0)
    (hD : ∀ k ≤ d, D + k ≠ 0)
    (hR : 0 < R) (hq0 : 0 ≤ q) (hq1 : q < 1)
    (hcenter : ∀ m : ℕ, m + 2 ≤ d →
      0 < recurrenceP2 A B C D y d m)
    (hcontract : ∀ m : ℕ, m + 2 ≤ d →
      |recurrenceP3 A C D y| * R ^ 3 +
          |recurrenceP1 A B C D y d m| * R +
          |recurrenceP0 A C D y d m| ≤
        q * recurrenceP2 A B C D y d m * R ^ 2) :
    FourTermCriticalRadiusCertificate
      (polynomialDerivativeRatio
        (terminating3F2Polynomial d A B C D (D / (A * C))) y)
      d R q where
  P3 := fun _ => recurrenceP3 A C D y
  P2 := fun m => recurrenceP2 A B C D y d m
  P1 := fun m => recurrenceP1 A B C D y d m
  P0 := fun m => recurrenceP0 A C D y d m
  radius_pos := hR
  contraction_nonneg := hq0
  contraction_lt_one := hq1
  zero_jet := by rw [polynomialDerivativeRatio_zero hp]; norm_num
  one_jet := by
    rw [polynomialDerivativeRatio_one_of_critical hcritical]
    simpa using hR.le
  terminal := polynomialDerivativeRatio_succ_degree_eq_zero
    (terminating3F2Polynomial_natDegree_le d A B C D (D / (A * C)))
  center_pos := hcenter
  recurrence := fun m hm =>
    terminating3F2_polynomialDerivativeRatio_fourTerm hm hA hC hB hD
  coefficient_contraction := hcontract

theorem terminating3F2_critical_radius
    {d : ℕ} {A B C D y R q : ℝ}
    (hp : (terminating3F2Polynomial d A B C D (D / (A * C))).eval y ≠ 0)
    (hcritical : (terminating3F2Polynomial d A B C D
      (D / (A * C))).derivative.eval y = 0)
    (hA : A ≠ 0) (hC : C ≠ 0)
    (hB : ∀ k ≤ d, B + k ≠ 0)
    (hD : ∀ k ≤ d, D + k ≠ 0)
    (hR : 0 < R) (hq0 : 0 ≤ q) (hq1 : q < 1)
    (hcenter : ∀ m : ℕ, m + 2 ≤ d →
      0 < recurrenceP2 A B C D y d m)
    (hcontract : ∀ m : ℕ, m + 2 ≤ d →
      |recurrenceP3 A C D y| * R ^ 3 +
          |recurrenceP1 A B C D y d m| * R +
          |recurrenceP0 A C D y d m| ≤
        q * recurrenceP2 A B C D y d m * R ^ 2) :
    ∀ k ≤ d,
      |polynomialDerivativeRatio
        (terminating3F2Polynomial d A B C D (D / (A * C))) y k| ≤ R ^ k :=
  (terminating3F2CriticalRadiusCertificate hp hcritical hA hC hB hD
    hR hq0 hq1 hcenter hcontract).derivative_radius

end

end Zeta23.Research.JensenWedge
