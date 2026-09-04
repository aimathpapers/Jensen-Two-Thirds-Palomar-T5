import Zeta23.Research.JensenWedge.DirectRecurrence

/-!
# Terminating hypergeometric recurrence from the finite polynomial

This module defines the consumed terminating `_3F_2` as an exact finite
polynomial and derives its Euler-operator differential equation from the
coefficient recursion.  External symbolic systems are not premises.
-/

namespace Zeta23.Research.JensenWedge

open Polynomial

/-- Exact coefficients of
`_3F_2(-d,A,C;B,D;lambda*y)`, defined by their finite product recursion. -/
noncomputable def terminating3F2Coefficient
    (d : ℕ) (A B C D lambda : ℝ) : ℕ → ℝ
  | 0 => 1
  | k + 1 =>
      terminating3F2Coefficient d A B C D lambda k *
        (lambda * ((k : ℝ) - d) * (A + k) * (C + k)) /
          ((B + k) * (D + k) * (k + 1))

/-- The genuine finite terminating polynomial. -/
noncomputable def terminating3F2Polynomial
    (d : ℕ) (A B C D lambda : ℝ) : ℝ[X] :=
  ∑ k ∈ Finset.range (d + 1),
    Polynomial.monomial k (terminating3F2Coefficient d A B C D lambda k)

theorem terminating3F2Coefficient_zero
    (d : ℕ) (A B C D lambda : ℝ) :
    terminating3F2Coefficient d A B C D lambda 0 = 1 := by
  rfl

theorem terminating3F2Coefficient_succ
    (d k : ℕ) (A B C D lambda : ℝ) :
    terminating3F2Coefficient d A B C D lambda (k + 1) =
      terminating3F2Coefficient d A B C D lambda k *
        (lambda * ((k : ℝ) - d) * (A + k) * (C + k)) /
          ((B + k) * (D + k) * (k + 1)) := by
  rfl

/-- Cross-multiplied coefficient ratio.  The nonzero assumptions are exactly
the denominator conditions required by the cancellation. -/
theorem terminating3F2Coefficient_ratio_cross
    {d k : ℕ} {A B C D lambda : ℝ}
    (hB : B + k ≠ 0) (hD : D + k ≠ 0) :
    terminating3F2Coefficient d A B C D lambda (k + 1) *
        ((B + k) * (D + k) * (k + 1)) =
      terminating3F2Coefficient d A B C D lambda k *
        (lambda * ((k : ℝ) - d) * (A + k) * (C + k)) := by
  rw [terminating3F2Coefficient_succ]
  field_simp [hB, hD]

theorem terminating3F2Coefficient_succ_degree
    (d : ℕ) (A B C D lambda : ℝ) :
    terminating3F2Coefficient d A B C D lambda (d + 1) = 0 := by
  rw [terminating3F2Coefficient_succ]
  simp

theorem terminating3F2Coefficient_eq_zero_of_degree_lt
    {d k : ℕ} (hdk : d < k) (A B C D lambda : ℝ) :
    terminating3F2Coefficient d A B C D lambda k = 0 := by
  obtain ⟨r, rfl⟩ := Nat.exists_eq_add_of_le (Nat.succ_le_iff.mp hdk)
  induction r with
  | zero => exact terminating3F2Coefficient_succ_degree d A B C D lambda
  | succ r ih =>
      rw [show d + 1 + (r + 1) = (d + 1 + r) + 1 by omega,
        terminating3F2Coefficient_succ, ih (by omega), zero_mul, zero_div]

theorem coeff_terminating3F2Polynomial
    (d k : ℕ) (A B C D lambda : ℝ) :
    (terminating3F2Polynomial d A B C D lambda).coeff k =
      if k ≤ d then terminating3F2Coefficient d A B C D lambda k else 0 := by
  simp [terminating3F2Polynomial, coeff_monomial]

theorem monic_constant_terminating3F2Polynomial
    (d : ℕ) (A B C D lambda : ℝ) :
    (terminating3F2Polynomial d A B C D lambda).coeff 0 = 1 := by
  rw [coeff_terminating3F2Polynomial]
  rw [if_pos (Nat.zero_le d), terminating3F2Coefficient_zero]

/-- Euler's operator shifted by a scalar: `(theta+a)p`. -/
noncomputable def polynomialEulerShift (a : ℝ) (p : ℝ[X]) : ℝ[X] :=
  Polynomial.X * p.derivative + Polynomial.C a * p

theorem coeff_polynomialEulerShift (a : ℝ) (p : ℝ[X]) (k : ℕ) :
    (polynomialEulerShift a p).coeff k = (k + a) * p.coeff k := by
  cases k with
  | zero => simp [polynomialEulerShift]
  | succ k =>
      simp only [polynomialEulerShift, coeff_add, coeff_X_mul, coeff_derivative,
        coeff_C_mul, Nat.cast_add, Nat.cast_one]
      ring

theorem coeff_polynomialEulerShift_three
    (a b c : ℝ) (p : ℝ[X]) (k : ℕ) :
    (polynomialEulerShift a (polynomialEulerShift b (polynomialEulerShift c p))).coeff k =
      (k + a) * (k + b) * (k + c) * p.coeff k := by
  simp only [coeff_polynomialEulerShift]
  ring

/-- The scaled derivative jet naturally diagonalized by Euler's operator. -/
noncomputable def polynomialEulerJet (p : ℝ[X]) (y : ℝ) (r : ℕ) : ℝ :=
  y ^ r * Polynomial.eval y (Polynomial.derivative^[r] p)

/-- Exact expansion of three shifted Euler operators into derivative jets. -/
theorem eval_polynomialEulerShift_three
    (a b c y : ℝ) (p : ℝ[X]) :
    Polynomial.eval y
        (polynomialEulerShift a (polynomialEulerShift b (polynomialEulerShift c p))) =
      polynomialEulerJet p y 3 +
        (3 + (a + b + c)) * polynomialEulerJet p y 2 +
        (1 + (a + b + c) + (a * b + a * c + b * c)) *
          polynomialEulerJet p y 1 +
        (a * b * c) * polynomialEulerJet p y 0 := by
  simp only [polynomialEulerShift, polynomialEulerJet, Function.iterate_zero_apply,
    Function.iterate_succ_apply, Polynomial.eval_add, Polynomial.eval_mul,
    Polynomial.eval_X, Polynomial.eval_C, Polynomial.derivative_add,
    Polynomial.derivative_mul, Polynomial.derivative_X, Polynomial.derivative_C,
    Polynomial.derivative_zero, Polynomial.derivative_one,
    Polynomial.eval_zero, Polynomial.eval_one]
  ring

theorem coeff_X_mul_polynomialEulerShift_three_succ
    (a b c : ℝ) (p : ℝ[X]) (k : ℕ) :
    (Polynomial.X *
        polynomialEulerShift a (polynomialEulerShift b (polynomialEulerShift c p))).coeff
        (k + 1) =
      (k + a) * (k + b) * (k + c) * p.coeff k := by
  rw [coeff_X_mul, coeff_polynomialEulerShift_three]

/-- The generalized hypergeometric differential equation, proved from the
finite coefficient recursion. -/
theorem terminating3F2_euler_ode
    {d : ℕ} {A B C D lambda : ℝ}
    (hB : ∀ k ≤ d, B + k ≠ 0)
    (hD : ∀ k ≤ d, D + k ≠ 0) :
    let p := terminating3F2Polynomial d A B C D lambda
    polynomialEulerShift 0
        (polynomialEulerShift (B - 1) (polynomialEulerShift (D - 1) p)) =
      Polynomial.C lambda * (Polynomial.X *
        polynomialEulerShift (-(d : ℝ))
          (polynomialEulerShift A (polynomialEulerShift C p))) := by
  dsimp
  ext n
  cases n with
  | zero => simp [coeff_polynomialEulerShift]
  | succ k =>
      rw [coeff_polynomialEulerShift_three]
      rw [coeff_C_mul, coeff_X_mul, coeff_polynomialEulerShift_three]
      rw [coeff_terminating3F2Polynomial, coeff_terminating3F2Polynomial]
      by_cases hk : k < d
      · have hk0 : k ≤ d := hk.le
        have hk1 : k + 1 ≤ d := by omega
        rw [if_pos hk1, if_pos hk0]
        have hratio := terminating3F2Coefficient_ratio_cross
          (d := d) (k := k) (A := A) (B := B) (C := C) (D := D)
          (lambda := lambda) (hB k hk0) (hD k hk0)
        push_cast
        ring_nf at hratio ⊢
        exact hratio
      · have hdk : d ≤ k := Nat.le_of_not_gt hk
        rw [if_neg (by omega : ¬ k + 1 ≤ d)]
        by_cases hkd : k = d
        · subst k
          rw [if_pos le_rfl]
          simp
        · rw [if_neg (by omega : ¬ k ≤ d)]
          simp

/-- The ODE is valid for every derivative-shift parameter set consumed in
the recurrence (`0 ≤ m ≤ d`). -/
theorem terminating3F2_shifted_euler_ode
    {d m : ℕ} {A B C D lambda : ℝ}
    (hmd : m ≤ d)
    (hB : ∀ k ≤ d - m, B + m + k ≠ 0)
    (hD : ∀ k ≤ d - m, D + m + k ≠ 0) :
    let p := terminating3F2Polynomial (d - m)
      (A + m) (B + m) (C + m) (D + m) lambda
    polynomialEulerShift 0
        (polynomialEulerShift (B + m - 1)
          (polynomialEulerShift (D + m - 1) p)) =
      Polynomial.C lambda * (Polynomial.X *
        polynomialEulerShift ((m : ℝ) - d)
          (polynomialEulerShift (A + m) (polynomialEulerShift (C + m) p))) := by
  have h := terminating3F2_euler_ode
    (d := d - m) (A := A + m) (B := B + m) (C := C + m)
    (D := D + m) (lambda := lambda) hB hD
  simpa [Nat.cast_sub hmd] using h

/-- Normalizing constant relating the `m`th derivative to the shifted
terminating polynomial. -/
noncomputable def terminating3F2DerivativePrefactor
    (d m : ℕ) (A B C D lambda : ℝ) : ℝ :=
  (m.factorial : ℝ) * terminating3F2Coefficient d A B C D lambda m

private theorem derivativeShiftStepAlgebra
    {df dfNext coefficient shiftedCoefficient prefactor numerator denominator
      small large : ℝ}
    (hdenominator : denominator ≠ 0) (hsmall : small ≠ 0) (hlarge : large ≠ 0)
    (hdesc : dfNext * small = large * df)
    (hcoeff : df * coefficient = prefactor * shiftedCoefficient) :
    dfNext * (coefficient * numerator / (denominator * large)) =
      prefactor * (shiftedCoefficient * numerator / (denominator * small)) := by
  field_simp [hdenominator, hsmall, hlarge]
  calc
    dfNext * coefficient * numerator * small =
        (dfNext * small) * coefficient * numerator := by ring
    _ = (large * df) * coefficient * numerator := by rw [hdesc]
    _ = large * (df * coefficient) * numerator := by ring
    _ = large * (prefactor * shiftedCoefficient) * numerator := by rw [hcoeff]
    _ = numerator * large * prefactor * shiftedCoefficient := by ring

/-- Coefficient identity behind the derivative shift. -/
theorem terminating3F2_derivative_shift_coefficient
    {d m k : ℕ} {A B C D lambda : ℝ}
    (hmd : m ≤ d) (hk : k ≤ d - m)
    (hB : ∀ r ≤ d, B + r ≠ 0)
    (hD : ∀ r ≤ d, D + r ≠ 0) :
    ((k + m).descFactorial m : ℝ) *
        terminating3F2Coefficient d A B C D lambda (k + m) =
      terminating3F2DerivativePrefactor d m A B C D lambda *
        terminating3F2Coefficient (d - m) (A + m) (B + m)
          (C + m) (D + m) lambda k := by
  induction k with
  | zero =>
      simp only [Nat.zero_add, terminating3F2DerivativePrefactor,
        terminating3F2Coefficient_zero, mul_one]
      rw [Nat.descFactorial_self]
  | succ k ih =>
      have hk' : k ≤ d - m := by omega
      have hmk : m + k ≤ d := by omega
      have hBmk : B + (m : ℝ) + k ≠ 0 := by
        simpa [Nat.cast_add, add_assoc] using hB (m + k) hmk
      have hDmk : D + (m : ℝ) + k ≠ 0 := by
        simpa [Nat.cast_add, add_assoc] using hD (m + k) hmk
      have ih' := ih hk'
      rw [show k + 1 + m = (k + m) + 1 by omega,
        terminating3F2Coefficient_succ,
        terminating3F2Coefficient_succ]
      have hdescNat := Nat.succ_descFactorial (k + m) m
      rw [show k + m + 1 - m = k + 1 by omega] at hdescNat
      have hdesc :
          (((k + m + 1).descFactorial m : ℕ) : ℝ) * (k + 1) =
            (k + m + 1) * (((k + m).descFactorial m : ℕ) : ℝ) := by
        have hc : (k + 1 : ℝ) * (((k + m + 1).descFactorial m : ℕ) : ℝ) =
            (k + m + 1) * (((k + m).descFactorial m : ℕ) : ℝ) := by
          exact_mod_cast hdescNat
        simpa [mul_comm] using hc
      have hdmcast : ((d - m : ℕ) : ℝ) = (d : ℝ) - m := by
        exact Nat.cast_sub hmd
      have hden : (B + (m : ℝ) + k) * (D + (m : ℝ) + k) ≠ 0 :=
        mul_ne_zero hBmk hDmk
      have hsmall : (k : ℝ) + 1 ≠ 0 := by positivity
      have hlarge : (k : ℝ) + m + 1 ≠ 0 := by positivity
      have halg := derivativeShiftStepAlgebra
        (df := (((k + m).descFactorial m : ℕ) : ℝ))
        (dfNext := (((k + m + 1).descFactorial m : ℕ) : ℝ))
        (coefficient := terminating3F2Coefficient d A B C D lambda (k + m))
        (shiftedCoefficient := terminating3F2Coefficient (d - m)
          (A + m) (B + m) (C + m) (D + m) lambda k)
        (prefactor := terminating3F2DerivativePrefactor d m A B C D lambda)
        (numerator := lambda * (((k : ℝ) + m) - d) * (A + m + k) * (C + m + k))
        (denominator := (B + m + k) * (D + m + k))
        (small := (k : ℝ) + 1) (large := (k : ℝ) + m + 1)
        hden hsmall hlarge hdesc (by simpa [Nat.cast_add, add_comm, add_left_comm,
          add_assoc] using ih')
      convert halg using 1 <;>
        push_cast
      all_goals try rw [hdmcast]
      all_goals ring

/-- Every derivative order `0 ≤ m ≤ d` is the displayed shifted
terminating `_3F_2`, with an exact scalar prefactor. -/
theorem iterate_derivative_terminating3F2Polynomial
    {d m : ℕ} {A B C D lambda : ℝ}
    (hmd : m ≤ d)
    (hB : ∀ r ≤ d, B + r ≠ 0)
    (hD : ∀ r ≤ d, D + r ≠ 0) :
    Polynomial.derivative^[m]
        (terminating3F2Polynomial d A B C D lambda) =
      Polynomial.C (terminating3F2DerivativePrefactor d m A B C D lambda) *
        terminating3F2Polynomial (d - m) (A + m) (B + m)
          (C + m) (D + m) lambda := by
  ext k
  rw [Polynomial.coeff_iterate_derivative, coeff_C_mul,
    coeff_terminating3F2Polynomial, coeff_terminating3F2Polynomial]
  by_cases hk : k ≤ d - m
  · rw [if_pos hk]
    have hkm : k + m ≤ d := by omega
    rw [if_pos hkm]
    simpa [add_comm] using terminating3F2_derivative_shift_coefficient
      (d := d) (m := m) (k := k) (A := A) (B := B) (C := C) (D := D)
      (lambda := lambda) hmd hk hB hD
  · rw [if_neg hk]
    have hdm : d < k + m := by omega
    rw [if_neg (by omega : ¬ k + m ≤ d)]
    simp

/-! Compact four-term coefficients obtained by expanding the shifted Euler
ODE in the basis `p^(m),...,p^(m+3)`. -/

noncomputable def shifted3F2E1 (A C d m : ℝ) : ℝ :=
  (m - d) + (A + m) + (C + m)

noncomputable def shifted3F2E2 (A C d m : ℝ) : ℝ :=
  (m - d) * (A + m) + (m - d) * (C + m) + (A + m) * (C + m)

noncomputable def shifted3F2E3 (A C d m : ℝ) : ℝ :=
  (m - d) * (A + m) * (C + m)

noncomputable def hypergeometricOdeP3 (lambda y : ℝ) : ℝ :=
  1 - lambda * y

noncomputable def hypergeometricOdeP2
    (A B C D lambda y d m : ℝ) : ℝ :=
  B + m + (D + m) + 1 - lambda * y * (3 + shifted3F2E1 A C d m)

noncomputable def hypergeometricOdeP1
    (A B C D lambda y d m : ℝ) : ℝ :=
  (B + m) * (D + m) - lambda * y *
    (1 + shifted3F2E1 A C d m + shifted3F2E2 A C d m)

noncomputable def hypergeometricOdeP0
    (A C lambda y d m : ℝ) : ℝ :=
  -lambda * y * shifted3F2E3 A C d m

theorem hypergeometricOdeP3_eq_recurrenceP3
    {A C D y : ℝ} (hA : A ≠ 0) (hC : C ≠ 0) :
    hypergeometricOdeP3 (D / (A * C)) y = recurrenceP3 A C D y := by
  simp only [hypergeometricOdeP3, recurrenceP3, recurrenceA, recurrenceEpsilon]
  field_simp [hA, hC]
  ring

theorem hypergeometricOdeP2_eq_recurrenceP2
    {A B C D y d m : ℝ} (hA : A ≠ 0) (hC : C ≠ 0) :
    hypergeometricOdeP2 A B C D (D / (A * C)) y d m =
      recurrenceP2 A B C D y d m := by
  simp only [hypergeometricOdeP2, shifted3F2E1, recurrenceP2,
    recurrenceA, recurrenceB, recurrenceEpsilon]
  field_simp [hA, hC]
  ring

theorem hypergeometricOdeP1_eq_recurrenceP1
    {A B C D y d m : ℝ} (hA : A ≠ 0) (hC : C ≠ 0) :
    hypergeometricOdeP1 A B C D (D / (A * C)) y d m =
      recurrenceP1 A B C D y d m := by
  simp only [hypergeometricOdeP1, shifted3F2E1, shifted3F2E2,
    recurrenceP1, recurrenceB, recurrenceC, recurrenceBeta,
    recurrenceEpsilon]
  field_simp [hA, hC]
  ring

theorem hypergeometricOdeP0_eq_recurrenceP0
    {A C D y d m : ℝ} (hA : A ≠ 0) (hC : C ≠ 0) :
    hypergeometricOdeP0 A C (D / (A * C)) y d m =
      recurrenceP0 A C D y d m := by
  simp only [hypergeometricOdeP0, shifted3F2E3, recurrenceP0,
    recurrenceC, recurrenceGamma, recurrenceEpsilon]
  field_simp [hA, hC]
  ring

/-- The ODE-derived compact coefficients are exactly the four coefficients
consumed by the direct recurrence. -/
theorem hypergeometricOdeCoefficients_match_directRecurrence
    {A B C D y d m : ℝ} (hA : A ≠ 0) (hC : C ≠ 0) :
    hypergeometricOdeP3 (D / (A * C)) y = recurrenceP3 A C D y ∧
    hypergeometricOdeP2 A B C D (D / (A * C)) y d m =
      recurrenceP2 A B C D y d m ∧
    hypergeometricOdeP1 A B C D (D / (A * C)) y d m =
      recurrenceP1 A B C D y d m ∧
    hypergeometricOdeP0 A C (D / (A * C)) y d m =
      recurrenceP0 A C D y d m := by
  exact ⟨hypergeometricOdeP3_eq_recurrenceP3 hA hC,
    hypergeometricOdeP2_eq_recurrenceP2 hA hC,
    hypergeometricOdeP1_eq_recurrenceP1 hA hC,
    hypergeometricOdeP0_eq_recurrenceP0 hA hC⟩

/-- The four-term recurrence holds identically on the genuine shifted finite
polynomial for every legal derivative order. -/
theorem terminating3F2_shifted_fourTerm_recurrence
    {d m : ℕ} {A B C D lambda y : ℝ}
    (hmd : m ≤ d)
    (hB : ∀ k ≤ d - m, B + m + k ≠ 0)
    (hD : ∀ k ≤ d - m, D + m + k ≠ 0) :
    let p := terminating3F2Polynomial (d - m)
      (A + m) (B + m) (C + m) (D + m) lambda
    hypergeometricOdeP3 lambda y * polynomialEulerJet p y 3 +
      hypergeometricOdeP2 A B C D lambda y d m * polynomialEulerJet p y 2 +
      hypergeometricOdeP1 A B C D lambda y d m * polynomialEulerJet p y 1 +
      hypergeometricOdeP0 A C lambda y d m * polynomialEulerJet p y 0 = 0 := by
  dsimp
  have hode := terminating3F2_shifted_euler_ode
    (d := d) (m := m) (A := A) (B := B) (C := C) (D := D)
    (lambda := lambda) hmd hB hD
  have heval := congrArg (Polynomial.eval y) hode
  rw [eval_polynomialEulerShift_three] at heval
  simp only [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_X] at heval
  rw [eval_polynomialEulerShift_three] at heval
  simp only [hypergeometricOdeP3, hypergeometricOdeP2, hypergeometricOdeP1,
    hypergeometricOdeP0, shifted3F2E1, shifted3F2E2, shifted3F2E3]
  ring_nf at heval ⊢
  linear_combination heval

end Zeta23.Research.JensenWedge
