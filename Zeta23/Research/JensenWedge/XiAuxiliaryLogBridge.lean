import Zeta23.Research.JensenWedge.ExactXiBranch
import Zeta23.Research.JensenWedge.XiCoefficientLogBridge

/-!
# Exact integer bridge to the auxiliary-moment logarithm

Gamma duplication says that the coefficient second difference plus the
half-shift is exactly the second difference of `Log M_z`.  This module proves
that identity at positive integers, including all positivity and principal-
log branch conditions.
-/

namespace Zeta23.Research.JensenWedge

open Complex

noncomputable section

def xiFactorialRatioReal (m : ℕ) : ℝ :=
  (m.factorial : ℝ) / ((2 * m).factorial : ℝ)

theorem xiFactorialRatioReal_pos (m : ℕ) : 0 < xiFactorialRatioReal m := by
  unfold xiFactorialRatioReal
  positivity

theorem complexFactorialRatio_nat_eq_ofReal (m : ℕ) :
    complexFactorialRatio (m : ℂ) = (xiFactorialRatioReal m : ℂ) := by
  rw [complexFactorialRatio_natCast]
  unfold xiFactorialRatioReal
  push_cast
  rfl

def riemannXiAuxiliaryMomentReal (m : ℕ) : ℝ :=
  riemannXiCoefficientReal m / xiFactorialRatioReal m

theorem riemannXiAuxiliaryMomentReal_pos (m : ℕ) :
    0 < riemannXiAuxiliaryMomentReal m := by
  unfold riemannXiAuxiliaryMomentReal
  exact div_pos (riemannXiCoefficientReal_pos m) (xiFactorialRatioReal_pos m)

theorem complexXiAuxiliaryMoment_nat_eq_ofReal
    {m : ℕ} (hm : 0 < m) :
    complexXiAuxiliaryMoment (m : ℂ) =
      (riemannXiAuxiliaryMomentReal m : ℂ) := by
  obtain ⟨q, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hm)
  have hprod := complexFactorialRatio_mul_auxiliary_nat_succ_eq_real q
  rw [complexFactorialRatio_nat_eq_ofReal] at hprod
  have hratio : (xiFactorialRatioReal (q + 1) : ℂ) ≠ 0 := by
    exact ofReal_ne_zero.mpr (xiFactorialRatioReal_pos (q + 1)).ne'
  apply (mul_left_cancel₀ hratio)
  rw [hprod]
  unfold riemannXiAuxiliaryMomentReal
  push_cast
  field_simp [hratio]

def complexXiDiscreteAuxiliaryLog (m : ℕ) : ℂ :=
  log (complexXiAuxiliaryMoment (m : ℂ))

theorem ofReal_log_riemannXiAuxiliaryMomentReal
    {m : ℕ} (hm : 0 < m) :
    ((Real.log (riemannXiAuxiliaryMomentReal m) : ℝ) : ℂ) =
      complexXiDiscreteAuxiliaryLog m := by
  unfold complexXiDiscreteAuxiliaryLog
  rw [complexXiAuxiliaryMoment_nat_eq_ofReal hm]
  exact Complex.ofReal_log (riemannXiAuxiliaryMomentReal_pos m).le

theorem exactXiCoefficientLog_eq_factorial_add_auxiliary
    (m : ℕ) :
    exactXiCoefficientLog m = Real.log (xiFactorialRatioReal m) +
      Real.log (riemannXiAuxiliaryMomentReal m) := by
  unfold exactXiCoefficientLog riemannXiAuxiliaryMomentReal
  have hr := (xiFactorialRatioReal_pos m).ne'
  have haux : 0 < riemannXiCoefficientReal m / xiFactorialRatioReal m :=
    div_pos (riemannXiCoefficientReal_pos m) (xiFactorialRatioReal_pos m)
  have hfactor : riemannXiCoefficientReal m =
      xiFactorialRatioReal m *
        (riemannXiCoefficientReal m / xiFactorialRatioReal m) := by
    field_simp
  calc
    Real.log (riemannXiCoefficientReal m) =
        Real.log (xiFactorialRatioReal m *
          (riemannXiCoefficientReal m / xiFactorialRatioReal m)) :=
      congrArg Real.log hfactor
    _ = Real.log (xiFactorialRatioReal m) +
        Real.log (riemannXiCoefficientReal m / xiFactorialRatioReal m) :=
      Real.log_mul hr haux.ne'

theorem xiFactorialRatioReal_succ (m : ℕ) :
    xiFactorialRatioReal (m + 1) =
      xiFactorialRatioReal m / (2 * (2 * (m : ℝ) + 1)) := by
  unfold xiFactorialRatioReal
  rw [show m + 1 = Nat.succ m by omega, Nat.factorial_succ]
  rw [show 2 * Nat.succ m = Nat.succ (Nat.succ (2 * m)) by omega,
    Nat.factorial_succ, Nat.factorial_succ]
  push_cast
  field_simp [Nat.factorial_ne_zero]
  ring

theorem secondDiff_log_xiFactorialRatioReal (m : ℕ) :
    secondDiff (fun j => Real.log (xiFactorialRatioReal j)) m =
      -exactXiHalfShiftLog m 0 := by
  have hstep (j : ℕ) :
      Real.log (xiFactorialRatioReal (j + 1)) -
          Real.log (xiFactorialRatioReal j) =
        -Real.log (2 * (2 * (j : ℝ) + 1)) := by
    rw [xiFactorialRatioReal_succ]
    rw [Real.log_div (xiFactorialRatioReal_pos j).ne'
      (by positivity : (2 * (2 * (j : ℝ) + 1) : ℝ) ≠ 0)]
    ring
  rw [secondDiff]
  rw [show Real.log (xiFactorialRatioReal (m + 2)) -
        2 * Real.log (xiFactorialRatioReal (m + 1)) +
          Real.log (xiFactorialRatioReal m) =
      (Real.log (xiFactorialRatioReal (m + 2)) -
        Real.log (xiFactorialRatioReal (m + 1))) -
      (Real.log (xiFactorialRatioReal (m + 1)) -
        Real.log (xiFactorialRatioReal m)) by ring]
  rw [show m + 2 = (m + 1) + 1 by omega, hstep (m + 1), hstep m]
  have hden0 : (0 : ℝ) < 2 * (2 * (m : ℝ) + 1) := by positivity
  have hden1 : (0 : ℝ) < 2 * (2 * ((m + 1 : ℕ) : ℝ) + 1) := by positivity
  rw [show -Real.log (2 * (2 * ((m + 1 : ℕ) : ℝ) + 1)) -
        -Real.log (2 * (2 * (m : ℝ) + 1)) =
      Real.log (2 * (2 * (m : ℝ) + 1)) -
        Real.log (2 * (2 * ((m + 1 : ℕ) : ℝ) + 1)) by ring]
  rw [← Real.log_div hden0.ne' hden1.ne']
  unfold exactXiHalfShiftLog
  have hbase : (0 : ℝ) < (m : ℝ) + 1 / 2 := by positivity
  have hratio :
      (2 * (2 * (m : ℝ) + 1)) /
          (2 * (2 * ((m + 1 : ℕ) : ℝ) + 1)) =
        (1 + 1 / ((m : ℝ) + 1 / 2))⁻¹ := by
    push_cast
    field_simp
    ring
  rw [hratio, Real.log_inv]
  simp only [Nat.add_zero]

def complexXiAuxiliarySecondDiff (m : ℕ) : ℂ :=
  complexXiDiscreteAuxiliaryLog (m + 2) -
    2 * complexXiDiscreteAuxiliaryLog (m + 1) +
      complexXiDiscreteAuxiliaryLog m

theorem ofReal_exactXiAuxiliarySecondDiff
    {n k : ℕ} (hn : 0 < n) :
    (exactXiAuxiliarySecondDiff n k : ℂ) =
      complexXiAuxiliarySecondDiff (n + k) := by
  have h0 : 0 < n + k := by omega
  have h1 : 0 < n + k + 1 := by omega
  have h2 : 0 < n + k + 2 := by omega
  unfold exactXiAuxiliarySecondDiff complexXiAuxiliarySecondDiff
  rw [secondDiff]
  rw [exactXiCoefficientLog_eq_factorial_add_auxiliary (n + k + 2),
    exactXiCoefficientLog_eq_factorial_add_auxiliary (n + k + 1),
    exactXiCoefficientLog_eq_factorial_add_auxiliary (n + k)]
  have hfactor := secondDiff_log_xiFactorialRatioReal (n + k)
  rw [secondDiff] at hfactor
  have hhalf : exactXiHalfShiftLog (n + k) 0 =
      exactXiHalfShiftLog n k := by
    simp only [exactXiHalfShiftLog, Nat.add_zero, Nat.cast_add]
  push_cast
  rw [ofReal_log_riemannXiAuxiliaryMomentReal h0,
    ofReal_log_riemannXiAuxiliaryMomentReal h1,
    ofReal_log_riemannXiAuxiliaryMomentReal h2]
  rw [hhalf] at hfactor
  have hfactorC := congrArg (fun x : ℝ => (x : ℂ)) hfactor
  push_cast at hfactorC
  linear_combination hfactorC

/-- Zeroth through third forward differences commute with the exact
Gamma-corrected bridge to the sampled auxiliary-moment logarithm. -/
theorem ofReal_exactXiAuxiliarySecondDiff_forwardDiffs
    {n : ℕ} (hn : 0 < n) :
    ((natForwardDiff0 (exactXiAuxiliarySecondDiff n) : ℝ) : ℂ) =
        complexNatForwardDiff0 (fun k => complexXiAuxiliarySecondDiff (n + k)) ∧
    ((natForwardDiff1 (exactXiAuxiliarySecondDiff n) : ℝ) : ℂ) =
        complexNatForwardDiff1 (fun k => complexXiAuxiliarySecondDiff (n + k)) ∧
    ((natForwardDiff2 (exactXiAuxiliarySecondDiff n) : ℝ) : ℂ) =
        complexNatForwardDiff2 (fun k => complexXiAuxiliarySecondDiff (n + k)) ∧
    ((natForwardDiff3 (exactXiAuxiliarySecondDiff n) : ℝ) : ℂ) =
        complexNatForwardDiff3 (fun k => complexXiAuxiliarySecondDiff (n + k)) := by
  have h (k : ℕ) :
      (exactXiAuxiliarySecondDiff n k : ℂ) =
        complexXiAuxiliarySecondDiff (n + k) :=
    ofReal_exactXiAuxiliarySecondDiff hn
  constructor
  · simpa [natForwardDiff0, complexNatForwardDiff0] using h 0
  constructor
  · simp only [natForwardDiff1, complexNatForwardDiff1]
    push_cast
    rw [h 1, h 0]
  constructor
  · simp only [natForwardDiff2, complexNatForwardDiff2]
    push_cast
    rw [h 2, h 1, h 0]
  · simp only [natForwardDiff3, complexNatForwardDiff3]
    push_cast
    rw [h 3, h 2, h 1, h 0]

end

end Zeta23.Research.JensenWedge
