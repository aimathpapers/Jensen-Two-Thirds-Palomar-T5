import Mathlib

/-!
# Exact finite bounds in the saddle branch

These are the algebraic and norm estimates used inside Lemma S.  They do not
claim the holomorphic implicit-function or Rouché part of that lemma; they
kernel-check the denominator identity and the explicit branch-box margins.
-/

namespace Zeta23.Research.JensenWedge

/-- Polynomial denominator before the scaled variables `r = 1/L` and
`σ = L/N` are introduced. -/
noncomputable def saddlePolynomialDenominator (N L : ℂ) : ℂ :=
  N * L + N - (3 / 4) * L ^ 2

theorem saddlePolynomialDenominator_scaled
    {N L r σ : ℂ} (hN : N ≠ 0) (hL : L ≠ 0)
    (hr : r = 1 / L) (hσ : σ = L / N) :
    saddlePolynomialDenominator N L =
      N * L * (1 + r - (3 / 4) * σ) := by
  rw [hr, hσ]
  unfold saddlePolynomialDenominator
  field_simp [hN, hL]

theorem saddle_scaled_factor_norm_lower
    {r σ : ℂ} (hr : ‖r‖ ≤ 7 / 50) (hσ : ‖σ‖ ≤ 7 / 50) :
    9 / 16 ≤ ‖1 + r - (3 / 4) * σ‖ := by
  have hperturb : ‖r - (3 / 4) * σ‖ ≤ (49 : ℝ) / 200 := by
    calc
      ‖r - (3 / 4) * σ‖ ≤ ‖r‖ + ‖(3 / 4 : ℂ) * σ‖ := norm_sub_le _ _
      _ = ‖r‖ + (3 / 4 : ℝ) * ‖σ‖ := by norm_num [norm_mul]
      _ ≤ 7 / 50 + (3 / 4 : ℝ) * (7 / 50) := by gcongr
      _ = 49 / 200 := by norm_num
  have htri : (1 : ℝ) ≤ ‖1 + (r - (3 / 4) * σ)‖ + ‖r - (3 / 4) * σ‖ := by
    calc
      (1 : ℝ) = ‖(1 : ℂ)‖ := by norm_num
      _ = ‖(1 + (r - (3 / 4) * σ)) - (r - (3 / 4) * σ)‖ := by ring_nf
      _ ≤ ‖1 + (r - (3 / 4) * σ)‖ + ‖r - (3 / 4) * σ‖ := norm_sub_le _ _
  have hshape : (1 : ℂ) + (r - (3 / 4) * σ) = 1 + r - (3 / 4) * σ := by ring
  rw [hshape] at htri
  linarith

theorem saddle_scaled_factor_ne_zero
    {r σ : ℂ} (hr : ‖r‖ ≤ 7 / 50) (hσ : ‖σ‖ ≤ 7 / 50) :
    1 + r - (3 / 4) * σ ≠ 0 := by
  intro hzero
  have h := saddle_scaled_factor_norm_lower hr hσ
  rw [hzero, norm_zero] at h
  norm_num at h

theorem saddle_reduced_denominator_norm_lower
    {r σ : ℂ} (hr : ‖r‖ ≤ 7 / 50) (hσ : ‖σ‖ ≤ 7 / 50) :
    (151 : ℝ) / 50 ≤ ‖4 + 4 * r - 3 * σ‖ := by
  have hperturb : ‖4 * r - 3 * σ‖ ≤ (49 : ℝ) / 50 := by
    calc
      ‖4 * r - 3 * σ‖ ≤ ‖(4 : ℂ) * r‖ + ‖(3 : ℂ) * σ‖ := norm_sub_le _ _
      _ = (4 : ℝ) * ‖r‖ + 3 * ‖σ‖ := by norm_num [norm_mul]
      _ ≤ 4 * (7 / 50 : ℝ) + 3 * (7 / 50 : ℝ) := by gcongr
      _ = 49 / 50 := by norm_num
  have htri : (4 : ℝ) ≤ ‖(4 : ℂ) + (4 * r - 3 * σ)‖ + ‖4 * r - 3 * σ‖ := by
    calc
      (4 : ℝ) = ‖(4 : ℂ)‖ := by norm_num
      _ = ‖((4 : ℂ) + (4 * r - 3 * σ)) - (4 * r - 3 * σ)‖ := by ring_nf
      _ ≤ ‖(4 : ℂ) + (4 * r - 3 * σ)‖ + ‖4 * r - 3 * σ‖ := norm_sub_le _ _
  have hshape : (4 : ℂ) + (4 * r - 3 * σ) = 4 + 4 * r - 3 * σ := by ring
  rw [hshape] at htri
  linarith

end Zeta23.Research.JensenWedge
