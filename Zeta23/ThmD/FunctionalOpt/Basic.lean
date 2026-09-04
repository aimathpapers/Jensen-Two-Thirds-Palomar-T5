/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
import Zeta23.ThmD.Functional

noncomputable section

open Real intervalIntegral

namespace Zeta23
namespace ThmD

/-- The kernel form on the scale-free interval. -/
def kerInt2 (v w : ℝ → ℝ) : ℝ :=
  ∫ s in (-(1 : ℝ) / 2)..(1 / 2),
    ∫ t in (-(1 : ℝ) / 2)..(1 / 2), |s - t| * v s * w t

/-- The symmetric form whose diagonal is the denominator of `cFun`. -/
def aInner (lam : ℝ) (v w : ℝ → ℝ) : ℝ :=
  (∫ s in (-(1 : ℝ) / 2)..(1 / 2), v s * w s) + lam ^ 2 * kerInt2 v w

def aEnergy (lam : ℝ) (v : ℝ → ℝ) : ℝ := aInner lam v v

def mass (v : ℝ → ℝ) : ℝ := ∫ s in (-(1 : ℝ) / 2)..(1 / 2), v s

def cInner (lam : ℝ) : ℝ :=
  Real.cos (theta lam) + theta lam * Real.sin (theta lam)

theorem aEnergy_eq_cFun_denom (lam : ℝ) (v : ℝ → ℝ) :
    aEnergy lam v = (∫ s in (-(1 : ℝ) / 2)..(1 / 2), v s ^ 2)
      + lam ^ 2 * ∫ s in (-(1 : ℝ) / 2)..(1 / 2),
        ∫ t in (-(1 : ℝ) / 2)..(1 / 2), |s - t| * v s * v t := by
  unfold aEnergy aInner kerInt2
  rw [intervalIntegral.integral_congr (fun s _ => by ring :
    ∀ s ∈ Set.uIcc (-(1 : ℝ) / 2) (1 / 2), v s * v s = v s ^ 2)]

theorem cInner_pos {lam : ℝ} (h0 : 0 ≤ lam) (h1 : lam ≤ 1) : 0 < cInner lam := by
  have h := cStar_denom_ge h0 h1
  unfold cInner
  linarith

theorem cStar_mul_cInner {lam : ℝ} (h0 : 0 ≤ lam) (h1 : lam ≤ 1) :
    cStar lam * cInner lam = Real.sqrt 2 * Real.sin (theta lam) := by
  have hd : cInner lam ≠ 0 := (cInner_pos h0 h1).ne'
  unfold cStar
  change (Real.sqrt 2 * Real.sin (theta lam) / cInner lam) * cInner lam = _
  exact div_mul_cancel₀ _ hd

/-- A scalar quadratic that is nonnegative everywhere has nonpositive discriminant. -/
theorem sq_le_mul_of_quad_nonneg {A B C : ℝ} (hC : 0 ≤ C)
    (h : ∀ t : ℝ, 0 ≤ A + 2 * B * t + C * t ^ 2) : B ^ 2 ≤ A * C := by
  rcases hC.eq_or_lt with hC0 | hCpos
  · have hB : B = 0 := by
      by_contra hB
      have ht := h ((-|A| - 1) / (2 * B))
      rw [← hC0, zero_mul, add_zero] at ht
      have he : 2 * B * ((-|A| - 1) / (2 * B)) = -|A| - 1 := by
        field_simp [hB]
      rw [he] at ht
      have hAabs : A - |A| ≤ 0 := sub_nonpos.mpr (le_abs_self A)
      linarith
    rw [hB, ← hC0]
    simp
  · have ht := h (-B / C)
    have he : A + 2 * B * (-B / C) + C * (-B / C) ^ 2 = A - B ^ 2 / C := by
      field_simp [hCpos.ne']
      ring
    rw [he] at ht
    have hle : B ^ 2 / C ≤ A := by linarith
    have := mul_le_mul_of_nonneg_right hle hCpos.le
    rwa [div_mul_cancel₀ _ hCpos.ne'] at this

theorem cFun_eq_mass (lam : ℝ) (v : ℝ → ℝ) :
    cFun lam v = lam * mass v ^ 2 / aEnergy lam v := by
  unfold cFun mass
  rw [aEnergy_eq_cFun_denom]

end ThmD
end Zeta23

end
