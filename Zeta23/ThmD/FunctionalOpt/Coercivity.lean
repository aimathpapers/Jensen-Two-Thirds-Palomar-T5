/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
import Zeta23.ThmD.FunctionalOpt.Kernel

noncomputable section

open Real intervalIntegral

namespace Zeta23
namespace ThmD

/-- On the parameter range used by the optimization theorem, the energy controls
one half of the ordinary squared norm. -/
theorem aEnergy_coercive {lam : ℝ} (h0 : 0 ≤ lam) (h1 : lam ≤ 1) {v : ℝ → ℝ}
    (hv : Continuous v) :
    (1 / 2 : ℝ) * (∫ s in (-(1 : ℝ) / 2)..(1 / 2), v s ^ 2) ≤ aEnergy lam v := by
  let Q : ℝ := ∫ s in (-(1 : ℝ) / 2)..(1 / 2), v s ^ 2
  let K : ℝ := kerInt2 v v
  have hQ : 0 ≤ Q := integral_nonneg (by norm_num) (fun x _ => sq_nonneg (v x))
  have hK : -(1 / 2 : ℝ) * Q ≤ K := kerInt2_self_lower v hv
  have hlam2nn : 0 ≤ lam ^ 2 := sq_nonneg lam
  have hlam2le : lam ^ 2 ≤ 1 := by nlinarith
  have henergy : aEnergy lam v = Q + lam ^ 2 * K := by
    unfold aEnergy aInner
    rw [intervalIntegral.integral_congr (fun s _ => by ring :
      ∀ s ∈ Set.uIcc (-(1 : ℝ) / 2) (1 / 2), v s * v s = v s ^ 2)]
  change (1 / 2 : ℝ) * Q ≤ aEnergy lam v
  rw [henergy]
  by_cases hKnn : 0 ≤ K
  · have : 0 ≤ lam ^ 2 * K := mul_nonneg hlam2nn hKnn
    linarith
  · have hKnonpos : K ≤ 0 := le_of_lt (lt_of_not_ge hKnn)
    have hscale : K ≤ lam ^ 2 * K := by
      have := mul_le_mul_of_nonpos_right hlam2le hKnonpos
      simpa using this
    nlinarith

/-- The energy is nonnegative for continuous profiles on `0 ≤ lam ≤ 1`. -/
theorem aEnergy_nonneg {lam : ℝ} (h0 : 0 ≤ lam) (h1 : lam ≤ 1) {v : ℝ → ℝ}
    (hv : Continuous v) : 0 ≤ aEnergy lam v := by
  have h := aEnergy_coercive h0 h1 hv
  have hQ : 0 ≤ ∫ s in (-(1 : ℝ) / 2)..(1 / 2), v s ^ 2 :=
    integral_nonneg (by norm_num) (fun x _ => sq_nonneg (v x))
  linarith

/-- The energy is positive when a continuous profile is nonzero somewhere on the interval. -/
theorem aEnergy_pos {lam : ℝ} (h0 : 0 ≤ lam) (h1 : lam ≤ 1) {v : ℝ → ℝ}
    (hv : Continuous v) {s : ℝ} (hs : s ∈ Set.Icc (-(1 : ℝ) / 2) (1 / 2))
    (hsv : v s ≠ 0) : 0 < aEnergy lam v := by
  have h := aEnergy_coercive h0 h1 hv
  have hQ : 0 < ∫ x in (-(1 : ℝ) / 2)..(1 / 2), v x ^ 2 := by
    apply intervalIntegral.integral_pos (by norm_num : (-(1 : ℝ) / 2 : ℝ) < 1 / 2)
      ((hv.pow 2).continuousOn) (fun x _ => sq_nonneg (v x))
    exact ⟨s, hs, sq_pos_of_ne_zero hsv⟩
  nlinarith

/-- Cauchy--Schwarz for the positive definite form `aInner`. -/
theorem aInner_cs {lam : ℝ} (h0 : 0 ≤ lam) (h1 : lam ≤ 1) {v w : ℝ → ℝ}
    (hv : Continuous v) (hw : Continuous w) :
    aInner lam v w ^ 2 ≤ aEnergy lam v * aEnergy lam w := by
  refine sq_le_mul_of_quad_nonneg (A := aEnergy lam v) (B := aInner lam v w)
    (C := aEnergy lam w) (aEnergy_nonneg h0 h1 hw) (fun t => ?_)
  have hexpand := aEnergy_add_smul (lam := lam) hv hw t
  have hvw : Continuous (fun x => v x + t * w x) := hv.add (continuous_const.mul hw)
  have hnn := aEnergy_nonneg h0 h1 hvw
  rw [hexpand] at hnn
  nlinarith

end ThmD
end Zeta23

end
