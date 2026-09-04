/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
import Zeta23.ThmD.FunctionalOpt.Coercivity

noncomputable section

open Real intervalIntegral

namespace Zeta23
namespace ThmD

private theorem hasDerivAt_left (omega s : ℝ) (homega : omega ≠ 0) (x : ℝ) :
    HasDerivAt
      (fun x => (s - x) * Real.sin (omega * x) / omega - Real.cos (omega * x) / omega ^ 2)
      ((s - x) * Real.cos (omega * x)) x := by
  have h1 : HasDerivAt (fun x : ℝ => s - x) (-1) x := by
    simpa using (hasDerivAt_id x).const_sub s
  have hlin : HasDerivAt (fun x : ℝ => omega * x) (omega * 1) x :=
    (hasDerivAt_id x).const_mul omega
  have h2 : HasDerivAt (fun x : ℝ => Real.sin (omega * x))
      (Real.cos (omega * x) * (omega * 1)) x :=
    (Real.hasDerivAt_sin (omega * x)).comp x hlin
  have h3 : HasDerivAt (fun x : ℝ => Real.cos (omega * x))
      (-Real.sin (omega * x) * (omega * 1)) x :=
    (Real.hasDerivAt_cos (omega * x)).comp x hlin
  have h4 := ((h1.mul h2).div_const omega).sub (h3.div_const (omega ^ 2))
  exact h4.congr_deriv (by field_simp; ring)

private theorem hasDerivAt_right (omega s : ℝ) (homega : omega ≠ 0) (x : ℝ) :
    HasDerivAt
      (fun x => (x - s) * Real.sin (omega * x) / omega + Real.cos (omega * x) / omega ^ 2)
      ((x - s) * Real.cos (omega * x)) x := by
  have h1 : HasDerivAt (fun x : ℝ => x - s) 1 x := by
    simpa using (hasDerivAt_id x).sub_const s
  have hlin : HasDerivAt (fun x : ℝ => omega * x) (omega * 1) x :=
    (hasDerivAt_id x).const_mul omega
  have h2 : HasDerivAt (fun x : ℝ => Real.sin (omega * x))
      (Real.cos (omega * x) * (omega * 1)) x :=
    (Real.hasDerivAt_sin (omega * x)).comp x hlin
  have h3 : HasDerivAt (fun x : ℝ => Real.cos (omega * x))
      (-Real.sin (omega * x) * (omega * 1)) x :=
    (Real.hasDerivAt_cos (omega * x)).comp x hlin
  have h4 := ((h1.mul h2).div_const omega).add (h3.div_const (omega ^ 2))
  exact h4.congr_deriv (by field_simp; ring)

/-- Pointwise Euler--Lagrange identity for the explicit candidate `vStar`. -/
theorem TvStar_eq {lam : ℝ} (h0 : 0 < lam) {s : ℝ} (hs1 : -(1 : ℝ) / 2 ≤ s)
    (hs2 : s ≤ 1 / 2) :
    (∫ t in (-(1 : ℝ) / 2)..(1 / 2), |s - t| * vStar lam t) =
      aStar lam / 2 + Real.cos (theta lam) / lam ^ 2 - vStar lam s / lam ^ 2 := by
  have homega : Real.sqrt 2 * lam ≠ 0 := by positivity
  have hsqrt : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  set omega := Real.sqrt 2 * lam with homegadef
  have hcont : ∀ a b : ℝ, IntervalIntegrable
      (fun t => |s - t| * Real.cos (omega * t)) MeasureTheory.volume a b := fun a b =>
    Continuous.intervalIntegrable (by fun_prop) a b
  have hsplit : (∫ t in (-(1 : ℝ) / 2)..(1 / 2), |s - t| * Real.cos (omega * t)) =
      (∫ t in (-(1 : ℝ) / 2)..s, |s - t| * Real.cos (omega * t)) +
        ∫ t in s..(1 / 2), |s - t| * Real.cos (omega * t) :=
    (intervalIntegral.integral_add_adjacent_intervals (hcont _ _) (hcont _ _)).symm
  have hleft : (∫ t in (-(1 : ℝ) / 2)..s, |s - t| * Real.cos (omega * t)) =
      ∫ t in (-(1 : ℝ) / 2)..s, (s - t) * Real.cos (omega * t) := by
    apply intervalIntegral.integral_congr
    intro x hx
    rw [Set.uIcc_of_le hs1] at hx
    change |s - x| * Real.cos (omega * x) = (s - x) * Real.cos (omega * x)
    rw [abs_of_nonneg (by linarith [hx.2] : (0 : ℝ) ≤ s - x)]
  have hleft2 : (∫ t in (-(1 : ℝ) / 2)..s, (s - t) * Real.cos (omega * t)) =
      ((s - s) * Real.sin (omega * s) / omega - Real.cos (omega * s) / omega ^ 2) -
        ((s - (-(1 : ℝ) / 2)) * Real.sin (omega * (-(1 : ℝ) / 2)) / omega -
          Real.cos (omega * (-(1 : ℝ) / 2)) / omega ^ 2) :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt
      (fun x _ => hasDerivAt_left omega s homega x)
      (Continuous.intervalIntegrable (by fun_prop) _ _)
  have hright : (∫ t in s..(1 / 2), |s - t| * Real.cos (omega * t)) =
      ∫ t in s..(1 / 2), (t - s) * Real.cos (omega * t) := by
    apply intervalIntegral.integral_congr
    intro x hx
    rw [Set.uIcc_of_le hs2] at hx
    change |s - x| * Real.cos (omega * x) = (x - s) * Real.cos (omega * x)
    rw [abs_of_nonpos (by linarith [hx.1] : s - x ≤ 0), neg_sub]
  have hright2 : (∫ t in s..(1 / 2), (t - s) * Real.cos (omega * t)) =
      (((1 : ℝ) / 2 - s) * Real.sin (omega * (1 / 2)) / omega +
          Real.cos (omega * (1 / 2)) / omega ^ 2) -
        ((s - s) * Real.sin (omega * s) / omega + Real.cos (omega * s) / omega ^ 2) :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt
      (fun x _ => hasDerivAt_right omega s homega x)
      (Continuous.intervalIntegrable (by fun_prop) _ _)
  change (∫ t in (-(1 : ℝ) / 2)..(1 / 2), |s - t| * Real.cos (omega * t)) = _
  rw [hsplit, hleft, hleft2, hright, hright2, aStar_eq h0]
  rw [show omega * (1 / 2) = theta lam from sqrt2_mul_half,
    show omega * (-(1 : ℝ) / 2) = -theta lam from sqrt2_mul_neg_half,
    Real.sin_neg, Real.cos_neg]
  have homega2 : omega ^ 2 = 2 * lam ^ 2 := by rw [homegadef, mul_pow, hsqrt]
  rw [homega2]
  have htheta2 : omega = 2 * theta lam := by
    have h := sqrt2_mul_half (lam := lam)
    rw [homegadef]
    linarith
  rw [htheta2]
  have htheta : 0 < theta lam := theta_pos h0
  have ev : vStar lam s = Real.cos (Real.sqrt 2 * lam * s) := rfl
  rw [ev, show Real.sqrt 2 * lam = omega from rfl, htheta2]
  field_simp
  ring_nf
  rw [show theta lam = lam / Real.sqrt 2 from rfl]
  field_simp
  ring_nf
  try rw [hsqrt]
  try ring

/-- The Euler--Lagrange equation integrated against an arbitrary continuous profile. -/
theorem aInner_vStar {lam : ℝ} (h0 : 0 < lam) (_h1 : lam ≤ 1) {v : ℝ → ℝ}
    (hv : Continuous v) : aInner lam v (vStar lam) = cInner lam * mass v := by
  have hvStar : Continuous (vStar lam) := by unfold vStar; fun_prop
  have hker : kerInt2 v (vStar lam) =
      ∫ s in (-(1 : ℝ) / 2)..(1 / 2),
        v s * (∫ t in (-(1 : ℝ) / 2)..(1 / 2), |s - t| * vStar lam t) := by
    unfold kerInt2
    apply intervalIntegral.integral_congr
    intro s _
    change (∫ t in (-(1 : ℝ) / 2)..(1 / 2), |s - t| * v s * vStar lam t) =
      v s * ∫ t in (-(1 : ℝ) / 2)..(1 / 2), |s - t| * vStar lam t
    rw [intervalIntegral.integral_congr (fun t _ => by ring :
      ∀ t ∈ Set.uIcc (-(1 : ℝ) / 2) (1 / 2),
        |s - t| * v s * vStar lam t = v s * (|s - t| * vStar lam t)),
      intervalIntegral.integral_const_mul]
  have hpt : ∀ s ∈ Set.uIcc (-(1 : ℝ) / 2 : ℝ) (1 / 2),
      v s * (∫ t in (-(1 : ℝ) / 2)..(1 / 2), |s - t| * vStar lam t) =
        v s * (aStar lam / 2 + Real.cos (theta lam) / lam ^ 2) -
          v s * vStar lam s / lam ^ 2 := by
    intro s hs
    rw [Set.uIcc_of_le (by norm_num : (-(1 : ℝ) / 2 : ℝ) ≤ 1 / 2)] at hs
    rw [TvStar_eq h0 hs.1 hs.2]
    ring
  unfold aInner
  rw [hker, intervalIntegral.integral_congr hpt]
  have hi1 : IntervalIntegrable
      (fun s => v s * (aStar lam / 2 + Real.cos (theta lam) / lam ^ 2))
      MeasureTheory.volume (-(1 : ℝ) / 2) (1 / 2) :=
    (hv.mul continuous_const).intervalIntegrable _ _
  have hi2 : IntervalIntegrable (fun s => v s * vStar lam s / lam ^ 2)
      MeasureTheory.volume (-(1 : ℝ) / 2) (1 / 2) :=
    ((hv.mul hvStar).div_const _).intervalIntegrable _ _
  rw [intervalIntegral.integral_sub hi1 hi2]
  rw [intervalIntegral.integral_mul_const, intervalIntegral.integral_div]
  have hlam : lam ≠ 0 := h0.ne'
  have hsqrtpos : (0 : ℝ) < Real.sqrt 2 := by positivity
  have hsqrt : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  unfold cInner mass
  rw [aStar_eq h0, show theta lam = lam / Real.sqrt 2 from rfl]
  field_simp [hlam, hsqrtpos.ne']
  ring_nf
  try rw [hsqrt]
  try ring

/-- The energy of the explicit candidate. -/
theorem aEnergy_vStar {lam : ℝ} (h0 : 0 < lam) (h1 : lam ≤ 1) :
    aEnergy lam (vStar lam) = cInner lam * aStar lam := by
  have hvStar : Continuous (vStar lam) := by unfold vStar; fun_prop
  have h := aInner_vStar h0 h1 hvStar
  show aInner lam (vStar lam) (vStar lam) = cInner lam * aStar lam
  rw [h]
  rfl

theorem aStar_pos {lam : ℝ} (h0 : 0 < lam) (h1 : lam ≤ 1) : 0 < aStar lam := by
  rw [aStar_eq h0]
  have hs := sin_theta_pos h0 h1
  positivity

theorem aEnergy_vStar_pos {lam : ℝ} (h0 : 0 < lam) (h1 : lam ≤ 1) :
    0 < aEnergy lam (vStar lam) := by
  rw [aEnergy_vStar h0 h1]
  exact mul_pos (cInner_pos h0.le h1) (aStar_pos h0 h1)

end ThmD
end Zeta23

end
