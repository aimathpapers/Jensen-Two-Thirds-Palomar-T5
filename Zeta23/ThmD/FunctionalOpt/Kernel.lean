/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
import Zeta23.ThmD.FunctionalOpt.Bilinear

noncomputable section

open Real intervalIntegral

namespace Zeta23
namespace ThmD

/-- Integral of the distance to a point of the scale-free interval. -/
theorem integral_abs_sub {s : ℝ} (hs : s ∈ Set.Icc (-(1 : ℝ) / 2) (1 / 2)) :
    (∫ t in (-(1 : ℝ) / 2)..(1 / 2), |s - t|) = s ^ 2 + 1 / 4 := by
  have hsplit : (∫ t in (-(1 : ℝ) / 2)..(1 / 2), |s - t|)
      = (∫ t in (-(1 : ℝ) / 2)..s, |s - t|) + ∫ t in s..(1 / 2), |s - t| :=
    (intervalIntegral.integral_add_adjacent_intervals
      (Continuous.intervalIntegrable (by fun_prop) _ _)
      (Continuous.intervalIntegrable (by fun_prop) _ _)).symm
  have hleft : (∫ t in (-(1 : ℝ) / 2)..s, |s - t|)
      = ∫ t in (-(1 : ℝ) / 2)..s, (s - t) := by
    apply intervalIntegral.integral_congr
    intro t ht
    rw [Set.uIcc_of_le hs.1] at ht
    change |s - t| = s - t
    rw [abs_of_nonneg (sub_nonneg.mpr ht.2)]
  have hright : (∫ t in s..(1 / 2), |s - t|)
      = ∫ t in s..(1 / 2), (t - s) := by
    apply intervalIntegral.integral_congr
    intro t ht
    rw [Set.uIcc_of_le hs.2] at ht
    change |s - t| = t - s
    rw [abs_of_nonpos (sub_nonpos.mpr ht.1), neg_sub]
  rw [hsplit, hleft, hright]
  have hl : (∫ t in (-(1 : ℝ) / 2)..s, (s - t))
      = s * (s - (-(1 : ℝ) / 2)) - (s ^ 2 / 2 - (-(1 : ℝ) / 2) ^ 2 / 2) := by
    have hsub := intervalIntegral.integral_sub
      (μ := MeasureTheory.volume)
      ((continuous_const : Continuous (fun _ : ℝ => s)).intervalIntegrable (-(1 : ℝ) / 2) s)
      ((continuous_id : Continuous (fun x : ℝ => x)).intervalIntegrable (-(1 : ℝ) / 2) s)
    calc
      (∫ t in (-(1 : ℝ) / 2)..s, (s - t)) =
          (s - (-(1 : ℝ) / 2)) * s - (s ^ 2 - (-(1 : ℝ) / 2) ^ 2) / 2 := by
            simpa [integral_const, integral_id, smul_eq_mul] using hsub
      _ = s * (s - (-(1 : ℝ) / 2)) -
          (s ^ 2 / 2 - (-(1 : ℝ) / 2) ^ 2 / 2) := by ring
  have hr : (∫ t in s..(1 / 2), (t - s))
      = ((1 : ℝ) / 2) ^ 2 / 2 - s ^ 2 / 2 - s * ((1 : ℝ) / 2 - s) := by
    have hsub :
        (∫ t in s..(1 / 2), (t - s)) =
          (∫ t in s..(1 / 2), t) - ∫ _t in s..(1 / 2), s :=
      intervalIntegral.integral_sub
        (μ := MeasureTheory.volume)
        ((continuous_id : Continuous (fun x : ℝ => x)).intervalIntegrable s (1 / 2))
        ((continuous_const : Continuous (fun _ : ℝ => s)).intervalIntegrable s (1 / 2))
    calc
      (∫ t in s..(1 / 2), (t - s)) =
          (∫ t in s..(1 / 2), t) - ∫ _t in s..(1 / 2), s := hsub
      _ =
          (((1 : ℝ) / 2) ^ 2 - s ^ 2) / 2 - ((1 : ℝ) / 2 - s) * s := by
            simp [integral_const, integral_id, smul_eq_mul]
      _ = ((1 : ℝ) / 2) ^ 2 / 2 - s ^ 2 / 2 -
          s * ((1 : ℝ) / 2 - s) := by ring
  rw [hl, hr]
  ring

private theorem sq_le_quarter {s : ℝ} (hs : s ∈ Set.Icc (-(1 : ℝ) / 2) (1 / 2)) :
    s ^ 2 ≤ (1 : ℝ) / 4 := by
  have hprod : 0 ≤ (s + 1 / 2) * (1 / 2 - s) :=
    mul_nonneg (by linarith [hs.1]) (by linarith [hs.2])
  nlinarith

/-- The distance-weighted square integral has operator weight at most one half. -/
theorem kerInt2_sq_one_le (v : ℝ → ℝ) (hv : Continuous v) :
    kerInt2 (fun s => v s ^ 2) (fun _ => 1) ≤
      (1 / 2 : ℝ) * ∫ s in (-(1 : ℝ) / 2)..(1 / 2), v s ^ 2 := by
  unfold kerInt2
  have hinner : ∀ s ∈ Set.Icc (-(1 : ℝ) / 2) (1 / 2),
      (∫ t in (-(1 : ℝ) / 2)..(1 / 2), |s - t| * v s ^ 2 * 1)
        = v s ^ 2 * (s ^ 2 + 1 / 4) := by
    intro s hs
    rw [intervalIntegral.integral_congr (fun t _ => by ring :
      ∀ t ∈ Set.uIcc (-(1 : ℝ) / 2) (1 / 2),
        |s - t| * v s ^ 2 * 1 = v s ^ 2 * |s - t|),
      intervalIntegral.integral_const_mul, integral_abs_sub hs]
  rw [intervalIntegral.integral_congr (fun s hs => hinner s
    (by rwa [Set.uIcc_of_le (by norm_num : (-(1 : ℝ) / 2 : ℝ) ≤ 1 / 2)] at hs))]
  have hmono : (∫ s in (-(1 : ℝ) / 2)..(1 / 2), v s ^ 2 * (s ^ 2 + 1 / 4))
      ≤ ∫ s in (-(1 : ℝ) / 2)..(1 / 2), (1 / 2) * v s ^ 2 := by
    apply intervalIntegral.integral_mono_on (by norm_num)
      ((hv.pow 2 |>.mul ((continuous_id.pow 2).add continuous_const)).intervalIntegrable _ _)
      ((continuous_const.mul (hv.pow 2)).intervalIntegrable _ _)
    intro s hs
    have hs' : s ∈ Set.Icc (-(1 : ℝ) / 2) (1 / 2) := hs
    have hvnn : 0 ≤ v s ^ 2 := sq_nonneg _
    have hsq := sq_le_quarter hs'
    change v s ^ 2 * (s ^ 2 + 1 / 4) ≤ (1 / 2) * v s ^ 2
    nlinarith
  rw [intervalIntegral.integral_const_mul] at hmono
  exact hmono

private theorem young_kernel (s t a b : ℝ) :
    -((|s - t| * a ^ 2 + |s - t| * b ^ 2) / 2) ≤ |s - t| * a * b := by
  have h := mul_nonneg (abs_nonneg (s - t)) (sq_nonneg (a + b))
  nlinarith

/-- The kernel is bounded below by minus one half of the square integral. -/
theorem kerInt2_self_lower (v : ℝ → ℝ) (hv : Continuous v) :
    -(1 / 2 : ℝ) * (∫ s in (-(1 : ℝ) / 2)..(1 / 2), v s ^ 2) ≤ kerInt2 v v := by
  let q : ℝ → ℝ := fun s => v s ^ 2
  have hq : Continuous q := hv.pow 2
  have hsym : kerInt2 (fun _ : ℝ => 1) q = kerInt2 q (fun _ => 1) :=
    kerInt2_symm continuous_const hq
  have hdouble : -(kerInt2 q (fun _ => 1)) ≤ kerInt2 v v := by
    unfold kerInt2
    have hinner : ∀ s : ℝ,
        -(1 / 2 : ℝ) *
            ((∫ t in (-(1 : ℝ) / 2)..(1 / 2), |s - t| * q s * 1)
              + ∫ t in (-(1 : ℝ) / 2)..(1 / 2), |s - t| * 1 * q t)
          ≤ ∫ t in (-(1 : ℝ) / 2)..(1 / 2), |s - t| * v s * v t := by
      intro s
      have hm : (∫ t in (-(1 : ℝ) / 2)..(1 / 2),
          -((|s - t| * q s + |s - t| * q t) / 2))
          ≤ ∫ t in (-(1 : ℝ) / 2)..(1 / 2), |s - t| * v s * v t := by
        apply intervalIntegral.integral_mono_on (by norm_num)
          (Continuous.intervalIntegrable (by fun_prop) _ _)
          (Continuous.intervalIntegrable (by fun_prop) _ _)
        intro t _
        exact young_kernel s t (v s) (v t)
      have he : (∫ t in (-(1 : ℝ) / 2)..(1 / 2),
          -((|s - t| * q s + |s - t| * q t) / 2))
          = -(1 / 2 : ℝ) *
            ((∫ t in (-(1 : ℝ) / 2)..(1 / 2), |s - t| * q s * 1)
              + ∫ t in (-(1 : ℝ) / 2)..(1 / 2), |s - t| * 1 * q t) := by
        rw [intervalIntegral.integral_congr (fun t _ => by ring :
          ∀ t ∈ Set.uIcc (-(1 : ℝ) / 2) (1 / 2),
            -((|s - t| * q s + |s - t| * q t) / 2)
              = -(1 / 2 : ℝ) * (|s - t| * q s * 1 + |s - t| * 1 * q t))]
        rw [intervalIntegral.integral_const_mul,
          intervalIntegral.integral_add (Continuous.intervalIntegrable (by fun_prop) _ _)
            (Continuous.intervalIntegrable (by fun_prop) _ _)]
      rwa [he] at hm
    have hmOuter : (∫ s in (-(1 : ℝ) / 2)..(1 / 2),
        -(1 / 2 : ℝ) *
          ((∫ t in (-(1 : ℝ) / 2)..(1 / 2), |s - t| * q s * 1)
            + ∫ t in (-(1 : ℝ) / 2)..(1 / 2), |s - t| * 1 * q t))
        ≤ ∫ s in (-(1 : ℝ) / 2)..(1 / 2),
          ∫ t in (-(1 : ℝ) / 2)..(1 / 2), |s - t| * v s * v t := by
      apply intervalIntegral.integral_mono_on (by norm_num)
        (Continuous.intervalIntegrable (by fun_prop) _ _)
        (Continuous.intervalIntegrable (by fun_prop) _ _)
      intro s _
      exact hinner s
    have heOuter : (∫ s in (-(1 : ℝ) / 2)..(1 / 2),
        -(1 / 2 : ℝ) *
          ((∫ t in (-(1 : ℝ) / 2)..(1 / 2), |s - t| * q s * 1)
            + ∫ t in (-(1 : ℝ) / 2)..(1 / 2), |s - t| * 1 * q t))
        = -(kerInt2 q (fun _ => 1)) := by
      rw [intervalIntegral.integral_const_mul]
      have hadd : (∫ s in (-(1 : ℝ) / 2)..(1 / 2),
          (∫ t in (-(1 : ℝ) / 2)..(1 / 2), |s - t| * q s * 1)
            + ∫ t in (-(1 : ℝ) / 2)..(1 / 2), |s - t| * 1 * q t)
          = kerInt2 q (fun _ => 1) + kerInt2 (fun _ => 1) q := by
        rw [intervalIntegral.integral_add
          (Continuous.intervalIntegrable (by fun_prop) _ _)
          (Continuous.intervalIntegrable (by fun_prop) _ _)]
        rfl
      rw [hadd, hsym]
      ring
    rwa [heOuter] at hmOuter
  have hweight := kerInt2_sq_one_le v hv
  nlinarith

end ThmD
end Zeta23

end
