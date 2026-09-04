/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
import Zeta23.ThmD.FunctionalOpt.Basic
import Mathlib.MeasureTheory.Function.LocallyIntegrable

noncomputable section

open Real intervalIntegral

namespace Zeta23
namespace ThmD

private theorem kernelOuter_continuous {v w : ℝ → ℝ} (hv : Continuous v) (hw : Continuous w) :
    Continuous fun s ↦ ∫ t in (-(1 : ℝ) / 2)..(1 / 2), |s - t| * v s * w t := by
  apply intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
  fun_prop

theorem kerInt2_symm {v w : ℝ → ℝ} (hv : Continuous v) (hw : Continuous w) :
    kerInt2 v w = kerInt2 w v := by
  have hab : (-(1 : ℝ) / 2 : ℝ) ≤ 1 / 2 := by norm_num
  have hF : Continuous (Function.uncurry fun s t : ℝ ↦ |s - t| * v s * w t) := by
    fun_prop
  have hInt : MeasureTheory.Integrable
      (Function.uncurry fun s t : ℝ ↦ |s - t| * v s * w t)
      ((MeasureTheory.volume.restrict (Set.Ioc (-(1 : ℝ) / 2) (1 / 2))).prod
        (MeasureTheory.volume.restrict (Set.Ioc (-(1 : ℝ) / 2) (1 / 2)))) := by
    rw [MeasureTheory.Measure.prod_restrict]
    exact (hF.continuousOn.integrableOn_compact (isCompact_Icc.prod isCompact_Icc)).mono_set
      (Set.prod_mono Set.Ioc_subset_Icc_self Set.Ioc_subset_Icc_self)
  have hswap := MeasureTheory.integral_integral_swap
    (μ := MeasureTheory.volume.restrict (Set.Ioc (-(1 : ℝ) / 2) (1 / 2)))
    (ν := MeasureTheory.volume.restrict (Set.Ioc (-(1 : ℝ) / 2) (1 / 2))) hInt
  unfold kerInt2
  rw [intervalIntegral.integral_congr (fun s _ ↦ intervalIntegral.integral_of_le hab),
    intervalIntegral.integral_of_le hab, hswap, ← intervalIntegral.integral_of_le hab]
  apply intervalIntegral.integral_congr
  intro t _
  change (∫ s in Set.Ioc (-(1 : ℝ) / 2) (1 / 2), |s - t| * v s * w t)
    = ∫ s in (-(1 : ℝ) / 2)..(1 / 2), |t - s| * w t * v s
  rw [← intervalIntegral.integral_of_le hab]
  apply intervalIntegral.integral_congr
  intro s _
  change |s - t| * v s * w t = |t - s| * w t * v s
  rw [abs_sub_comm]
  ring

theorem kerInt2_add_left {u v w : ℝ → ℝ} (hu : Continuous u) (hv : Continuous v)
    (hw : Continuous w) :
    kerInt2 (fun x ↦ u x + v x) w = kerInt2 u w + kerInt2 v w := by
  unfold kerInt2
  have hinner : ∀ s : ℝ,
      (∫ t in (-(1 : ℝ) / 2)..(1 / 2), |s - t| * (u s + v s) * w t)
        = (∫ t in (-(1 : ℝ) / 2)..(1 / 2), |s - t| * u s * w t)
          + ∫ t in (-(1 : ℝ) / 2)..(1 / 2), |s - t| * v s * w t := by
    intro s
    rw [intervalIntegral.integral_congr (fun t _ => by ring :
      ∀ t ∈ Set.uIcc (-(1 : ℝ) / 2) (1 / 2),
        |s - t| * (u s + v s) * w t = |s - t| * u s * w t + |s - t| * v s * w t),
      intervalIntegral.integral_add (Continuous.intervalIntegrable (by fun_prop) _ _)
        (Continuous.intervalIntegrable (by fun_prop) _ _)]
  rw [intervalIntegral.integral_congr (fun s _ => hinner s),
    intervalIntegral.integral_add
      (kernelOuter_continuous hu hw |>.intervalIntegrable _ _)
      (kernelOuter_continuous hv hw |>.intervalIntegrable _ _)]

theorem kerInt2_smul_left {v w : ℝ → ℝ} (_hv : Continuous v) (_hw : Continuous w) (c : ℝ) :
    kerInt2 (fun x ↦ c * v x) w = c * kerInt2 v w := by
  unfold kerInt2
  have hinner : ∀ s : ℝ,
      (∫ t in (-(1 : ℝ) / 2)..(1 / 2), |s - t| * (c * v s) * w t)
        = c * ∫ t in (-(1 : ℝ) / 2)..(1 / 2), |s - t| * v s * w t := by
    intro s
    rw [intervalIntegral.integral_congr (fun t _ => by ring :
      ∀ t ∈ Set.uIcc (-(1 : ℝ) / 2) (1 / 2),
        |s - t| * (c * v s) * w t = c * (|s - t| * v s * w t)),
      intervalIntegral.integral_const_mul]
  rw [intervalIntegral.integral_congr (fun s _ => hinner s),
    intervalIntegral.integral_const_mul]

theorem aInner_symm {lam : ℝ} {v w : ℝ → ℝ} (hv : Continuous v) (hw : Continuous w) :
    aInner lam v w = aInner lam w v := by
  unfold aInner
  rw [kerInt2_symm hv hw]
  have hmul : (∫ s in (-(1 : ℝ) / 2)..(1 / 2), v s * w s)
      = ∫ s in (-(1 : ℝ) / 2)..(1 / 2), w s * v s :=
    intervalIntegral.integral_congr (fun s _ => mul_comm _ _)
  rw [hmul]

theorem aInner_add_left {lam : ℝ} {u v w : ℝ → ℝ} (hu : Continuous u)
    (hv : Continuous v) (hw : Continuous w) :
    aInner lam (fun x ↦ u x + v x) w = aInner lam u w + aInner lam v w := by
  unfold aInner
  rw [kerInt2_add_left hu hv hw]
  have hi : (∫ s in (-(1 : ℝ) / 2)..(1 / 2), (u s + v s) * w s)
      = (∫ s in (-(1 : ℝ) / 2)..(1 / 2), u s * w s)
        + ∫ s in (-(1 : ℝ) / 2)..(1 / 2), v s * w s := by
    rw [intervalIntegral.integral_congr (fun s _ => by ring :
      ∀ s ∈ Set.uIcc (-(1 : ℝ) / 2) (1 / 2),
        (u s + v s) * w s = u s * w s + v s * w s)]
    simpa only [Pi.add_apply, Pi.mul_apply] using
      intervalIntegral.integral_add ((hu.mul hw).intervalIntegrable (-(1 : ℝ) / 2) (1 / 2))
        ((hv.mul hw).intervalIntegrable (-(1 : ℝ) / 2) (1 / 2))
  rw [hi]
  ring

theorem aInner_smul_left {lam : ℝ} {v w : ℝ → ℝ} (hv : Continuous v)
    (hw : Continuous w) (c : ℝ) :
    aInner lam (fun x ↦ c * v x) w = c * aInner lam v w := by
  unfold aInner
  rw [kerInt2_smul_left hv hw]
  have hi : (∫ s in (-(1 : ℝ) / 2)..(1 / 2), (c * v s) * w s)
      = c * ∫ s in (-(1 : ℝ) / 2)..(1 / 2), v s * w s := by
    rw [intervalIntegral.integral_congr (fun s _ => by ring :
      ∀ s ∈ Set.uIcc (-(1 : ℝ) / 2) (1 / 2), (c * v s) * w s = c * (v s * w s)),
      intervalIntegral.integral_const_mul]
  rw [hi]
  ring

theorem aEnergy_add_smul {lam : ℝ} {v w : ℝ → ℝ} (hv : Continuous v)
    (hw : Continuous w) (t : ℝ) :
    aEnergy lam (fun x ↦ v x + t * w x)
      = aEnergy lam v + 2 * t * aInner lam v w + t ^ 2 * aEnergy lam w := by
  unfold aEnergy
  have hz : Continuous (fun x => t * w x) := continuous_const.mul hw
  have hvz : Continuous (fun x => v x + t * w x) := hv.add hz
  rw [aInner_add_left hv hz hvz]
  have hright1 : aInner lam v (fun x ↦ v x + t * w x)
      = aInner lam v v + t * aInner lam v w := by
    calc
      aInner lam v (fun x ↦ v x + t * w x)
          = aInner lam (fun x ↦ v x + t * w x) v := aInner_symm hv hvz
      _ = aInner lam v v + aInner lam (fun x ↦ t * w x) v :=
        aInner_add_left hv hz hv
      _ = aInner lam v v + t * aInner lam w v := by rw [aInner_smul_left hw hv t]
      _ = aInner lam v v + t * aInner lam v w := by rw [aInner_symm hw hv]
  have hright2 : aInner lam (fun x ↦ t * w x) (fun x ↦ v x + t * w x)
      = t * aInner lam w v + t ^ 2 * aInner lam w w := by
    calc
      aInner lam (fun x ↦ t * w x) (fun x ↦ v x + t * w x)
          = aInner lam (fun x ↦ v x + t * w x) (fun x ↦ t * w x) :=
            aInner_symm hz hvz
      _ = aInner lam v (fun x ↦ t * w x)
          + aInner lam (fun x ↦ t * w x) (fun x ↦ t * w x) :=
            aInner_add_left hv hz hz
      _ = t * aInner lam v w + t ^ 2 * aInner lam w w := by
        have hww : aInner lam w (fun x ↦ t * w x) = t * aInner lam w w := by
          calc
            aInner lam w (fun x ↦ t * w x) = aInner lam (fun x ↦ t * w x) w :=
              aInner_symm hw hz
            _ = t * aInner lam w w := aInner_smul_left hw hw t
        have hzz : aInner lam (fun x ↦ t * w x) (fun x ↦ t * w x)
            = t ^ 2 * aInner lam w w := by
          rw [aInner_smul_left hw hz t, hww]
          ring
        have hs : aInner lam w v = aInner lam v w := aInner_symm hw hv
        rw [aInner_symm hv hz, aInner_smul_left hw hv t, hzz]
        rw [hs]
      _ = t * aInner lam w v + t ^ 2 * aInner lam w w := by
        have hs : aInner lam w v = aInner lam v w := aInner_symm hw hv
        rw [hs]
  rw [hright1, hright2, aInner_symm hw hv]
  ring

end ThmD
end Zeta23

end
