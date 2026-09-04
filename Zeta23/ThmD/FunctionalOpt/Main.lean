/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
import Zeta23.ThmD.FunctionalOpt.Euler

noncomputable section

open Real intervalIntegral

namespace Zeta23
namespace ThmD

/-- The master inequality obtained by applying Cauchy--Schwarz to `vStar`. -/
theorem cInner_mass_sq_le {lam : ℝ} (h0 : 0 < lam) (h1 : lam ≤ 1) {v : ℝ → ℝ}
    (hv : Continuous v) :
    cInner lam * mass v ^ 2 ≤ aStar lam * aEnergy lam v := by
  have hvStar : Continuous (vStar lam) := by unfold vStar; fun_prop
  have hcs := aInner_cs h0.le h1 hv hvStar
  rw [aInner_vStar h0 h1 hv, aEnergy_vStar h0 h1] at hcs
  have hc := cInner_pos h0.le h1
  have hleft : (cInner lam * mass v) ^ 2 =
      cInner lam * (cInner lam * mass v ^ 2) := by ring
  have hright : aEnergy lam v * (cInner lam * aStar lam) =
      cInner lam * (aStar lam * aEnergy lam v) := by ring
  rw [hleft, hright] at hcs
  nlinarith

/-- The division-free upper bound underlying optimality. -/
theorem lam_mass_sq_le_cStar_mul {lam : ℝ} (h0 : 0 < lam) (h1 : lam ≤ 1)
    {v : ℝ → ℝ} (hv : Continuous v) :
    lam * mass v ^ 2 ≤ cStar lam * aEnergy lam v := by
  have h := cInner_mass_sq_le h0 h1 hv
  have hc := cInner_pos h0.le h1
  have key1 : cStar lam * cInner lam = Real.sqrt 2 * Real.sin (theta lam) :=
    cStar_mul_cInner h0.le h1
  have key2 : lam * aStar lam = Real.sqrt 2 * Real.sin (theta lam) := by
    rw [aStar_eq h0]
    field_simp [h0.ne']
  have hscaled : lam * (cInner lam * mass v ^ 2) ≤
      lam * (aStar lam * aEnergy lam v) := mul_le_mul_of_nonneg_left h h0.le
  have hright : lam * (aStar lam * aEnergy lam v) =
      cInner lam * (cStar lam * aEnergy lam v) := by
    calc
      lam * (aStar lam * aEnergy lam v) =
          (lam * aStar lam) * aEnergy lam v := by ring
      _ = (cStar lam * cInner lam) * aEnergy lam v := by rw [key2, key1]
      _ = cInner lam * (cStar lam * aEnergy lam v) := by ring
  have hleft : lam * (cInner lam * mass v ^ 2) =
      cInner lam * (lam * mass v ^ 2) := by ring
  rw [hright, hleft] at hscaled
  nlinarith

/-- Every continuous profile satisfies the sharp upper bound. -/
theorem cFun_le_cStar {lam : ℝ} (h0 : 0 < lam) (h1 : lam ≤ 1) {v : ℝ → ℝ}
    (hv : Continuous v) : cFun lam v ≤ cStar lam := by
  have hmain := lam_mass_sq_le_cStar_mul h0 h1 hv
  have hnonneg := aEnergy_nonneg h0.le h1 hv
  rw [cFun_eq_mass]
  by_cases hpositive : 0 < aEnergy lam v
  · rw [div_le_iff₀ hpositive]
    exact hmain
  · have hzero : aEnergy lam v = 0 := by linarith
    rw [hzero, mul_zero] at hmain
    have hnumerator : 0 ≤ lam * mass v ^ 2 := mul_nonneg h0.le (sq_nonneg _)
    have hnumerator_zero : lam * mass v ^ 2 = 0 := le_antisymm hmain hnumerator
    have hmass : mass v = 0 := by
      rcases mul_eq_zero.mp hnumerator_zero with hlam | hmasssq
      · exact (h0.ne' hlam).elim
      · nlinarith [sq_nonneg (mass v)]
    rw [hmass, hzero]
    simp [le_of_lt (cStar_pos h0 h1)]

/-- The explicit cosine profile attains the sharp bound. -/
theorem cStar_attained {lam : ℝ} (h0 : 0 < lam) (h1 : lam ≤ 1) :
    Continuous (vStar lam) ∧ cFun lam (vStar lam) = cStar lam := by
  constructor
  · unfold vStar
    fun_prop
  · exact cFun_vStar h0 h1

/-- A self-contained maximum statement: the candidate is admissible, attains the value,
and dominates every admissible profile. -/
theorem cStar_isMaximum {lam : ℝ} (h0 : 0 < lam) (h1 : lam ≤ 1) :
    Continuous (vStar lam) ∧ cFun lam (vStar lam) = cStar lam ∧
      ∀ v : ℝ → ℝ, Continuous v → cFun lam v ≤ cFun lam (vStar lam) := by
  refine ⟨(cStar_attained h0 h1).1, (cStar_attained h0 h1).2, ?_⟩
  intro v hv
  rw [cFun_vStar h0 h1]
  exact cFun_le_cStar h0 h1 hv

/-- `vStar` is a maximizer on the set of continuous profiles. -/
theorem cStar_isMaxOn {lam : ℝ} (h0 : 0 < lam) (h1 : lam ≤ 1) :
    IsMaxOn (cFun lam) {v : ℝ → ℝ | Continuous v} (vStar lam) := by
  intro v hv
  rw [cFun_vStar h0 h1]
  exact cFun_le_cStar h0 h1 hv

/-- The energy is homogeneous of degree two. -/
theorem aEnergy_smul {lam : ℝ} {v : ℝ → ℝ} (hv : Continuous v) (c : ℝ) :
    aEnergy lam (fun s => c * v s) = c ^ 2 * aEnergy lam v := by
  have hz : Continuous (fun _ : ℝ => (0 : ℝ)) := continuous_const
  have hexpand := aEnergy_add_smul (lam := lam) (v := fun _ : ℝ => (0 : ℝ)) (w := v) hz hv c
  have hzeroEnergy : aEnergy lam (fun _ : ℝ => (0 : ℝ)) = 0 := by
    unfold aEnergy aInner kerInt2
    simp
  have hzeroInner : aInner lam (fun _ : ℝ => (0 : ℝ)) v = 0 := by
    unfold aInner kerInt2
    simp
  simpa [hzeroEnergy, hzeroInner] using hexpand

/-- The mass is homogeneous of degree one. -/
theorem mass_smul {v : ℝ → ℝ} (c : ℝ) :
    mass (fun s => c * v s) = c * mass v := by
  unfold mass
  rw [intervalIntegral.integral_const_mul]

/-- Every nonzero scalar multiple of the candidate is also a maximizer. -/
theorem cFun_smul_vStar {lam : ℝ} (h0 : 0 < lam) (h1 : lam ≤ 1) {c : ℝ}
    (hc : c ≠ 0) : cFun lam (fun s => c * vStar lam s) = cStar lam := by
  have hvStar : Continuous (vStar lam) := by unfold vStar; fun_prop
  rw [cFun_eq_mass, mass_smul, aEnergy_smul hvStar, mul_pow]
  have henergy : aEnergy lam (vStar lam) ≠ 0 := (aEnergy_vStar_pos h0 h1).ne'
  have hcancel : lam * (c ^ 2 * mass (vStar lam) ^ 2) /
        (c ^ 2 * aEnergy lam (vStar lam)) =
      lam * mass (vStar lam) ^ 2 / aEnergy lam (vStar lam) := by
    field_simp [hc, henergy]
  rw [hcancel, ← cFun_eq_mass, cFun_vStar h0 h1]

/-- The functional depends only on values on the integration interval. -/
theorem cFun_congr_of_eqOn {lam : ℝ} {v u : ℝ → ℝ}
    (h : ∀ s ∈ Set.Icc (-(1 : ℝ) / 2) (1 / 2), v s = u s) :
    cFun lam v = cFun lam u := by
  unfold cFun
  have huIcc : Set.uIcc (-(1 : ℝ) / 2 : ℝ) (1 / 2) =
      Set.Icc (-(1 : ℝ) / 2) (1 / 2) := Set.uIcc_of_le (by norm_num)
  have hmass : (∫ s in (-(1 : ℝ) / 2)..(1 / 2), v s) =
      ∫ s in (-(1 : ℝ) / 2)..(1 / 2), u s :=
    intervalIntegral.integral_congr (fun s hs => h s (by rwa [huIcc] at hs))
  have hsquare : (∫ s in (-(1 : ℝ) / 2)..(1 / 2), v s ^ 2) =
      ∫ s in (-(1 : ℝ) / 2)..(1 / 2), u s ^ 2 :=
    intervalIntegral.integral_congr (fun s hs => by rw [h s (by rwa [huIcc] at hs)])
  have hkernel : (∫ s in (-(1 : ℝ) / 2)..(1 / 2),
        ∫ t in (-(1 : ℝ) / 2)..(1 / 2), |s - t| * v s * v t) =
      ∫ s in (-(1 : ℝ) / 2)..(1 / 2),
        ∫ t in (-(1 : ℝ) / 2)..(1 / 2), |s - t| * u s * u t := by
    apply intervalIntegral.integral_congr
    intro s hs
    rw [huIcc] at hs
    apply intervalIntegral.integral_congr
    intro t ht
    rw [huIcc] at ht
    change |s - t| * v s * v t = |s - t| * u s * u t
    rw [h s hs, h t ht]
  rw [hmass, hsquare, hkernel]

/-- Equality is attained exactly by nonzero scalar multiples of `vStar`, where
functions are compared only on the interval seen by `cFun`. -/
theorem cFun_eq_cStar_iff {lam : ℝ} (h0 : 0 < lam) (h1 : lam ≤ 1) {v : ℝ → ℝ}
    (hv : Continuous v)
    (hvne : ∃ s ∈ Set.Icc (-(1 : ℝ) / 2) (1 / 2), v s ≠ 0) :
    cFun lam v = cStar lam ↔
      ∃ c : ℝ, c ≠ 0 ∧
        ∀ s ∈ Set.Icc (-(1 : ℝ) / 2) (1 / 2), v s = c * vStar lam s := by
  have hvStar : Continuous (vStar lam) := by unfold vStar; fun_prop
  obtain ⟨s0, hs0, hsv0⟩ := hvne
  have henergy : 0 < aEnergy lam v := aEnergy_pos h0.le h1 hv hs0 hsv0
  have hstarEnergy : 0 < aEnergy lam (vStar lam) := aEnergy_vStar_pos h0 h1
  constructor
  · intro heq
    rw [cFun_eq_mass] at heq
    have hquotient : lam * mass v ^ 2 = cStar lam * aEnergy lam v := by
      rw [div_eq_iff henergy.ne'] at heq
      exact heq
    have hmasterEq : cInner lam * mass v ^ 2 = aStar lam * aEnergy lam v := by
      have key1 : cStar lam * cInner lam = Real.sqrt 2 * Real.sin (theta lam) :=
        cStar_mul_cInner h0.le h1
      have key2 : lam * aStar lam = Real.sqrt 2 * Real.sin (theta lam) := by
        rw [aStar_eq h0]
        field_simp [h0.ne']
      have hscaled : cInner lam * (lam * mass v ^ 2) =
          cInner lam * (cStar lam * aEnergy lam v) := by rw [hquotient]
      have hleft : cInner lam * (lam * mass v ^ 2) =
          lam * (cInner lam * mass v ^ 2) := by ring
      have hright : cInner lam * (cStar lam * aEnergy lam v) =
          lam * (aStar lam * aEnergy lam v) := by
        calc
          cInner lam * (cStar lam * aEnergy lam v) =
              (cStar lam * cInner lam) * aEnergy lam v := by ring
          _ = (lam * aStar lam) * aEnergy lam v := by rw [key1, key2]
          _ = lam * (aStar lam * aEnergy lam v) := by ring
      rw [hleft, hright] at hscaled
      nlinarith
    have hcsEq : aInner lam v (vStar lam) ^ 2 =
        aEnergy lam v * aEnergy lam (vStar lam) := by
      rw [aInner_vStar h0 h1 hv, aEnergy_vStar h0 h1]
      calc
        (cInner lam * mass v) ^ 2 =
            cInner lam * (cInner lam * mass v ^ 2) := by ring
        _ = cInner lam * (aStar lam * aEnergy lam v) := by rw [hmasterEq]
        _ = aEnergy lam v * (cInner lam * aStar lam) := by ring
    let c : ℝ := aInner lam v (vStar lam) / aEnergy lam (vStar lam)
    have hcEnergy : c * aEnergy lam (vStar lam) = aInner lam v (vStar lam) := by
      dsimp [c]
      field_simp [hstarEnergy.ne']
    have hdiff : aEnergy lam (fun s => v s - c * vStar lam s) = 0 := by
      have hfun : (fun s => v s - c * vStar lam s) =
          (fun s => v s + (-c) * vStar lam s) := by
        funext s
        ring
      rw [hfun, aEnergy_add_smul hv hvStar (-c)]
      nlinarith [hcsEq, sq_nonneg c]
    have hdiffContinuous : Continuous (fun s => v s - c * vStar lam s) :=
      hv.sub (continuous_const.mul hvStar)
    have hzero : ∀ s ∈ Set.Icc (-(1 : ℝ) / 2) (1 / 2),
        v s - c * vStar lam s = 0 := by
      intro s hs
      by_contra hne
      have hpos := aEnergy_pos h0.le h1 hdiffContinuous hs hne
      linarith
    have hcne : c ≠ 0 := by
      intro hc0
      have hz := hzero s0 hs0
      rw [hc0, zero_mul, sub_zero] at hz
      exact hsv0 hz
    exact ⟨c, hcne, fun s hs => sub_eq_zero.mp (hzero s hs)⟩
  · rintro ⟨c, hc, hceq⟩
    rw [cFun_congr_of_eqOn hceq]
    exact cFun_smul_vStar h0 h1 hc

end ThmD
end Zeta23

end
