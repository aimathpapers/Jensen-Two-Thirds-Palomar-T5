import Mathlib

/-!
# Elementary cube-kernel bounds

This module records the finite-dimensional estimate used in the elementary
`C₁` argument.  The domain is the genuine unit cube in `Fin q → ℝ`; its
Lebesgue volume is proved to be one, and a pointwise reciprocal-power bound
is promoted to the corresponding cube-integral bound.
-/

namespace Zeta23.Research.JensenWedge

open MeasureTheory Set

/-- The closed `q`-dimensional unit cube. -/
def unitCube (q : ℕ) : Set (Fin q → ℝ) :=
  Set.Icc (fun _ => 0) (fun _ => 1)

/-- The affine denominator occurring in the cube representation. -/
def cubeDenominator {q : ℕ} (s z : ℝ) (u : Fin q → ℝ) : ℝ :=
  s + z * ∑ i, u i

theorem unitCube_volume_real (q : ℕ) :
    (volume (unitCube q)).toReal = 1 := by
  rw [unitCube, Real.volume_Icc_pi_toReal]
  · simp
  · intro i
    norm_num

theorem cubeDenominator_lower_bound
    {q : ℕ} {s s₀ z : ℝ} {u : Fin q → ℝ}
    (hs₀ : s₀ ≤ s) (hz : 0 ≤ z) (hu : u ∈ unitCube q) :
    s₀ ≤ cubeDenominator s z u := by
  have hsum : 0 ≤ ∑ i, u i := by
    apply Finset.sum_nonneg
    intro i _
    exact hu.1 i
  dsimp [cubeDenominator]
  nlinarith

/-- Pointwise reciprocal-power estimate underlying the `C₁` derivative
bounds.  The combinatorial rising-factorial multiplier is deliberately left
outside this lemma, so the analytic and finite algebraic factors cannot be
conflated. -/
theorem cube_reciprocal_power_bound
    {q p : ℕ} {s s₀ z : ℝ} {u : Fin q → ℝ}
    (hs₀ : 0 < s₀) (hs : s₀ ≤ s) (hz : 0 ≤ z)
    (hu : u ∈ unitCube q) :
    |(cubeDenominator s z u)⁻¹ ^ p| ≤ s₀⁻¹ ^ p := by
  have hdenom := cubeDenominator_lower_bound hs hz hu
  have hdenom_pos : 0 < cubeDenominator s z u := hs₀.trans_le hdenom
  have hinv : (cubeDenominator s z u)⁻¹ ≤ s₀⁻¹ :=
    (inv_le_inv₀ hdenom_pos hs₀).2 hdenom
  rw [abs_of_nonneg (pow_nonneg (le_of_lt (inv_pos.mpr hdenom_pos)) _)]
  exact pow_le_pow_left₀ (le_of_lt (inv_pos.mpr hdenom_pos)) hinv p

/-- An exact pointwise kernel bound, with an arbitrary nonnegative finite
multiplier `A` (in the application, `A = (q)₍r₎`). -/
theorem cube_derivative_kernel_bound
    {q p : ℕ} {A s s₀ z : ℝ} {u : Fin q → ℝ}
    (hA : 0 ≤ A) (hs₀ : 0 < s₀) (hs : s₀ ≤ s) (hz : 0 ≤ z)
    (hu : u ∈ unitCube q) :
    |A * (cubeDenominator s z u)⁻¹ ^ p| ≤ A * s₀⁻¹ ^ p := by
  rw [abs_mul, abs_of_nonneg hA]
  exact mul_le_mul_of_nonneg_left
    (cube_reciprocal_power_bound hs₀ hs hz hu) hA

/-- Since the unit cube has volume one, any uniform norm bound is also a
bound for the corresponding Bochner cube integral. -/
theorem norm_unitCube_integral_le
    {q : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (F : (Fin q → ℝ) → E) {C : ℝ}
    (hF : ∀ u ∈ unitCube q, ‖F u‖ ≤ C) :
    ‖∫ u in unitCube q, F u‖ ≤ C := by
  have h := norm_setIntegral_le_of_norm_le_const
    (measure_Icc_lt_top : volume (unitCube q) < ⊤) hF
  change ‖∫ u in unitCube q, F u‖ ≤ C * volume.real (unitCube q) at h
  have hvolume : volume.real (unitCube q) = 1 := by
    change (volume (unitCube q)).toReal = 1
    exact unitCube_volume_real q
  rw [hvolume, mul_one] at h
  exact h

end Zeta23.Research.JensenWedge
