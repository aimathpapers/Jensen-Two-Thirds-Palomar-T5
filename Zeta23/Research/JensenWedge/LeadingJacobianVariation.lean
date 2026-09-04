import Zeta23.Research.JensenWedge.ElementaryJacobianOperator

/-!
# Variation of the limiting Jacobian on the inner branch box

The fixed inverse is taken at `branchCenter`, whereas the limiting Jacobian
varies with `(alpha,t,w)`.  This file proves a rational whole-box enclosure
for that variation; no point sampling is used.
-/

namespace Zeta23.Research.JensenWedge

open Metric Set

noncomputable section

theorem branchInnerBox_coordinate_error
    {y : BranchPoint} (hy : y ∈ branchInnerBox) (i : Fin 4) :
    |y i - branchCenter i| ≤ branchInnerRadius := by
  have hdist : dist y branchCenter ≤ branchInnerRadius := by
    simpa [branchInnerBox, dist_comm] using hy
  have hi := (dist_pi_le_iff branchInnerRadius_pos.le).mp hdist i
  simpa [Real.dist_eq] using hi

/-- Symmetric reciprocal-power perturbation estimate around an arbitrary
positive center. -/
theorem reciprocalPower_center_error
    {p : ℕ} {s s₀ c r : ℝ}
    (hs₀ : 0 < s₀) (hs : s₀ ≤ s) (hc : s₀ ≤ c)
    (_hr : 0 ≤ r) (hsc : |s - c| ≤ r) :
    |s⁻¹ ^ p - c⁻¹ ^ p| ≤ (p : ℝ) * r * s₀⁻¹ ^ (p + 1) := by
  rw [abs_le] at hsc
  rcases le_total s c with hle | hge
  · have hh : 0 ≤ c - s := sub_nonneg.mpr hle
    have hhR : c - s ≤ r := by linarith
    have hraw := reciprocalPower_add_error
      (p := p) (s := s) (s₀ := s₀) (h := c - s) hs₀ hs hh
    rw [show s + (c - s) = c by ring, abs_sub_comm] at hraw
    exact hraw.trans (by gcongr)
  · have hh : 0 ≤ s - c := sub_nonneg.mpr hge
    have hhR : s - c ≤ r := by linarith
    have hraw := reciprocalPower_add_error
      (p := p) (s := c) (s₀ := s₀) (h := s - c) hs₀ hc hh
    rw [show c + (s - c) = s by ring] at hraw
    exact hraw.trans (by gcongr)

/-- Product perturbation estimate used for every `w*t^{-p}` entry. -/
theorem mul_reciprocalPower_center_error
    {p : ℕ} {s s₀ c w w₀ rs rw : ℝ}
    (hs₀ : 0 < s₀) (hs : s₀ ≤ s) (hc : s₀ ≤ c)
    (hrs : 0 ≤ rs) (hrw : 0 ≤ rw)
    (hsc : |s - c| ≤ rs) (hww : |w - w₀| ≤ rw) :
    |w * s⁻¹ ^ p - w₀ * c⁻¹ ^ p| ≤
      rw * s₀⁻¹ ^ p + |w₀| * ((p : ℝ) * rs * s₀⁻¹ ^ (p + 1)) := by
  have hspos : 0 < s := hs₀.trans_le hs
  have hinv : s⁻¹ ≤ s₀⁻¹ := (inv_le_inv₀ hspos hs₀).2 hs
  have hpow : |s⁻¹ ^ p| ≤ s₀⁻¹ ^ p := by
    rw [abs_of_nonneg (pow_nonneg (inv_nonneg.mpr hspos.le) p)]
    exact pow_le_pow_left₀ (inv_nonneg.mpr hspos.le) hinv p
  have hrecip := reciprocalPower_center_error (p := p) hs₀ hs hc hrs hsc
  rw [show w * s⁻¹ ^ p - w₀ * c⁻¹ ^ p =
      (w - w₀) * s⁻¹ ^ p + w₀ * (s⁻¹ ^ p - c⁻¹ ^ p) by ring]
  calc
    |(w - w₀) * s⁻¹ ^ p + w₀ * (s⁻¹ ^ p - c⁻¹ ^ p)| ≤
        |w - w₀| * |s⁻¹ ^ p| + |w₀| * |s⁻¹ ^ p - c⁻¹ ^ p| := by
      simpa [abs_mul] using abs_add_le
        ((w - w₀) * s⁻¹ ^ p) (w₀ * (s⁻¹ ^ p - c⁻¹ ^ p))
    _ ≤ rw * s₀⁻¹ ^ p +
        |w₀| * ((p : ℝ) * rs * s₀⁻¹ ^ (p + 1)) := by
      gcongr

theorem leadingElementaryJacobian_center :
    leadingElementaryJacobian branchCenter = gaugeJacobianReal := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [leadingElementaryJacobian, leadingElementaryCoordinatePartialAlpha,
      leadingElementaryCoordinatePartialT, leadingElementaryCoordinatePartialW,
      leadingElementaryCoordinatePartialDelta, elementaryComponentCoefficient,
      elementaryComponentOrder, elementaryWeight, componentScale, logRatioLeading,
      branchCenter, gaugeJacobianReal, gaugeJacobian, Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three]

/-- Every limiting-Jacobian entry varies by at most `2e-5` on the exact
inner box. -/
theorem leadingElementaryJacobian_innerBox_entry_error
    {y : BranchPoint} (hy : y ∈ branchInnerBox) (i j : Fin 4) :
    |leadingElementaryJacobian y i j - gaugeJacobianReal i j| ≤ 1 / 50000 := by
  have ho := branchInnerBox_subset_outer hy
  rcases ho with ⟨ha0, _ha1, ht0, _ht1, _hw0, _hw1, _hd0, _hd1⟩
  have ha := branchInnerBox_coordinate_error hy 0
  have ht := branchInnerBox_coordinate_error hy 1
  have hw := branchInnerBox_coordinate_error hy 2
  simp [branchCenter, branchInnerRadius] at ha ht hw
  have ha' : |y 0 - 3| ≤ (1 / 1000000 : ℝ) := by simpa [one_div] using ha
  have ht' : |y 1 - 2| ≤ (1 / 1000000 : ℝ) := by simpa [one_div] using ht
  have hw' : |y 2 - 16 / 3| ≤ (1 / 1000000 : ℝ) := by simpa [one_div] using hw
  have hA := reciprocalPower_center_error
    (p := 2) (s₀ := 5 / 2) (s := y 0) (c := 3)
    (r := 1 / 1000000) (by norm_num) ha0 (by norm_num) (by norm_num) ha'
  have hT (p : ℕ) := reciprocalPower_center_error
    (p := p) (s₀ := 7 / 4) (s := y 1) (c := 2)
    (r := 1 / 1000000) (by norm_num) ht0 (by norm_num) (by norm_num) ht'
  have hWT (p : ℕ) := mul_reciprocalPower_center_error
    (p := p) (s₀ := 7 / 4) (s := y 1) (c := 2)
    (w := y 2) (w₀ := 16 / 3) (rs := 1 / 1000000)
    (rw := 1 / 1000000) (by norm_num) ht0 (by norm_num)
    (by norm_num) (by norm_num) ht' hw'
  fin_cases i <;> fin_cases j
  all_goals
    norm_num [leadingElementaryJacobian, leadingElementaryCoordinatePartialAlpha,
      leadingElementaryCoordinatePartialT, leadingElementaryCoordinatePartialW,
      leadingElementaryCoordinatePartialDelta, elementaryComponentCoefficient,
      elementaryComponentOrder, elementaryWeight, componentScale, logRatioLeading,
      gaugeJacobianReal, gaugeJacobian, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.cons_val_three] at ⊢
  all_goals simp only [← inv_pow] at ⊢
  · change |-((y 0)⁻¹ ^ 2) + 1 / 9| ≤ 1 / 50000
    rw [show -((y 0)⁻¹ ^ 2) + 1 / 9 =
      -((y 0)⁻¹ ^ 2 - (3 : ℝ)⁻¹ ^ 2) by norm_num; ring, abs_neg]
    exact hA.trans (by norm_num)
  · have h := hWT 3
    rw [show -(2 * y 2 * (y 1)⁻¹ ^ 3) + 4 / 3 =
        -2 * (y 2 * (y 1)⁻¹ ^ 3 - (16 / 3) * (2 : ℝ)⁻¹ ^ 3) by
      norm_num; ring,
      abs_mul, abs_neg, abs_of_nonneg (by norm_num : 0 ≤ (2 : ℝ))]
    exact (mul_le_mul_of_nonneg_left h (by norm_num)).trans (by norm_num)
  · change |(y 1)⁻¹ ^ 2 - 1 / 4| ≤ 1 / 50000
    have h := hT 2
    norm_num at h
    calc
      |(y 1)⁻¹ ^ 2 - 1 / 4| ≤ 2 / 5359375 := by simpa [← inv_pow] using h
      _ ≤ 1 / 50000 := by norm_num
  · have h := hWT 4
    rw [show -(1 / 2 * (6 * y 2 * (y 1)⁻¹ ^ 4)) + 1 =
        -3 * (y 2 * (y 1)⁻¹ ^ 4 - (16 / 3) * (2 : ℝ)⁻¹ ^ 4) by
      norm_num; ring,
      abs_mul, abs_neg, abs_of_nonneg (by norm_num : 0 ≤ (3 : ℝ))]
    exact (mul_le_mul_of_nonneg_left h (by norm_num)).trans (by norm_num)
  · rw [show 1 / 2 * (2 * (y 1)⁻¹ ^ 3) - 1 / 8 =
      (y 1)⁻¹ ^ 3 - 1 / 8 by ring]
    have h := hT 3
    norm_num at h
    calc
      |(y 1)⁻¹ ^ 3 - 1 / 8| ≤ 12 / 37515625 := by simpa [← inv_pow] using h
      _ ≤ 1 / 50000 := by norm_num
  · have h := hWT 5
    rw [show -(12 * y 2 * (y 1)⁻¹ ^ 5) + 2 =
        -12 * (y 2 * (y 1)⁻¹ ^ 5 - (16 / 3) * (2 : ℝ)⁻¹ ^ 5) by
      norm_num; ring,
      abs_mul, abs_neg, abs_of_nonneg (by norm_num : 0 ≤ (12 : ℝ))]
    exact (mul_le_mul_of_nonneg_left h (by norm_num)).trans (by norm_num)
  · have h := hT 4
    change |3 * (y 1)⁻¹ ^ 4 - 3 / 16| ≤ 1 / 50000
    rw [show 3 * (y 1)⁻¹ ^ 4 - 3 / 16 =
        3 * ((y 1)⁻¹ ^ 4 - (2 : ℝ)⁻¹ ^ 4) by norm_num; ring,
      abs_mul, abs_of_nonneg (by norm_num : 0 ≤ (3 : ℝ))]
    exact (mul_le_mul_of_nonneg_left h (by norm_num)).trans (by norm_num)
  · have h := hWT 6
    rw [show -(20 * y 2 * (y 1)⁻¹ ^ 6) + 5 / 3 =
        -20 * (y 2 * (y 1)⁻¹ ^ 6 - (16 / 3) * (2 : ℝ)⁻¹ ^ 6) by
      norm_num; ring,
      abs_mul, abs_neg, abs_of_nonneg (by norm_num : 0 ≤ (20 : ℝ))]
    exact (mul_le_mul_of_nonneg_left h (by norm_num)).trans (by norm_num)
  · have h := hT 5
    change |4 * (y 1)⁻¹ ^ 5 - 1 / 8| ≤ 1 / 50000
    rw [show 4 * (y 1)⁻¹ ^ 5 - 1 / 8 =
        4 * ((y 1)⁻¹ ^ 5 - (2 : ℝ)⁻¹ ^ 5) by norm_num; ring,
      abs_mul, abs_of_nonneg (by norm_num : 0 ≤ (4 : ℝ))]
    exact (mul_le_mul_of_nonneg_left h (by norm_num)).trans (by norm_num)

/-- Operator-norm form of the whole inner-box variation estimate. -/
theorem leadingElementaryJacobian_innerBox_operator_error
    {y : BranchPoint} (hy : y ∈ branchInnerBox) :
    ‖branchMatrixCLM (leadingElementaryJacobian y) -
        branchMatrixCLM gaugeJacobianReal‖ ≤ 1 / 12500 := by
  have h := branchMatrixCLM_sub_norm_le_of_entrywise
    (C := (1 / 50000 : ℝ)) (by norm_num)
    (leadingElementaryJacobian_innerBox_entry_error hy)
  norm_num at h ⊢
  exact h

end

end Zeta23.Research.JensenWedge
