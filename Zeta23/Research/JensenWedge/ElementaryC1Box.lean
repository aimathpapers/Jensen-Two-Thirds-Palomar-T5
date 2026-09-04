import Zeta23.Research.JensenWedge.ElementaryJacobianAssembly

/-!
# Fixed-box elementary `C¹` bounds

This module instantiates the componentwise value and Jacobian estimates on
the manuscript's exact rational outer box.  The constants are deliberately
coarse rational envelopes suitable for the downstream interval certificate.
-/

namespace Zeta23.Research.JensenWedge

noncomputable section

theorem elementaryScale_comparisons
    {e x : ℝ} (he : 0 < e) (he1 : e ≤ 1) (hx : 0 ≤ x) :
    x * e ≤ x ∧ x ≤ x / e ∧ e ^ 2 ≤ e ∧ e ^ 3 ≤ e := by
  have hxe : x * e ≤ x := by nlinarith
  have hxdiv : x ≤ x / e := (le_div_iff₀ he).2 hxe
  have he2 : e ^ 2 ≤ e := by nlinarith
  have he3 : e ^ 3 ≤ e := by
    calc
      e ^ 3 = e * e ^ 2 := by ring
      _ ≤ e * e := mul_le_mul_of_nonneg_left he2 he.le
      _ = e ^ 2 := by ring
      _ ≤ e := he2
  exact ⟨hxe, hxdiv, he2, he3⟩

set_option maxHeartbeats 1000000 in
/-- Uniform value bound on the fixed outer parameter box. -/
theorem exactElementaryParameterMap_outerBox_value_error
    {y : BranchPoint} (hy : InOuterParameterBox y)
    {e x : ℝ} (he : 0 < e) (he1 : e ≤ 1) (hx : 0 ≤ x)
    (j : Fin 4) :
    |exactElementaryParameterMap y x e j -
        leadingElementaryParameterMap y j| ≤
      10000 * (e + x / e) := by
  rcases hy with ⟨ha0, _ha1, ht0, _ht1, hw0, hw1, hd0, hd1⟩
  have hraw := elementaryCoordinateComponent_value_error
    (j := j) (alpha₀ := 5 / 2) (t₀ := 7 / 4)
    (alpha := y 0) (t := y 1) (w := y 2) (delta := y 3)
    (e := e) (x := x) (by norm_num) ha0 (by norm_num) ht0
    (by linarith) (by linarith) he hx
  have hs := elementaryScale_comparisons he he1 hx
  rw [elementaryCoordinateComponent_eq_exact he.ne',
    leadingElementaryCoordinateComponent_eq_map] at hraw
  refine hraw.trans ?_
  rcases hs with ⟨hxe, hxdiv, he2, he3⟩
  have hw_nonneg : 0 ≤ y 2 := by linarith
  have hd_nonneg : 0 ≤ y 3 := by linarith
  have hwx : y 2 * x ≤ 6 * x :=
    mul_le_mul_of_nonneg_right hw1 hx
  have hdx : y 3 * x ≤ (5 / 12 : ℝ) * x :=
    mul_le_mul_of_nonneg_right hd1 hx
  have hwe : y 2 * e ≤ 6 * e :=
    mul_le_mul_of_nonneg_right hw1 he.le
  have hde : y 3 * e ≤ (5 / 12 : ℝ) * e :=
    mul_le_mul_of_nonneg_right hd1 he.le
  have hw2 : y 2 * y 2 ≤ (36 : ℝ) := by
    have h := mul_self_le_mul_self hw_nonneg hw1
    norm_num at h
    exact h
  have hd2 : y 3 * y 3 ≤ (25 / 144 : ℝ) := by
    have h := mul_self_le_mul_self hd_nonneg hd1
    norm_num at h
    exact h
  have hw2e : y 2 * y 2 * e ≤ 36 * e :=
    mul_le_mul_of_nonneg_right hw2 he.le
  have hd2e : y 3 * y 3 * e ≤ (25 / 144 : ℝ) * e :=
    mul_le_mul_of_nonneg_right hd2 he.le
  fin_cases j <;>
    norm_num [elementaryRemoteErrorBound, elementaryComponentOrder,
      elementaryComponentCoefficient, elementaryWeight, componentScale,
      logRatioLeading] at hraw ⊢ <;>
    nlinarith [div_nonneg hx he.le]

set_option maxHeartbeats 1000000 in
/-- Uniform entrywise Jacobian bound on the same box. -/
theorem exactElementaryJacobian_outerBox_entry_error
    {y : BranchPoint} (hy : InOuterParameterBox y)
    {e x : ℝ} (he : 0 < e) (he1 : e ≤ 1) (hx : 0 ≤ x)
    (j k : Fin 4) :
    |exactElementaryJacobian y e x j k -
        leadingElementaryJacobian y j k| ≤
      10000 * (e + x) := by
  rcases hy with ⟨ha0, _ha1, ht0, _ht1, hw0, hw1, hd0, hd1⟩
  have hraw := exactElementaryJacobian_entry_error
    (j := j) (k := k) (y := y) (alpha₀ := 5 / 2) (t₀ := 7 / 4)
    (e := e) (x := x) (by norm_num) ha0 (by norm_num) ht0
    (by linarith) (by linarith) he hx
  have hs := elementaryScale_comparisons he he1 hx
  refine hraw.trans ?_
  rcases hs with ⟨hxe, _hxdiv, he2, he3⟩
  have hw_nonneg : 0 ≤ y 2 := by linarith
  have hd_nonneg : 0 ≤ y 3 := by linarith
  have hwx : y 2 * x ≤ 6 * x :=
    mul_le_mul_of_nonneg_right hw1 hx
  have hdx : y 3 * x ≤ (5 / 12 : ℝ) * x :=
    mul_le_mul_of_nonneg_right hd1 hx
  have hwe : y 2 * e ≤ 6 * e :=
    mul_le_mul_of_nonneg_right hw1 he.le
  have hde : y 3 * e ≤ (5 / 12 : ℝ) * e :=
    mul_le_mul_of_nonneg_right hd1 he.le
  have hw2 : y 2 * y 2 ≤ (36 : ℝ) := by
    have h := mul_self_le_mul_self hw_nonneg hw1
    norm_num at h
    exact h
  have hd2 : y 3 * y 3 ≤ (25 / 144 : ℝ) := by
    have h := mul_self_le_mul_self hd_nonneg hd1
    norm_num at h
    exact h
  have hw2e : y 2 * y 2 * e ≤ 36 * e :=
    mul_le_mul_of_nonneg_right hw2 he.le
  have hd2e : y 3 * y 3 * e ≤ (25 / 144 : ℝ) * e :=
    mul_le_mul_of_nonneg_right hd2 he.le
  fin_cases j <;> fin_cases k <;>
    norm_num [elementaryJacobianEntryErrorBound,
      elementaryRemoteDerivativeErrorBound, elementaryComponentOrder,
      elementaryComponentCoefficient, elementaryWeight, componentScale,
      logRatioLeading] at hraw ⊢ <;>
    nlinarith

end

end Zeta23.Research.JensenWedge
