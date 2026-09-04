import Zeta23.Research.JensenWedge.ElementaryBoundaryEstimates

/-!
# Elementary parameter derivatives

This module packages the three exact elementary boundary terms and proves
their parameter derivatives together with explicit errors from the limiting
map.  It is the derivative half of the elementary `C¹` certificate.
-/

namespace Zeta23.Research.JensenWedge

open MeasureTheory Set

noncomputable section

/-- The normalized remote `A` boundary before the component coefficient. -/
def elementaryRemoteTerm (q : ℕ) (alpha e x : ℝ) : ℝ :=
  e ^ (q - 1) * elementaryPhi q alpha (x * e)

/-- The normalized paired `B-C` boundary before the component coefficient. -/
def elementaryPairedTerm (q : ℕ) (t w e x : ℝ) : ℝ :=
  (elementaryPhi q t x - elementaryPhi q (t + w * e) x) / e

/-- The normalized paired `D`/gamma boundary before the component coefficient. -/
def elementaryGammaBoundaryTerm (q : ℕ) (delta e x : ℝ) : ℝ :=
  (elementaryPhi q (1 + x / 2) x -
    elementaryPhi q (1 + delta * e) x) / e

/-- The exact elementary component is the component coefficient times the
sum of its three normalized boundary terms. -/
theorem exactElementaryParameterComponent_eq_boundaryTerms
    {j : Fin 4} {y : BranchPoint} {x e : ℝ} (he : e ≠ 0) :
    exactElementaryParameterComponent j y x e =
      elementaryComponentCoefficient j *
        (elementaryRemoteTerm (elementaryComponentOrder j) (y 0) e x +
          elementaryPairedTerm (elementaryComponentOrder j) (y 1) (y 2) e x +
          elementaryGammaBoundaryTerm (elementaryComponentOrder j) (y 3) e x) := by
  fin_cases j <;>
    norm_num [exactElementaryParameterComponent, elementaryComponentOrder,
      elementaryRemoteTerm, elementaryPairedTerm, elementaryGammaBoundaryTerm] <;>
    field_simp [he] <;> ring

/-- Exact derivative of the remote boundary in `alpha`. -/
theorem hasDerivAt_elementaryRemoteTerm_alpha
    {q : ℕ} {alpha e x : ℝ}
    (halpha : 0 < alpha) (hx : 0 ≤ x) (he : 0 ≤ e) :
    HasDerivAt (fun a => elementaryRemoteTerm q a e x)
      (e ^ (q - 1) * elementaryPhiD1 q alpha (x * e)) alpha := by
  simpa only [elementaryRemoteTerm] using
    (hasDerivAt_elementaryPhi (q := q) halpha (mul_nonneg hx he)).const_mul
      (e ^ (q - 1))

/-- In the surviving remote coordinate `q=1`, the alpha derivative has the
explicit reciprocal-square error. -/
theorem elementaryRemoteTerm_alpha_q1_error
    {alpha alpha₀ e x : ℝ}
    (halpha₀ : 0 < alpha₀) (halpha : alpha₀ ≤ alpha)
    (hx : 0 ≤ x) (he : 0 ≤ e) :
    |elementaryPhiD1 1 alpha (x * e) - (-alpha⁻¹ ^ 2)| ≤
      2 * x * e * alpha₀⁻¹ ^ 3 := by
  have h := elementaryPhiD1_firstOrder_error
    (q := 1) halpha₀ halpha (mul_nonneg hx he)
  norm_num at h ⊢
  simpa [mul_assoc] using h

/-- Uniformly averaging the displaced second derivative retains the same
explicit error. -/
theorem elementaryPhiD2_average_base_error
    {q : ℕ} {t t₀ w e x : ℝ}
    (ht₀ : 0 < t₀) (ht : t₀ ≤ t) (hw : 0 ≤ w)
    (he : 0 ≤ e) (hx : 0 ≤ x) :
    |(∫ u in Set.Icc (0 : ℝ) 1,
        elementaryPhiD2 q (t + u * (w * e)) x) -
        ((q : ℝ) * (q + 1) * t⁻¹ ^ (q + 2))| ≤
      (q : ℝ) * (q + 1) * (q + 2) *
        ((q : ℝ) * x + w * e) * t₀⁻¹ ^ (q + 3) := by
  let f : ℝ → ℝ := fun u => elementaryPhiD2 q (t + u * (w * e)) x
  have hfcont : ContinuousOn f (Set.Icc (0 : ℝ) 1) := by
    intro u hu
    have hh : 0 ≤ u * (w * e) := mul_nonneg hu.1 (mul_nonneg hw he)
    have hpos : 0 < t + u * (w * e) := by linarith
    have hinner : HasDerivAt (fun v : ℝ => t + v * (w * e)) (w * e) u := by
      simpa [mul_comm] using ((hasDerivAt_id u).mul_const (w * e)).const_add t
    have hcomp := (hasDerivAt_elementaryCubeIntegral
      (q := q) (p := q + 2) hpos hx).comp u hinner
    have hc : ContinuousAt
        (fun v : ℝ => elementaryCubeIntegral q (q + 2)
          (t + v * (w * e)) x) u := by
      simpa [Function.comp_def] using hcomp.continuousAt
    have hcoef : ContinuousAt
        (fun v : ℝ => (q : ℝ) * (q + 1) *
          elementaryCubeIntegral q (q + 2) (t + v * (w * e)) x) u := by
      fun_prop
    simpa [f, elementaryPhiD2] using hcoef.continuousWithinAt
  apply abs_integral_Icc_zero_one_sub_const_le
    (hfcont.integrableOn_compact isCompact_Icc)
  intro u hu
  have huwe : 0 ≤ u * (w * e) :=
    mul_nonneg hu.1 (mul_nonneg hw he)
  have huwe_le : u * (w * e) ≤ w * e := by
    have hwe : 0 ≤ w * e := mul_nonneg hw he
    nlinarith [mul_le_mul_of_nonneg_right hu.2 hwe]
  have hraw := elementaryPhiD2_base_error
    (q := q) ht₀ ht huwe hx
  change |f u - ((q : ℝ) * (q + 1) * t⁻¹ ^ (q + 2))| ≤ _
  calc
    |f u - ((q : ℝ) * (q + 1) * t⁻¹ ^ (q + 2))| ≤
        (q : ℝ) * (q + 1) * (q + 2) *
          ((q : ℝ) * x + u * (w * e)) * t₀⁻¹ ^ (q + 3) := hraw
    _ ≤ (q : ℝ) * (q + 1) * (q + 2) *
          ((q : ℝ) * x + w * e) * t₀⁻¹ ^ (q + 3) := by
      gcongr

/-- Exact derivative of the paired term in `w`. -/
theorem hasDerivAt_elementaryPairedTerm_w
    {q : ℕ} {t w e x : ℝ}
    (ht : 0 < t) (hw : 0 ≤ w) (he : 0 < e) (hx : 0 ≤ x) :
    HasDerivAt (fun v => elementaryPairedTerm q t v e x)
      (-elementaryPhiD1 q (t + w * e) x) w := by
  simpa only [elementaryPairedTerm] using
    hasDerivAt_elementaryPhi_paired_w (q := q) ht hw he hx

/-- The `w` derivative converges to the derivative of the rational leading
map with an explicit `O(x+e)` error. -/
theorem elementaryPairedTerm_w_error
    {q : ℕ} {t t₀ w e x : ℝ}
    (ht₀ : 0 < t₀) (ht : t₀ ≤ t) (hw : 0 ≤ w)
    (he : 0 ≤ e) (hx : 0 ≤ x) :
    |-elementaryPhiD1 q (t + w * e) x -
        (q : ℝ) * t⁻¹ ^ (q + 1)| ≤
      (q : ℝ) * (q + 1) * ((q : ℝ) * x + w * e) *
        t₀⁻¹ ^ (q + 2) := by
  have h := elementaryPhiD1_base_error
    (q := q) ht₀ ht (mul_nonneg hw he) hx
  rw [show -elementaryPhiD1 q (t + w * e) x -
      (q : ℝ) * t⁻¹ ^ (q + 1) =
    -(elementaryPhiD1 q (t + w * e) x -
      (-(q : ℝ) * t⁻¹ ^ (q + 1))) by ring, abs_neg]
  exact h

/-- Exact derivative of the paired term in `t`. -/
theorem hasDerivAt_elementaryPairedTerm_t
    {q : ℕ} {t w e x : ℝ}
    (ht : 0 < t) (hw : 0 ≤ w) (he : 0 < e) (hx : 0 ≤ x) :
    HasDerivAt (fun v => elementaryPairedTerm q v w e x)
      ((elementaryPhiD1 q t x -
        elementaryPhiD1 q (t + w * e) x) / e) t := by
  simpa only [elementaryPairedTerm] using
    hasDerivAt_elementaryPhi_paired_t (q := q) ht hw he hx

/-- The `t` derivative converges to the derivative of the rational leading
map with an explicit `O(x+e)` error. -/
theorem elementaryPairedTerm_t_error
    {q : ℕ} {t t₀ w e x : ℝ}
    (ht₀ : 0 < t₀) (ht : t₀ ≤ t) (hw : 0 ≤ w)
    (he : 0 < e) (hx : 0 ≤ x) :
    |(elementaryPhiD1 q t x -
          elementaryPhiD1 q (t + w * e) x) / e -
        (-(q : ℝ) * (q + 1) * w * t⁻¹ ^ (q + 2))| ≤
      w * ((q : ℝ) * (q + 1) * (q + 2) *
        ((q : ℝ) * x + w * e) * t₀⁻¹ ^ (q + 3)) := by
  have hseg := elementaryPhiD1_add_sub_eq_segment
    (q := q) (s := t) (h := w * e) (z := x)
    (ht₀.trans_le ht) (mul_nonneg hw he.le) hx
  have havg := elementaryPhiD2_average_base_error
    (q := q) ht₀ ht hw he.le hx
  rw [show (elementaryPhiD1 q t x -
      elementaryPhiD1 q (t + w * e) x) / e =
      -w * ∫ u in Set.Icc (0 : ℝ) 1,
        elementaryPhiD2 q (t + u * (w * e)) x by
      rw [show elementaryPhiD1 q t x -
          elementaryPhiD1 q (t + w * e) x =
        -(elementaryPhiD1 q (t + w * e) x -
          elementaryPhiD1 q t x) by ring, hseg]
      field_simp [ne_of_gt he]]
  rw [show -w * (∫ u in Set.Icc (0 : ℝ) 1,
      elementaryPhiD2 q (t + u * (w * e)) x) -
        (-(q : ℝ) * (q + 1) * w * t⁻¹ ^ (q + 2)) =
      -w * ((∫ u in Set.Icc (0 : ℝ) 1,
        elementaryPhiD2 q (t + u * (w * e)) x) -
          ((q : ℝ) * (q + 1) * t⁻¹ ^ (q + 2))) by ring,
    abs_mul, abs_neg, abs_of_nonneg hw]
  exact mul_le_mul_of_nonneg_left havg hw

/-- Exact derivative of the paired gamma boundary in `delta`. -/
theorem hasDerivAt_elementaryGammaBoundaryTerm_delta
    {q : ℕ} {delta e x : ℝ}
    (hdelta : 0 ≤ delta) (he : 0 < e) (hx : 0 ≤ x) :
    HasDerivAt (fun v => elementaryGammaBoundaryTerm q v e x)
      (-elementaryPhiD1 q (1 + delta * e) x) delta := by
  have hpos : 0 < 1 + delta * e := by positivity
  have hinner : HasDerivAt (fun v : ℝ => 1 + v * e) e delta := by
    simpa [mul_comm] using ((hasDerivAt_id delta).mul_const e).const_add 1
  have hright := (hasDerivAt_elementaryPhi (q := q) hpos hx).comp delta hinner
  have hraw := ((hasDerivAt_const delta
    (elementaryPhi q (1 + x / 2) x)).sub hright).div_const e
  have htyped : HasDerivAt (fun v => elementaryGammaBoundaryTerm q v e x)
      ((0 - elementaryPhiD1 q (1 + delta * e) x * e) / e) delta := by
    simpa [elementaryGammaBoundaryTerm, Function.comp_def] using hraw
  apply htyped.congr_deriv
  field_simp [ne_of_gt he]
  ring

/-- The `delta` derivative converges to the exact integer boundary weight. -/
theorem elementaryGammaBoundaryTerm_delta_error
    {q : ℕ} {delta e x : ℝ}
    (hdelta : 0 ≤ delta) (he : 0 ≤ e) (hx : 0 ≤ x) :
    |-elementaryPhiD1 q (1 + delta * e) x - (q : ℝ)| ≤
      (q : ℝ) * (q + 1) * ((q : ℝ) * x + delta * e) := by
  have h := elementaryPhiD1_base_error
    (q := q) (s₀ := 1) (s := 1) (h := delta * e) (z := x)
    (by norm_num) (by norm_num) (mul_nonneg hdelta he) hx
  simp only [inv_one, one_pow, mul_one] at h
  rw [show -elementaryPhiD1 q (1 + delta * e) x - (q : ℝ) =
    -(elementaryPhiD1 q (1 + delta * e) x - (-(q : ℝ))) by ring,
    abs_neg]
  exact h

end

end Zeta23.Research.JensenWedge
