import Zeta23.Research.JensenWedge.ElementaryComponentDifferential

/-!
# Elementary component value certificate

This module proves the value half of the elementary `C¹` estimate directly
from the three exact boundary terms.  The unique surviving remote limit and
the gamma half-shift error remain explicit.
-/

namespace Zeta23.Research.JensenWedge

noncomputable section

/-- Only the zeroth component retains a remote-boundary limit. -/
def elementaryRemoteLimit (j : Fin 4) (alpha : ℝ) : ℝ :=
  if j = 0 then alpha⁻¹ else 0

/-- The limiting scalar component in order-indexed form. -/
def leadingElementaryCoordinateComponent
    (j : Fin 4) (alpha t w delta : ℝ) : ℝ :=
  elementaryComponentCoefficient j *
    (elementaryRemoteLimit j alpha +
      (elementaryComponentOrder j : ℝ) * w *
        t⁻¹ ^ (elementaryComponentOrder j + 1) +
      (elementaryComponentOrder j : ℝ) * delta)

theorem leadingElementaryCoordinateComponent_eq_map
    (j : Fin 4) (y : BranchPoint) :
    leadingElementaryCoordinateComponent j (y 0) (y 1) (y 2) (y 3) =
      leadingElementaryParameterMap y j := by
  fin_cases j <;>
    norm_num [leadingElementaryCoordinateComponent, elementaryRemoteLimit,
      elementaryComponentCoefficient, elementaryComponentOrder,
      leadingElementaryParameterMap, elementaryWeight, componentScale,
      logRatioLeading, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.cons_val_three, div_eq_mul_inv] <;> ring

/-- Explicit case-split remote-boundary error. -/
def elementaryRemoteErrorBound
    (j : Fin 4) (alpha₀ e x : ℝ) : ℝ :=
  if j = 0 then x * e * alpha₀⁻¹ ^ 2
  else e ^ (elementaryComponentOrder j - 1) *
    alpha₀⁻¹ ^ elementaryComponentOrder j

theorem elementaryRemoteTerm_limit_error
    {j : Fin 4} {alpha alpha₀ e x : ℝ}
    (halpha₀ : 0 < alpha₀) (halpha : alpha₀ ≤ alpha)
    (he : 0 ≤ e) (hx : 0 ≤ x) :
    |elementaryRemoteTerm (elementaryComponentOrder j) alpha e x -
        elementaryRemoteLimit j alpha| ≤
      elementaryRemoteErrorBound j alpha₀ e x := by
  fin_cases j
  · simpa [elementaryRemoteTerm, elementaryRemoteLimit,
      elementaryRemoteErrorBound, elementaryComponentOrder] using
      elementaryPhi_remote_q1_error halpha₀ halpha hx he
  · simpa [elementaryRemoteTerm, elementaryRemoteLimit,
      elementaryRemoteErrorBound, elementaryComponentOrder] using
      (abs_elementaryPhi_remote_le (q := 2) halpha₀ halpha hx he)
  · simpa [elementaryRemoteTerm, elementaryRemoteLimit,
      elementaryRemoteErrorBound, elementaryComponentOrder] using
      (abs_elementaryPhi_remote_le (q := 3) halpha₀ halpha hx he)
  · simpa [elementaryRemoteTerm, elementaryRemoteLimit,
      elementaryRemoteErrorBound, elementaryComponentOrder] using
      (abs_elementaryPhi_remote_le (q := 4) halpha₀ halpha hx he)

/-- Full explicit value estimate before finite-box instantiation. -/
theorem elementaryCoordinateComponent_value_error
    {j : Fin 4} {alpha alpha₀ t t₀ w delta e x : ℝ}
    (halpha₀ : 0 < alpha₀) (halpha : alpha₀ ≤ alpha)
    (ht₀ : 0 < t₀) (ht : t₀ ≤ t) (hw : 0 ≤ w)
    (hdelta : 0 ≤ delta) (he : 0 < e) (hx : 0 ≤ x) :
    |elementaryCoordinateComponent j alpha t w delta e x -
        leadingElementaryCoordinateComponent j alpha t w delta| ≤
      |elementaryComponentCoefficient j| *
        (elementaryRemoteErrorBound j alpha₀ e x +
          w * ((elementaryComponentOrder j : ℝ) *
            (elementaryComponentOrder j + 1) *
            ((elementaryComponentOrder j : ℝ) * x + w * e) *
            t₀⁻¹ ^ (elementaryComponentOrder j + 2)) +
          ((elementaryComponentOrder j : ℝ) * (x / e) +
            delta * ((elementaryComponentOrder j : ℝ) *
              (elementaryComponentOrder j + 1) *
              ((elementaryComponentOrder j : ℝ) * x + delta * e)))) := by
  let q := elementaryComponentOrder j
  let R := elementaryRemoteTerm q alpha e x
  let R₀ := elementaryRemoteLimit j alpha
  let P := elementaryPairedTerm q t w e x
  let P₀ := (q : ℝ) * w * t⁻¹ ^ (q + 1)
  let G := elementaryGammaBoundaryTerm q delta e x
  let G₀ := (q : ℝ) * delta
  let BP := w * ((q : ℝ) * (q + 1) * ((q : ℝ) * x + w * e) *
    t₀⁻¹ ^ (q + 2))
  let BG := (q : ℝ) * (x / e) +
    delta * ((q : ℝ) * (q + 1) * ((q : ℝ) * x + delta * e))
  have hR : |R - R₀| ≤ elementaryRemoteErrorBound j alpha₀ e x := by
    exact elementaryRemoteTerm_limit_error halpha₀ halpha he.le hx
  have hP : |P - P₀| ≤ BP := by
    exact elementaryPhi_paired_value_error ht₀ ht hw he hx
  have hG : |G - G₀| ≤ BG := by
    exact elementaryPhi_boundary_value_error hdelta he hx
  rw [elementaryCoordinateComponent, leadingElementaryCoordinateComponent,
    show elementaryComponentCoefficient j * (R + P + G) -
        elementaryComponentCoefficient j * (R₀ + P₀ + G₀) =
      elementaryComponentCoefficient j *
        ((R - R₀) + (P - P₀) + (G - G₀)) by ring,
    abs_mul]
  apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
  calc
    |(R - R₀) + (P - P₀) + (G - G₀)| ≤
        |(R - R₀) + (P - P₀)| + |G - G₀| := abs_add_le _ _
    _ ≤ (|R - R₀| + |P - P₀|) + |G - G₀| :=
      add_le_add (abs_add_le _ _) (le_refl _)
    _ = |R - R₀| + |P - P₀| + |G - G₀| := rfl
    _ ≤ elementaryRemoteErrorBound j alpha₀ e x + BP + BG :=
      add_le_add (add_le_add hR hP) hG
    _ = elementaryRemoteErrorBound j alpha₀ e x +
          w * ((elementaryComponentOrder j : ℝ) *
            (elementaryComponentOrder j + 1) *
            ((elementaryComponentOrder j : ℝ) * x + w * e) *
            t₀⁻¹ ^ (elementaryComponentOrder j + 2)) +
          ((elementaryComponentOrder j : ℝ) * (x / e) +
            delta * ((elementaryComponentOrder j : ℝ) *
              (elementaryComponentOrder j + 1) *
              ((elementaryComponentOrder j : ℝ) * x + delta * e))) := by
      rfl

end

end Zeta23.Research.JensenWedge
