import Zeta23.Research.JensenWedge.ElementaryAlphaDifferential

/-!
# Elementary Jacobian assembly

This module assembles the four scalar partial derivatives into exact and
limiting Jacobian matrices and proves their entrywise error certificate.
-/

namespace Zeta23.Research.JensenWedge

noncomputable section

def exactElementaryJacobian
    (y : BranchPoint) (e x : ℝ) : Matrix (Fin 4) (Fin 4) ℝ :=
  fun j k => ![
    elementaryCoordinatePartialAlpha j (y 0) e x,
    elementaryCoordinatePartialT j (y 1) (y 2) e x,
    elementaryCoordinatePartialW j (y 1) (y 2) e x,
    elementaryCoordinatePartialDelta j (y 3) e x
  ] k

def leadingElementaryJacobian
    (y : BranchPoint) : Matrix (Fin 4) (Fin 4) ℝ :=
  fun j k => ![
    leadingElementaryCoordinatePartialAlpha j (y 0),
    leadingElementaryCoordinatePartialT j (y 1) (y 2),
    leadingElementaryCoordinatePartialW j (y 1),
    leadingElementaryCoordinatePartialDelta j
  ] k

/-- Every exact Jacobian row is produced by the four independently proved
scalar partial derivatives. -/
theorem elementaryCoordinateComponent_has_all_partials
    {j : Fin 4} {alpha t w delta e x : ℝ}
    (halpha : 0 < alpha) (ht : 0 < t) (hw : 0 ≤ w)
    (hdelta : 0 ≤ delta) (he : 0 < e) (hx : 0 ≤ x) :
    HasDerivAt (fun a => elementaryCoordinateComponent j a t w delta e x)
        (elementaryCoordinatePartialAlpha j alpha e x) alpha ∧
      HasDerivAt (fun v => elementaryCoordinateComponent j alpha v w delta e x)
        (elementaryCoordinatePartialT j t w e x) t ∧
      HasDerivAt (fun v => elementaryCoordinateComponent j alpha t v delta e x)
        (elementaryCoordinatePartialW j t w e x) w ∧
      HasDerivAt (fun v => elementaryCoordinateComponent j alpha t w v e x)
        (elementaryCoordinatePartialDelta j delta e x) delta := by
  exact ⟨hasDerivAt_elementaryCoordinateComponent_alpha halpha hx he,
    hasDerivAt_elementaryCoordinateComponent_t ht hw he hx,
    hasDerivAt_elementaryCoordinateComponent_w ht hw he hx,
    hasDerivAt_elementaryCoordinateComponent_delta hdelta he hx⟩

def elementaryJacobianEntryErrorBound
    (j k : Fin 4) (alpha₀ t₀ w delta e x : ℝ) : ℝ :=
  ![
    elementaryRemoteDerivativeErrorBound j alpha₀ e x,
    |elementaryComponentCoefficient j| *
      (w * ((elementaryComponentOrder j : ℝ) *
        (elementaryComponentOrder j + 1) *
        (elementaryComponentOrder j + 2) *
        ((elementaryComponentOrder j : ℝ) * x + w * e) *
        t₀⁻¹ ^ (elementaryComponentOrder j + 3))),
    |elementaryComponentCoefficient j| *
      ((elementaryComponentOrder j : ℝ) *
        (elementaryComponentOrder j + 1) *
        ((elementaryComponentOrder j : ℝ) * x + w * e) *
        t₀⁻¹ ^ (elementaryComponentOrder j + 2)),
    |elementaryComponentCoefficient j| *
      ((elementaryComponentOrder j : ℝ) *
        (elementaryComponentOrder j + 1) *
        ((elementaryComponentOrder j : ℝ) * x + delta * e))
  ] k

/-- Unified entrywise Jacobian error before fixed-box arithmetic. -/
theorem exactElementaryJacobian_entry_error
    {j k : Fin 4} {y : BranchPoint} {alpha₀ t₀ e x : ℝ}
    (halpha₀ : 0 < alpha₀) (halpha : alpha₀ ≤ y 0)
    (ht₀ : 0 < t₀) (ht : t₀ ≤ y 1) (hw : 0 ≤ y 2)
    (hdelta : 0 ≤ y 3) (he : 0 < e) (hx : 0 ≤ x) :
    |exactElementaryJacobian y e x j k -
        leadingElementaryJacobian y j k| ≤
      elementaryJacobianEntryErrorBound j k alpha₀ t₀ (y 2) (y 3) e x := by
  fin_cases k
  · simpa [exactElementaryJacobian, leadingElementaryJacobian,
      elementaryJacobianEntryErrorBound] using
      (elementaryCoordinatePartialAlpha_error
        (j := j) halpha₀ halpha he.le hx)
  · simpa [exactElementaryJacobian, leadingElementaryJacobian,
      elementaryJacobianEntryErrorBound] using
      (elementaryCoordinatePartialT_error
        (j := j) ht₀ ht hw he hx)
  · simpa [exactElementaryJacobian, leadingElementaryJacobian,
      elementaryJacobianEntryErrorBound] using
      (elementaryCoordinatePartialW_error
        (j := j) ht₀ ht hw he.le hx)
  · simpa [exactElementaryJacobian, leadingElementaryJacobian,
      elementaryJacobianEntryErrorBound] using
      (elementaryCoordinatePartialDelta_error
        (j := j) hdelta he.le hx)

end

end Zeta23.Research.JensenWedge
