import Zeta23.Research.JensenWedge.ElementaryParameterDerivatives

/-!
# Exact elementary component differential

The four-variable scalar component in this file is definitionally assembled
from the three exact boundary terms.  Its four partial derivatives are proved
separately, so every entry of the eventual elementary Jacobian has a direct
kernel-checked producer.
-/

namespace Zeta23.Research.JensenWedge

noncomputable section

/-- One exact elementary component with its four branch coordinates exposed
as scalar arguments. -/
def elementaryCoordinateComponent
    (j : Fin 4) (alpha t w delta e x : ℝ) : ℝ :=
  elementaryComponentCoefficient j *
    (elementaryRemoteTerm (elementaryComponentOrder j) alpha e x +
      elementaryPairedTerm (elementaryComponentOrder j) t w e x +
      elementaryGammaBoundaryTerm (elementaryComponentOrder j) delta e x)

/-- The exposed scalar component is exactly the corresponding entry of the
finite elementary parameter map. -/
theorem elementaryCoordinateComponent_eq_exact
    {j : Fin 4} {y : BranchPoint} {e x : ℝ} (he : e ≠ 0) :
    elementaryCoordinateComponent j (y 0) (y 1) (y 2) (y 3) e x =
      exactElementaryParameterComponent j y x e := by
  exact (exactElementaryParameterComponent_eq_boundaryTerms
    (j := j) (y := y) (x := x) (e := e) he).symm

/-- Exact alpha partial derivative. -/
def elementaryCoordinatePartialAlpha
    (j : Fin 4) (alpha e x : ℝ) : ℝ :=
  elementaryComponentCoefficient j *
    (e ^ (elementaryComponentOrder j - 1) *
      elementaryPhiD1 (elementaryComponentOrder j) alpha (x * e))

/-- Exact t partial derivative. -/
def elementaryCoordinatePartialT
    (j : Fin 4) (t w e x : ℝ) : ℝ :=
  elementaryComponentCoefficient j *
    ((elementaryPhiD1 (elementaryComponentOrder j) t x -
      elementaryPhiD1 (elementaryComponentOrder j) (t + w * e) x) / e)

/-- Exact w partial derivative. -/
def elementaryCoordinatePartialW
    (j : Fin 4) (t w e x : ℝ) : ℝ :=
  elementaryComponentCoefficient j *
    (-elementaryPhiD1 (elementaryComponentOrder j) (t + w * e) x)

/-- Exact delta partial derivative. -/
def elementaryCoordinatePartialDelta
    (j : Fin 4) (delta e x : ℝ) : ℝ :=
  elementaryComponentCoefficient j *
    (-elementaryPhiD1 (elementaryComponentOrder j) (1 + delta * e) x)

theorem hasDerivAt_elementaryCoordinateComponent_alpha
    {j : Fin 4} {alpha t w delta e x : ℝ}
    (halpha : 0 < alpha) (hx : 0 ≤ x) (he : 0 < e) :
    HasDerivAt (fun a => elementaryCoordinateComponent j a t w delta e x)
      (elementaryCoordinatePartialAlpha j alpha e x) alpha := by
  have hr := hasDerivAt_elementaryRemoteTerm_alpha
    (q := elementaryComponentOrder j) halpha hx he.le
  have hp := hasDerivAt_const alpha
    (elementaryPairedTerm (elementaryComponentOrder j) t w e x)
  have hg := hasDerivAt_const alpha
    (elementaryGammaBoundaryTerm (elementaryComponentOrder j) delta e x)
  simpa [elementaryCoordinateComponent, elementaryCoordinatePartialAlpha,
    add_assoc] using ((hr.add hp).add hg).const_mul
      (elementaryComponentCoefficient j)

theorem hasDerivAt_elementaryCoordinateComponent_t
    {j : Fin 4} {alpha t w delta e x : ℝ}
    (ht : 0 < t) (hw : 0 ≤ w) (he : 0 < e) (hx : 0 ≤ x) :
    HasDerivAt (fun v => elementaryCoordinateComponent j alpha v w delta e x)
      (elementaryCoordinatePartialT j t w e x) t := by
  have hr := hasDerivAt_const t
    (elementaryRemoteTerm (elementaryComponentOrder j) alpha e x)
  have hp := hasDerivAt_elementaryPairedTerm_t
    (q := elementaryComponentOrder j) ht hw he hx
  have hg := hasDerivAt_const t
    (elementaryGammaBoundaryTerm (elementaryComponentOrder j) delta e x)
  simpa [elementaryCoordinateComponent, elementaryCoordinatePartialT,
    add_assoc] using ((hr.add hp).add hg).const_mul
      (elementaryComponentCoefficient j)

theorem hasDerivAt_elementaryCoordinateComponent_w
    {j : Fin 4} {alpha t w delta e x : ℝ}
    (ht : 0 < t) (hw : 0 ≤ w) (he : 0 < e) (hx : 0 ≤ x) :
    HasDerivAt (fun v => elementaryCoordinateComponent j alpha t v delta e x)
      (elementaryCoordinatePartialW j t w e x) w := by
  have hr := hasDerivAt_const w
    (elementaryRemoteTerm (elementaryComponentOrder j) alpha e x)
  have hp := hasDerivAt_elementaryPairedTerm_w
    (q := elementaryComponentOrder j) ht hw he hx
  have hg := hasDerivAt_const w
    (elementaryGammaBoundaryTerm (elementaryComponentOrder j) delta e x)
  simpa [elementaryCoordinateComponent, elementaryCoordinatePartialW,
    add_assoc] using ((hr.add hp).add hg).const_mul
      (elementaryComponentCoefficient j)

theorem hasDerivAt_elementaryCoordinateComponent_delta
    {j : Fin 4} {alpha t w delta e x : ℝ}
    (hdelta : 0 ≤ delta) (he : 0 < e) (hx : 0 ≤ x) :
    HasDerivAt (fun v => elementaryCoordinateComponent j alpha t w v e x)
      (elementaryCoordinatePartialDelta j delta e x) delta := by
  have hr := hasDerivAt_const delta
    (elementaryRemoteTerm (elementaryComponentOrder j) alpha e x)
  have hp := hasDerivAt_const delta
    (elementaryPairedTerm (elementaryComponentOrder j) t w e x)
  have hg := hasDerivAt_elementaryGammaBoundaryTerm_delta
    (q := elementaryComponentOrder j) hdelta he hx
  simpa [elementaryCoordinateComponent, elementaryCoordinatePartialDelta,
    add_assoc] using ((hr.add hp).add hg).const_mul
      (elementaryComponentCoefficient j)

/-- Leading t partial derivative for the same component. -/
def leadingElementaryCoordinatePartialT (j : Fin 4) (t w : ℝ) : ℝ :=
  elementaryComponentCoefficient j *
    (-(elementaryComponentOrder j : ℝ) *
      (elementaryComponentOrder j + 1) * w *
      t⁻¹ ^ (elementaryComponentOrder j + 2))

/-- Leading w partial derivative for the same component. -/
def leadingElementaryCoordinatePartialW (j : Fin 4) (t : ℝ) : ℝ :=
  elementaryComponentCoefficient j *
    ((elementaryComponentOrder j : ℝ) *
      t⁻¹ ^ (elementaryComponentOrder j + 1))

/-- Leading delta partial derivative for the same component. -/
def leadingElementaryCoordinatePartialDelta (j : Fin 4) : ℝ :=
  elementaryComponentCoefficient j * (elementaryComponentOrder j : ℝ)

/-- Explicit error for the t partial derivative before finite box
instantiation. -/
theorem elementaryCoordinatePartialT_error
    {j : Fin 4} {t t₀ w e x : ℝ}
    (ht₀ : 0 < t₀) (ht : t₀ ≤ t) (hw : 0 ≤ w)
    (he : 0 < e) (hx : 0 ≤ x) :
    |elementaryCoordinatePartialT j t w e x -
        leadingElementaryCoordinatePartialT j t w| ≤
      |elementaryComponentCoefficient j| *
        (w * ((elementaryComponentOrder j : ℝ) *
          (elementaryComponentOrder j + 1) *
          (elementaryComponentOrder j + 2) *
          ((elementaryComponentOrder j : ℝ) * x + w * e) *
          t₀⁻¹ ^ (elementaryComponentOrder j + 3))) := by
  have h := elementaryPairedTerm_t_error
    (q := elementaryComponentOrder j) ht₀ ht hw he hx
  rw [elementaryCoordinatePartialT, leadingElementaryCoordinatePartialT,
    show elementaryComponentCoefficient j *
        ((elementaryPhiD1 (elementaryComponentOrder j) t x -
          elementaryPhiD1 (elementaryComponentOrder j) (t + w * e) x) / e) -
        elementaryComponentCoefficient j *
          (-(elementaryComponentOrder j : ℝ) *
            (elementaryComponentOrder j + 1) * w *
            t⁻¹ ^ (elementaryComponentOrder j + 2)) =
      elementaryComponentCoefficient j *
        (((elementaryPhiD1 (elementaryComponentOrder j) t x -
          elementaryPhiD1 (elementaryComponentOrder j) (t + w * e) x) / e) -
          (-(elementaryComponentOrder j : ℝ) *
            (elementaryComponentOrder j + 1) * w *
            t⁻¹ ^ (elementaryComponentOrder j + 2))) by ring,
    abs_mul]
  exact mul_le_mul_of_nonneg_left h (abs_nonneg _)

theorem elementaryCoordinatePartialW_error
    {j : Fin 4} {t t₀ w e x : ℝ}
    (ht₀ : 0 < t₀) (ht : t₀ ≤ t) (hw : 0 ≤ w)
    (he : 0 ≤ e) (hx : 0 ≤ x) :
    |elementaryCoordinatePartialW j t w e x -
        leadingElementaryCoordinatePartialW j t| ≤
      |elementaryComponentCoefficient j| *
        ((elementaryComponentOrder j : ℝ) *
          (elementaryComponentOrder j + 1) *
          ((elementaryComponentOrder j : ℝ) * x + w * e) *
          t₀⁻¹ ^ (elementaryComponentOrder j + 2)) := by
  have h := elementaryPairedTerm_w_error
    (q := elementaryComponentOrder j) ht₀ ht hw he hx
  rw [elementaryCoordinatePartialW, leadingElementaryCoordinatePartialW,
    show elementaryComponentCoefficient j *
        (-elementaryPhiD1 (elementaryComponentOrder j) (t + w * e) x) -
        elementaryComponentCoefficient j *
          ((elementaryComponentOrder j : ℝ) *
            t⁻¹ ^ (elementaryComponentOrder j + 1)) =
      elementaryComponentCoefficient j *
        (-elementaryPhiD1 (elementaryComponentOrder j) (t + w * e) x -
          (elementaryComponentOrder j : ℝ) *
            t⁻¹ ^ (elementaryComponentOrder j + 1)) by ring,
    abs_mul]
  exact mul_le_mul_of_nonneg_left h (abs_nonneg _)

theorem elementaryCoordinatePartialDelta_error
    {j : Fin 4} {delta e x : ℝ}
    (hdelta : 0 ≤ delta) (he : 0 ≤ e) (hx : 0 ≤ x) :
    |elementaryCoordinatePartialDelta j delta e x -
        leadingElementaryCoordinatePartialDelta j| ≤
      |elementaryComponentCoefficient j| *
        ((elementaryComponentOrder j : ℝ) *
          (elementaryComponentOrder j + 1) *
          ((elementaryComponentOrder j : ℝ) * x + delta * e)) := by
  have h := elementaryGammaBoundaryTerm_delta_error
    (q := elementaryComponentOrder j) hdelta he hx
  rw [elementaryCoordinatePartialDelta,
    leadingElementaryCoordinatePartialDelta,
    show elementaryComponentCoefficient j *
        (-elementaryPhiD1 (elementaryComponentOrder j) (1 + delta * e) x) -
        elementaryComponentCoefficient j * (elementaryComponentOrder j : ℝ) =
      elementaryComponentCoefficient j *
        (-elementaryPhiD1 (elementaryComponentOrder j) (1 + delta * e) x -
          (elementaryComponentOrder j : ℝ)) by ring,
    abs_mul]
  exact mul_le_mul_of_nonneg_left h (abs_nonneg _)

end

end Zeta23.Research.JensenWedge
