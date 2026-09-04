import Zeta23.Research.JensenWedge.ExactParameterDecomposition

/-!
# Fréchet derivative of the elementary parameter map

This module upgrades the four scalar partial-derivative producers to a
genuine multivariable derivative.  The resulting continuous linear map is
then identified with the exact elementary Jacobian entry by entry.
-/

namespace Zeta23.Research.JensenWedge

noncomputable section

/-- A matrix acting on the four-dimensional branch space, regarded as a
continuous linear map for the sup norm. -/
def branchMatrixCLM (A : Matrix (Fin 4) (Fin 4) ℝ) :
    BranchPoint →L[ℝ] BranchPoint :=
  ContinuousLinearMap.mk (Matrix.mulVecLin A)

/-- The exact elementary map is differentiable on the positive parameter
orthant.  This is proved from the three boundary terms, before identifying
the derivative with a matrix. -/
theorem exactElementaryParameterMap_differentiableAt
    {y : BranchPoint} {e x : ℝ}
    (halpha : 0 < y 0) (ht : 0 < y 1) (hw : 0 ≤ y 2)
    (hdelta : 0 ≤ y 3) (he : 0 < e) (hx : 0 ≤ x) :
    DifferentiableAt ℝ (fun z => exactElementaryParameterMap z x e) y := by
  rw [differentiableAt_pi]
  intro j
  change DifferentiableAt ℝ
    (fun z => exactElementaryParameterComponent j z x e) y
  have heq : (fun z : BranchPoint => exactElementaryParameterComponent j z x e) =
      fun z => elementaryCoordinateComponent j (z 0) (z 1) (z 2) (z 3) e x := by
    funext z
    exact (elementaryCoordinateComponent_eq_exact
      (j := j) (y := z) (e := e) (x := x) he.ne').symm
  rw [heq]
  let q := elementaryComponentOrder j
  have hremote : DifferentiableAt ℝ
      (fun z : BranchPoint => elementaryRemoteTerm q (z 0) e x) y :=
    DifferentiableAt.fun_comp' y
      (f := fun z : BranchPoint => z 0)
      (g := fun a => elementaryRemoteTerm q a e x)
      (hasDerivAt_elementaryRemoteTerm_alpha
        (q := q) halpha hx he.le).differentiableAt
      (differentiableAt_apply 0 y)
  have hleft : DifferentiableAt ℝ
      (fun z : BranchPoint => elementaryPhi q (z 1) x) y :=
    DifferentiableAt.fun_comp' y
      (f := fun z : BranchPoint => z 1)
      (g := fun t => elementaryPhi q t x)
      (hasDerivAt_elementaryPhi (q := q) ht hx).differentiableAt
      (differentiableAt_apply 1 y)
  have hshift_pos : 0 < y 1 + y 2 * e := by positivity
  have hshift : DifferentiableAt ℝ
      (fun z : BranchPoint => elementaryPhi q (z 1 + z 2 * e) x) y := by
    apply DifferentiableAt.fun_comp' y
      (g := fun t => elementaryPhi q t x)
      (hasDerivAt_elementaryPhi (q := q) hshift_pos hx).differentiableAt
    fun_prop
  have hpaired : DifferentiableAt ℝ
      (fun z : BranchPoint => elementaryPairedTerm q (z 1) (z 2) e x) y := by
    have hp := (hleft.sub hshift).const_mul e⁻¹
    have heq : (fun z : BranchPoint =>
        elementaryPairedTerm q (z 1) (z 2) e x) =
        fun z => e⁻¹ * (elementaryPhi q (z 1) x -
          elementaryPhi q (z 1 + z 2 * e) x) := by
      funext z
      simp only [elementaryPairedTerm]
      rw [div_eq_mul_inv, mul_comm]
    rw [heq]
    simpa only [Pi.sub_apply] using hp
  have hgamma_pos : 0 < 1 + y 3 * e := by positivity
  have hgamma_right : DifferentiableAt ℝ
      (fun z : BranchPoint => elementaryPhi q (1 + z 3 * e) x) y := by
    apply DifferentiableAt.fun_comp' y
      (g := fun t => elementaryPhi q t x)
      (hasDerivAt_elementaryPhi (q := q) hgamma_pos hx).differentiableAt
    fun_prop
  have hgamma : DifferentiableAt ℝ
      (fun z : BranchPoint => elementaryGammaBoundaryTerm q (z 3) e x) y := by
    have hg := ((differentiableAt_const
      (c := elementaryPhi q (1 + x / 2) x)).sub hgamma_right).const_mul e⁻¹
    have heq : (fun z : BranchPoint =>
        elementaryGammaBoundaryTerm q (z 3) e x) =
        fun z => e⁻¹ * (elementaryPhi q (1 + x / 2) x -
          elementaryPhi q (1 + z 3 * e) x) := by
      funext z
      simp only [elementaryGammaBoundaryTerm]
      rw [div_eq_mul_inv, mul_comm]
    rw [heq]
    simpa only [Pi.sub_apply] using hg
  simpa [elementaryCoordinateComponent, q, add_assoc] using
    ((hremote.add hpaired).add hgamma).const_mul
      (elementaryComponentCoefficient j)

/-- Applying the Fréchet derivative to a coordinate vector recovers the
corresponding independently proved scalar partial derivative. -/
theorem exactElementaryParameterMap_fderiv_single
    {y : BranchPoint} {e x : ℝ}
    (halpha : 0 < y 0) (ht : 0 < y 1) (hw : 0 ≤ y 2)
    (hdelta : 0 ≤ y 3) (he : 0 < e) (hx : 0 ≤ x)
    (j k : Fin 4) :
    (fderiv ℝ (fun z => exactElementaryParameterMap z x e) y
        (Pi.single k 1)) j = exactElementaryJacobian y e x j k := by
  have hdiff := exactElementaryParameterMap_differentiableAt
    halpha ht hw hdelta he hx
  have hcurve : HasDerivAt
      (fun a => exactElementaryParameterMap (Function.update y k a) x e j)
      ((fderiv ℝ (fun z => exactElementaryParameterMap z x e) y
        (Pi.single k 1)) j) (y k) := by
    have houter : HasFDerivAt
        (fun z => exactElementaryParameterMap z x e)
        (fderiv ℝ (fun z => exactElementaryParameterMap z x e) y)
        (Function.update y k (y k)) := by
      simpa using hdiff.hasFDerivAt
    have hcomp := houter.comp (y k)
      (hasFDerivAt_update y (i := k) (y k))
    have hproj :=
      ((ContinuousLinearMap.proj (R := ℝ) j : BranchPoint →L[ℝ] ℝ).hasFDerivAt.comp
      (y k) hcomp
      )
    have hsingle :
        ((ContinuousLinearMap.pi
          (Pi.single k (ContinuousLinearMap.id ℝ ℝ))) :
            ℝ →L[ℝ] BranchPoint) (1 : ℝ) =
            Pi.single k 1 := by
      ext i
      rw [ContinuousLinearMap.pi_apply]
      by_cases hik : i = k <;> simp [hik]
    have hd := hproj.hasDerivAt
    simp only [ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.proj_apply] at hd
    rw [hsingle] at hd
    simpa [Function.comp_def] using hd
  fin_cases k
  · have hpartial := hasDerivAt_elementaryCoordinateComponent_alpha
      (j := j) (alpha := y 0) (t := y 1) (w := y 2) (delta := y 3)
      (e := e) (x := x) halpha hx he
    have hc : HasDerivAt
        (fun a => elementaryCoordinateComponent j a (y 1) (y 2) (y 3) e x)
        ((fderiv ℝ (fun z => exactElementaryParameterMap z x e) y
          (Pi.single (0 : Fin 4) 1)) j) (y 0) := by
      convert hcurve using 1
      · funext a
        simpa [exactElementaryParameterMap] using
          (elementaryCoordinateComponent_eq_exact
            (j := j) (y := Function.update y (0 : Fin 4) a)
            (e := e) (x := x) he.ne')
      · simp
      · simp
    have hu := hc.unique hpartial
    simpa [exactElementaryJacobian] using hu
  · have hpartial := hasDerivAt_elementaryCoordinateComponent_t
      (j := j) (alpha := y 0) (t := y 1) (w := y 2) (delta := y 3)
      (e := e) (x := x) ht hw he hx
    have hc : HasDerivAt
        (fun a => elementaryCoordinateComponent j (y 0) a (y 2) (y 3) e x)
        ((fderiv ℝ (fun z => exactElementaryParameterMap z x e) y
          (Pi.single (1 : Fin 4) 1)) j) (y 1) := by
      convert hcurve using 1
      · funext a
        simpa [exactElementaryParameterMap] using
          (elementaryCoordinateComponent_eq_exact
            (j := j) (y := Function.update y (1 : Fin 4) a)
            (e := e) (x := x) he.ne')
      · simp
      · simp
    have hu := hc.unique hpartial
    simpa [exactElementaryJacobian] using hu
  · have hpartial := hasDerivAt_elementaryCoordinateComponent_w
      (j := j) (alpha := y 0) (t := y 1) (w := y 2) (delta := y 3)
      (e := e) (x := x) ht hw he hx
    have hc : HasDerivAt
        (fun a => elementaryCoordinateComponent j (y 0) (y 1) a (y 3) e x)
        ((fderiv ℝ (fun z => exactElementaryParameterMap z x e) y
          (Pi.single (2 : Fin 4) 1)) j) (y 2) := by
      convert hcurve using 1
      · funext a
        simpa [exactElementaryParameterMap] using
          (elementaryCoordinateComponent_eq_exact
            (j := j) (y := Function.update y (2 : Fin 4) a)
            (e := e) (x := x) he.ne')
      · simp
      · simp
    have hu := hc.unique hpartial
    simpa [exactElementaryJacobian] using hu
  · have hpartial := hasDerivAt_elementaryCoordinateComponent_delta
      (j := j) (alpha := y 0) (t := y 1) (w := y 2) (delta := y 3)
      (e := e) (x := x) hdelta he hx
    have hc : HasDerivAt
        (fun a => elementaryCoordinateComponent j (y 0) (y 1) (y 2) a e x)
        ((fderiv ℝ (fun z => exactElementaryParameterMap z x e) y
          (Pi.single (3 : Fin 4) 1)) j) (y 3) := by
      convert hcurve using 1
      · funext a
        simpa [exactElementaryParameterMap] using
          (elementaryCoordinateComponent_eq_exact
            (j := j) (y := Function.update y (3 : Fin 4) a)
            (e := e) (x := x) he.ne')
      · simp
      · simp
    have hu := hc.unique hpartial
    simpa [exactElementaryJacobian] using hu

/-- The exact elementary Jacobian is the full Fréchet derivative, not merely
a table of separately computed partial derivatives. -/
theorem exactElementaryParameterMap_hasFDerivAt
    {y : BranchPoint} {e x : ℝ}
    (halpha : 0 < y 0) (ht : 0 < y 1) (hw : 0 ≤ y 2)
    (hdelta : 0 ≤ y 3) (he : 0 < e) (hx : 0 ≤ x) :
    HasFDerivAt (fun z => exactElementaryParameterMap z x e)
      (branchMatrixCLM (exactElementaryJacobian y e x)) y := by
  have hdiff := exactElementaryParameterMap_differentiableAt
    halpha ht hw hdelta he hx
  apply hdiff.hasFDerivAt.congr_fderiv
  apply ContinuousLinearMap.ext
  intro v
  ext j
  have hv : v = ∑ k : Fin 4, v k • Pi.single k (1 : ℝ) := by
    ext i
    simp [Pi.single_apply]
  calc
    (fderiv ℝ (fun z => exactElementaryParameterMap z x e) y v) j =
        (fderiv ℝ (fun z => exactElementaryParameterMap z x e) y
          (∑ k : Fin 4, v k • Pi.single k (1 : ℝ))) j := by rw [← hv]
    _ = ∑ k : Fin 4, v k *
        (fderiv ℝ (fun z => exactElementaryParameterMap z x e) y
          (Pi.single k 1)) j := by
      simp only [map_sum, map_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    _ = ∑ k : Fin 4, v k * exactElementaryJacobian y e x j k := by
      apply Finset.sum_congr rfl
      intro k _hk
      rw [exactElementaryParameterMap_fderiv_single
        halpha ht hw hdelta he hx j k]
    _ = ∑ k : Fin 4, exactElementaryJacobian y e x j k * v k := by
      apply Finset.sum_congr rfl
      intro k _hk
      ring
    _ = branchMatrixCLM (exactElementaryJacobian y e x) v j := by
      rfl

end

end Zeta23.Research.JensenWedge
