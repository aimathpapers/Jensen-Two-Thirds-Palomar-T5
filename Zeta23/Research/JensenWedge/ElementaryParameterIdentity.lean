import Zeta23.Research.JensenWedge.ElementaryParameterMap

/-!
# Exact logarithmic-boundary to cube-vector identity

The elementary part of the four-parameter residual begins as five logarithmic
boundaries.  This module proves that its four triangular finite differences
are exactly the cube-integral vector from `ElementaryParameterMap`.  The
identity is algebraic/FTC based and precedes every asymptotic inequality.
-/

namespace Zeta23.Research.JensenWedge

open MeasureTheory Set

noncomputable section

/-- Simultaneous scaling of both affine denominator variables. -/
theorem elementaryPhi_div_scale
    {q : ℕ} {s z e : ℝ} (he : 0 < e) :
    elementaryPhi q (s / e) z = e ^ q * elementaryPhi q s (z * e) := by
  unfold elementaryPhi elementaryCubeIntegral
  rw [← integral_const_mul]
  apply setIntegral_congr_fun (measurableSet_unitCube q)
  intro u _hu
  simp only [elementaryCubeKernel, cubeDenominator]
  have hden : s / e + z * ∑ i, u i =
      e⁻¹ * (s + z * e * ∑ i, u i) := by
    field_simp [ne_of_gt he]
  rw [hden, mul_inv_rev, mul_pow, inv_inv]
  ring

theorem natForwardDiff0_logRatio_scaled
    {s x : ℝ} (hs : 0 < s) (hx : 0 < x) :
    natForwardDiff0 (fun k => logRatio (s / x) k) =
      -x * elementaryPhi 1 s x := by
  simpa [natForwardDiff0, logRatio, elementaryLogFactor,
    iteratedForwardDifference] using elementaryLogFactor_scaled_q1 hs hx

theorem natForwardDiff1_logRatio_scaled
    {s x : ℝ} (hs : 0 < s) (hx : 0 < x) :
    natForwardDiff1 (fun k => logRatio (s / x) k) =
      x ^ 2 * elementaryPhi 2 s x := by
  simpa [natForwardDiff1, logRatio, elementaryLogFactor,
    iteratedForwardDifference] using elementaryLogFactor_scaled_q2 hs hx

theorem natForwardDiff2_logRatio_scaled
    {s x : ℝ} (hs : 0 < s) (hx : 0 < x) :
    natForwardDiff2 (fun k => logRatio (s / x) k) =
      -2 * x ^ 3 * elementaryPhi 3 s x := by
  convert elementaryLogFactor_scaled_q3 hs hx using 1 <;>
    simp [natForwardDiff2, logRatio, elementaryLogFactor,
      iteratedForwardDifference] <;> ring_nf

theorem natForwardDiff3_logRatio_scaled
    {s x : ℝ} (hs : 0 < s) (hx : 0 < x) :
    natForwardDiff3 (fun k => logRatio (s / x) k) =
      6 * x ^ 4 * elementaryPhi 4 s x := by
  convert elementaryLogFactor_scaled_q4 hs hx using 1 <;>
    simp [natForwardDiff3, logRatio, elementaryLogFactor,
      iteratedForwardDifference] <;> ring_nf

private theorem natForwardDiff0_five
    (A B C D G : ℕ → ℝ) :
    natForwardDiff0 (fun k => A k - B k + C k - D k + G k) =
      natForwardDiff0 A - natForwardDiff0 B + natForwardDiff0 C -
        natForwardDiff0 D + natForwardDiff0 G := by
  rfl

private theorem natForwardDiff1_five
    (A B C D G : ℕ → ℝ) :
    natForwardDiff1 (fun k => A k - B k + C k - D k + G k) =
      natForwardDiff1 A - natForwardDiff1 B + natForwardDiff1 C -
        natForwardDiff1 D + natForwardDiff1 G := by
  simp only [natForwardDiff1]
  ring

private theorem natForwardDiff2_five
    (A B C D G : ℕ → ℝ) :
    natForwardDiff2 (fun k => A k - B k + C k - D k + G k) =
      natForwardDiff2 A - natForwardDiff2 B + natForwardDiff2 C -
        natForwardDiff2 D + natForwardDiff2 G := by
  simp only [natForwardDiff2]
  ring

private theorem natForwardDiff3_five
    (A B C D G : ℕ → ℝ) :
    natForwardDiff3 (fun k => A k - B k + C k - D k + G k) =
      natForwardDiff3 A - natForwardDiff3 B + natForwardDiff3 C -
        natForwardDiff3 D + natForwardDiff3 G := by
  simp only [natForwardDiff3]
  ring

/-- The exact five-boundary elementary quotient residual. -/
def elementaryQuotientResidual
    (y : BranchPoint) (x e : ℝ) (k : ℕ) : ℝ :=
  logRatio (y 0 / (x * e)) k -
    logRatio ((y 1 + y 2 * e) / x) k +
    logRatio (y 1 / x) k -
    logRatio ((1 + y 3 * e) / x) k +
    logRatio ((1 + x / 2) / x) k

/-- The exact triangular normalization of the five logarithmic boundaries. -/
def elementaryTriangularParameterMap
    (y : BranchPoint) (x e : ℝ) : BranchPoint := ![
  -(1 / (x * e)) * natForwardDiff0 (elementaryQuotientResidual y x e),
  (1 / (2 * x ^ 2 * e)) * natForwardDiff1 (elementaryQuotientResidual y x e),
  -(1 / (2 * x ^ 3 * e)) * natForwardDiff2 (elementaryQuotientResidual y x e),
  (1 / (6 * x ^ 4 * e)) * natForwardDiff3 (elementaryQuotientResidual y x e)
]

private theorem elementaryBoundaryScales
    {y : BranchPoint} {x e : ℝ}
    (hy : InOuterParameterBox y) (hx : 0 < x) (he : 0 < e) :
    0 < y 0 / e ∧ 0 < y 1 + y 2 * e ∧ 0 < y 1 ∧
      0 < 1 + y 3 * e ∧ 0 < 1 + x / 2 := by
  rcases hy with ⟨ha0, _ha1, ht0, _ht1, hw0, _hw1, hd0, _hd1⟩
  constructor
  · exact div_pos (by linarith) he
  constructor
  · nlinarith
  constructor
  · linarith
  constructor <;> nlinarith

theorem elementaryQuotientResidual_forward0
    {y : BranchPoint} {x e : ℝ}
    (hy : InOuterParameterBox y) (hx : 0 < x) (he : 0 < e) :
    natForwardDiff0 (elementaryQuotientResidual y x e) =
      -x * (elementaryPhi 1 (y 0 / e) x -
        elementaryPhi 1 (y 1 + y 2 * e) x +
        elementaryPhi 1 (y 1) x -
        elementaryPhi 1 (1 + y 3 * e) x +
        elementaryPhi 1 (1 + x / 2) x) := by
  rcases elementaryBoundaryScales hy hx he with ⟨hA, hB, hC, hD, hG⟩
  have A := natForwardDiff0_logRatio_scaled (s := y 0 / e) hA hx
  have B := natForwardDiff0_logRatio_scaled (s := y 1 + y 2 * e) hB hx
  have C := natForwardDiff0_logRatio_scaled (s := y 1) hC hx
  have D := natForwardDiff0_logRatio_scaled (s := 1 + y 3 * e) hD hx
  have G := natForwardDiff0_logRatio_scaled (s := 1 + x / 2) hG hx
  have hremote : y 0 / (x * e) = (y 0 / e) / x := by
    field_simp [ne_of_gt hx, ne_of_gt he]
  rw [show elementaryQuotientResidual y x e = fun k : ℕ =>
      logRatio ((y 0 / e) / x) (k : ℝ) -
        logRatio ((y 1 + y 2 * e) / x) (k : ℝ) +
        logRatio (y 1 / x) (k : ℝ) - logRatio ((1 + y 3 * e) / x) (k : ℝ) +
        logRatio ((1 + x / 2) / x) (k : ℝ) by
      funext k
      simp only [elementaryQuotientResidual, hremote]]
  rw [natForwardDiff0_five, A, B, C, D, G]
  ring

theorem elementaryQuotientResidual_forward1
    {y : BranchPoint} {x e : ℝ}
    (hy : InOuterParameterBox y) (hx : 0 < x) (he : 0 < e) :
    natForwardDiff1 (elementaryQuotientResidual y x e) =
      x ^ 2 * (elementaryPhi 2 (y 0 / e) x -
        elementaryPhi 2 (y 1 + y 2 * e) x +
        elementaryPhi 2 (y 1) x -
        elementaryPhi 2 (1 + y 3 * e) x +
        elementaryPhi 2 (1 + x / 2) x) := by
  rcases elementaryBoundaryScales hy hx he with ⟨hA, hB, hC, hD, hG⟩
  have A := natForwardDiff1_logRatio_scaled (s := y 0 / e) hA hx
  have B := natForwardDiff1_logRatio_scaled (s := y 1 + y 2 * e) hB hx
  have C := natForwardDiff1_logRatio_scaled (s := y 1) hC hx
  have D := natForwardDiff1_logRatio_scaled (s := 1 + y 3 * e) hD hx
  have G := natForwardDiff1_logRatio_scaled (s := 1 + x / 2) hG hx
  have hremote : y 0 / (x * e) = (y 0 / e) / x := by
    field_simp [ne_of_gt hx, ne_of_gt he]
  rw [show elementaryQuotientResidual y x e = fun k : ℕ =>
      logRatio ((y 0 / e) / x) (k : ℝ) -
        logRatio ((y 1 + y 2 * e) / x) (k : ℝ) +
        logRatio (y 1 / x) (k : ℝ) - logRatio ((1 + y 3 * e) / x) (k : ℝ) +
        logRatio ((1 + x / 2) / x) (k : ℝ) by
      funext k
      simp only [elementaryQuotientResidual, hremote]]
  rw [natForwardDiff1_five, A, B, C, D, G]
  ring

theorem elementaryQuotientResidual_forward2
    {y : BranchPoint} {x e : ℝ}
    (hy : InOuterParameterBox y) (hx : 0 < x) (he : 0 < e) :
    natForwardDiff2 (elementaryQuotientResidual y x e) =
      -2 * x ^ 3 * (elementaryPhi 3 (y 0 / e) x -
        elementaryPhi 3 (y 1 + y 2 * e) x +
        elementaryPhi 3 (y 1) x -
        elementaryPhi 3 (1 + y 3 * e) x +
        elementaryPhi 3 (1 + x / 2) x) := by
  rcases elementaryBoundaryScales hy hx he with ⟨hA, hB, hC, hD, hG⟩
  have A := natForwardDiff2_logRatio_scaled (s := y 0 / e) hA hx
  have B := natForwardDiff2_logRatio_scaled (s := y 1 + y 2 * e) hB hx
  have C := natForwardDiff2_logRatio_scaled (s := y 1) hC hx
  have D := natForwardDiff2_logRatio_scaled (s := 1 + y 3 * e) hD hx
  have G := natForwardDiff2_logRatio_scaled (s := 1 + x / 2) hG hx
  have hremote : y 0 / (x * e) = (y 0 / e) / x := by
    field_simp [ne_of_gt hx, ne_of_gt he]
  rw [show elementaryQuotientResidual y x e = fun k : ℕ =>
      logRatio ((y 0 / e) / x) (k : ℝ) -
        logRatio ((y 1 + y 2 * e) / x) (k : ℝ) +
        logRatio (y 1 / x) (k : ℝ) - logRatio ((1 + y 3 * e) / x) (k : ℝ) +
        logRatio ((1 + x / 2) / x) (k : ℝ) by
      funext k
      simp only [elementaryQuotientResidual, hremote]]
  rw [natForwardDiff2_five, A, B, C, D, G]
  ring

theorem elementaryQuotientResidual_forward3
    {y : BranchPoint} {x e : ℝ}
    (hy : InOuterParameterBox y) (hx : 0 < x) (he : 0 < e) :
    natForwardDiff3 (elementaryQuotientResidual y x e) =
      6 * x ^ 4 * (elementaryPhi 4 (y 0 / e) x -
        elementaryPhi 4 (y 1 + y 2 * e) x +
        elementaryPhi 4 (y 1) x -
        elementaryPhi 4 (1 + y 3 * e) x +
        elementaryPhi 4 (1 + x / 2) x) := by
  rcases elementaryBoundaryScales hy hx he with ⟨hA, hB, hC, hD, hG⟩
  have A := natForwardDiff3_logRatio_scaled (s := y 0 / e) hA hx
  have B := natForwardDiff3_logRatio_scaled (s := y 1 + y 2 * e) hB hx
  have C := natForwardDiff3_logRatio_scaled (s := y 1) hC hx
  have D := natForwardDiff3_logRatio_scaled (s := 1 + y 3 * e) hD hx
  have G := natForwardDiff3_logRatio_scaled (s := 1 + x / 2) hG hx
  have hremote : y 0 / (x * e) = (y 0 / e) / x := by
    field_simp [ne_of_gt hx, ne_of_gt he]
  rw [show elementaryQuotientResidual y x e = fun k : ℕ =>
      logRatio ((y 0 / e) / x) (k : ℝ) -
        logRatio ((y 1 + y 2 * e) / x) (k : ℝ) +
        logRatio (y 1 / x) (k : ℝ) - logRatio ((1 + y 3 * e) / x) (k : ℝ) +
        logRatio ((1 + x / 2) / x) (k : ℝ) by
      funext k
      simp only [elementaryQuotientResidual, hremote]]
  rw [natForwardDiff3_five, A, B, C, D, G]
  ring

/-- Exact source identity: the five logarithmic boundaries and the cube
vector are the same four-parameter map. -/
theorem elementaryTriangularParameterMap_eq_exactElementary
    {y : BranchPoint} {x e : ℝ}
    (hy : InOuterParameterBox y) (hx : 0 < x) (he : 0 < e) :
    elementaryTriangularParameterMap y x e =
      exactElementaryParameterMap y x e := by
  have h0 :
      elementaryTriangularParameterMap y x e 0 =
        exactElementaryParameterMap y x e 0 := by
    norm_num [elementaryTriangularParameterMap, exactElementaryParameterMap,
      exactElementaryParameterComponent, elementaryComponentOrder,
      elementaryComponentCoefficient, elementaryWeight, componentScale,
      logRatioLeading, Matrix.cons_val_zero]
    rw [elementaryQuotientResidual_forward0 hy hx he,
      elementaryPhi_div_scale (q := 1) (s := y 0) (z := x) he]
    field_simp [ne_of_gt hx, ne_of_gt he]
  have h1 :
      elementaryTriangularParameterMap y x e 1 =
        exactElementaryParameterMap y x e 1 := by
    norm_num [elementaryTriangularParameterMap, exactElementaryParameterMap,
      exactElementaryParameterComponent, elementaryComponentOrder,
      elementaryComponentCoefficient, elementaryWeight, componentScale,
      logRatioLeading, Matrix.cons_val_zero, Matrix.cons_val_one]
    rw [elementaryQuotientResidual_forward1 hy hx he,
      elementaryPhi_div_scale (q := 2) (s := y 0) (z := x) he]
    field_simp [ne_of_gt hx, ne_of_gt he]
  have h2 :
      elementaryTriangularParameterMap y x e 2 =
        exactElementaryParameterMap y x e 2 := by
    norm_num [elementaryTriangularParameterMap, exactElementaryParameterMap,
      exactElementaryParameterComponent, elementaryComponentOrder,
      elementaryComponentCoefficient, elementaryWeight, componentScale,
      logRatioLeading, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two]
    rw [elementaryQuotientResidual_forward2 hy hx he,
      elementaryPhi_div_scale (q := 3) (s := y 0) (z := x) he]
    field_simp [ne_of_gt hx, ne_of_gt he]
  have h3 :
      elementaryTriangularParameterMap y x e 3 =
        exactElementaryParameterMap y x e 3 := by
    norm_num [elementaryTriangularParameterMap, exactElementaryParameterMap,
      exactElementaryParameterComponent, elementaryComponentOrder,
      elementaryComponentCoefficient, elementaryWeight, componentScale,
      logRatioLeading, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.cons_val_three]
    rw [elementaryQuotientResidual_forward3 hy hx he,
      elementaryPhi_div_scale (q := 4) (s := y 0) (z := x) he]
    field_simp [ne_of_gt hx, ne_of_gt he]
  ext j
  fin_cases j
  · simpa using h0
  · simpa using h1
  · simpa using h2
  · simpa using h3

end

end Zeta23.Research.JensenWedge
