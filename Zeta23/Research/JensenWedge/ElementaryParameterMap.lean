import Zeta23.Research.JensenWedge.ExactParameterMap
import Zeta23.Research.JensenWedge.ElementaryCubeCalculus
import Zeta23.Research.JensenWedge.CanonicalCertificates

/-!
# Elementary and limiting four-parameter maps

This module fixes the exact cube-integral vector appearing in the finite
parameter map and the rational limiting map to which it converges.  It also
checks that the latter is exactly the denominator-cleared leading system
already audited in Lean, rather than a nearby normalization.
-/

namespace Zeta23.Research.JensenWedge

noncomputable section

/-- The cube dimension/reciprocal order in component `j`. -/
def elementaryComponentOrder (j : Fin 4) : ℕ := j + 1

/-- The four exact rational prefactors `(1,1/2,1,1)`. -/
def elementaryComponentCoefficient (j : Fin 4) : ℝ :=
  (elementaryWeight j : ℚ)

theorem elementaryComponentCoefficient_values :
    elementaryComponentCoefficient 0 = 1 ∧
    elementaryComponentCoefficient 1 = 1 / 2 ∧
    elementaryComponentCoefficient 2 = 1 ∧
    elementaryComponentCoefficient 3 = 1 := by
  norm_num [elementaryComponentCoefficient, elementaryWeight,
    componentScale, logRatioLeading, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three]

/-- The exact normalized elementary component in equation `(H_{n,j})` of
the manuscript. -/
def exactElementaryParameterComponent
    (j : Fin 4) (y : BranchPoint) (x e : ℝ) : ℝ :=
  let q := elementaryComponentOrder j
  elementaryComponentCoefficient j / e *
    (e ^ q * elementaryPhi q (y 0) (x * e) -
      elementaryPhi q (y 1 + y 2 * e) x +
      elementaryPhi q (y 1) x -
      elementaryPhi q (1 + y 3 * e) x +
      elementaryPhi q (1 + x / 2) x)

/-- The exact four-component elementary map. -/
def exactElementaryParameterMap
    (y : BranchPoint) (x e : ℝ) : BranchPoint :=
  fun j => exactElementaryParameterComponent j y x e

/-- The rational elementary limit before adding the xi saddle constants. -/
def leadingElementaryParameterMap (y : BranchPoint) : BranchPoint := ![
  1 / y 0 + y 2 / y 1 ^ 2 + y 3,
  y 2 / y 1 ^ 3 + y 3,
  3 * y 2 / y 1 ^ 4 + 3 * y 3,
  4 * y 2 / y 1 ^ 5 + 4 * y 3
]

/-- The signed xi saddle limit `(-2,-1,-2,-2)`. -/
def leadingXiSaddleVector : BranchPoint := ![-2, -1, -2, -2]

/-- The complete limiting map `F=H^infinity+S^infinity`. -/
def leadingXiParameterMap (y : BranchPoint) : BranchPoint :=
  leadingElementaryParameterMap y + leadingXiSaddleVector

theorem leadingXiSaddleVector_values :
    leadingXiSaddleVector 0 = -2 ∧ leadingXiSaddleVector 1 = -1 ∧
      leadingXiSaddleVector 2 = -2 ∧ leadingXiSaddleVector 3 = -2 := by
  constructor
  · norm_num [leadingXiSaddleVector, Matrix.cons_val_zero]
  constructor
  · norm_num [leadingXiSaddleVector, Matrix.cons_val_one]
  constructor
  · norm_num [leadingXiSaddleVector, Matrix.cons_val_two]
  · norm_num [leadingXiSaddleVector, Matrix.cons_val_three]

theorem leadingXiParameterMap_center :
    leadingXiParameterMap branchCenter = 0 := by
  ext i
  fin_cases i
  · change 1 / 3 + (16 / 3 : ℝ) / 2 ^ 2 + 1 / 3 - 2 = 0
    norm_num
  · change (16 / 3 : ℝ) / 2 ^ 3 + 1 / 3 - 1 = 0
    norm_num
  · change 3 * (16 / 3 : ℝ) / 2 ^ 4 + 3 * (1 / 3) - 2 = 0
    norm_num
  · change 4 * (16 / 3 : ℝ) / 2 ^ 5 + 4 * (1 / 3) - 2 = 0
    norm_num

/-- The rational limiting map has exactly the four leading equations, with
no changed sign or coordinate normalization. -/
theorem leadingXiParameterMap_eq_zero_iff
    {y : BranchPoint} (halpha : y 0 ≠ 0) (ht : y 1 ≠ 0) :
    leadingXiParameterMap y = 0 ↔
      SixthOrderLeadingSystem (y 1) (y 2) (y 3) (y 0) := by
  constructor
  · intro h
    have h0 := congrFun h 0
    have h1 := congrFun h 1
    have h2 := congrFun h 2
    have h3 := congrFun h 3
    change 1 / y 0 + y 2 / y 1 ^ 2 + y 3 - 2 = 0 at h0
    change y 2 / y 1 ^ 3 + y 3 - 1 = 0 at h1
    change 3 * y 2 / y 1 ^ 4 + 3 * y 3 - 2 = 0 at h2
    change 4 * y 2 / y 1 ^ 5 + 4 * y 3 - 2 = 0 at h3
    constructor
    · field_simp [ht] at h1
      nlinarith
    · field_simp [ht] at h2
      nlinarith
    · field_simp [ht] at h3
      nlinarith
    · field_simp [halpha, ht] at h0
      nlinarith
  · intro h
    ext i
    fin_cases i
    · change 1 / y 0 + y 2 / y 1 ^ 2 + y 3 - 2 = 0
      field_simp [halpha, ht]
      nlinarith [h.orderOne]
    · change y 2 / y 1 ^ 3 + y 3 - 1 = 0
      field_simp [ht]
      nlinarith [h.orderTwo]
    · change 3 * y 2 / y 1 ^ 4 + 3 * y 3 - 2 = 0
      field_simp [ht]
      nlinarith [h.orderThree]
    · change 4 * y 2 / y 1 ^ 5 + 4 * y 3 - 2 = 0
      field_simp [ht]
      nlinarith [h.orderFour]

/-- The positive zero of the rational limiting map is unique. -/
theorem leadingXiParameterMap_unique_positive
    {y : BranchPoint} (halpha : 0 < y 0) (ht : 0 < y 1) (hw : 0 < y 2)
    (hzero : leadingXiParameterMap y = 0) :
    y = branchCenter := by
  have hs := (leadingXiParameterMap_eq_zero_iff
    (ne_of_gt halpha) (ne_of_gt ht)).mp hzero
  rcases sixthOrderLeadingSystem_unique_of_t_w_pos ht hw hs with
    ⟨htwo, hwv, hd, ha⟩
  ext i
  fin_cases i <;> simp [branchCenter, ha, htwo, hwv, hd]

end

end Zeta23.Research.JensenWedge
