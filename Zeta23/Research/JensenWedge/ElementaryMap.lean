import Zeta23.Research.JensenWedge.TriangularMap

/-!
# Exact finite-difference signs for the Jensen parameter map

This module checks the finite algebra used before the analytic cube-integral
estimate.  It does not formalize logarithmic integrals or asymptotic bounds.
-/

namespace Zeta23.Research.JensenWedge

/-- Fourth forward difference at zero. -/
def forwardDiff4 (f : ℝ → ℝ) : ℝ :=
  f 4 - 4 * f 3 + 6 * f 2 - 4 * f 1 + f 0

noncomputable def logBase (U x : ℝ) : ℝ := Real.log (U + x)

/-- The elementary Jacobi logarithmic quotient. -/
noncomputable def logRatio (U x : ℝ) : ℝ :=
  Real.log (U + x) - Real.log (U + x + 1)

/-- `logRatio` is exactly the negative first forward difference of `logBase`,
through all four coordinates used by the parameter map. -/
theorem logRatio_forwardDiffs (U : ℝ) :
    forwardDiff0 (logRatio U) = -forwardDiff1 (logBase U) ∧
    forwardDiff1 (logRatio U) = -forwardDiff2 (logBase U) ∧
    forwardDiff2 (logRatio U) = -forwardDiff3 (logBase U) ∧
    forwardDiff3 (logRatio U) = -forwardDiff4 (logBase U) := by
  simp only [forwardDiff0, forwardDiff1, forwardDiff2, forwardDiff3,
    forwardDiff4, logRatio, logBase]
  constructor
  · ring_nf
  constructor
  · ring_nf
  constructor <;> ring_nf

/-- Coefficients multiplying `n^(j+1) L` in the four triangular components. -/
def componentScale : Fin 4 → ℚ := ![-1, 1 / 2, -1 / 2, 1 / 6]

/-- Leading coefficients `(-1)^(j+1) j!` of the exact cube-integral formula
for the forward differences of `logRatio`. -/
def logRatioLeading : Fin 4 → ℚ := ![-1, 1, -2, 6]

/-- Product of the triangular scale and the logarithmic-difference sign. -/
def elementaryWeight (j : Fin 4) : ℚ :=
  componentScale j * logRatioLeading j

theorem elementaryWeight_values :
    elementaryWeight 0 = 1 ∧
    elementaryWeight 1 = 1 / 2 ∧
    elementaryWeight 2 = 1 ∧
    elementaryWeight 3 = 1 := by
  norm_num [elementaryWeight, componentScale, logRatioLeading,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.cons_val_three]

/-- Derivative orders `j+1` in the paired boundary terms. -/
def boundaryOrder : Fin 4 → ℚ := ![1, 2, 3, 4]

/-- The exact coefficients of the `delta` boundary contribution.  The same
coefficients multiply `w / t^(j+2)` for the `B-C` pair. -/
def boundaryWeight (j : Fin 4) : ℚ :=
  elementaryWeight j * boundaryOrder j

theorem boundaryWeight_values :
    boundaryWeight 0 = 1 ∧
    boundaryWeight 1 = 1 ∧
    boundaryWeight 2 = 3 ∧
    boundaryWeight 3 = 4 := by
  norm_num [boundaryWeight, elementaryWeight, componentScale,
    logRatioLeading, boundaryOrder, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three]

/-- Signed leading constants of `h^(j+2)` before applying the triangular
component scales. -/
def saddleDerivativeLeading : Fin 4 → ℚ := ![2, -2, 4, -12]

/-- The saddle contribution to the four limiting residual components. -/
def saddleWeight (j : Fin 4) : ℚ :=
  componentScale j * saddleDerivativeLeading j

theorem saddleWeight_values :
    saddleWeight 0 = -2 ∧
    saddleWeight 1 = -1 ∧
    saddleWeight 2 = -2 ∧
    saddleWeight 3 = -2 := by
  norm_num [saddleWeight, componentScale, saddleDerivativeLeading,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.cons_val_three]

end Zeta23.Research.JensenWedge
