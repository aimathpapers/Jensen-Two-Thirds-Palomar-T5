import Mathlib

/-!
# Finite-difference normalization for the Jensen-wedge parameter map

This module checks the exact finite algebra behind the triangular readout used
in the Phase-7 analytic specification.  It contains no xi-function asymptotic
input.
-/

namespace Zeta23.Research.JensenWedge

/-- Zeroth through third forward differences at zero. -/
def forwardDiff0 (f : ℝ → ℝ) : ℝ := f 0
def forwardDiff1 (f : ℝ → ℝ) : ℝ := f 1 - f 0
def forwardDiff2 (f : ℝ → ℝ) : ℝ := f 2 - 2 * f 1 + f 0
def forwardDiff3 (f : ℝ → ℝ) : ℝ := f 3 - 3 * f 2 + 3 * f 1 - f 0

/-- Cubic polynomial in the Newton falling-factorial basis. -/
noncomputable def newtonCubic (c0 c1 c2 c3 x : ℝ) : ℝ :=
  c0 + c1 * x + c2 * (x * (x - 1) / 2) +
    c3 * (x * (x - 1) * (x - 2) / 6)

/-- Forward differences recover Newton-basis coefficients without mixing. -/
theorem forwardDiff_newtonCubic (c0 c1 c2 c3 : ℝ) :
    forwardDiff0 (newtonCubic c0 c1 c2 c3) = c0 ∧
    forwardDiff1 (newtonCubic c0 c1 c2 c3) = c1 ∧
    forwardDiff2 (newtonCubic c0 c1 c2 c3) = c2 ∧
    forwardDiff3 (newtonCubic c0 c1 c2 c3) = c3 := by
  constructor
  · norm_num [forwardDiff0, newtonCubic]
  constructor
  · norm_num [forwardDiff1, newtonCubic]
  constructor <;> norm_num [forwardDiff2, forwardDiff3, newtonCubic] <;> ring

/-- Vanishing of the triangular forward-difference coordinates is equivalent
to vanishing of the four original values. -/
theorem forwardDiffs_zero_iff_values_zero (f : ℝ → ℝ) :
    (forwardDiff0 f = 0 ∧ forwardDiff1 f = 0 ∧
      forwardDiff2 f = 0 ∧ forwardDiff3 f = 0) ↔
    (f 0 = 0 ∧ f 1 = 0 ∧ f 2 = 0 ∧ f 3 = 0) := by
  simp only [forwardDiff0, forwardDiff1, forwardDiff2, forwardDiff3]
  constructor
  · rintro ⟨h0, h1, h2, h3⟩
    constructor
    · exact h0
    constructor
    · linarith
    constructor <;> linarith
  · rintro ⟨h0, h1, h2, h3⟩
    constructor
    · exact h0
    constructor
    · linarith
    constructor <;> linarith

/-- The exact model for the four differently scaled residual components. -/
noncomputable def triangularErrorModel
    (n L F0 F1 F2 F3 x : ℝ) : ℝ :=
  newtonCubic
    (-F0 / (n * L))
    (2 * F1 / (n ^ 2 * L))
    (-2 * F2 / (n ^ 3 * L))
    (6 * F3 / (n ^ 4 * L)) x

/-- The proposed triangular normalization recovers the four leading equations
exactly on the Newton-basis error model. -/
theorem triangularReadout_exact
    {n L F0 F1 F2 F3 : ℝ} (hn : n ≠ 0) (hL : L ≠ 0) :
    -(n * L) * forwardDiff0 (triangularErrorModel n L F0 F1 F2 F3) = F0 ∧
    (n ^ 2 * L / 2) * forwardDiff1 (triangularErrorModel n L F0 F1 F2 F3) = F1 ∧
    -(n ^ 3 * L / 2) * forwardDiff2 (triangularErrorModel n L F0 F1 F2 F3) = F2 ∧
    (n ^ 4 * L / 6) * forwardDiff3 (triangularErrorModel n L F0 F1 F2 F3) = F3 := by
  have hcoeff := forwardDiff_newtonCubic
    (-F0 / (n * L))
    (2 * F1 / (n ^ 2 * L))
    (-2 * F2 / (n ^ 3 * L))
    (6 * F3 / (n ^ 4 * L))
  change
    -(n * L) * forwardDiff0
        (newtonCubic (-F0 / (n * L)) (2 * F1 / (n ^ 2 * L))
          (-2 * F2 / (n ^ 3 * L)) (6 * F3 / (n ^ 4 * L))) = F0 ∧
      (n ^ 2 * L / 2) * forwardDiff1
        (newtonCubic (-F0 / (n * L)) (2 * F1 / (n ^ 2 * L))
          (-2 * F2 / (n ^ 3 * L)) (6 * F3 / (n ^ 4 * L))) = F1 ∧
      -(n ^ 3 * L / 2) * forwardDiff2
        (newtonCubic (-F0 / (n * L)) (2 * F1 / (n ^ 2 * L))
          (-2 * F2 / (n ^ 3 * L)) (6 * F3 / (n ^ 4 * L))) = F2 ∧
      (n ^ 4 * L / 6) * forwardDiff3
        (newtonCubic (-F0 / (n * L)) (2 * F1 / (n ^ 2 * L))
          (-2 * F2 / (n ^ 3 * L)) (6 * F3 / (n ^ 4 * L))) = F3
  rw [hcoeff.1, hcoeff.2.1, hcoeff.2.2.1, hcoeff.2.2.2]
  constructor
  · field_simp [hn, hL]
  constructor
  · field_simp [hn, hL]
  constructor <;> field_simp [hn, hL]

end Zeta23.Research.JensenWedge
