import Zeta23.Research.JensenWedge.ElementaryC1Box

/-!
# Exact elementary/saddle decomposition of the xi parameter map

The true four-parameter map splits into the five-boundary elementary map and
a vector depending only on the xi coefficient sequence.  This module proves
that split before any asymptotic estimate or differentiation is applied.
-/

namespace Zeta23.Research.JensenWedge

noncomputable section

/-- Exact discrete second difference of the auxiliary-moment logarithm,
written using the coefficient log and the Gamma-duplication half-shift. -/
def exactXiAuxiliarySecondDiff (n k : ℕ) : ℝ :=
  exactXiHalfShiftLog n k + secondDiff exactXiCoefficientLog (n + k)

/-- The exact xi-only auxiliary-moment contribution after the four
triangular readouts. -/
def exactXiSaddleParameterMap (n : ℕ) (L : ℝ) : BranchPoint := ![
  -((n : ℝ) * L) *
    natForwardDiff0 (exactXiAuxiliarySecondDiff n),
  ((n : ℝ) ^ 2 * L / 2) *
    natForwardDiff1 (exactXiAuxiliarySecondDiff n),
  -((n : ℝ) ^ 3 * L / 2) *
    natForwardDiff2 (exactXiAuxiliarySecondDiff n),
  ((n : ℝ) ^ 4 * L / 6) *
    natForwardDiff3 (exactXiAuxiliarySecondDiff n)
]

/-- The half-shift logarithm is exactly the negative fifth elementary
boundary.  Positivity is stated explicitly so `Real.log_div` is legal. -/
theorem exactXiHalfShiftLog_eq_neg_logRatio
    {n k : ℕ} (hn : 0 < n) :
    exactXiHalfShiftLog n k =
      -logRatio (((1 : ℝ) + (1 / (n : ℝ)) / 2) / (1 / (n : ℝ))) k := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  let a : ℝ := (n : ℝ) + k + 1 / 2
  have ha : 0 < a := by
    dsimp only [a]
    positivity
  have ha1 : 0 < a + 1 := by linarith
  have hscale :
      ((1 : ℝ) + (1 / (n : ℝ)) / 2) / (1 / (n : ℝ)) + k = a := by
    dsimp only [a]
    field_simp [hnR.ne']
    ring
  unfold exactXiHalfShiftLog logRatio
  rw [hscale]
  have hcast : ((n + k : ℕ) : ℝ) + 1 / 2 = a := by
    simp only [Nat.cast_add]
    rfl
  rw [hcast]
  change Real.log (1 + 1 / a) = -(Real.log a - Real.log (a + 1))
  have hquot : 1 + 1 / a = (a + 1) / a := by
    field_simp [ha.ne']
  rw [hquot, Real.log_div ha1.ne' ha.ne']
  ring

/-- Before triangular normalization, the true quotient residual is the sum
of the five elementary logarithmic boundaries and the exact auxiliary-
moment second difference. -/
theorem exactXiQuotientResidual_eq_elementary_add_saddle
    {y : BranchPoint} {n k : ℕ} {L : ℝ}
    (hn : 0 < n) (hL : 0 < L) :
    exactXiQuotientResidual y n L k =
      elementaryQuotientResidual y (1 / (n : ℝ)) (1 / L) k +
        exactXiAuxiliarySecondDiff n k := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have he : 0 < (1 / L : ℝ) := one_div_pos.mpr hL
  rcases residualParameters_eq_jacobiParameters
      (y := y) (n := n) (e := 1 / L) hn he with
    ⟨hA, hB, hC, hD⟩
  have hhalf := exactXiHalfShiftLog_eq_neg_logRatio (n := n) (k := k) hn
  unfold exactXiQuotientResidual exactJacobiLogQuotient
  rw [hA, hB, hC, hD]
  simp only [exactXiAuxiliarySecondDiff, elementaryQuotientResidual,
    jacobiA, jacobiB, jacobiC, jacobiD]
  rw [hhalf]
  ring

/-- The true normalized parameter map is exactly elementary plus xi saddle
on the manuscript's outer box. -/
theorem exactXiParameterMap_eq_elementary_add_saddle
    {y : BranchPoint} (hy : InOuterParameterBox y)
    {n : ℕ} (hn : 0 < n) {L : ℝ} (hL : 0 < L) :
    exactXiParameterMap n L y =
      exactElementaryParameterMap y (1 / (n : ℝ)) (1 / L) +
        exactXiSaddleParameterMap n L := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hx : 0 < (1 / (n : ℝ)) := one_div_pos.mpr hnR
  have he : 0 < (1 / L : ℝ) := one_div_pos.mpr hL
  have helem := elementaryTriangularParameterMap_eq_exactElementary hy hx he
  have hres : exactXiQuotientResidual y n L =
      fun k => elementaryQuotientResidual y (1 / (n : ℝ)) (1 / L) k +
        exactXiAuxiliarySecondDiff n k := by
    funext k
    exact exactXiQuotientResidual_eq_elementary_add_saddle hn hL
  rw [← helem]
  unfold exactXiParameterMap
  rw [hres]
  unfold elementaryTriangularParameterMap exactXiSaddleParameterMap
  ext j
  fin_cases j <;>
    norm_num [natForwardDiff0, natForwardDiff1, natForwardDiff2,
      natForwardDiff3] <;>
    field_simp [hnR.ne', hL.ne'] <;>
    ring

end

end Zeta23.Research.JensenWedge
