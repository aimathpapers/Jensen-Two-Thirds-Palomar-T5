import Zeta23.Research.JensenWedge.ElementaryResidualBranch
import Zeta23.Research.JensenWedge.ExactParameterDecomposition

/-!
# Exact xi saddle certificate and positive branch

The four normalized finite-difference enclosures are packaged here with
their signs and scales exposed.  They imply a sup-norm enclosure for the
exact xi saddle vector and instantiate the elementary contraction theorem
as a locally unique branch for the actual `exactXiParameterMap`.
-/

namespace Zeta23.Research.JensenWedge

noncomputable section

/-- Four exact normalized finite-difference inequalities.  This is the
finite certificate that the remaining analytic estimates must produce. -/
structure ExactXiSaddleIntervalCertificate
    (n : ℕ) (L epsilon : ℝ) : Prop where
  epsilon_nonneg : 0 ≤ epsilon
  orderTwo :
    |-((n : ℝ) * L) *
        natForwardDiff0 (exactXiAuxiliarySecondDiff n) + 2| ≤
      epsilon
  orderThree :
    |((n : ℝ) ^ 2 * L / 2) *
        natForwardDiff1 (exactXiAuxiliarySecondDiff n) + 1| ≤
      epsilon
  orderFour :
    |-((n : ℝ) ^ 3 * L / 2) *
        natForwardDiff2 (exactXiAuxiliarySecondDiff n) + 2| ≤
      epsilon
  orderFive :
    |((n : ℝ) ^ 4 * L / 6) *
        natForwardDiff3 (exactXiAuxiliarySecondDiff n) + 2| ≤
      epsilon

/-- The four scalar inequalities are exactly the branch-space sup-norm
enclosure required by the residual certificate. -/
theorem ExactXiSaddleIntervalCertificate.norm_sub_le
    {n : ℕ} {L epsilon : ℝ}
    (C : ExactXiSaddleIntervalCertificate n L epsilon) :
    ‖exactXiSaddleParameterMap n L - leadingXiSaddleVector‖ ≤ epsilon := by
  rw [pi_norm_le_iff_of_nonneg C.epsilon_nonneg]
  intro j
  fin_cases j
  · simpa [exactXiSaddleParameterMap, leadingXiSaddleVector,
      Real.norm_eq_abs, Matrix.cons_val_zero] using C.orderTwo
  · simpa [exactXiSaddleParameterMap, leadingXiSaddleVector,
      Real.norm_eq_abs, Matrix.cons_val_one] using C.orderThree
  · simpa [exactXiSaddleParameterMap, leadingXiSaddleVector,
      Real.norm_eq_abs, Matrix.cons_val_two] using C.orderFour
  · simpa [exactXiSaddleParameterMap, leadingXiSaddleVector,
      Real.norm_eq_abs, Matrix.cons_val_three] using C.orderFive

/-- The finite xi saddle certificate and the two explicit scale budgets
construct a locally unique positive branch for the true normalized xi map.
The map identity is used on the whole inner box, not merely at the selected
point. -/
noncomputable def exactXi_positiveParameterBranch
    {n : ℕ} (hn : 0 < n) {L epsilon : ℝ}
    (hL : 1 ≤ L)
    (C : ExactXiSaddleIntervalCertificate n L epsilon)
    (hjacobianScale : 1 / L + 1 / (n : ℝ) ≤ 1 / 100000000)
    (hresidualBudget :
      10000 * (1 / L + (1 / (n : ℝ)) / (1 / L)) + epsilon ≤
        (3 / 608) * branchInnerRadius) :
    PositiveParameterBranch (exactXiParameterMap n L) := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hLpos : 0 < L := zero_lt_one.trans_le hL
  have he : 0 < (1 / L : ℝ) := one_div_pos.mpr hLpos
  have he1 : (1 / L : ℝ) ≤ 1 := (div_le_one₀ hLpos).2 hL
  have hx : 0 ≤ (1 / (n : ℝ)) := (one_div_pos.mpr hnR).le
  let B := exactElementaryAffine_positiveParameterBranch
    he he1 hx hjacobianScale C.norm_sub_le hresidualBudget
  refine {
    parameters := B.parameters
    in_inner_box := B.in_inner_box
    equation := ?_
    locally_unique := ?_
  }
  · have hsplit := exactXiParameterMap_eq_elementary_add_saddle
      B.in_outer_box hn hLpos
    rw [hsplit]
    simpa only [exactElementaryAffineMap] using B.equation
  · intro z hz hzero
    apply B.locally_unique z hz
    have hsplit := exactXiParameterMap_eq_elementary_add_saddle
      (branchInnerBox_subset_outer hz) hn hLpos
    rw [hsplit] at hzero
    simpa only [exactElementaryAffineMap] using hzero

end

end Zeta23.Research.JensenWedge
