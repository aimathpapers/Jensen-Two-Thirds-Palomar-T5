import Zeta23.Research.JensenWedge.LeadingHorizontalConcavity
import Zeta23.Research.JensenWedge.LeadingCentralWindow

/-!
# Quantitative central-window boundary data

This module converts the local fourth-order expansion into a uniform phase
drop at the two endpoints `r = ±rho`, where `rho = |K|^(-2/5)`.  It then
combines that drop with strict horizontal concavity to prove the derivative
signs needed for the left and right tail integrals.
-/

namespace Zeta23.Research.JensenWedge

open Complex Set

noncomputable section

/-- The explicit curvature lower bound makes `|K| rho` large. -/
theorem quantitativeSaddleBranch_curvature_mul_centralRadius_ge
    {s : ℂ} (hs : s ∈ leanSaddleSector) :
    125 ≤ ‖leadingCurvature s (quantitativeSaddleBranch s)‖ *
      leadingCentralRadius
        (leadingCurvature s (quantitativeSaddleBranch s)) := by
  let Kabs : ℝ := ‖leadingCurvature s (quantitativeSaddleBranch s)‖
  have hK : (3125 : ℝ) ≤ Kabs := by
    linarith [quantitativeSaddleBranch_curvature_norm_ge_fourThousand hs]
  have hKpos : 0 < Kabs := lt_of_lt_of_le (by norm_num) hK
  have hid : Kabs * Kabs ^ (-(2 / 5 : ℝ)) = Kabs ^ (3 / 5 : ℝ) := by
    calc
      Kabs * Kabs ^ (-(2 / 5 : ℝ)) =
          Kabs ^ (1 : ℝ) * Kabs ^ (-(2 / 5 : ℝ)) := by rw [Real.rpow_one]
      _ = Kabs ^ ((1 : ℝ) + (-(2 / 5 : ℝ))) := by
        rw [Real.rpow_add hKpos]
      _ = Kabs ^ (3 / 5 : ℝ) := by norm_num
  unfold leadingCentralRadius
  change 125 ≤ Kabs * Kabs ^ (-(2 / 5 : ℝ))
  rw [hid]
  calc
    (125 : ℝ) = (3125 : ℝ) ^ (3 / 5 : ℝ) := by
      rw [show (3125 : ℝ) = 5 ^ 5 by norm_num, ← Real.rpow_natCast,
        ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 5)]
      norm_num
    _ ≤ Kabs ^ (3 / 5 : ℝ) :=
      Real.rpow_le_rpow (by norm_num) hK (by norm_num)

/-- At either endpoint of the concrete central window, the real phase has
dropped by at least `|K| rho^2 / 20` from its saddle value. -/
theorem quantitativeSaddleBranch_horizontal_boundary_phase_gap
    {s : ℂ} (hs : s ∈ leanSaddleSector) {r : ℝ}
    (hr : |r| = leadingCentralRadius
      (leadingCurvature s (quantitativeSaddleBranch s))) :
    (leadingLogIntegrand s (quantitativeSaddleBranch s + r)).re -
        (leadingLogIntegrand s (quantitativeSaddleBranch s)).re ≤
      -(‖leadingCurvature s (quantitativeSaddleBranch s)‖ * r ^ 2 / 20) := by
  let L : ℂ := quantitativeSaddleBranch s
  let K : ℂ := leadingCurvature s L
  let Kabs : ℝ := ‖K‖
  let ρ : ℝ := leadingCentralRadius K
  let c : ℂ := leadingCubicCoefficient s L
  let R : ℂ := leadingLocalRemainder s L r
  have hρpos : 0 < ρ := by
    simpa only [L, K, ρ] using quantitativeSaddleBranch_centralRadius_pos hs
  have hrabs : |r| = ρ := by simpa only [L, K, ρ] using hr
  have hrle : |r| ≤ 1 / 10 := by
    rw [hrabs]
    simpa only [L, K, ρ] using
      quantitativeSaddleBranch_centralRadius_le_tenth hs
  have hexact := quantitativeSaddleBranch_localExpansion_exact hs hrle
  have hc : ‖c‖ ≤ Kabs := by
    simpa only [L, K, Kabs, c] using
      quantitativeSaddleBranch_cubicCoefficient_norm_le hs
  have hR : ‖R‖ ≤ 6 * Kabs * |r| ^ 4 := by
    simpa only [L, K, Kabs, R] using
      quantitativeSaddleBranch_localRemainder_norm_le hs hrle
  have hKre : Kabs ≤ 2 * K.re := by
    simpa only [L, K, Kabs] using
      (quantitativeSaddleBranch_curvature_strong_bounds hs).2
  have hrealC : (c * (r : ℂ) ^ 3).re ≤ Kabs * |r| ^ 3 := by
    calc
      (c * (r : ℂ) ^ 3).re ≤ ‖c * (r : ℂ) ^ 3‖ := Complex.re_le_norm _
      _ = ‖c‖ * |r| ^ 3 := by
        rw [norm_mul, norm_pow, norm_real, Real.norm_eq_abs]
      _ ≤ Kabs * |r| ^ 3 := by gcongr
  have hrealR : R.re ≤ 6 * Kabs * |r| ^ 4 :=
    (Complex.re_le_norm R).trans hR
  have hraw :
      (leadingLogIntegrand s (L + r)).re - (leadingLogIntegrand s L).re ≤
        |r| - Kabs * r ^ 2 / 4 + Kabs * |r| ^ 3 +
          6 * Kabs * |r| ^ 4 := by
    rw [← sub_re, hexact]
    have hquad : (K * (r : ℂ) ^ 2 / 2).re = K.re * r ^ 2 / 2 := by
      norm_num [Complex.div_re, pow_two]
    simp only [add_re, sub_re, ofReal_re]
    rw [hquad]
    have hrself : r ≤ |r| := le_abs_self r
    have hquadBound : Kabs * r ^ 2 / 4 ≤ K.re * r ^ 2 / 2 := by
      have hr2nonneg : 0 ≤ r ^ 2 := sq_nonneg r
      nlinarith
    nlinarith
  have hKρ : 125 ≤ Kabs * ρ := by
    simpa only [L, K, Kabs, ρ] using
      quantitativeSaddleBranch_curvature_mul_centralRadius_ge hs
  have hlin : ρ ≤ Kabs * ρ ^ 2 / 125 := by
    have := mul_le_mul_of_nonneg_right hKρ hρpos.le
    nlinarith
  have hcubic : Kabs * ρ ^ 3 ≤ Kabs * ρ ^ 2 / 10 := by
    have hρle : ρ ≤ 1 / 10 := by
      simpa only [L, K, ρ] using
        quantitativeSaddleBranch_centralRadius_le_tenth hs
    have hKnonneg : 0 ≤ Kabs := norm_nonneg K
    nlinarith [sq_nonneg ρ]
  have hquartic :
      6 * Kabs * ρ ^ 4 ≤ (3 / 50 : ℝ) * Kabs * ρ ^ 2 := by
    have hρle : ρ ≤ 1 / 10 := by
      simpa only [L, K, ρ] using
        quantitativeSaddleBranch_centralRadius_le_tenth hs
    have hρ2 : ρ ^ 2 ≤ 1 / 100 := by nlinarith
    have hKnonneg : 0 ≤ Kabs := norm_nonneg K
    nlinarith [sq_nonneg ρ]
  rw [hrabs] at hraw
  have hr2 : r ^ 2 = ρ ^ 2 := by nlinarith [sq_abs r]
  rw [hr2] at hraw ⊢
  calc
    (leadingLogIntegrand s (L + r)).re - (leadingLogIntegrand s L).re ≤
        ρ - Kabs * ρ ^ 2 / 4 + Kabs * ρ ^ 3 +
          6 * Kabs * ρ ^ 4 := hraw
    _ ≤ -(Kabs * ρ ^ 2 / 20) := by
      have hKρ2nonneg : 0 ≤ Kabs * ρ ^ 2 :=
        mul_nonneg (norm_nonneg K) (sq_nonneg ρ)
      nlinarith [hlin, hcubic, hquartic]

/-- Both signed endpoints satisfy the preceding phase gap. -/
theorem quantitativeSaddleBranch_horizontal_boundary_phase_gaps
    {s : ℂ} (hs : s ∈ leanSaddleSector) :
    let L := quantitativeSaddleBranch s
    let K := leadingCurvature s L
    let ρ := leadingCentralRadius K
    (leadingLogIntegrand s (L + ρ)).re - (leadingLogIntegrand s L).re ≤
        -(‖K‖ * ρ ^ 2 / 20) ∧
      (leadingLogIntegrand s (L - ρ)).re - (leadingLogIntegrand s L).re ≤
        -(‖K‖ * ρ ^ 2 / 20) := by
  dsimp only
  let L : ℂ := quantitativeSaddleBranch s
  let K : ℂ := leadingCurvature s L
  let ρ : ℝ := leadingCentralRadius K
  have hρpos : 0 < ρ := by
    simpa only [L, K, ρ] using quantitativeSaddleBranch_centralRadius_pos hs
  constructor
  · simpa only [L, K, ρ] using
      quantitativeSaddleBranch_horizontal_boundary_phase_gap hs
        (r := ρ) (abs_of_pos hρpos)
  · have hgap := quantitativeSaddleBranch_horizontal_boundary_phase_gap hs
      (r := -ρ) (by simp [L, K, ρ, abs_of_pos hρpos])
    simpa [L, K, ρ, sub_eq_add_neg] using hgap

/-- Strict concavity turns the two phase gaps into the outward derivative
signs used by the exponential-tail integrals. -/
theorem quantitativeSaddleBranch_horizontal_boundary_derivative_signs
    {s : ℂ} (hs : s ∈ leanSaddleSector) :
    let L := quantitativeSaddleBranch s
    let K := leadingCurvature s L
    let ρ := leadingCentralRadius K
    1 < deriv (leadingHorizontalRealLog s L) (-ρ) ∧
      deriv (leadingHorizontalRealLog s L) ρ < -(‖K‖ * ρ / 20) := by
  dsimp only
  let L : ℂ := quantitativeSaddleBranch s
  let K : ℂ := leadingCurvature s L
  let ρ : ℝ := leadingCentralRadius K
  let f : ℝ → ℝ := leadingHorizontalRealLog s L
  let S : Set ℝ := Ici (1 - L.re)
  have hLre : 1000 < L.re := by
    simpa only [L] using quantitativeSaddleBranch_re_gt hs
  have hρpos : 0 < ρ := by
    simpa only [L, K, ρ] using quantitativeSaddleBranch_centralRadius_pos hs
  have hρle : ρ ≤ 1 / 10 := by
    simpa only [L, K, ρ] using
      quantitativeSaddleBranch_centralRadius_le_tenth hs
  have hleftMem : -ρ ∈ S := by
    simp only [S, mem_Ici]
    linarith
  have hzeroMem : (0 : ℝ) ∈ S := by
    simp only [S, mem_Ici]
    linarith
  have hrightMem : ρ ∈ S := by
    simp only [S, mem_Ici]
    linarith
  have hdiff : ∀ x ∈ S, DifferentiableAt ℝ f x := by
    intro x hx
    apply (hasDerivAt_leadingHorizontalRealLog
      (s := s) (L := L) (r := x) ?_).differentiableAt
    simp only [add_re, ofReal_re]
    have hx' : 1 - L.re ≤ x := hx
    linarith
  have hconc : StrictConcaveOn ℝ S f := by
    simpa only [L, S, f] using
      quantitativeSaddleBranch_horizontal_strictConcaveOn hs
  have hroot : sectorialSaddleEquation s L = 0 := by
    simpa only [L] using
      (quantitativeSaddleBranch_spec
        (leanSaddleSector_quantitative hs)).2.1
  have hLne : L ≠ 0 := by
    intro hzero
    rw [hzero] at hLre
    norm_num at hLre
  have hd1 : leadingHorizontalRealD1 s L 0 = 1 := by
    unfold leadingHorizontalRealD1 leadingHorizontalD1
    norm_num
    rw [leadingLogD1_at_saddle hLne hroot]
    norm_num
  have hderivZero : deriv f 0 = 1 := by
    have hpos : 0 < (L + (0 : ℝ)).re := by simp; linarith
    have h := hasDerivAt_leadingHorizontalRealLog (s := s) (L := L) hpos
    simpa only [f, h.deriv, hd1]
  constructor
  · have hanti := hconc.strictAntiOn_deriv hdiff
    have h := hanti hleftMem hzeroMem (by linarith : -ρ < 0)
    rw [hderivZero] at h
    exact h
  · have hpos : 0 < (L + (ρ : ℝ)).re := by
      simp only [add_re, ofReal_re]
      linarith
    have hderivR :=
      hasDerivAt_leadingHorizontalRealLog (s := s) (L := L) hpos
    have hslope :=
      hconc.lt_slope_of_hasDerivAt hzeroMem hrightMem hρpos hderivR
    have hgap := quantitativeSaddleBranch_horizontal_boundary_phase_gap hs
      (r := ρ) (abs_of_pos hρpos)
    have hslopeBound : slope f 0 ρ ≤ -(‖K‖ * ρ / 20) := by
      rw [slope_def_field, sub_zero]
      apply (div_le_iff₀ hρpos).2
      change f ρ - f 0 ≤ -(‖K‖ * ρ / 20) * ρ
      have hgap' : f ρ - f 0 ≤ -(‖K‖ * ρ ^ 2 / 20) := by
        simpa [f, L, K, leadingHorizontalRealLog,
          leadingHorizontalLog] using hgap
      nlinarith
    have hfinal := hslope.trans_le hslopeBound
    have hderivReq : deriv f ρ = leadingHorizontalRealD1 s L ρ := by
      simpa only [f] using hderivR.deriv
    rw [hderivReq]
    simpa only [L, K, ρ, f] using hfinal

end

end Zeta23.Research.JensenWedge
