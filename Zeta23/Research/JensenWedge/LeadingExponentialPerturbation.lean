import Zeta23.Research.JensenWedge.LeadingLocalExpansion

/-!
# Exponentiating the local saddle perturbation

This module is the pointwise bridge between the exact cubic Taylor formula
and the central Gaussian integral.  It keeps the signed cubic term separate,
proves a concrete bound for its coefficient on the selected saddle branch,
and uses the quadratic remainder estimate for the complex exponential.  No
asymptotic `O`-notation or unnamed Taylor constant occurs in the statements.
-/

namespace Zeta23.Research.JensenWedge

open Complex Set

noncomputable section

/-- The part of the local logarithmic phase beyond the linear-quadratic
Gaussian model. -/
def leadingLocalPerturbation (s L : ℂ) (r : ℝ) : ℂ :=
  leadingCubicCoefficient s L * (r : ℂ) ^ 3 + leadingLocalRemainder s L r

/-- On the selected branch the cubic coefficient is no larger than the
Gaussian curvature. -/
theorem quantitativeSaddleBranch_cubicCoefficient_norm_le
    {s : ℂ} (hs : s ∈ leanSaddleSector) :
    ‖leadingCubicCoefficient s (quantitativeSaddleBranch s)‖ ≤
      ‖leadingCurvature s (quantitativeSaddleBranch s)‖ := by
  let L : ℂ := quantitativeSaddleBranch s
  let B : ℂ := s / L
  have hinput := leanSaddleSector_quantitative hs
  have hbounds := quantitativeSaddleBranch_scaled_bounds hinput
  have hLne : L ≠ 0 := hbounds.1
  have hroot : sectorialSaddleEquation s L = 0 :=
    (quantitativeSaddleBranch_spec hinput).2.1
  have hmap : s = L * ((Real.pi : ℂ) * exp L + 3 / 4) := by
    unfold sectorialSaddleEquation saddleParameterMap at hroot
    exact (eq_of_sub_eq_zero hroot).symm
  have hB : B = (Real.pi : ℂ) * exp L + 3 / 4 := by
    simp only [B]
    rw [hmap]
    field_simp [hLne]
  have hratio := quantitativeSaddleBranch_ratio_norm_bounds hs
  have hfirstId : 2 * s / L ^ 3 = 2 * B * (1 / L) ^ 2 := by
    simp only [B]
    field_simp [hLne]
  have hinv : ‖(1 : ℂ) / L‖ ≤ 7 / 50 := by
    simpa only [L] using hbounds.2.1
  have hfirst : ‖2 * s / L ^ 3‖ ≤ ‖B‖ := by
    calc
      ‖2 * s / L ^ 3‖ = ‖2 * B * (1 / L) ^ 2‖ := congrArg norm hfirstId
      _ = 2 * ‖B‖ * ‖(1 : ℂ) / L‖ ^ 2 := by
        rw [norm_mul, norm_mul, norm_pow]
        norm_num
      _ = ‖B‖ * (2 * ‖(1 : ℂ) / L‖ ^ 2) := by ring
      _ ≤ ‖B‖ * 1 := by
        gcongr
        nlinarith [hinv, norm_nonneg ((1 : ℂ) / L),
          sq_nonneg (‖(1 : ℂ) / L‖)]
      _ = ‖B‖ := mul_one _
  have hpiL : (Real.pi : ℂ) * exp L = B - 3 / 4 := by
    rw [hB]
    ring
  have hsecond : ‖(Real.pi : ℂ) * exp L‖ ≤ 2 * ‖B‖ := by
    rw [hpiL]
    calc
      ‖B - 3 / 4‖ ≤ ‖B‖ + 3 / 4 := by
        exact (norm_sub_le B (3 / 4)).trans_eq (by norm_num)
      _ ≤ 2 * ‖B‖ := by nlinarith [hratio.1]
  have hD3 : ‖leadingLogD3 s L‖ ≤ 3 * ‖B‖ := by
    unfold leadingLogD3
    calc
      ‖2 * s / L ^ 3 - (Real.pi : ℂ) * exp L‖ ≤
          ‖2 * s / L ^ 3‖ + ‖(Real.pi : ℂ) * exp L‖ := norm_sub_le _ _
      _ ≤ ‖B‖ + 2 * ‖B‖ := add_le_add hfirst hsecond
      _ = 3 * ‖B‖ := by ring
  change ‖leadingLogD3 s L / 6‖ ≤ ‖leadingCurvature s L‖
  rw [norm_div]
  norm_num
  calc
    ‖leadingLogD3 s L‖ / 6 ≤ (3 * ‖B‖) / 6 := by gcongr
    _ ≤ ‖leadingCurvature s L‖ := by nlinarith [hratio.2]

/-- Concrete norm bound for the entire cubic-plus-quartic logarithmic
perturbation. -/
theorem quantitativeSaddleBranch_localPerturbation_norm_le
    {s : ℂ} (hs : s ∈ leanSaddleSector) {r : ℝ} (hr : |r| ≤ 1 / 10) :
    ‖leadingLocalPerturbation s (quantitativeSaddleBranch s) r‖ ≤
      2 * ‖leadingCurvature s (quantitativeSaddleBranch s)‖ * |r| ^ 3 := by
  let Kabs : ℝ := ‖leadingCurvature s (quantitativeSaddleBranch s)‖
  have hc := quantitativeSaddleBranch_cubicCoefficient_norm_le hs
  have hR := quantitativeSaddleBranch_localRemainder_norm_le hs hr
  have hnonneg : 0 ≤ Kabs * |r| ^ 3 :=
    mul_nonneg (norm_nonneg _) (pow_nonneg (abs_nonneg _) _)
  calc
    ‖leadingLocalPerturbation s (quantitativeSaddleBranch s) r‖ ≤
        ‖leadingCubicCoefficient s (quantitativeSaddleBranch s) * (r : ℂ) ^ 3‖ +
          ‖leadingLocalRemainder s (quantitativeSaddleBranch s) r‖ :=
      norm_add_le _ _
    _ ≤ Kabs * |r| ^ 3 + 6 * Kabs * |r| ^ 4 := by
      gcongr
      rw [norm_mul, norm_pow, norm_real, Real.norm_eq_abs]
      exact mul_le_mul_of_nonneg_right hc (pow_nonneg (abs_nonneg _) _)
    _ = (Kabs * |r| ^ 3) * (1 + 6 * |r|) := by ring
    _ ≤ (Kabs * |r| ^ 3) * 2 := by
      gcongr
      linarith
    _ = 2 * Kabs * |r| ^ 3 := by ring

/-- Exact factorization of the local integrand into its value at the saddle,
the full Gaussian (including the Jacobian-induced linear term), and the
cubic-plus-quartic perturbation. -/
theorem quantitativeSaddleBranch_localFactorization
    {s : ℂ} (hs : s ∈ leanSaddleSector) {r : ℝ} (hr : |r| ≤ 1 / 10) :
    leadingIntegrand s (quantitativeSaddleBranch s + r) =
      leadingIntegrand s (quantitativeSaddleBranch s) *
        leadingGaussian (leadingCurvature s (quantitativeSaddleBranch s)) r *
        exp (leadingLocalPerturbation s (quantitativeSaddleBranch s) r) := by
  let L : ℂ := quantitativeSaddleBranch s
  let K : ℂ := leadingCurvature s L
  have hexact := quantitativeSaddleBranch_localExpansion_exact hs hr
  have hlog :
      leadingLogIntegrand s (L + r) =
        leadingLogIntegrand s L + ((r : ℂ) - K * (r : ℂ) ^ 2 / 2) +
          leadingLocalPerturbation s L r := by
    simp only [L, K] at hexact ⊢
    calc
      leadingLogIntegrand s (quantitativeSaddleBranch s + r) =
          (leadingLogIntegrand s (quantitativeSaddleBranch s + r) -
            leadingLogIntegrand s (quantitativeSaddleBranch s)) +
            leadingLogIntegrand s (quantitativeSaddleBranch s) := by ring
      _ = ((r : ℂ) -
            leadingCurvature s (quantitativeSaddleBranch s) * (r : ℂ) ^ 2 / 2) +
          leadingLocalPerturbation s (quantitativeSaddleBranch s) r +
          leadingLogIntegrand s (quantitativeSaddleBranch s) := by
        rw [hexact]
        unfold leadingLocalPerturbation
        ring
      _ = leadingLogIntegrand s (quantitativeSaddleBranch s) +
          ((r : ℂ) -
            leadingCurvature s (quantitativeSaddleBranch s) * (r : ℂ) ^ 2 / 2) +
          leadingLocalPerturbation s (quantitativeSaddleBranch s) r := by ring
  rw [leadingIntegrand_eq_exp_logIntegrand,
    leadingIntegrand_eq_exp_logIntegrand, hlog, exp_add, exp_add]
  rfl

/-- Once the central scale makes `|K||r|^3 <= 1/2`, exponentiating the
perturbation leaves exactly the quartic and squared-cubic error terms used in
the paper. -/
theorem quantitativeSaddleBranch_expPerturbation_sub_cubic_norm_le
    {s : ℂ} (hs : s ∈ leanSaddleSector) {r : ℝ} (hr : |r| ≤ 1 / 10)
    (hcentral :
      ‖leadingCurvature s (quantitativeSaddleBranch s)‖ * |r| ^ 3 ≤ 1 / 2) :
    ‖exp (leadingLocalPerturbation s (quantitativeSaddleBranch s) r) - 1 -
        leadingCubicCoefficient s (quantitativeSaddleBranch s) * (r : ℂ) ^ 3‖ ≤
      6 * ‖leadingCurvature s (quantitativeSaddleBranch s)‖ * |r| ^ 4 +
        4 * ‖leadingCurvature s (quantitativeSaddleBranch s)‖ ^ 2 * |r| ^ 6 := by
  let L : ℂ := quantitativeSaddleBranch s
  let Kabs : ℝ := ‖leadingCurvature s L‖
  let cterm : ℂ := leadingCubicCoefficient s L * (r : ℂ) ^ 3
  let R : ℂ := leadingLocalRemainder s L r
  let z : ℂ := leadingLocalPerturbation s L r
  have hzBound : ‖z‖ ≤ 2 * Kabs * |r| ^ 3 :=
    quantitativeSaddleBranch_localPerturbation_norm_le hs hr
  have hzOne : ‖z‖ ≤ 1 := by
    calc
      ‖z‖ ≤ 2 * Kabs * |r| ^ 3 := hzBound
      _ = 2 * (Kabs * |r| ^ 3) := by ring
      _ ≤ 1 := by linarith
  have hexp := Complex.norm_exp_sub_one_sub_id_le hzOne
  have hR : ‖R‖ ≤ 6 * Kabs * |r| ^ 4 :=
    quantitativeSaddleBranch_localRemainder_norm_le hs hr
  have hzSq : ‖z‖ ^ 2 ≤ 4 * Kabs ^ 2 * |r| ^ 6 := by
    calc
      ‖z‖ ^ 2 ≤ (2 * Kabs * |r| ^ 3) ^ 2 :=
        pow_le_pow_left₀ (norm_nonneg _) hzBound 2
      _ = 4 * Kabs ^ 2 * |r| ^ 6 := by ring
  have hrewrite : exp z - 1 - cterm = (exp z - 1 - z) + R := by
    simp only [z, cterm, R, leadingLocalPerturbation]
    ring
  change ‖exp z - 1 - cterm‖ ≤
    6 * Kabs * |r| ^ 4 + 4 * Kabs ^ 2 * |r| ^ 6
  rw [hrewrite]
  calc
    ‖(exp z - 1 - z) + R‖ ≤ ‖exp z - 1 - z‖ + ‖R‖ := norm_add_le _ _
    _ ≤ ‖z‖ ^ 2 + 6 * Kabs * |r| ^ 4 := add_le_add hexp hR
    _ ≤ 4 * Kabs ^ 2 * |r| ^ 6 + 6 * Kabs * |r| ^ 4 :=
      add_le_add hzSq (le_refl _)
    _ = 6 * Kabs * |r| ^ 4 + 4 * Kabs ^ 2 * |r| ^ 6 := by ring

/-- Pointwise central-window comparison after restoring the saddle-value and
Gaussian factors. -/
theorem quantitativeSaddleBranch_integrand_sub_cubicGaussian_norm_le
    {s : ℂ} (hs : s ∈ leanSaddleSector) {r : ℝ} (hr : |r| ≤ 1 / 10)
    (hcentral :
      ‖leadingCurvature s (quantitativeSaddleBranch s)‖ * |r| ^ 3 ≤ 1 / 2) :
    ‖leadingIntegrand s (quantitativeSaddleBranch s + r) -
        leadingIntegrand s (quantitativeSaddleBranch s) *
          leadingGaussian (leadingCurvature s (quantitativeSaddleBranch s)) r *
          (1 + leadingCubicCoefficient s (quantitativeSaddleBranch s) *
            (r : ℂ) ^ 3)‖ ≤
      ‖leadingIntegrand s (quantitativeSaddleBranch s)‖ *
        ‖leadingGaussian (leadingCurvature s (quantitativeSaddleBranch s)) r‖ *
        (6 * ‖leadingCurvature s (quantitativeSaddleBranch s)‖ * |r| ^ 4 +
          4 * ‖leadingCurvature s (quantitativeSaddleBranch s)‖ ^ 2 * |r| ^ 6) := by
  rw [quantitativeSaddleBranch_localFactorization hs hr]
  have hfactor :
      leadingIntegrand s (quantitativeSaddleBranch s) *
          leadingGaussian (leadingCurvature s (quantitativeSaddleBranch s)) r *
          exp (leadingLocalPerturbation s (quantitativeSaddleBranch s) r) -
        leadingIntegrand s (quantitativeSaddleBranch s) *
          leadingGaussian (leadingCurvature s (quantitativeSaddleBranch s)) r *
          (1 + leadingCubicCoefficient s (quantitativeSaddleBranch s) *
            (r : ℂ) ^ 3) =
      (leadingIntegrand s (quantitativeSaddleBranch s) *
          leadingGaussian (leadingCurvature s (quantitativeSaddleBranch s)) r) *
        (exp (leadingLocalPerturbation s (quantitativeSaddleBranch s) r) - 1 -
          leadingCubicCoefficient s (quantitativeSaddleBranch s) * (r : ℂ) ^ 3) := by
    ring
  rw [hfactor, norm_mul, norm_mul]
  gcongr
  exact quantitativeSaddleBranch_expPerturbation_sub_cubic_norm_le hs hr hcentral

end

end Zeta23.Research.JensenWedge
