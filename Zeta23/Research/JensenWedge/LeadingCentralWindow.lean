import Zeta23.Research.JensenWedge.LeadingExponentialPerturbation

/-!
# The concrete central saddle window

This module instantiates the paper's radius `rho = |K|^(-2/5)`.  It first
derives a large explicit lower bound for the selected curvature from the
already proved saddle box and sector cutoff.  That lower bound proves both
that the window stays inside the local Taylor segment and that the
exponential perturbation is small.  The pointwise comparison is then
integrated over the central interval and dominated by the whole-line fourth
and sixth absolute Gaussian moments.
-/

namespace Zeta23.Research.JensenWedge

open Complex Filter MeasureTheory Set

noncomputable section

/-- The central radius used in the paper. -/
def leadingCentralRadius (K : ℂ) : ℝ :=
  ‖K‖ ^ (-(2 / 5 : ℝ))

/-- The very large radial cutoff and the sharpened saddle disc force a
concrete lower bound on the Gaussian curvature. -/
theorem quantitativeSaddleBranch_curvature_norm_ge_fourThousand
    {s : ℂ} (hs : s ∈ leanSaddleSector) :
    4000 ≤ ‖leadingCurvature s (quantitativeSaddleBranch s)‖ := by
  let L : ℂ := quantitativeSaddleBranch s
  let B : ℂ := s / L
  have hinput := leanSaddleSector_quantitative hs
  have hsne : s ≠ 0 := hinput.parameter_ne_zero
  have hLne : L ≠ 0 := (quantitativeSaddleBranch_scaled_bounds hinput).1
  have hdist : ‖L - saddleComparisonCenter s‖ ≤ 11 / 750 := by
    simpa only [L, dist_eq] using quantitativeSaddleBranch_dist_center_le hinput
  have hratioIdentity :
      L / s = saddleComparisonCenter s / s +
        (L - saddleComparisonCenter s) * ((1 : ℂ) / s) := by
    field_simp [hsne]
    ring
  have hLs : ‖L / s‖ ≤ 1 / 8000 := by
    rw [hratioIdentity]
    calc
      ‖saddleComparisonCenter s / s +
          (L - saddleComparisonCenter s) * ((1 : ℂ) / s)‖ ≤
          ‖saddleComparisonCenter s / s‖ +
            ‖(L - saddleComparisonCenter s) * ((1 : ℂ) / s)‖ :=
        norm_add_le _ _
      _ = ‖saddleComparisonCenter s / s‖ +
          ‖L - saddleComparisonCenter s‖ * ‖(1 : ℂ) / s‖ := by
        rw [norm_mul]
      _ ≤ 1 / 10000 + (11 / 750) * (1 / 1000) := by
        exact add_le_add hinput.center_parameter_ratio_le
          (mul_le_mul hdist hinput.parameter_inverse_le
            (norm_nonneg ((1 : ℂ) / s)) (by norm_num))
      _ ≤ 1 / 8000 := by norm_num
  have hprod : B * (L / s) = 1 := by
    simp only [B]
    field_simp [hsne, hLne]
  have hprodNorm : (1 : ℝ) = ‖B‖ * ‖L / s‖ := by
    calc
      (1 : ℝ) = ‖(1 : ℂ)‖ := by norm_num
      _ = ‖B * (L / s)‖ := by rw [hprod]
      _ = ‖B‖ * ‖L / s‖ := norm_mul _ _
  have hBone : (8000 : ℝ) ≤ ‖B‖ := by
    have hupper : ‖B‖ * ‖L / s‖ ≤ ‖B‖ * (1 / 8000) := by
      gcongr
    nlinarith [hprodNorm, norm_nonneg B]
  have hratio := quantitativeSaddleBranch_ratio_norm_bounds hs
  change 4000 ≤ ‖leadingCurvature s L‖
  nlinarith

theorem quantitativeSaddleBranch_centralRadius_pos
    {s : ℂ} (hs : s ∈ leanSaddleSector) :
    0 < leadingCentralRadius
      (leadingCurvature s (quantitativeSaddleBranch s)) := by
  unfold leadingCentralRadius
  apply Real.rpow_pos_of_pos
  have hK := quantitativeSaddleBranch_curvature_norm_ge_fourThousand hs
  linarith

theorem quantitativeSaddleBranch_centralRadius_le_tenth
    {s : ℂ} (hs : s ∈ leanSaddleSector) :
    leadingCentralRadius (leadingCurvature s (quantitativeSaddleBranch s)) ≤
      1 / 10 := by
  let Kabs : ℝ := ‖leadingCurvature s (quantitativeSaddleBranch s)‖
  have hK : (1000 : ℝ) ≤ Kabs := by
    linarith [quantitativeSaddleBranch_curvature_norm_ge_fourThousand hs]
  unfold leadingCentralRadius
  change Kabs ^ (-(2 / 5 : ℝ)) ≤ 1 / 10
  calc
    Kabs ^ (-(2 / 5 : ℝ)) ≤ (1000 : ℝ) ^ (-(2 / 5 : ℝ)) := by
      exact Real.rpow_le_rpow_of_nonpos (by norm_num) hK (by norm_num)
    _ = (10 : ℝ) ^ (-(6 / 5 : ℝ)) := by
      rw [show (1000 : ℝ) = 10 ^ 3 by norm_num, ← Real.rpow_natCast,
        ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 10)]
      norm_num
    _ ≤ (10 : ℝ) ^ (-1 : ℝ) := by
      exact Real.rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num)
    _ = 1 / 10 := by norm_num [Real.rpow_neg_one]

/-- The radius makes the cubic perturbation uniformly small. -/
theorem quantitativeSaddleBranch_curvature_mul_centralRadius_cube_le_half
    {s : ℂ} (hs : s ∈ leanSaddleSector) :
    ‖leadingCurvature s (quantitativeSaddleBranch s)‖ *
        leadingCentralRadius
          (leadingCurvature s (quantitativeSaddleBranch s)) ^ 3 ≤
      1 / 2 := by
  let Kabs : ℝ := ‖leadingCurvature s (quantitativeSaddleBranch s)‖
  have hK : (32 : ℝ) ≤ Kabs := by
    linarith [quantitativeSaddleBranch_curvature_norm_ge_fourThousand hs]
  have hKpos : 0 < Kabs := lt_of_lt_of_le (by norm_num) hK
  have hid :
      Kabs * (Kabs ^ (-(2 / 5 : ℝ))) ^ 3 =
        Kabs ^ (-(1 / 5 : ℝ)) := by
    calc
      Kabs * (Kabs ^ (-(2 / 5 : ℝ))) ^ 3 =
          Kabs ^ (1 : ℝ) * Kabs ^ ((-(2 / 5 : ℝ)) * 3) := by
        rw [Real.rpow_one, ← Real.rpow_mul_natCast hKpos.le]
        norm_num
      _ = Kabs ^ ((1 : ℝ) + (-(2 / 5 : ℝ)) * 3) := by
        rw [Real.rpow_add hKpos]
      _ = Kabs ^ (-(1 / 5 : ℝ)) := by norm_num
  unfold leadingCentralRadius
  change Kabs * (Kabs ^ (-(2 / 5 : ℝ))) ^ 3 ≤ 1 / 2
  rw [hid]
  calc
    Kabs ^ (-(1 / 5 : ℝ)) ≤ (32 : ℝ) ^ (-(1 / 5 : ℝ)) := by
      exact Real.rpow_le_rpow_of_nonpos (by norm_num) hK (by norm_num)
    _ = 1 / 2 := by
      rw [show (32 : ℝ) = 2 ^ 5 by norm_num, ← Real.rpow_natCast,
        ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2)]
      norm_num [Real.rpow_neg_one]

/-- Every point in the concrete central interval satisfies both hypotheses
of the pointwise exponential comparison. -/
theorem quantitativeSaddleBranch_centralWindow_conditions
    {s : ℂ} (hs : s ∈ leanSaddleSector) {r : ℝ}
    (hr : |r| ≤ leadingCentralRadius
      (leadingCurvature s (quantitativeSaddleBranch s))) :
    |r| ≤ 1 / 10 ∧
      ‖leadingCurvature s (quantitativeSaddleBranch s)‖ * |r| ^ 3 ≤ 1 / 2 := by
  have hrhoNonneg : 0 ≤ leadingCentralRadius
      (leadingCurvature s (quantitativeSaddleBranch s)) :=
    (quantitativeSaddleBranch_centralRadius_pos hs).le
  constructor
  · exact hr.trans (quantitativeSaddleBranch_centralRadius_le_tenth hs)
  · calc
      ‖leadingCurvature s (quantitativeSaddleBranch s)‖ * |r| ^ 3 ≤
          ‖leadingCurvature s (quantitativeSaddleBranch s)‖ *
            leadingCentralRadius
              (leadingCurvature s (quantitativeSaddleBranch s)) ^ 3 := by
        exact mul_le_mul_of_nonneg_left
          (pow_le_pow_left₀ (abs_nonneg r) hr 3) (norm_nonneg _)
      _ ≤ 1 / 2 :=
        quantitativeSaddleBranch_curvature_mul_centralRadius_cube_le_half hs

/-- Pointwise comparison specialized to the actual paper radius. -/
theorem quantitativeSaddleBranch_centralWindow_pointwise
    {s : ℂ} (hs : s ∈ leanSaddleSector) {r : ℝ}
    (hr : |r| ≤ leadingCentralRadius
      (leadingCurvature s (quantitativeSaddleBranch s))) :
    ‖leadingIntegrand s (quantitativeSaddleBranch s + r) -
        leadingIntegrand s (quantitativeSaddleBranch s) *
          leadingGaussian (leadingCurvature s (quantitativeSaddleBranch s)) r *
          (1 + leadingCubicCoefficient s (quantitativeSaddleBranch s) *
            (r : ℂ) ^ 3)‖ ≤
      ‖leadingIntegrand s (quantitativeSaddleBranch s)‖ *
        ‖leadingGaussian (leadingCurvature s (quantitativeSaddleBranch s)) r‖ *
        (6 * ‖leadingCurvature s (quantitativeSaddleBranch s)‖ * |r| ^ 4 +
          4 * ‖leadingCurvature s (quantitativeSaddleBranch s)‖ ^ 2 * |r| ^ 6) := by
  exact quantitativeSaddleBranch_integrand_sub_cubicGaussian_norm_le hs
    (quantitativeSaddleBranch_centralWindow_conditions hs hr).1
    (quantitativeSaddleBranch_centralWindow_conditions hs hr).2

/-- The integrated local error is controlled by the whole-line fourth and
sixth absolute Gaussian moments. -/
theorem quantitativeSaddleBranch_centralWindow_integral_error_le
    {s : ℂ} (hs : s ∈ leanSaddleSector) :
    let L := quantitativeSaddleBranch s
    let K := leadingCurvature s L
    let ρ := leadingCentralRadius K
    ‖∫ r : ℝ in Icc (-ρ) ρ,
        (leadingIntegrand s (L + r) -
          leadingIntegrand s L * leadingGaussian K r *
            (1 + leadingCubicCoefficient s L * (r : ℂ) ^ 3))‖ ≤
      ‖leadingIntegrand s L‖ *
        (6 * ‖K‖ * (∫ r : ℝ, ‖(r : ℂ) ^ 4 * leadingGaussian K r‖) +
          4 * ‖K‖ ^ 2 * (∫ r : ℝ, ‖(r : ℂ) ^ 6 * leadingGaussian K r‖)) := by
  dsimp only
  let L : ℂ := quantitativeSaddleBranch s
  let K : ℂ := leadingCurvature s L
  let A : ℝ := ‖leadingIntegrand s L‖
  let E : ℝ → ℂ := fun r =>
    leadingIntegrand s (L + r) - leadingIntegrand s L * leadingGaussian K r *
      (1 + leadingCubicCoefficient s L * (r : ℂ) ^ 3)
  let G : ℝ → ℝ := fun r =>
    A * (6 * ‖K‖ * ‖(r : ℂ) ^ 4 * leadingGaussian K r‖ +
      4 * ‖K‖ ^ 2 * ‖(r : ℂ) ^ 6 * leadingGaussian K r‖)
  have hKre : 0 < K.re := quantitativeSaddleBranch_curvature_re_pos hs
  have h4 : Integrable (fun r : ℝ => ‖(r : ℂ) ^ 4 * leadingGaussian K r‖) :=
    (integrable_pow_mul_leadingGaussian hKre 4).norm
  have h6 : Integrable (fun r : ℝ => ‖(r : ℂ) ^ 6 * leadingGaussian K r‖) :=
    (integrable_pow_mul_leadingGaussian hKre 6).norm
  have hG : Integrable G := by
    exact (((h4.const_mul (6 * ‖K‖)).add
      (h6.const_mul (4 * ‖K‖ ^ 2))).const_mul A)
  have hpoint : ∀ r ∈ Icc (-leadingCentralRadius K) (leadingCentralRadius K),
      ‖E r‖ ≤ G r := by
    intro r hr
    have habs : |r| ≤ leadingCentralRadius K := by
      rw [abs_le]
      exact hr
    have hp := quantitativeSaddleBranch_centralWindow_pointwise hs habs
    change ‖E r‖ ≤ G r
    calc
      ‖E r‖ ≤ A * ‖leadingGaussian K r‖ *
          (6 * ‖K‖ * |r| ^ 4 + 4 * ‖K‖ ^ 2 * |r| ^ 6) := hp
      _ = G r := by
        simp only [G, norm_mul, norm_pow, norm_real, Real.norm_eq_abs]
        ring
  have hrestricted :
      ‖∫ r : ℝ in Icc (-leadingCentralRadius K) (leadingCentralRadius K), E r‖ ≤
        ∫ r : ℝ in Icc (-leadingCentralRadius K) (leadingCentralRadius K), G r := by
    apply norm_integral_le_of_norm_le hG.restrict
    filter_upwards [ae_restrict_mem measurableSet_Icc] with r hr
    exact hpoint r hr
  have hnonneg : ∀ r : ℝ, 0 ≤ G r := by
    intro r
    dsimp only [G, A]
    positivity
  have hwhole :
      (∫ r : ℝ in Icc (-leadingCentralRadius K) (leadingCentralRadius K), G r) ≤
        ∫ r : ℝ, G r :=
    setIntegral_le_integral hG (Eventually.of_forall hnonneg)
  change ‖∫ r : ℝ in Icc (-leadingCentralRadius K) (leadingCentralRadius K), E r‖ ≤
    A * (6 * ‖K‖ * (∫ r : ℝ, ‖(r : ℂ) ^ 4 * leadingGaussian K r‖) +
      4 * ‖K‖ ^ 2 * (∫ r : ℝ, ‖(r : ℂ) ^ 6 * leadingGaussian K r‖))
  calc
    ‖∫ r : ℝ in Icc (-leadingCentralRadius K) (leadingCentralRadius K), E r‖ ≤
        ∫ r : ℝ in Icc (-leadingCentralRadius K) (leadingCentralRadius K), G r :=
      hrestricted
    _ ≤ ∫ r : ℝ, G r := hwhole
    _ = A * (6 * ‖K‖ * (∫ r : ℝ, ‖(r : ℂ) ^ 4 * leadingGaussian K r‖) +
        4 * ‖K‖ ^ 2 * (∫ r : ℝ, ‖(r : ℂ) ^ 6 * leadingGaussian K r‖)) := by
      simp only [G]
      rw [integral_const_mul, integral_add (h4.const_mul _) (h6.const_mul _),
        integral_const_mul, integral_const_mul]

end

end Zeta23.Research.JensenWedge
