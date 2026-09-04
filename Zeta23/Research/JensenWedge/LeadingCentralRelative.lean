import Zeta23.Research.JensenWedge.LeadingMomentScale

/-!
# Relative central Gaussian theorem

This module closes the central portion of T3.  It inserts the fixed fourth,
sixth, eighth, and tenth moment bounds into the local and truncation ledgers,
then divides by the exact nonzero Gaussian main term.  The final statement is
about the actual central integral, not an abstract error placeholder.
-/

namespace Zeta23.Research.JensenWedge

open Complex MeasureTheory Set

noncomputable section

theorem quantitativeSaddleBranch_localMomentLedger_le
    {s : ℂ} (hs : s ∈ leanSaddleSector) :
    let K := leadingCurvature s (quantitativeSaddleBranch s)
    6 * ‖K‖ * (∫ r : ℝ, ‖(r : ℂ) ^ 4 * leadingGaussian K r‖) +
        4 * ‖K‖ ^ 2 * (∫ r : ℝ, ‖(r : ℂ) ^ 6 * leadingGaussian K r‖) ≤
      286720 * ‖K‖ ^ (-(3 / 2 : ℝ)) := by
  dsimp only
  let K := leadingCurvature s (quantitativeSaddleBranch s)
  have hKpos : 0 < ‖K‖ := by
    linarith [quantitativeSaddleBranch_curvature_norm_ge_fourThousand hs]
  have h4 := quantitativeSaddleBranch_fourthGaussianMoment_le hs
  have h6 := quantitativeSaddleBranch_sixthGaussianMoment_le hs
  have hid4 : ‖K‖ * ‖K‖ ^ (-(5 / 2 : ℝ)) =
      ‖K‖ ^ (-(3 / 2 : ℝ)) := by
    calc
      ‖K‖ * ‖K‖ ^ (-(5 / 2 : ℝ)) =
          ‖K‖ ^ (1 : ℝ) * ‖K‖ ^ (-(5 / 2 : ℝ)) := by
        rw [Real.rpow_one]
      _ = ‖K‖ ^ ((1 : ℝ) + (-(5 / 2 : ℝ))) := by
        rw [Real.rpow_add hKpos]
      _ = ‖K‖ ^ (-(3 / 2 : ℝ)) := by norm_num
  have hid6 : ‖K‖ ^ 2 * ‖K‖ ^ (-(7 / 2 : ℝ)) =
      ‖K‖ ^ (-(3 / 2 : ℝ)) := by
    calc
      ‖K‖ ^ 2 * ‖K‖ ^ (-(7 / 2 : ℝ)) =
          ‖K‖ ^ (2 : ℝ) * ‖K‖ ^ (-(7 / 2 : ℝ)) := by
        rw [show ‖K‖ ^ 2 = ‖K‖ ^ (2 : ℝ) from
          (Real.rpow_natCast ‖K‖ 2).symm]
      _ = ‖K‖ ^ ((2 : ℝ) + (-(7 / 2 : ℝ))) := by
        rw [Real.rpow_add hKpos]
      _ = ‖K‖ ^ (-(3 / 2 : ℝ)) := by norm_num
  calc
    6 * ‖K‖ * (∫ r : ℝ, ‖(r : ℂ) ^ 4 * leadingGaussian K r‖) +
        4 * ‖K‖ ^ 2 * (∫ r : ℝ, ‖(r : ℂ) ^ 6 * leadingGaussian K r‖) ≤
      6 * ‖K‖ * (4096 * ‖K‖ ^ (-(5 / 2 : ℝ))) +
        4 * ‖K‖ ^ 2 * (65536 * ‖K‖ ^ (-(7 / 2 : ℝ))) := by
      gcongr
    _ = 286720 * ‖K‖ ^ (-(3 / 2 : ℝ)) := by
      rw [show 6 * ‖K‖ * (4096 * ‖K‖ ^ (-(5 / 2 : ℝ))) =
          (6 * 4096) * (‖K‖ * ‖K‖ ^ (-(5 / 2 : ℝ))) by ring,
        hid4,
        show 4 * ‖K‖ ^ 2 * (65536 * ‖K‖ ^ (-(7 / 2 : ℝ))) =
          (4 * 65536) * (‖K‖ ^ 2 * ‖K‖ ^ (-(7 / 2 : ℝ))) by ring,
        hid6]
      ring

theorem quantitativeSaddleBranch_cubicGaussian_truncation_scaled_le
    {s : ℂ} (hs : s ∈ leanSaddleSector) :
    let L := quantitativeSaddleBranch s
    let K := leadingCurvature s L
    let ρ := leadingCentralRadius K
    ‖(∫ r : ℝ,
          leadingCubicGaussianApproximation K (leadingCubicCoefficient s L) r) -
        ∫ r : ℝ in Icc (-ρ) ρ,
          leadingCubicGaussianApproximation K (leadingCubicCoefficient s L) r‖ ≤
      69206016 * ‖K‖ ^ (-(3 / 2 : ℝ)) := by
  dsimp only
  let L := quantitativeSaddleBranch s
  let K := leadingCurvature s L
  let ρ := leadingCentralRadius K
  have hKre : 0 < K.re := quantitativeSaddleBranch_curvature_re_pos hs
  have hKpos : 0 < ‖K‖ := by
    linarith [quantitativeSaddleBranch_curvature_norm_ge_fourThousand hs]
  have hρpos : 0 < ρ := quantitativeSaddleBranch_centralRadius_pos hs
  have hc := quantitativeSaddleBranch_cubicCoefficient_norm_le hs
  have h8 := quantitativeSaddleBranch_eighthGaussianMoment_le hs
  have h10 := quantitativeSaddleBranch_tenthGaussianMoment_le hs
  have htrunc := leadingCubicGaussianApproximation_truncation_error_le
    hKre hρpos (c := leadingCubicCoefficient s L)
  have hρ10 : (ρ ^ 10)⁻¹ = ‖K‖ ^ (4 : ℝ) := by
    simp only [ρ, leadingCentralRadius]
    rw [← Real.rpow_natCast, ← Real.rpow_mul hKpos.le]
    norm_num
  have hρ5 : (ρ ^ 5)⁻¹ = ‖K‖ ^ (2 : ℝ) := by
    simp only [ρ, leadingCentralRadius]
    rw [← Real.rpow_natCast, ← Real.rpow_mul hKpos.le]
    norm_num
  have hid10 : ‖K‖ ^ (4 : ℝ) * ‖K‖ ^ (-(11 / 2 : ℝ)) =
      ‖K‖ ^ (-(3 / 2 : ℝ)) := by
    rw [← Real.rpow_add hKpos]
    norm_num
  have hid8 : ‖K‖ * ‖K‖ ^ (2 : ℝ) *
      ‖K‖ ^ (-(9 / 2 : ℝ)) =
      ‖K‖ ^ (-(3 / 2 : ℝ)) := by
    calc
      ‖K‖ * ‖K‖ ^ (2 : ℝ) * ‖K‖ ^ (-(9 / 2 : ℝ)) =
          ‖K‖ ^ (1 : ℝ) * ‖K‖ ^ (2 : ℝ) *
            ‖K‖ ^ (-(9 / 2 : ℝ)) := by rw [Real.rpow_one]
      _ = ‖K‖ ^ ((1 : ℝ) + 2) * ‖K‖ ^ (-(9 / 2 : ℝ)) := by
        rw [Real.rpow_add hKpos]
      _ = ‖K‖ ^ (((1 : ℝ) + 2) + (-(9 / 2 : ℝ))) := by
        exact (Real.rpow_add hKpos _ _).symm
      _ = ‖K‖ ^ (-(3 / 2 : ℝ)) := by norm_num
  calc
    ‖(∫ r : ℝ,
          leadingCubicGaussianApproximation K (leadingCubicCoefficient s L) r) -
        ∫ r : ℝ in Icc (-ρ) ρ,
          leadingCubicGaussianApproximation K (leadingCubicCoefficient s L) r‖ ≤
      (ρ ^ 10)⁻¹ * (∫ r : ℝ, ‖(r : ℂ) ^ 10 * leadingGaussian K r‖) +
        ‖leadingCubicCoefficient s L‖ * (ρ ^ 5)⁻¹ *
          (∫ r : ℝ, ‖(r : ℂ) ^ 8 * leadingGaussian K r‖) := htrunc
    _ ≤ ‖K‖ ^ (4 : ℝ) *
          (67108864 * ‖K‖ ^ (-(11 / 2 : ℝ))) +
        ‖K‖ * ‖K‖ ^ (2 : ℝ) *
          (2097152 * ‖K‖ ^ (-(9 / 2 : ℝ))) := by
      rw [hρ10, hρ5]
      gcongr
    _ = 69206016 * ‖K‖ ^ (-(3 / 2 : ℝ)) := by
      rw [show ‖K‖ ^ (4 : ℝ) *
          (67108864 * ‖K‖ ^ (-(11 / 2 : ℝ))) =
          67108864 * (‖K‖ ^ (4 : ℝ) *
            ‖K‖ ^ (-(11 / 2 : ℝ))) by ring,
        hid10,
        show ‖K‖ * ‖K‖ ^ (2 : ℝ) *
          (2097152 * ‖K‖ ^ (-(9 / 2 : ℝ))) =
          2097152 * (‖K‖ * ‖K‖ ^ (2 : ℝ) *
            ‖K‖ ^ (-(9 / 2 : ℝ))) by ring,
        hid8]
      ring

theorem quantitativeSaddleBranch_centralWindow_scaled_error_le
    {s : ℂ} (hs : s ∈ leanSaddleSector) :
    let L := quantitativeSaddleBranch s
    let K := leadingCurvature s L
    let ρ := leadingCentralRadius K
    ‖∫ r : ℝ in Icc (-ρ) ρ,
        (leadingIntegrand s (L + r) -
          leadingIntegrand s L * leadingGaussian K r *
            (1 + leadingCubicCoefficient s L * (r : ℂ) ^ 3))‖ ≤
      286720 * ‖leadingIntegrand s L‖ * ‖K‖ ^ (-(3 / 2 : ℝ)) := by
  dsimp only
  let L := quantitativeSaddleBranch s
  let K := leadingCurvature s L
  let ρ := leadingCentralRadius K
  have hraw := quantitativeSaddleBranch_centralWindow_integral_error_le hs
  have hledger := quantitativeSaddleBranch_localMomentLedger_le hs
  calc
    ‖∫ r : ℝ in Icc (-ρ) ρ,
        (leadingIntegrand s (L + r) -
          leadingIntegrand s L * leadingGaussian K r *
            (1 + leadingCubicCoefficient s L * (r : ℂ) ^ 3))‖ ≤
      ‖leadingIntegrand s L‖ *
        (6 * ‖K‖ * (∫ r : ℝ, ‖(r : ℂ) ^ 4 * leadingGaussian K r‖) +
          4 * ‖K‖ ^ 2 *
            (∫ r : ℝ, ‖(r : ℂ) ^ 6 * leadingGaussian K r‖)) := hraw
    _ ≤ ‖leadingIntegrand s L‖ *
        (286720 * ‖K‖ ^ (-(3 / 2 : ℝ))) := by gcongr
    _ = 286720 * ‖leadingIntegrand s L‖ *
        ‖K‖ ^ (-(3 / 2 : ℝ)) := by ring

/-- The actual central saddle integral has the exact Gaussian main term with
an explicit relative `1 / |K|` error. -/
theorem quantitativeSaddleBranch_centralGaussian_relative_error_le
    {s : ℂ} (hs : s ∈ leanSaddleSector) :
    let L := quantitativeSaddleBranch s
    let K := leadingCurvature s L
    let ρ := leadingCentralRadius K
    ‖(∫ r : ℝ in Icc (-ρ) ρ, leadingIntegrand s (L + r)) -
        leadingIntegrand s L * (∫ r : ℝ, leadingGaussian K r)‖ ≤
      (71000000 / ‖K‖) *
        ‖leadingIntegrand s L * (∫ r : ℝ, leadingGaussian K r)‖ := by
  dsimp only
  let L := quantitativeSaddleBranch s
  let K := leadingCurvature s L
  let ρ := leadingCentralRadius K
  let c := leadingCubicCoefficient s L
  let F : ℝ → ℂ := fun r => leadingIntegrand s (L + r)
  let A : ℝ → ℂ := leadingCubicGaussianApproximation K c
  let I : ℂ := ∫ r : ℝ in Icc (-ρ) ρ, F r
  let AC : ℂ := ∫ r : ℝ in Icc (-ρ) ρ, A r
  let AW : ℂ := ∫ r : ℝ, A r
  let M : ℂ := ∫ r : ℝ, leadingGaussian K r
  let g : ℂ := leadingIntegrand s L
  have hKre : 0 < K.re := quantitativeSaddleBranch_curvature_re_pos hs
  have hKpos : 0 < ‖K‖ := by
    linarith [quantitativeSaddleBranch_curvature_norm_ge_fourThousand hs]
  have hρle : ρ ≤ 1 / 10 := quantitativeSaddleBranch_centralRadius_le_tenth hs
  have hLre : 1000 < L.re := quantitativeSaddleBranch_re_gt hs
  have hFint : IntegrableOn F (Icc (-ρ) ρ) := by
    apply ContinuousOn.integrableOn_Icc
    exact (leadingIntegrand_differentiableOn_domain s).continuousOn.comp'
      (by fun_prop) (by
        intro r hr
        change 0 < (L + (r : ℂ)).re
        simp only [add_re, ofReal_re]
        linarith [hr.1])
  have hAint : Integrable A :=
    integrable_leadingCubicGaussianApproximation hKre
  have hlocalEq : I - g * AC =
      ∫ r : ℝ in Icc (-ρ) ρ,
        (leadingIntegrand s (L + r) -
          leadingIntegrand s L * leadingGaussian K r *
            (1 + leadingCubicCoefficient s L * (r : ℂ) ^ 3)) := by
    have hconst : IntegrableOn (fun r : ℝ => g * A r) (Icc (-ρ) ρ) :=
      hAint.const_mul g |>.restrict
    calc
      I - g * AC = (∫ r : ℝ in Icc (-ρ) ρ, F r) -
          ∫ r : ℝ in Icc (-ρ) ρ, g * A r := by
        simp only [I, AC]
        rw [integral_const_mul]
      _ = ∫ r : ℝ in Icc (-ρ) ρ, F r - g * A r :=
        (integral_sub hFint hconst).symm
      _ = _ := by
        apply integral_congr_ae
        filter_upwards with r
        simp only [F, A, c, g, leadingCubicGaussianApproximation]
        ring
  have hlocalRaw := quantitativeSaddleBranch_centralWindow_scaled_error_le hs
  have hlocal : ‖I - g * AC‖ ≤
      286720 * ‖g‖ * ‖K‖ ^ (-(3 / 2 : ℝ)) := by
    rw [hlocalEq]
    exact hlocalRaw
  have htruncRaw :=
    quantitativeSaddleBranch_cubicGaussian_truncation_scaled_le hs
  have htrunc : ‖g * (AC - AW)‖ ≤
      69206016 * ‖g‖ * ‖K‖ ^ (-(3 / 2 : ℝ)) := by
    rw [norm_mul]
    have hrev : ‖AC - AW‖ = ‖AW - AC‖ := by
      rw [← norm_neg, neg_sub]
    rw [hrev]
    calc
      ‖g‖ * ‖AW - AC‖ ≤
          ‖g‖ * (69206016 * ‖K‖ ^ (-(3 / 2 : ℝ))) := by gcongr
      _ = 69206016 * ‖g‖ * ‖K‖ ^ (-(3 / 2 : ℝ)) := by ring
  have hcubicRaw := quantitativeSaddleBranch_cubicGaussian_relative_error_le hs
  have hcubic : ‖g * (AW - M)‖ ≤
      (4 / ‖K‖) * (‖g‖ * ‖M‖) := by
    rw [norm_mul]
    calc
      ‖g‖ * ‖AW - M‖ ≤ ‖g‖ * ((4 / ‖K‖) * ‖M‖) := by gcongr
      _ = (4 / ‖K‖) * (‖g‖ * ‖M‖) := by ring
  have hmain := quantitativeSaddleBranch_norm_integral_leadingGaussian_lower hs
  have hidscale : ‖K‖ ^ (-(3 / 2 : ℝ)) =
      (1 / ‖K‖) * ‖K‖ ^ (-(1 / 2 : ℝ)) := by
    calc
      ‖K‖ ^ (-(3 / 2 : ℝ)) =
          ‖K‖ ^ ((-1 : ℝ) + (-(1 / 2 : ℝ))) := by norm_num
      _ = ‖K‖ ^ (-1 : ℝ) * ‖K‖ ^ (-(1 / 2 : ℝ)) := by
        rw [Real.rpow_add hKpos]
      _ = (1 / ‖K‖) * ‖K‖ ^ (-(1 / 2 : ℝ)) := by
        rw [Real.rpow_neg_one]
        simp only [one_div]
  have hscaleMain : ‖K‖ ^ (-(3 / 2 : ℝ)) ≤
      (1 / ‖K‖) * ‖M‖ := by
    rw [hidscale]
    gcongr
  have hdecomp : I - g * M =
      (I - g * AC) + g * (AC - AW) + g * (AW - M) := by ring
  change ‖I - g * M‖ ≤ (71000000 / ‖K‖) * ‖g * M‖
  rw [hdecomp]
  calc
    ‖(I - g * AC) + g * (AC - AW) + g * (AW - M)‖ ≤
        ‖I - g * AC‖ + ‖g * (AC - AW)‖ + ‖g * (AW - M)‖ := by
      exact (norm_add_le _ _).trans
        (add_le_add (norm_add_le _ _) (le_refl _))
    _ ≤ (286720 + 69206016) * ‖g‖ *
          ‖K‖ ^ (-(3 / 2 : ℝ)) +
        (4 / ‖K‖) * (‖g‖ * ‖M‖) := by
      calc
        ‖I - g * AC‖ + ‖g * (AC - AW)‖ + ‖g * (AW - M)‖ ≤
            (286720 * ‖g‖ * ‖K‖ ^ (-(3 / 2 : ℝ))) +
              (69206016 * ‖g‖ * ‖K‖ ^ (-(3 / 2 : ℝ))) +
              (4 / ‖K‖) * (‖g‖ * ‖M‖) :=
          add_le_add (add_le_add hlocal htrunc) hcubic
        _ = _ := by ring
    _ ≤ (286720 + 69206016) * ‖g‖ *
          ((1 / ‖K‖) * ‖M‖) +
        (4 / ‖K‖) * (‖g‖ * ‖M‖) := by gcongr
    _ ≤ (71000000 / ‖K‖) * ‖g * M‖ := by
      rw [norm_mul]
      field_simp [hKpos.ne']
      nlinarith [mul_nonneg (norm_nonneg g) (norm_nonneg M)]

end

end Zeta23.Research.JensenWedge
