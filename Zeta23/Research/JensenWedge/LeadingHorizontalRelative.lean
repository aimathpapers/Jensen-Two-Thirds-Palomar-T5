import Zeta23.Research.JensenWedge.LeadingHorizontalTails
import Zeta23.Research.JensenWedge.LeadingGaussianRelative

/-!
# Relative normalization of the horizontal tails

The integrated tail estimates are normalized here by the exact nonzero
complex Gaussian main term.  The resulting scalar coefficient remains in its
explicit exponential form; a later quantitative sector lemma reduces it to a
simple inverse-curvature bound.
-/

namespace Zeta23.Research.JensenWedge

open Complex MeasureTheory Set

noncomputable section

theorem quantitativeSaddleBranch_amplitude_le_gaussianMain_scale
    {s : ℂ} (hs : s ∈ leanSaddleSector) :
    let L := quantitativeSaddleBranch s
    let K := leadingCurvature s L
    let M := ∫ r : ℝ, leadingGaussian K r
    ‖leadingIntegrand s L‖ ≤
      ‖K‖ ^ (1 / 2 : ℝ) * ‖leadingIntegrand s L * M‖ := by
  dsimp only
  let L : ℂ := quantitativeSaddleBranch s
  let K : ℂ := leadingCurvature s L
  let M : ℂ := ∫ r : ℝ, leadingGaussian K r
  let g : ℝ := ‖leadingIntegrand s L‖
  have hKpos : 0 < ‖K‖ := by
    have hKge : 4000 ≤ ‖K‖ := by
      simpa only [L, K] using
        quantitativeSaddleBranch_curvature_norm_ge_fourThousand hs
    linarith
  have hmain : ‖K‖ ^ (-(1 / 2 : ℝ)) ≤ ‖M‖ := by
    simpa only [L, K, M] using
      quantitativeSaddleBranch_norm_integral_leadingGaussian_lower hs
  have hgmain : g * ‖K‖ ^ (-(1 / 2 : ℝ)) ≤ g * ‖M‖ :=
    mul_le_mul_of_nonneg_left hmain (norm_nonneg _)
  have hid : ‖K‖ ^ (1 / 2 : ℝ) * ‖K‖ ^ (-(1 / 2 : ℝ)) = 1 := by
    rw [← Real.rpow_add hKpos]
    norm_num
  have hlocal : g ≤ ‖K‖ ^ (1 / 2 : ℝ) * (g * ‖M‖) := by
    calc
      g = g * 1 := by ring
      _ = g * (‖K‖ ^ (1 / 2 : ℝ) * ‖K‖ ^ (-(1 / 2 : ℝ))) := by rw [hid]
      _ = ‖K‖ ^ (1 / 2 : ℝ) *
          (g * ‖K‖ ^ (-(1 / 2 : ℝ))) := by ring
      _ ≤ ‖K‖ ^ (1 / 2 : ℝ) * (g * ‖M‖) :=
        mul_le_mul_of_nonneg_left hgmain
          (Real.rpow_nonneg (norm_nonneg K) (1 / 2 : ℝ))
  simpa only [L, K, M, g, norm_mul] using hlocal

theorem quantitativeSaddleBranch_horizontal_tail_relative_bound
    {s : ℂ} (hs : s ∈ leanSaddleSector) :
    let L := quantitativeSaddleBranch s
    let K := leadingCurvature s L
    let ρ := leadingCentralRadius K
    let M := ∫ r : ℝ, leadingGaussian K r
    (∫ r : ℝ in Icc (1 - L.re) (-ρ), ‖leadingIntegrand s (L + r)‖) +
        (∫ r : ℝ in Ioi ρ, ‖leadingIntegrand s (L + r)‖) ≤
      ((L.re + 20 / (‖K‖ * ρ)) *
          Real.exp (-(‖K‖ * ρ ^ 2 / 20)) * ‖K‖ ^ (1 / 2 : ℝ)) *
        ‖leadingIntegrand s L * M‖ := by
  dsimp only
  let L : ℂ := quantitativeSaddleBranch s
  let K : ℂ := leadingCurvature s L
  let ρ : ℝ := leadingCentralRadius K
  let M : ℂ := ∫ r : ℝ, leadingGaussian K r
  let g : ℝ := ‖leadingIntegrand s L‖
  let E : ℝ := Real.exp (-(‖K‖ * ρ ^ 2 / 20))
  let q : ℝ := 20 / (‖K‖ * ρ)
  have htails := quantitativeSaddleBranch_horizontal_tail_integral_bounds hs
  have hleft := htails.1
  have hright := htails.2
  have hamp : g ≤ ‖K‖ ^ (1 / 2 : ℝ) *
      ‖leadingIntegrand s L * M‖ := by
    simpa only [L, K, M, g] using
      quantitativeSaddleBranch_amplitude_le_gaussianMain_scale hs
  have hLpos : 0 < L.re := by
    have hgt : 1000 < L.re := by
      simpa only [L] using quantitativeSaddleBranch_re_gt hs
    linarith
  have hρpos : 0 < ρ := by
    simpa only [L, K, ρ] using quantitativeSaddleBranch_centralRadius_pos hs
  have hKpos : 0 < ‖K‖ := by
    have hKge : 4000 ≤ ‖K‖ := by
      simpa only [L, K] using
        quantitativeSaddleBranch_curvature_norm_ge_fourThousand hs
    linarith
  have hq : 0 ≤ q := by dsimp [q]; positivity
  have hE : 0 ≤ E := (Real.exp_pos _).le
  have hlocal :
      (∫ r : ℝ in Icc (1 - L.re) (-ρ), ‖leadingIntegrand s (L + r)‖) +
          (∫ r : ℝ in Ioi ρ, ‖leadingIntegrand s (L + r)‖) ≤
        ((L.re + q) * E * ‖K‖ ^ (1 / 2 : ℝ)) *
          ‖leadingIntegrand s L * M‖ := by
    calc
      (∫ r : ℝ in Icc (1 - L.re) (-ρ), ‖leadingIntegrand s (L + r)‖) +
          (∫ r : ℝ in Ioi ρ, ‖leadingIntegrand s (L + r)‖) ≤
        L.re * g * E + g * E * q := by
          simpa only [L, K, ρ, g, E, q] using add_le_add hleft hright
      _ = (L.re + q) * E * g := by ring
      _ ≤ (L.re + q) * E *
          (‖K‖ ^ (1 / 2 : ℝ) * ‖leadingIntegrand s L * M‖) := by
        gcongr
      _ = ((L.re + q) * E * ‖K‖ ^ (1 / 2 : ℝ)) *
          ‖leadingIntegrand s L * M‖ := by ring
  simpa only [L, K, ρ, M, g, E, q] using hlocal

end

end Zeta23.Research.JensenWedge
