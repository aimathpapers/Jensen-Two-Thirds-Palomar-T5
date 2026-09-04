import Zeta23.Research.JensenWedge.LeadingEndpointConnector
import Zeta23.Research.JensenWedge.LeadingCentralRelative

/-!
# Complete leading-mode saddle assembly

This module translates the exact top ray to saddle-centered coordinates,
partitions it into the left tail, central window, and right tail, and joins
their independently proved estimates.  The legal rectangular contour then
reinstates the endpoint connector and yields the complete T3 leading-mode
relative approximation.
-/

namespace Zeta23.Research.JensenWedge

open Complex MeasureTheory Set

noncomputable section

theorem leadingTopRay_eq_centered
    (s L : ℂ) :
    leadingTopRay s L.im =
      ∫ r : ℝ in Ioi (1 - L.re), leadingIntegrand s (L + r) := by
  let F : ℝ → ℂ := fun x =>
    (Ioi (1 : ℝ)).indicator
      (fun x : ℝ => leadingIntegrand s (x + L.im * I)) x
  have hshift := integral_add_right_eq_self (μ := volume) F L.re
  unfold leadingTopRay
  rw [← MeasureTheory.integral_indicator measurableSet_Ioi]
  change (∫ x : ℝ, F x) = _
  calc
    (∫ x : ℝ, F x) = ∫ r : ℝ, F (r + L.re) := hshift.symm
    _ = ∫ r : ℝ,
        (Ioi (1 - L.re)).indicator
          (fun r : ℝ => leadingIntegrand s (L + r)) r := by
      apply integral_congr_ae
      filter_upwards with r
      by_cases hr : r ∈ Ioi (1 - L.re)
      · have hr' : r + L.re ∈ Ioi (1 : ℝ) := by
          simp only [mem_Ioi] at hr ⊢
          linarith
        simp only [F, indicator_of_mem hr, indicator_of_mem hr']
        congr 1
        apply Complex.ext <;> simp <;> ring
      · have hr' : r + L.re ∉ Ioi (1 : ℝ) := by
          simp only [mem_Ioi] at hr ⊢
          linarith
        simp [F, hr, hr']
    _ = ∫ r : ℝ in Ioi (1 - L.re), leadingIntegrand s (L + r) :=
      MeasureTheory.integral_indicator measurableSet_Ioi

theorem integrableOn_quantitativeSaddleBranch_centeredRay
    {s : ℂ} (hs : s ∈ leanSaddleSector) :
    let L := quantitativeSaddleBranch s
    IntegrableOn (fun r : ℝ => leadingIntegrand s (L + r))
      (Ioi (1 - L.re)) := by
  dsimp only
  let L : ℂ := quantitativeSaddleBranch s
  let top : ℝ → ℂ := fun x => leadingIntegrand s (x + L.im * I)
  let F : ℝ → ℂ := fun x => (Ioi (1 : ℝ)).indicator top x
  have hb : |L.im| ≤ 1 / 20 := by
    simpa only [L] using (quantitativeSaddleBranch_im_abs_lt hs).le
  have htop : IntegrableOn top (Ioi 1) := by
    simpa only [L, top] using integrableOn_leadingHorizontalRay s hb
  have hF : Integrable F := by
    exact (integrable_indicator_iff measurableSet_Ioi).2 htop
  have hshift : Integrable (fun r : ℝ => F (r + L.re)) :=
    hF.comp_add_right L.re
  have heq : (fun r : ℝ => F (r + L.re)) =
      fun r : ℝ => (Ioi (1 - L.re)).indicator
        (fun r : ℝ => leadingIntegrand s (L + r)) r := by
    funext r
    by_cases hr : r ∈ Ioi (1 - L.re)
    · have hr' : r + L.re ∈ Ioi (1 : ℝ) := by
        simp only [mem_Ioi] at hr ⊢
        linarith
      simp only [F, top, indicator_of_mem hr, indicator_of_mem hr']
      congr 1
      apply Complex.ext <;> simp <;> ring
    · have hr' : r + L.re ∉ Ioi (1 : ℝ) := by
        simp only [mem_Ioi] at hr ⊢
        linarith
      simp [F, hr, hr']
  rw [heq] at hshift
  exact (integrable_indicator_iff measurableSet_Ioi).1 hshift

theorem quantitativeSaddleBranch_centeredRay_integral_split
    {s : ℂ} (hs : s ∈ leanSaddleSector) :
    let L := quantitativeSaddleBranch s
    let K := leadingCurvature s L
    let ρ := leadingCentralRadius K
    (∫ r : ℝ in Ioi (1 - L.re), leadingIntegrand s (L + r)) =
      (∫ r : ℝ in Icc (1 - L.re) (-ρ), leadingIntegrand s (L + r)) +
      (∫ r : ℝ in Icc (-ρ) ρ, leadingIntegrand s (L + r)) +
      (∫ r : ℝ in Ioi ρ, leadingIntegrand s (L + r)) := by
  dsimp only
  let L : ℂ := quantitativeSaddleBranch s
  let K : ℂ := leadingCurvature s L
  let ρ : ℝ := leadingCentralRadius K
  let a : ℝ := 1 - L.re
  let f : ℝ → ℂ := fun r => leadingIntegrand s (L + r)
  have hLre : 1000 < L.re := by
    simpa only [L] using quantitativeSaddleBranch_re_gt hs
  have hρpos : 0 < ρ := by
    simpa only [L, K, ρ] using quantitativeSaddleBranch_centralRadius_pos hs
  have hρle : ρ ≤ 1 / 10 := by
    simpa only [L, K, ρ] using
      quantitativeSaddleBranch_centralRadius_le_tenth hs
  have haNeg : a ≤ -ρ := by dsimp [a]; linarith
  have hnegPos : -ρ ≤ ρ := by linarith
  have haRho : a ≤ ρ := haNeg.trans hnegPos
  have hfull : IntegrableOn f (Ioi a) := by
    simpa only [L, a, f] using
      integrableOn_quantitativeSaddleBranch_centeredRay hs
  have hA : IntegrableOn f (Ioc a (-ρ)) :=
    hfull.mono_set (fun r hr => hr.1)
  have hB : IntegrableOn f (Ioc (-ρ) ρ) :=
    hfull.mono_set (fun r hr => haNeg.trans_lt hr.1)
  have hAB : IntegrableOn f (Ioc a ρ) :=
    hfull.mono_set (fun r hr => hr.1)
  have hC : IntegrableOn f (Ioi ρ) :=
    hfull.mono_set (Ioi_subset_Ioi haRho)
  have hsplitAB := setIntegral_union
    (Ioc_disjoint_Ioc_of_le (a := a) (d := ρ) (le_refl (-ρ)))
    measurableSet_Ioc hA hB
  rw [Ioc_union_Ioc_eq_Ioc haNeg hnegPos] at hsplitAB
  have hsplitC := setIntegral_union Ioc_disjoint_Ioi_same
    measurableSet_Ioi hAB hC
  rw [Ioc_union_Ioi_eq_Ioi haRho] at hsplitC
  have hAclosed : (∫ r : ℝ in Ioc a (-ρ), f r) =
      ∫ r : ℝ in Icc a (-ρ), f r :=
    setIntegral_congr_set Ioc_ae_eq_Icc
  have hBclosed : (∫ r : ℝ in Ioc (-ρ) ρ, f r) =
      ∫ r : ℝ in Icc (-ρ) ρ, f r :=
    setIntegral_congr_set Ioc_ae_eq_Icc
  calc
    (∫ r : ℝ in Ioi a, f r) =
        (∫ r : ℝ in Ioc a ρ, f r) +
          ∫ r : ℝ in Ioi ρ, f r := hsplitC
    _ = ((∫ r : ℝ in Ioc a (-ρ), f r) +
          ∫ r : ℝ in Ioc (-ρ) ρ, f r) +
          ∫ r : ℝ in Ioi ρ, f r := by rw [hsplitAB]
    _ = (∫ r : ℝ in Icc a (-ρ), f r) +
        (∫ r : ℝ in Icc (-ρ) ρ, f r) +
        (∫ r : ℝ in Ioi ρ, f r) := by rw [hAclosed, hBclosed]
    _ = _ := by simp only [L, K, ρ, a, f]

theorem quantitativeSaddleBranch_leadingTopRay_relative_error_le
    {s : ℂ} (hs : s ∈ leanSaddleSector) :
    let L := quantitativeSaddleBranch s
    let K := leadingCurvature s L
    let M := ∫ r : ℝ, leadingGaussian K r
    ‖leadingTopRay s L.im - leadingIntegrand s L * M‖ ≤
      ((71000000 + 2 * 20 ^ 15 * (Nat.factorial 15 : ℝ)) / ‖K‖) *
        ‖leadingIntegrand s L * M‖ := by
  dsimp only
  let L : ℂ := quantitativeSaddleBranch s
  let K : ℂ := leadingCurvature s L
  let ρ : ℝ := leadingCentralRadius K
  let f : ℝ → ℂ := fun r => leadingIntegrand s (L + r)
  let A : ℂ := ∫ r : ℝ in Icc (1 - L.re) (-ρ), f r
  let B : ℂ := ∫ r : ℝ in Icc (-ρ) ρ, f r
  let C : ℂ := ∫ r : ℝ in Ioi ρ, f r
  let M : ℂ := ∫ r : ℝ, leadingGaussian K r
  let G : ℂ := leadingIntegrand s L * M
  let T : ℝ := 2 * 20 ^ 15 * (Nat.factorial 15 : ℝ)
  have hsplit : leadingTopRay s L.im = A + B + C := by
    rw [leadingTopRay_eq_centered]
    simpa only [L, K, ρ, f, A, B, C] using
      quantitativeSaddleBranch_centeredRay_integral_split hs
  have hnormA : ‖A‖ ≤
      ∫ r : ℝ in Icc (1 - L.re) (-ρ), ‖f r‖ := by
    dsimp only [A]
    exact norm_integral_le_integral_norm f
  have hnormC : ‖C‖ ≤ ∫ r : ℝ in Ioi ρ, ‖f r‖ := by
    dsimp only [C]
    exact norm_integral_le_integral_norm f
  have hcentral : ‖B - G‖ ≤ (71000000 / ‖K‖) * ‖G‖ := by
    simpa only [L, K, ρ, f, B, M, G] using
      quantitativeSaddleBranch_centralGaussian_relative_error_le hs
  have htails :
      (∫ r : ℝ in Icc (1 - L.re) (-ρ), ‖f r‖) +
          (∫ r : ℝ in Ioi ρ, ‖f r‖) ≤
        (T / ‖K‖) * ‖G‖ := by
    simpa only [L, K, ρ, f, M, G, T] using
      quantitativeSaddleBranch_horizontal_tail_relative_inverse_curvature hs
  rw [hsplit]
  have halgebra : A + B + C - G = A + (B - G) + C := by ring
  rw [halgebra]
  calc
    ‖A + (B - G) + C‖ ≤ ‖A‖ + ‖B - G‖ + ‖C‖ := by
      calc
        ‖A + (B - G) + C‖ ≤ ‖A + (B - G)‖ + ‖C‖ := norm_add_le _ _
        _ ≤ (‖A‖ + ‖B - G‖) + ‖C‖ :=
          add_le_add (norm_add_le _ _) (le_refl _)
    _ ≤ (∫ r : ℝ in Icc (1 - L.re) (-ρ), ‖f r‖) +
          ((71000000 / ‖K‖) * ‖G‖) +
          (∫ r : ℝ in Ioi ρ, ‖f r‖) := by gcongr
    _ = ((71000000 / ‖K‖) * ‖G‖) +
          ((∫ r : ℝ in Icc (1 - L.re) (-ρ), ‖f r‖) +
            ∫ r : ℝ in Ioi ρ, ‖f r‖) := by ring
    _ ≤ ((71000000 / ‖K‖) * ‖G‖) + (T / ‖K‖) * ‖G‖ := by gcongr
    _ = ((71000000 + T) / ‖K‖) * ‖G‖ := by ring
    _ = _ := by simp only [L, K, M, G, T]

/-- The complete leading Mellin ray has the exact complex Gaussian saddle
main term with an explicit inverse-curvature relative error. -/
theorem quantitativeSaddleBranch_leadingBottomRay_relative_error_le
    {s : ℂ} (hs : s ∈ leanSaddleSector) :
    let L := quantitativeSaddleBranch s
    let K := leadingCurvature s L
    let M := ∫ r : ℝ, leadingGaussian K r
    ‖leadingBottomRay s - leadingIntegrand s L * M‖ ≤
      ((71000001 + 2 * 20 ^ 15 * (Nat.factorial 15 : ℝ)) / ‖K‖) *
        ‖leadingIntegrand s L * M‖ := by
  dsimp only
  let L : ℂ := quantitativeSaddleBranch s
  let K : ℂ := leadingCurvature s L
  let M : ℂ := ∫ r : ℝ, leadingGaussian K r
  let G : ℂ := leadingIntegrand s L * M
  let T : ℝ := 2 * 20 ^ 15 * (Nat.factorial 15 : ℝ)
  have hb : |L.im| ≤ 1 / 20 := by
    simpa only [L] using (quantitativeSaddleBranch_im_abs_lt hs).le
  have hrectangle :
      leadingBottomRay s =
        leadingTopRay s L.im + leadingLeftSegment s L.im :=
    leading_infinite_rectangle_identity s hb
  have htop : ‖leadingTopRay s L.im - G‖ ≤
      ((71000000 + T) / ‖K‖) * ‖G‖ := by
    simpa only [L, K, M, G, T] using
      quantitativeSaddleBranch_leadingTopRay_relative_error_le hs
  have hconnector : ‖leadingLeftSegment s L.im‖ ≤
      (1 / ‖K‖) * ‖G‖ := by
    simpa only [L, K, M, G] using
      quantitativeSaddleBranch_leftSegment_relative_inverse_curvature hs
  rw [hrectangle]
  have halgebra :
      leadingTopRay s L.im + leadingLeftSegment s L.im - G =
        (leadingTopRay s L.im - G) + leadingLeftSegment s L.im := by ring
  rw [halgebra]
  calc
    ‖(leadingTopRay s L.im - G) + leadingLeftSegment s L.im‖ ≤
        ‖leadingTopRay s L.im - G‖ + ‖leadingLeftSegment s L.im‖ :=
      norm_add_le _ _
    _ ≤ ((71000000 + T) / ‖K‖) * ‖G‖ +
        (1 / ‖K‖) * ‖G‖ := by gcongr
    _ = ((71000001 + T) / ‖K‖) * ‖G‖ := by ring
    _ = _ := by simp only [L, K, M, G, T]

end

end Zeta23.Research.JensenWedge
