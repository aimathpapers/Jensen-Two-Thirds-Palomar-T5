import Zeta23.Research.JensenWedge.LeadingCentralWindow

/-!
# Truncating the leading complex Gaussian

The central-window proof must replace truncated Gaussian and signed cubic
integrals by their exact whole-line values.  This file proves a general
moment tail inequality and then applies it with orders ten and eight.  Those
orders are deliberately stronger than the local fourth/sixth moments: after
`rho = |K|^(-2/5)` they give enough decay for the final relative `1/|K|`
estimate without appealing to an informal exponential-tail assertion.
-/

namespace Zeta23.Research.JensenWedge

open Complex Filter MeasureTheory Set

noncomputable section

/-- Outside `[-rho,rho]`, an absolute moment is bounded by a higher absolute
moment times `rho^(-m)`. -/
theorem leadingGaussian_tail_moment_le_higher
    {K : ℂ} (hK : 0 < K.re) {ρ : ℝ} (hρ : 0 < ρ) (k m : ℕ) :
    (∫ r : ℝ in (Icc (-ρ) ρ)ᶜ,
        ‖(r : ℂ) ^ k * leadingGaussian K r‖) ≤
      (ρ ^ m)⁻¹ *
        (∫ r : ℝ, ‖(r : ℂ) ^ (k + m) * leadingGaussian K r‖) := by
  let f : ℝ → ℝ := fun r => ‖(r : ℂ) ^ k * leadingGaussian K r‖
  let g : ℝ → ℝ := fun r =>
    (ρ ^ m)⁻¹ * ‖(r : ℂ) ^ (k + m) * leadingGaussian K r‖
  have hf : Integrable f := (integrable_pow_mul_leadingGaussian hK k).norm
  have hg : Integrable g :=
    (integrable_pow_mul_leadingGaussian hK (k + m)).norm.const_mul _
  have hpoint : ∀ r ∈ (Icc (-ρ) ρ)ᶜ, f r ≤ g r := by
    intro r hr
    have hrnot : r ∉ Icc (-ρ) ρ := by simpa only [mem_compl_iff] using hr
    have hρabs : ρ ≤ |r| := by
      by_contra hnot
      apply hrnot
      exact (abs_le.mp (lt_of_not_ge hnot).le)
    have hpow : ρ ^ m ≤ |r| ^ m :=
      pow_le_pow_left₀ hρ.le hρabs m
    have hρpow : 0 < ρ ^ m := pow_pos hρ _
    dsimp only [f, g]
    rw [norm_mul, norm_pow, norm_mul, norm_pow, norm_real,
      Real.norm_eq_abs, pow_add]
    have hcore : |r| ^ k ≤ (ρ ^ m)⁻¹ * (|r| ^ k * |r| ^ m) := by
      rw [inv_mul_eq_div, le_div_iff₀ hρpow]
      nlinarith [mul_nonneg (pow_nonneg (abs_nonneg r) k)
        (sub_nonneg.mpr hpow)]
    calc
      |r| ^ k * ‖leadingGaussian K r‖ ≤
          ((ρ ^ m)⁻¹ * (|r| ^ k * |r| ^ m)) *
            ‖leadingGaussian K r‖ :=
        mul_le_mul_of_nonneg_right hcore (norm_nonneg (leadingGaussian K r))
      _ = (ρ ^ m)⁻¹ *
          (|r| ^ k * |r| ^ m * ‖leadingGaussian K r‖) := by ring
  calc
    (∫ r : ℝ in (Icc (-ρ) ρ)ᶜ, f r) ≤
        ∫ r : ℝ in (Icc (-ρ) ρ)ᶜ, g r :=
      setIntegral_mono_on hf.restrict hg.restrict measurableSet_Icc.compl hpoint
    _ ≤ ∫ r : ℝ, g r :=
      setIntegral_le_integral hg (Eventually.of_forall fun r => by
        dsimp only [g]
        positivity)
    _ = (ρ ^ m)⁻¹ *
        (∫ r : ℝ, ‖(r : ℂ) ^ (k + m) * leadingGaussian K r‖) := by
      simp only [g]
      rw [integral_const_mul]

/-- The Gaussian plus its signed cubic correction. -/
def leadingCubicGaussianApproximation (K c : ℂ) (r : ℝ) : ℂ :=
  leadingGaussian K r * (1 + c * (r : ℂ) ^ 3)

theorem integrable_leadingCubicGaussianApproximation
    {K c : ℂ} (hK : 0 < K.re) :
    Integrable (leadingCubicGaussianApproximation K c) := by
  have h0 := integrable_leadingGaussian hK
  have h3 := integrable_pow_mul_leadingGaussian hK 3
  refine (h0.add (h3.const_mul c)).congr ?_
  filter_upwards with r
  unfold leadingCubicGaussianApproximation
  simp only [Pi.add_apply]
  ring

/-- Exact whole-line evaluation of the cubic-corrected Gaussian. -/
theorem integral_leadingCubicGaussianApproximation
    {K c : ℂ} (hK : 0 < K.re) :
    (∫ r : ℝ, leadingCubicGaussianApproximation K c r) =
      (∫ r : ℝ, leadingGaussian K r) *
        (1 + c * (3 / K ^ 2 + 1 / K ^ 3)) := by
  have h0 := integrable_leadingGaussian hK
  have h3 := integrable_pow_mul_leadingGaussian hK 3
  have hm3 := leadingGaussianMoment_three hK
  rw [show (fun r : ℝ => leadingCubicGaussianApproximation K c r) =
      fun r : ℝ => leadingGaussian K r +
        c * ((r : ℂ) ^ 3 * leadingGaussian K r) by
    funext r
    unfold leadingCubicGaussianApproximation
    ring]
  rw [integral_add h0 (h3.const_mul c), integral_const_mul]
  change (∫ r : ℝ, leadingGaussian K r) +
      c * leadingGaussianMoment K 3 = _
  rw [hm3, leadingGaussianMoment_zero]
  ring

/-- Truncating the cubic-corrected Gaussian at the paper radius is dominated
by the tenth Gaussian moment and the eighth moment attached to the cubic
term. -/
theorem leadingCubicGaussianApproximation_truncation_error_le
    {K c : ℂ} (hK : 0 < K.re) {ρ : ℝ} (hρ : 0 < ρ) :
    ‖(∫ r : ℝ, leadingCubicGaussianApproximation K c r) -
        ∫ r : ℝ in Icc (-ρ) ρ, leadingCubicGaussianApproximation K c r‖ ≤
      (ρ ^ 10)⁻¹ *
          (∫ r : ℝ, ‖(r : ℂ) ^ 10 * leadingGaussian K r‖) +
        ‖c‖ * (ρ ^ 5)⁻¹ *
          (∫ r : ℝ, ‖(r : ℂ) ^ 8 * leadingGaussian K r‖) := by
  let C : Set ℝ := Icc (-ρ) ρ
  let F : ℝ → ℂ := leadingCubicGaussianApproximation K c
  have hF : Integrable F := integrable_leadingCubicGaussianApproximation hK
  have hsplit : (∫ r : ℝ, F r) - ∫ r : ℝ in C, F r = ∫ r : ℝ in Cᶜ, F r := by
    rw [sub_eq_iff_eq_add, add_comm, integral_add_compl measurableSet_Icc hF]
  have hmajorant : Integrable (fun r : ℝ =>
      ‖leadingGaussian K r‖ +
        ‖c‖ * ‖(r : ℂ) ^ 3 * leadingGaussian K r‖) :=
    (integrable_leadingGaussian hK).norm.add
      ((integrable_pow_mul_leadingGaussian hK 3).norm.const_mul ‖c‖)
  have hpoint : ∀ r : ℝ,
      ‖F r‖ ≤ ‖leadingGaussian K r‖ +
        ‖c‖ * ‖(r : ℂ) ^ 3 * leadingGaussian K r‖ := by
    intro r
    unfold F leadingCubicGaussianApproximation
    rw [mul_add, mul_one]
    calc
      ‖leadingGaussian K r + leadingGaussian K r * (c * (r : ℂ) ^ 3)‖ ≤
          ‖leadingGaussian K r‖ +
            ‖leadingGaussian K r * (c * (r : ℂ) ^ 3)‖ := norm_add_le _ _
      _ = _ := by simp only [norm_mul]; ring
  have hnorm :
      ‖∫ r : ℝ in Cᶜ, F r‖ ≤
        (∫ r : ℝ in Cᶜ, ‖leadingGaussian K r‖) +
          ‖c‖ * (∫ r : ℝ in Cᶜ,
            ‖(r : ℂ) ^ 3 * leadingGaussian K r‖) := by
    calc
      ‖∫ r : ℝ in Cᶜ, F r‖ ≤ ∫ r : ℝ in Cᶜ, ‖F r‖ :=
        norm_integral_le_integral_norm _
      _ ≤ ∫ r : ℝ in Cᶜ,
          (‖leadingGaussian K r‖ +
            ‖c‖ * ‖(r : ℂ) ^ 3 * leadingGaussian K r‖) := by
        exact setIntegral_mono_on hF.norm.restrict hmajorant.restrict
          measurableSet_Icc.compl (fun r _ => hpoint r)
      _ = (∫ r : ℝ in Cᶜ, ‖leadingGaussian K r‖) +
          ‖c‖ * (∫ r : ℝ in Cᶜ,
            ‖(r : ℂ) ^ 3 * leadingGaussian K r‖) := by
        rw [integral_add (integrable_leadingGaussian hK).norm.restrict
          ((integrable_pow_mul_leadingGaussian hK 3).norm.const_mul ‖c‖).restrict,
          integral_const_mul]
  have htail0 :
      (∫ r : ℝ in (Icc (-ρ) ρ)ᶜ, ‖leadingGaussian K r‖) ≤
        (ρ ^ 10)⁻¹ *
          (∫ r : ℝ, ‖(r : ℂ) ^ 10 * leadingGaussian K r‖) := by
    simpa only [pow_zero, one_mul, zero_add] using
      (leadingGaussian_tail_moment_le_higher hK hρ 0 10)
  have htail3 :
      (∫ r : ℝ in (Icc (-ρ) ρ)ᶜ,
          ‖(r : ℂ) ^ 3 * leadingGaussian K r‖) ≤
        (ρ ^ 5)⁻¹ *
          (∫ r : ℝ, ‖(r : ℂ) ^ 8 * leadingGaussian K r‖) := by
    simpa only [Nat.reduceAdd] using
      (leadingGaussian_tail_moment_le_higher hK hρ 3 5)
  rw [hsplit]
  calc
    ‖∫ r : ℝ in Cᶜ, F r‖ ≤
        (∫ r : ℝ in Cᶜ, ‖leadingGaussian K r‖) +
          ‖c‖ * (∫ r : ℝ in Cᶜ,
            ‖(r : ℂ) ^ 3 * leadingGaussian K r‖) := hnorm
    _ ≤ (ρ ^ 10)⁻¹ *
          (∫ r : ℝ, ‖(r : ℂ) ^ 10 * leadingGaussian K r‖) +
        ‖c‖ * ((ρ ^ 5)⁻¹ *
          (∫ r : ℝ, ‖(r : ℂ) ^ 8 * leadingGaussian K r‖)) := by
      gcongr
    _ = (ρ ^ 10)⁻¹ *
          (∫ r : ℝ, ‖(r : ℂ) ^ 10 * leadingGaussian K r‖) +
        ‖c‖ * (ρ ^ 5)⁻¹ *
          (∫ r : ℝ, ‖(r : ℂ) ^ 8 * leadingGaussian K r‖) := by ring

end

end Zeta23.Research.JensenWedge
