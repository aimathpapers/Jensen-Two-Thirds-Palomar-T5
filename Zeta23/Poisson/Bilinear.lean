/-
# Oriented bilinear Poisson summation

This is the two-window version of `Poisson.hasSum_paperFT_mul_paperFT`.
The two real windows need not be even.  The reflection on the right-hand side
records the orientation which is invisible in the same-window even case.
-/
import Zeta23.Poisson

open Complex MeasureTheory Real Set Filter Topology Asymptotics
open scoped FourierTransform

namespace Zeta23.Poisson

variable (φ ψ : ℝ → ℝ) (L T τ τ' : ℝ)

/-- Integrand for the oriented two-window auxiliary function. -/
noncomputable def gIntBilinear (ξ u : ℝ) : ℂ :=
  (L : ℂ) * ((φ u : ℂ) * (ψ (L * ξ - u) : ℂ) *
    cexp (I * (τ * u + τ' * (L * ξ - u) - T * L * ξ)))

/-- The compactly supported auxiliary function used in bilinear Poisson summation. -/
noncomputable def GauxBilinear (ξ : ℝ) : ℂ :=
  ∫ u, gIntBilinear φ ψ L T τ τ' ξ u

variable {φ ψ L T τ τ'}

theorem gIntBilinear_eq_zero_of_not_mem (hL : 0 < L)
    (hφsupp : ∀ u, L / 2 ≤ |u| → φ u = 0)
    (hψsupp : ∀ u, L / 2 ≤ |u| → ψ u = 0)
    {ξ u : ℝ} (h : ¬ (|ξ| < 1 ∧ |u| < L / 2)) :
    gIntBilinear φ ψ L T τ τ' ξ u = 0 := by
  unfold gIntBilinear
  by_cases hu : |u| < L / 2
  · have hξ : 1 ≤ |ξ| := by
      by_contra h'
      exact h ⟨not_le.mp h', hu⟩
    have : L / 2 ≤ |L * ξ - u| := by
      have h4 : |L * ξ| - |u| ≤ |L * ξ - u| := abs_sub_abs_le_abs_sub _ _
      rw [abs_mul, abs_of_pos hL] at h4
      nlinarith
    rw [hψsupp _ this]
    simp
  · rw [hφsupp u (not_lt.mp hu)]
    simp

theorem gIntBilinear_continuous (hφc : Continuous φ) (hψc : Continuous ψ) :
    Continuous (Function.uncurry (gIntBilinear φ ψ L T τ τ')) := by
  unfold gIntBilinear Function.uncurry
  fun_prop

theorem gIntBilinear_hasCompactSupport (hL : 0 < L)
    (hφsupp : ∀ u, L / 2 ≤ |u| → φ u = 0)
    (hψsupp : ∀ u, L / 2 ≤ |u| → ψ u = 0) :
    HasCompactSupport (Function.uncurry (gIntBilinear φ ψ L T τ τ')) := by
  refine HasCompactSupport.of_support_subset_isCompact
    ((isCompact_Icc (a := (-1 : ℝ)) (b := 1)).prod
      (isCompact_Icc (a := -(L / 2)) (b := L / 2))) ?_
  rintro ⟨ξ, u⟩ hne
  rw [Function.mem_support, Function.uncurry_apply_pair] at hne
  by_contra hmem
  apply hne (gIntBilinear_eq_zero_of_not_mem hL hφsupp hψsupp _)
  rintro ⟨h1, h2⟩
  apply hmem
  rw [mem_prod, mem_Icc, mem_Icc]
  exact ⟨⟨by linarith [neg_abs_le ξ], by linarith [le_abs_self ξ]⟩,
    ⟨by linarith [neg_abs_le u], by linarith [le_abs_self u]⟩⟩

theorem gIntBilinear_integrable_prod (hL : 0 < L)
    (hφc : Continuous φ) (hψc : Continuous ψ)
    (hφsupp : ∀ u, L / 2 ≤ |u| → φ u = 0)
    (hψsupp : ∀ u, L / 2 ≤ |u| → ψ u = 0) :
    Integrable (Function.uncurry (gIntBilinear φ ψ L T τ τ')) (volume.prod volume) :=
  (gIntBilinear_continuous hφc hψc).integrable_of_hasCompactSupport
    (gIntBilinear_hasCompactSupport hL hφsupp hψsupp)

theorem GauxBilinear_continuous (hL : 0 < L)
    (hφc : Continuous φ) (hψc : Continuous ψ)
    (hφsupp : ∀ u, L / 2 ≤ |u| → φ u = 0)
    (hψsupp : ∀ u, L / 2 ≤ |u| → ψ u = 0) :
    Continuous (GauxBilinear φ ψ L T τ τ') := by
  have hrewrite : GauxBilinear φ ψ L T τ τ' =
      fun ξ => ∫ u in Icc (-(L / 2)) (L / 2), gIntBilinear φ ψ L T τ τ' ξ u := by
    funext ξ
    unfold GauxBilinear
    rw [setIntegral_eq_integral_of_forall_compl_eq_zero]
    intro u hu
    apply gIntBilinear_eq_zero_of_not_mem hL hφsupp hψsupp
    rintro ⟨-, h2⟩
    apply hu
    rw [mem_Icc]
    exact ⟨by linarith [neg_abs_le u], by linarith [le_abs_self u]⟩
  rw [hrewrite]
  exact continuous_parametric_integral_of_continuous
    (gIntBilinear_continuous hφc hψc) isCompact_Icc

theorem GauxBilinear_eq_zero (hL : 0 < L)
    (hφsupp : ∀ u, L / 2 ≤ |u| → φ u = 0)
    (hψsupp : ∀ u, L / 2 ≤ |u| → ψ u = 0)
    {ξ : ℝ} (hξ : 1 ≤ |ξ|) : GauxBilinear φ ψ L T τ τ' ξ = 0 := by
  unfold GauxBilinear
  rw [← integral_zero]
  congr 1 with u
  apply gIntBilinear_eq_zero_of_not_mem hL hφsupp hψsupp
  rintro ⟨h1, -⟩
  linarith

/-- The zero sample retains the reflected second window. -/
theorem GauxBilinear_zero :
    GauxBilinear φ ψ L T τ τ' 0 =
      L * paperFT (fun u => ((φ u * ψ (-u) : ℝ) : ℂ)) ((τ - τ' : ℝ) : ℂ) := by
  unfold GauxBilinear gIntBilinear
  rw [paperFT_def, integral_const_mul_C]
  congr 1
  congr 1 with u
  simp only [mul_zero, zero_sub]
  push_cast
  ring_nf

/-- Fourier transform of the bilinear auxiliary function. -/
theorem fourier_GauxBilinear (hL : 0 < L)
    (hφc : Continuous φ) (hψc : Continuous ψ)
    (hφsupp : ∀ u, L / 2 ≤ |u| → φ u = 0)
    (hψsupp : ∀ u, L / 2 ≤ |u| → ψ u = 0) (w : ℝ) :
    𝓕 (GauxBilinear φ ψ L T τ τ') w =
      paperFT (fun u => (φ u : ℂ))
          ((τ - (T + w * (2 * π / L)) : ℝ) : ℂ) *
        paperFT (fun u => (ψ u : ℂ))
          ((τ' - (T + w * (2 * π / L)) : ℝ) : ℂ) := by
  set α : ℝ := τ - (T + w * (2 * π / L)) with hα
  set β : ℝ := τ' - (T + w * (2 * π / L)) with hβ
  set J : ℝ → ℝ → ℂ := fun ξ u =>
    cexp (↑(-2 * π * ξ * w) * I) * gIntBilinear φ ψ L T τ τ' ξ u with hJ
  have hJint : Integrable (Function.uncurry J) (volume.prod volume) := by
    have hc : Continuous (Function.uncurry J) := by
      have hcont := gIntBilinear_continuous
        (L := L) (T := T) (τ := τ) (τ' := τ') hφc hψc
      simp only [hJ]
      apply Continuous.mul _ hcont
      fun_prop
    apply hc.integrable_of_hasCompactSupport
    apply (gIntBilinear_hasCompactSupport
      (T := T) (τ := τ) (τ' := τ') hL hφsupp hψsupp).mono
    intro p hp
    rw [Function.mem_support] at hp ⊢
    intro h0
    apply hp
    simp only [hJ, Function.uncurry] at h0 ⊢
    rw [show p = (p.1, p.2) from rfl] at h0
    simp only at h0
    rw [h0, mul_zero]
  rw [Real.fourier_real_eq_integral_exp_smul]
  have step1 :
      (fun ξ : ℝ => cexp (↑(-2 * π * ξ * w) * I) •
        GauxBilinear φ ψ L T τ τ' ξ) = fun ξ => ∫ u, J ξ u := by
    funext ξ
    rw [smul_eq_mul, GauxBilinear, hJ]
    beta_reduce
    rw [integral_const_mul_C]
  rw [step1]
  rw [integral_integral_swap hJint]
  have step3 : ∀ u : ℝ, ∫ ξ, J ξ u =
      (φ u : ℂ) * cexp (I * α * u) * paperFT (fun v => (ψ v : ℂ)) β := by
    intro u
    set F0 : ℝ → ℂ := fun v => (ψ v : ℂ) * cexp (I * β * (v : ℂ)) with hF0
    have hpt : ∀ ξ : ℝ, J ξ u =
        (φ u : ℂ) * cexp (I * α * u) *
          ((L : ℂ) * ((fun y : ℝ => F0 (y - u)) (L * ξ))) := by
      intro ξ
      simp only [hJ, gIntBilinear, hF0]
      have hbook := cexp_bookkeeping
        (T := T) (τ := τ) (τ' := τ') hL.ne' ξ u w
      rw [← hα, ← hβ] at hbook
      calc
        cexp (↑(-2 * π * ξ * w) * I) *
            (↑L * (↑(φ u) * ↑(ψ (L * ξ - u)) *
              cexp (I * (↑τ * ↑u + ↑τ' * (↑L * ↑ξ - ↑u) - ↑T * ↑L * ↑ξ)))) =
            ↑L * ↑(φ u) * ↑(ψ (L * ξ - u)) *
              (cexp (I * (↑τ * ↑u + ↑τ' * (↑L * ↑ξ - ↑u) - ↑T * ↑L * ↑ξ)) *
                cexp (↑(-2 * π * ξ * w) * I)) := by ring
        _ = ↑L * ↑(φ u) * ↑(ψ (L * ξ - u)) *
              (cexp (I * ↑α * ↑u) * cexp (I * ↑β * ↑(L * ξ - u))) := by
              rw [hbook]
        _ = _ := by push_cast; ring
    have hint : ∫ ξ, J ξ u = ∫ ξ,
        (φ u : ℂ) * cexp (I * α * u) *
          ((L : ℂ) * ((fun y : ℝ => F0 (y - u)) (L * ξ))) := by
      congr 1 with ξ
      exact hpt ξ
    rw [hint, integral_const_mul_C, integral_const_mul_C,
      Measure.integral_comp_mul_left (fun y : ℝ => F0 (y - u)) L,
      integral_sub_right_eq_self F0 u, paperFT_def, abs_of_pos (inv_pos.mpr hL)]
    congr 1
    rw [← Complex.coe_smul, smul_eq_mul, ← mul_assoc, ofReal_inv,
      mul_inv_cancel₀ (ofReal_ne_zero.mpr hL.ne'), one_mul]
  simp_rw [step3]
  rw [integral_mul_const_C, paperFT_def, paperFT_def]

/-- Oriented bilinear Poisson summation for two real windows. -/
theorem hasSum_paperFT_mul_paperFT_bilinear {φ ψ : ℝ → ℝ} {L : ℝ}
    (hL : 0 < L) (hφc : Continuous φ) (hψc : Continuous ψ)
    (hφsupp : ∀ u, L / 2 ≤ |u| → φ u = 0)
    (hψsupp : ∀ u, L / 2 ≤ |u| → ψ u = 0)
    (hφdecay : ∃ C, ∀ s : ℝ,
      ‖paperFT (fun u => (φ u : ℂ)) s‖ * (1 + s ^ 2) ≤ C)
    (hψdecay : ∃ C, ∀ s : ℝ,
      ‖paperFT (fun u => (ψ u : ℂ)) s‖ * (1 + s ^ 2) ≤ C)
    (T τ τ' : ℝ) :
    HasSum (fun k : ℤ =>
      paperFT (fun u => (φ u : ℂ))
          ((τ - (T + k * (2 * π / L)) : ℝ) : ℂ) *
        paperFT (fun u => (ψ u : ℂ))
          ((τ' - (T + k * (2 * π / L)) : ℝ) : ℂ))
      (L * paperFT (fun u => ((φ u * ψ (-u) : ℝ) : ℂ))
        ((τ - τ' : ℝ) : ℂ)) := by
  obtain ⟨Cφ, hCφ⟩ := hφdecay
  obtain ⟨Cψ, hCψ⟩ := hψdecay
  set G := GauxBilinear φ ψ L T τ τ' with hG
  have hGc : Continuous G :=
    GauxBilinear_continuous hL hφc hψc hφsupp hψsupp
  have hGO : G =O[cocompact ℝ] fun x : ℝ => |x| ^ (-2 : ℝ) := by
    refine IsBigO.of_bound 0 ?_
    have hev : ∀ᶠ x : ℝ in cocompact ℝ, (1 : ℝ) ≤ ‖x‖ :=
      tendsto_norm_cocompact_atTop.eventually (eventually_ge_atTop _)
    filter_upwards [hev] with x hx
    rw [hG, GauxBilinear_eq_zero hL hφsupp hψsupp (by simpa using hx)]
    simp
  have hφhat_bdd : ∀ s : ℝ, ‖paperFT (fun u => (φ u : ℂ)) s‖ ≤ Cφ := by
    intro s
    have h := hCφ s
    have h1 : ‖paperFT (fun u => (φ u : ℂ)) s‖ * 1 ≤
        ‖paperFT (fun u => (φ u : ℂ)) s‖ * (1 + s ^ 2) := by
      gcongr
      nlinarith
    linarith
  have hψhat_bdd : ∀ s : ℝ, ‖paperFT (fun u => (ψ u : ℂ)) s‖ ≤ Cψ := by
    intro s
    have h := hCψ s
    have h1 : ‖paperFT (fun u => (ψ u : ℂ)) s‖ * 1 ≤
        ‖paperFT (fun u => (ψ u : ℂ)) s‖ * (1 + s ^ 2) := by
      gcongr
      nlinarith
    linarith
  have hCφ0 : 0 ≤ Cφ := le_trans (norm_nonneg _) (hφhat_bdd 0)
  have hCψ0 : 0 ≤ Cψ := le_trans (norm_nonneg _) (hψhat_bdd 0)
  have hFO : 𝓕 G =O[cocompact ℝ] fun x : ℝ => |x| ^ (-2 : ℝ) := by
    apply isBigO_of_decay (c := τ - T) (h := 2 * π / L)
      (C := Cφ * Cψ) (by positivity)
    intro w
    rw [hG, fourier_GauxBilinear hL hφc hψc hφsupp hψsupp w, norm_mul]
    have e1 : τ - T - w * (2 * π / L) = τ - (T + w * (2 * π / L)) := by ring
    rw [e1]
    calc
      ‖paperFT (fun u => (φ u : ℂ)) ↑(τ - (T + w * (2 * π / L)))‖ *
            ‖paperFT (fun u => (ψ u : ℂ)) ↑(τ' - (T + w * (2 * π / L)))‖ *
            (1 + (τ - (T + w * (2 * π / L))) ^ 2) =
          (‖paperFT (fun u => (φ u : ℂ)) ↑(τ - (T + w * (2 * π / L)))‖ *
            (1 + (τ - (T + w * (2 * π / L))) ^ 2)) *
            ‖paperFT (fun u => (ψ u : ℂ)) ↑(τ' - (T + w * (2 * π / L)))‖ := by ring
      _ ≤ Cφ * Cψ := by
        apply mul_le_mul (hCφ _) (hψhat_bdd _) (norm_nonneg _) hCφ0
  have hsum : Summable fun n : ℤ => 𝓕 G n :=
    summable_of_isBigO (Real.summable_abs_int_rpow one_lt_two)
      (hFO.comp_tendsto Int.tendsto_coe_cofinite)
  have key := Real.tsum_eq_tsum_fourier_of_rpow_decay_of_summable
    hGc one_lt_two hGO hsum 0
  have lhs : ∑' n : ℤ, G (0 + n) = G 0 := by
    rw [tsum_eq_single 0]
    · simp
    · intro n hn
      rw [zero_add, hG, GauxBilinear_eq_zero hL hφsupp hψsupp]
      rw [← Int.cast_abs]
      exact_mod_cast Int.one_le_abs hn
  have rhs : ∑' n : ℤ, 𝓕 G n * fourier n ((0 : ℝ) : UnitAddCircle) =
      ∑' n : ℤ, 𝓕 G n := by
    congr 1 with n
    rw [fourier_coe_apply]
    simp
  rw [lhs, rhs] at key
  have hs : HasSum (fun n : ℤ => 𝓕 G n) (G 0) := by
    rw [key]
    exact hsum.hasSum
  rw [hG, GauxBilinear_zero] at hs
  convert hs using 1
  funext k
  rw [fourier_GauxBilinear hL hφc hψc hφsupp hψsupp]

end Zeta23.Poisson
