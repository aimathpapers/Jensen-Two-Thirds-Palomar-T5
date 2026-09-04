import Zeta23.Research.JensenWedge.LeadingSaddleContour
import Mathlib.MeasureTheory.Integral.Gamma

/-!
# Exact moments of the leading complex Gaussian

The central T3 calculation needs the signed cubic moment, not an
absolute-value substitute.  This module proves integrability of every
polynomial moment of the complex Gaussian and derives the first three moments
by whole-line integration by parts.  In particular, the cubic contribution
is exactly of relative order `K⁻²`, which is the cancellation used in the
paper.
-/

namespace Zeta23.Research.JensenWedge

open Complex Filter MeasureTheory Set Topology

noncomputable section

/-- The `n`th signed moment of the full Gaussian comparison. -/
def leadingGaussianMoment (K : ℂ) (n : ℕ) : ℂ :=
  ∫ r : ℝ, (r : ℂ) ^ n * leadingGaussian K r

theorem norm_leadingGaussian (K : ℂ) (r : ℝ) :
    ‖leadingGaussian K r‖ = Real.exp (r - K.re * r ^ 2 / 2) := by
  rw [leadingGaussian, norm_exp]
  congr 1
  norm_num [Complex.div_re, ← ofReal_pow]

theorem integrable_abs_pow_mul_exp_neg_mul_sq
    {b : ℝ} (hb : 0 < b) (n : ℕ) :
    Integrable (fun r : ℝ => |r| ^ n * Real.exp (-b * r ^ 2)) := by
  have hn0 : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
  have hn : (-1 : ℝ) < (n : ℝ) := by linarith
  have h := integrable_rpow_mul_exp_neg_mul_sq hb hn
  apply Integrable.congr h.norm
  filter_upwards with r
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (Real.exp_pos _).le,
    Real.rpow_natCast, abs_pow]

/-- Exact whole-line absolute Gaussian moment, retained in Gamma form so all
orders share one statement. -/
theorem integral_abs_pow_mul_exp_neg_mul_sq
    {b : ℝ} (hb : 0 < b) (n : ℕ) :
    (∫ r : ℝ, |r| ^ n * Real.exp (-b * r ^ 2)) =
      2 * (b ^ (-(n + 1 : ℝ) / 2) * (1 / 2) *
        Real.Gamma ((n + 1 : ℝ) / 2)) := by
  let f : ℝ → ℝ := fun r => |r| ^ n * Real.exp (-b * r ^ 2)
  have hf : Integrable f := integrable_abs_pow_mul_exp_neg_mul_sq hb n
  have heven : ∀ r : ℝ, f (-r) = f r := by
    intro r
    simp only [f, abs_neg, neg_sq]
  have hhalves : (∫ r : ℝ in Iic 0, f r) = ∫ r : ℝ in Ioi 0, f r := by
    calc
      (∫ r : ℝ in Iic 0, f r) = ∫ r : ℝ in Ioi 0, f (-r) := by
        simpa using (integral_comp_neg_Ioi 0 f).symm
      _ = ∫ r : ℝ in Ioi 0, f r :=
        setIntegral_congr_fun measurableSet_Ioi fun r _ => heven r
  have hhalf : (∫ r : ℝ in Ioi 0, f r) =
      b ^ (-(n + 1 : ℝ) / 2) * (1 / 2) *
        Real.Gamma ((n + 1 : ℝ) / 2) := by
    rw [show (∫ r : ℝ in Ioi 0, f r) =
        ∫ r : ℝ in Ioi 0, r ^ (n : ℝ) * Real.exp (-b * r ^ (2 : ℝ)) by
      apply setIntegral_congr_fun measurableSet_Ioi
      intro r hr
      change |r| ^ n * Real.exp (-b * r ^ 2) =
        r ^ (n : ℝ) * Real.exp (-b * r ^ (2 : ℝ))
      rw [abs_of_pos hr, Real.rpow_natCast, Real.rpow_two]]
    have hn0 : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
    simpa using _root_.integral_rpow_mul_exp_neg_mul_rpow
      (show (0 : ℝ) < 2 by norm_num) (show (-1 : ℝ) < (n : ℝ) by linarith) hb
  change (∫ r : ℝ, f r) = _
  rw [← integral_add_compl (s := Ioi 0) measurableSet_Ioi hf,
    compl_Ioi, hhalves, hhalf]
  ring

/-- A polynomial times the complex Gaussian is integrable whenever the
quadratic coefficient has positive real part. -/
theorem integrable_pow_mul_leadingGaussian
    {K : ℂ} (hK : 0 < K.re) (n : ℕ) :
    Integrable (fun r : ℝ => (r : ℂ) ^ n * leadingGaussian K r) := by
  let b : ℝ := K.re / 4
  let C : ℝ := Real.exp (1 / K.re)
  have hb : 0 < b := by dsimp [b]; linarith
  have hn : (-1 : ℝ) < ((2 * n : ℕ) : ℝ) := by
    have hnonneg : (0 : ℝ) ≤ ((2 * n : ℕ) : ℝ) := Nat.cast_nonneg _
    linarith
  have hpow : Integrable (fun r : ℝ => r ^ (2 * n) * Real.exp (-b * r ^ 2)) := by
    simpa only [Real.rpow_natCast] using
      (integrable_rpow_mul_exp_neg_mul_sq hb hn)
  have hbase : Integrable (fun r : ℝ => Real.exp (-b * r ^ 2)) :=
    integrable_exp_neg_mul_sq hb
  have hmajorant : Integrable
      (fun r : ℝ => C * ((1 + r ^ (2 * n)) * Real.exp (-b * r ^ 2))) := by
    refine ((hbase.add hpow).const_mul C).congr ?_
    filter_upwards with r
    change C * (Real.exp (-b * r ^ 2) +
      r ^ (2 * n) * Real.exp (-b * r ^ 2)) =
        C * ((1 + r ^ (2 * n)) * Real.exp (-b * r ^ 2))
    ring
  apply Integrable.mono' hmajorant
  · apply Continuous.aestronglyMeasurable
    unfold leadingGaussian
    fun_prop
  filter_upwards with r
  have hquad : r ≤ 1 / K.re + K.re * r ^ 2 / 4 := by
    have hsquare : 0 ≤ (K.re * r - 2) ^ 2 := sq_nonneg _
    field_simp [ne_of_gt hK]
    nlinarith
  have hexponent :
      r - K.re * r ^ 2 / 2 ≤ 1 / K.re - b * r ^ 2 := by
    dsimp [b]
    nlinarith
  have hpoly : |r| ^ n ≤ 1 + r ^ (2 * n) := by
    have hy : 0 ≤ |r| ^ n := pow_nonneg (abs_nonneg _) _
    have hsq : 0 ≤ (|r| ^ n - 1 / 2) ^ 2 := sq_nonneg _
    rw [show r ^ (2 * n) = (|r| ^ n) ^ 2 by
      calc
        r ^ (2 * n) = (r ^ n) ^ 2 := by rw [mul_comm, pow_mul]
        _ = (|r| ^ n) ^ 2 := by rw [← abs_pow, sq_abs]]
    nlinarith
  rw [norm_mul, norm_pow, norm_real, norm_leadingGaussian]
  have hC : 0 < C := Real.exp_pos _
  have hgauss : 0 < Real.exp (-b * r ^ 2) := Real.exp_pos _
  calc
    |r| ^ n * Real.exp (r - K.re * r ^ 2 / 2) ≤
        |r| ^ n * Real.exp (1 / K.re - b * r ^ 2) := by
      gcongr
    _ = C * (|r| ^ n * Real.exp (-b * r ^ 2)) := by
      rw [Real.exp_sub]
      rw [div_eq_mul_inv]
      rw [← Real.exp_neg]
      dsimp [C]
      ring
    _ ≤ C * ((1 + r ^ (2 * n)) * Real.exp (-b * r ^ 2)) := by
      gcongr

/-- A uniform Gamma-form upper bound for absolute moments of the shifted
complex Gaussian. -/
theorem integral_norm_pow_mul_leadingGaussian_le
    {K : ℂ} (hK : 0 < K.re) (n : ℕ) :
    (∫ r : ℝ, ‖(r : ℂ) ^ n * leadingGaussian K r‖) ≤
      Real.exp (1 / K.re) *
        (2 * ((K.re / 4) ^ (-(n + 1 : ℝ) / 2) * (1 / 2) *
          Real.Gamma ((n + 1 : ℝ) / 2))) := by
  let b : ℝ := K.re / 4
  have hb : 0 < b := by dsimp [b]; linarith
  have hleft : Integrable
      (fun r : ℝ => ‖(r : ℂ) ^ n * leadingGaussian K r‖) :=
    (integrable_pow_mul_leadingGaussian hK n).norm
  have hright : Integrable
      (fun r : ℝ => Real.exp (1 / K.re) *
        (|r| ^ n * Real.exp (-b * r ^ 2))) :=
    (integrable_abs_pow_mul_exp_neg_mul_sq hb n).const_mul _
  calc
    (∫ r : ℝ, ‖(r : ℂ) ^ n * leadingGaussian K r‖) ≤
        ∫ r : ℝ, Real.exp (1 / K.re) *
          (|r| ^ n * Real.exp (-b * r ^ 2)) := by
      apply integral_mono hleft hright
      intro r
      change ‖(r : ℂ) ^ n * leadingGaussian K r‖ ≤
        Real.exp (1 / K.re) * (|r| ^ n * Real.exp (-b * r ^ 2))
      rw [norm_mul, norm_pow, norm_real, norm_leadingGaussian]
      have hquad : r ≤ 1 / K.re + K.re * r ^ 2 / 4 := by
        have hsquare : 0 ≤ (K.re * r - 2) ^ 2 := sq_nonneg _
        field_simp [ne_of_gt hK]
        nlinarith
      have hexponent : r - K.re * r ^ 2 / 2 ≤
          1 / K.re - b * r ^ 2 := by
        dsimp [b]
        nlinarith
      calc
        |r| ^ n * Real.exp (r - K.re * r ^ 2 / 2) ≤
            |r| ^ n * Real.exp (1 / K.re - b * r ^ 2) := by
          gcongr
        _ = Real.exp (1 / K.re) *
            (|r| ^ n * Real.exp (-b * r ^ 2)) := by
          rw [Real.exp_sub, div_eq_mul_inv, ← Real.exp_neg]
          ring
    _ = Real.exp (1 / K.re) *
        (2 * (b ^ (-(n + 1 : ℝ) / 2) * (1 / 2) *
          Real.Gamma ((n + 1 : ℝ) / 2))) := by
      rw [MeasureTheory.integral_const_mul,
        integral_abs_pow_mul_exp_neg_mul_sq hb]
    _ = _ := by rfl

/-- The fourth absolute moment needed for the quartic Taylor remainder. -/
theorem integral_norm_fourth_mul_leadingGaussian_le
    {K : ℂ} (hK : 0 < K.re) :
    (∫ r : ℝ, ‖(r : ℂ) ^ 4 * leadingGaussian K r‖) ≤
      Real.exp (1 / K.re) *
        (2 * ((K.re / 4) ^ (-(5 : ℝ) / 2) * (1 / 2) *
          Real.Gamma ((5 : ℝ) / 2))) := by
  convert integral_norm_pow_mul_leadingGaussian_le hK 4 using 1 <;> norm_num

/-- The sixth absolute moment needed after squaring a cubic remainder. -/
theorem integral_norm_sixth_mul_leadingGaussian_le
    {K : ℂ} (hK : 0 < K.re) :
    (∫ r : ℝ, ‖(r : ℂ) ^ 6 * leadingGaussian K r‖) ≤
      Real.exp (1 / K.re) *
        (2 * ((K.re / 4) ^ (-(7 : ℝ) / 2) * (1 / 2) *
          Real.Gamma ((7 : ℝ) / 2))) := by
  convert integral_norm_pow_mul_leadingGaussian_le hK 6 using 1 <;> norm_num

theorem leadingGaussianMoment_zero (K : ℂ) :
    leadingGaussianMoment K 0 = ∫ r : ℝ, leadingGaussian K r := by
  simp [leadingGaussianMoment]

/-- The complex derivative of the Gaussian along the real coordinate. -/
theorem hasDerivAt_leadingGaussian
    (K : ℂ) (r : ℝ) :
    HasDerivAt (leadingGaussian K)
      ((1 - K * r) * leadingGaussian K r) r := by
  unfold leadingGaussian
  have hid : HasDerivAt (fun x : ℝ => (x : ℂ)) 1 r :=
    HasDerivAt.ofReal_comp (hasDerivAt_id r)
  let p : ℝ → ℂ := fun x => (x : ℂ) - K * (x : ℂ) ^ 2 / 2
  have hp : HasDerivAt p (1 - K * r) r := by
    have hraw := hid.sub ((((hid.pow 2).const_mul K).div_const 2))
    apply (hraw.congr_of_eventuallyEq
      (Eventually.of_forall fun x => by simp [p])).congr_deriv
    ring
  simpa [p, mul_comm] using hp.cexp

theorem leadingGaussianMoment_one
    {K : ℂ} (hK : 0 < K.re) :
    leadingGaussianMoment K 1 = leadingGaussianMoment K 0 / K := by
  have hKne : K ≠ 0 := by
    intro hzero
    rw [hzero] at hK
    simpa using hK
  have hderiv : ∀ r : ℝ, HasDerivAt (leadingGaussian K)
      ((1 - K * r) * leadingGaussian K r) r :=
    hasDerivAt_leadingGaussian K
  have hint : Integrable
      (fun r : ℝ => (1 - K * r) * leadingGaussian K r) := by
    have h0 := integrable_leadingGaussian hK
    have h1 : Integrable (fun r : ℝ => (r : ℂ) * leadingGaussian K r) := by
      simpa only [pow_one] using integrable_pow_mul_leadingGaussian hK 1
    refine (h0.sub (h1.const_mul K)).congr ?_
    filter_upwards with r
    change leadingGaussian K r - K * ((r : ℂ) * leadingGaussian K r) =
      (1 - K * r) * leadingGaussian K r
    ring
  have hzero := integral_eq_zero_of_hasDerivAt_of_integrable hderiv hint
    (integrable_leadingGaussian hK)
  have h1 : Integrable (fun r : ℝ => (r : ℂ) * leadingGaussian K r) := by
    simpa only [pow_one] using integrable_pow_mul_leadingGaussian hK 1
  have hrelation : leadingGaussianMoment K 0 -
      K * leadingGaussianMoment K 1 = 0 := by
    calc
      leadingGaussianMoment K 0 - K * leadingGaussianMoment K 1 =
          ∫ r : ℝ, (1 - K * r) * leadingGaussian K r := by
        rw [leadingGaussianMoment, leadingGaussianMoment]
        simp only [pow_zero, one_mul, pow_one]
        rw [show (fun r : ℝ => (1 - K * r) * leadingGaussian K r) =
            fun r : ℝ => leadingGaussian K r -
              K * ((r : ℂ) * leadingGaussian K r) by
          funext r
          ring]
        rw [integral_sub (integrable_leadingGaussian hK) (h1.const_mul K),
          MeasureTheory.integral_const_mul]
      _ = 0 := hzero
  apply (eq_div_iff hKne).2
  linear_combination -hrelation

theorem leadingGaussianMoment_two
    {K : ℂ} (hK : 0 < K.re) :
    leadingGaussianMoment K 2 =
      leadingGaussianMoment K 0 * (1 / K + 1 / K ^ 2) := by
  have hKne : K ≠ 0 := by
    intro hzero
    rw [hzero] at hK
    simpa using hK
  let F : ℝ → ℂ := fun r => (r : ℂ) * leadingGaussian K r
  let F' : ℝ → ℂ := fun r =>
    leadingGaussian K r + (r : ℂ) * leadingGaussian K r -
      K * ((r : ℂ) ^ 2 * leadingGaussian K r)
  have hderiv : ∀ r : ℝ, HasDerivAt F (F' r) r := by
    intro r
    have hid : HasDerivAt (fun x : ℝ => (x : ℂ)) 1 r :=
      HasDerivAt.ofReal_comp (hasDerivAt_id r)
    have hraw := hid.mul (hasDerivAt_leadingGaussian K r)
    apply (hraw.congr_of_eventuallyEq
      (Eventually.of_forall fun x => by simp [F])).congr_deriv
    simp only [F']
    ring
  have hint : Integrable F' := by
    dsimp only [F']
    have h0 := integrable_leadingGaussian hK
    have h1 : Integrable (fun r : ℝ => (r : ℂ) * leadingGaussian K r) := by
      simpa only [pow_one] using integrable_pow_mul_leadingGaussian hK 1
    have h2 := integrable_pow_mul_leadingGaussian hK 2
    exact (h0.add h1).sub (h2.const_mul K)
  have hFint : Integrable F := by
    simpa only [F, pow_one] using integrable_pow_mul_leadingGaussian hK 1
  have hzero := integral_eq_zero_of_hasDerivAt_of_integrable hderiv hint hFint
  have h0 := integrable_leadingGaussian hK
  have h1 : Integrable (fun r : ℝ => (r : ℂ) * leadingGaussian K r) := by
    simpa only [pow_one] using integrable_pow_mul_leadingGaussian hK 1
  have h2 := integrable_pow_mul_leadingGaussian hK 2
  have hlinear : (∫ r : ℝ, F' r) =
      (∫ r : ℝ, leadingGaussian K r) +
        (∫ r : ℝ, (r : ℂ) * leadingGaussian K r) -
        K * (∫ r : ℝ, (r : ℂ) ^ 2 * leadingGaussian K r) := by
    let G0 : ℝ → ℂ := leadingGaussian K
    let G1 : ℝ → ℂ := fun r => (r : ℂ) * leadingGaussian K r
    let G2 : ℝ → ℂ := fun r => (r : ℂ) ^ 2 * leadingGaussian K r
    have hG0 : Integrable G0 := h0
    have hG1 : Integrable G1 := h1
    have hG2 : Integrable G2 := h2
    have hfun : F' = G0 + G1 - fun r => K * G2 r := by
      funext r
      rfl
    have hadd : (∫ r : ℝ, (G0 + G1) r) =
        (∫ r : ℝ, G0 r) + (∫ r : ℝ, G1 r) := by
      simpa only [Pi.add_apply] using integral_add hG0 hG1
    have hconst : (∫ r : ℝ, K * G2 r) = K * (∫ r : ℝ, G2 r) :=
      MeasureTheory.integral_const_mul K G2
    rw [hfun]
    calc
      (∫ r : ℝ, (G0 + G1 - fun r => K * G2 r) r) =
          (∫ r : ℝ, (G0 + G1) r) - (∫ r : ℝ, K * G2 r) :=
        integral_sub (hG0.add hG1) (hG2.const_mul K)
      _ = (∫ r : ℝ, G0 r) + (∫ r : ℝ, G1 r) -
          K * (∫ r : ℝ, G2 r) := by
        rw [hadd, hconst]
      _ = _ := by rfl
  have hrelation : leadingGaussianMoment K 0 + leadingGaussianMoment K 1 -
      K * leadingGaussianMoment K 2 = 0 := by
    calc
      leadingGaussianMoment K 0 + leadingGaussianMoment K 1 -
          K * leadingGaussianMoment K 2 = ∫ r : ℝ, F' r := by
        rw [leadingGaussianMoment, leadingGaussianMoment, leadingGaussianMoment]
        simp only [pow_zero, one_mul, pow_one, F']
        exact hlinear.symm
      _ = 0 := hzero
  have hm2 : leadingGaussianMoment K 2 =
      (leadingGaussianMoment K 0 + leadingGaussianMoment K 1) / K := by
    apply (eq_div_iff hKne).2
    linear_combination -hrelation
  rw [hm2, leadingGaussianMoment_one hK]
  field_simp [hKne] <;> ring

theorem leadingGaussianMoment_three
    {K : ℂ} (hK : 0 < K.re) :
    leadingGaussianMoment K 3 =
      leadingGaussianMoment K 0 * (3 / K ^ 2 + 1 / K ^ 3) := by
  have hKne : K ≠ 0 := by
    intro hzero
    rw [hzero] at hK
    simpa using hK
  let F : ℝ → ℂ := fun r => (r : ℂ) ^ 2 * leadingGaussian K r
  let F' : ℝ → ℂ := fun r =>
    2 * ((r : ℂ) * leadingGaussian K r) +
      (r : ℂ) ^ 2 * leadingGaussian K r -
      K * ((r : ℂ) ^ 3 * leadingGaussian K r)
  have hderiv : ∀ r : ℝ, HasDerivAt F (F' r) r := by
    intro r
    have hid : HasDerivAt (fun x : ℝ => (x : ℂ)) 1 r :=
      HasDerivAt.ofReal_comp (hasDerivAt_id r)
    have hraw := (hid.pow 2).mul (hasDerivAt_leadingGaussian K r)
    apply (hraw.congr_of_eventuallyEq
      (Eventually.of_forall fun x => by simp [F])).congr_deriv
    simp only [F', Pi.pow_apply]
    ring
  have hint : Integrable F' := by
    dsimp only [F']
    have h1 : Integrable (fun r : ℝ => (r : ℂ) * leadingGaussian K r) := by
      simpa only [pow_one] using integrable_pow_mul_leadingGaussian hK 1
    have h2 := integrable_pow_mul_leadingGaussian hK 2
    have h3 := integrable_pow_mul_leadingGaussian hK 3
    exact (h1.const_mul 2 |>.add h2).sub (h3.const_mul K)
  have hFint : Integrable F := by
    simpa only [F] using integrable_pow_mul_leadingGaussian hK 2
  have hzero := integral_eq_zero_of_hasDerivAt_of_integrable hderiv hint hFint
  have h1 : Integrable (fun r : ℝ => (r : ℂ) * leadingGaussian K r) := by
    simpa only [pow_one] using integrable_pow_mul_leadingGaussian hK 1
  have h2 := integrable_pow_mul_leadingGaussian hK 2
  have h3 := integrable_pow_mul_leadingGaussian hK 3
  have hlinear : (∫ r : ℝ, F' r) =
      2 * (∫ r : ℝ, (r : ℂ) * leadingGaussian K r) +
        (∫ r : ℝ, (r : ℂ) ^ 2 * leadingGaussian K r) -
        K * (∫ r : ℝ, (r : ℂ) ^ 3 * leadingGaussian K r) := by
    let G1 : ℝ → ℂ := fun r => (r : ℂ) * leadingGaussian K r
    let G2 : ℝ → ℂ := fun r => (r : ℂ) ^ 2 * leadingGaussian K r
    let G3 : ℝ → ℂ := fun r => (r : ℂ) ^ 3 * leadingGaussian K r
    have hG1 : Integrable G1 := h1
    have hG2 : Integrable G2 := h2
    have hG3 : Integrable G3 := h3
    have hfun : F' = (fun r => 2 * G1 r) + G2 - fun r => K * G3 r := by
      funext r
      rfl
    have hadd : (∫ r : ℝ, ((fun r => 2 * G1 r) + G2) r) =
        (∫ r : ℝ, 2 * G1 r) + (∫ r : ℝ, G2 r) := by
      simpa only [Pi.add_apply] using integral_add (hG1.const_mul 2) hG2
    have hconstK : (∫ r : ℝ, K * G3 r) = K * (∫ r : ℝ, G3 r) :=
      MeasureTheory.integral_const_mul K G3
    have hconstTwo : (∫ r : ℝ, 2 * G1 r) = 2 * (∫ r : ℝ, G1 r) :=
      MeasureTheory.integral_const_mul 2 G1
    rw [hfun]
    calc
      (∫ r : ℝ, ((fun r => 2 * G1 r) + G2 - fun r => K * G3 r) r) =
          (∫ r : ℝ, ((fun r => 2 * G1 r) + G2) r) -
            (∫ r : ℝ, K * G3 r) :=
        integral_sub ((hG1.const_mul 2).add hG2) (hG3.const_mul K)
      _ = (∫ r : ℝ, 2 * G1 r) + (∫ r : ℝ, G2 r) -
          K * (∫ r : ℝ, G3 r) := by
        rw [hadd, hconstK]
      _ = _ := by rw [hconstTwo]
  have hrelation : 2 * leadingGaussianMoment K 1 + leadingGaussianMoment K 2 -
      K * leadingGaussianMoment K 3 = 0 := by
    calc
      2 * leadingGaussianMoment K 1 + leadingGaussianMoment K 2 -
          K * leadingGaussianMoment K 3 = ∫ r : ℝ, F' r := by
        rw [leadingGaussianMoment, leadingGaussianMoment, leadingGaussianMoment]
        simp only [pow_one, F']
        exact hlinear.symm
      _ = 0 := hzero
  have hm3 : leadingGaussianMoment K 3 =
      (2 * leadingGaussianMoment K 1 + leadingGaussianMoment K 2) / K := by
    apply (eq_div_iff hKne).2
    linear_combination -hrelation
  rw [hm3, leadingGaussianMoment_one hK, leadingGaussianMoment_two hK]
  field_simp [hKne] <;> ring

theorem integral_cubic_mul_leadingGaussian
    {K : ℂ} (hK : 0 < K.re) :
    (∫ r : ℝ, (r : ℂ) ^ 3 * leadingGaussian K r) /
        (∫ r : ℝ, leadingGaussian K r) = 3 / K ^ 2 + 1 / K ^ 3 := by
  rw [← leadingGaussianMoment_zero K, ← leadingGaussianMoment]
  rw [leadingGaussianMoment_three hK]
  have hKne : K ≠ 0 := by
    intro hzero
    rw [hzero] at hK
    simpa using hK
  have hbase : leadingGaussianMoment K 0 ≠ 0 := by
    rw [leadingGaussianMoment_zero, integral_leadingGaussian hK]
    apply mul_ne_zero
    · have htwopi : (2 * Real.pi : ℂ) ≠ 0 :=
        mul_ne_zero (by norm_num) (ofReal_ne_zero.mpr Real.pi_ne_zero)
      exact cpow_ne_zero_iff.mpr (Or.inl (div_ne_zero htwopi hKne))
    · exact exp_ne_zero _
  field_simp [hbase]

end

end Zeta23.Research.JensenWedge
