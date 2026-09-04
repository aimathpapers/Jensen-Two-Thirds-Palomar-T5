import Zeta23.Research.JensenWedge.ThetaOmegaDecay
import Mathlib.MeasureTheory.Integral.IntegralEqImproper

/-!
# Exact theta-to-omega moment conversion

This module performs the two improper integrations by parts used in T1.
The endpoint term at `u = 0` is retained explicitly, so the cancellation
with Riemann's standalone `1/2` normalization is visible to the kernel.
-/

namespace Zeta23.Research.JensenWedge

open Complex Filter Function MeasureTheory Set Topology Asymptotics

noncomputable section

/-- The positive-half-line omega amplitude in the manuscript's logarithmic
variable. -/
def omegaLogAmplitude (u : ℝ) : ℝ :=
  Real.exp (u / 2) * riemannOmega (Real.exp (2 * u))

/-- The exact differential-operator relation, with all theta derivatives
already justified. -/
theorem four_mul_omegaLogAmplitude (u : ℝ) :
    4 * omegaLogAmplitude u =
      iteratedDeriv 2 thetaLogAmplitude u - thetaLogAmplitude u / 4 := by
  unfold omegaLogAmplitude
  rw [thetaLogAmplitude_second_sub_quarter_eq_omega_concrete]
  ring

/-- Every polynomially weighted omega amplitude is integrable on the
positive half-line. -/
theorem integrableOn_pow_mul_omegaLogAmplitude (m : ℕ) :
    IntegrableOn (fun u => u ^ m * omegaLogAmplitude u) (Ioi 0) := by
  have h2 := integrableOn_pow_mul_iteratedDeriv_two_thetaLogAmplitude m
  have h0 := (integrableOn_pow_mul_thetaLogAmplitude m).const_mul (1 / 4 : ℝ)
  have hdiff := h2.sub h0
  have hscaled := hdiff.const_mul (1 / 4 : ℝ)
  apply IntegrableOn.congr_fun hscaled _ measurableSet_Ioi
  intro u _hu
  change (1 / 4 : ℝ) *
      (u ^ m * iteratedDeriv 2 thetaLogAmplitude u -
        1 / 4 * (u ^ m * thetaLogAmplitude u)) =
    u ^ m * omegaLogAmplitude u
  rw [show omegaLogAmplitude u =
      (iteratedDeriv 2 thetaLogAmplitude u - thetaLogAmplitude u / 4) / 4 by
    linarith [four_mul_omegaLogAmplitude u]]
  ring

/-- The second derivative has integral `1/4`; this is the nonzero endpoint
term that cancels the standalone constant in the entire-xi definition. -/
theorem integral_iteratedDeriv_two_thetaLogAmplitude :
    ∫ u in Ioi (0 : ℝ), iteratedDeriv 2 thetaLogAmplitude u = 1 / 4 := by
  have hu : ∀ x ∈ Ioi (0 : ℝ),
      HasDerivAt (fun _ : ℝ => (1 : ℝ)) 0 x := by
    intro x _hx
    exact hasDerivAt_const x 1
  have hv : ∀ x ∈ Ioi (0 : ℝ),
      HasDerivAt (deriv thetaLogAmplitude)
        (iteratedDeriv 2 thetaLogAmplitude x) x := by
    intro x _hx
    have h := thetaLogAmplitude_contDiff_two.differentiable_deriv_two x
    rw [show iteratedDeriv 2 thetaLogAmplitude x =
        deriv (deriv thetaLogAmplitude) x by
      rw [show 2 = 1 + 1 by norm_num, iteratedDeriv_succ, iteratedDeriv_one]]
    exact h.hasDerivAt
  have huv' : IntegrableOn
      ((fun _ : ℝ => (1 : ℝ)) * fun x => iteratedDeriv 2 thetaLogAmplitude x)
      (Ioi 0) := by
    apply IntegrableOn.congr_fun
      (integrableOn_pow_mul_iteratedDeriv_two_thetaLogAmplitude 0) _ measurableSet_Ioi
    intro x _hx
    simp only [zero_add, pow_zero, one_mul, Pi.mul_apply]
  have hu'v : IntegrableOn
      ((fun _ : ℝ => (0 : ℝ)) * deriv thetaLogAmplitude) (Ioi 0) := by
    refine IntegrableOn.congr_fun (f := fun _ : ℝ => (0 : ℝ))
      (g := (fun _ : ℝ => (0 : ℝ)) * deriv thetaLogAmplitude)
      integrableOn_zero ?_ measurableSet_Ioi
    intro x _hx
    simp only [Pi.mul_apply, zero_mul]
  have hzero : Tendsto
      ((fun _ : ℝ => (1 : ℝ)) * deriv thetaLogAmplitude)
      (nhdsWithin 0 (Ioi 0)) (nhds (-1 / 4 : ℝ)) := by
    have hcont : ContinuousAt (deriv thetaLogAmplitude) 0 :=
      (thetaLogAmplitude_contDiff_two.continuous_deriv (by norm_num)).continuousAt
    have ht : Tendsto (deriv thetaLogAmplitude) (nhdsWithin 0 (Ioi 0))
        (nhds (deriv thetaLogAmplitude 0)) :=
      hcont.tendsto.mono_left nhdsWithin_le_nhds
    rw [deriv_thetaLogAmplitude_zero] at ht
    apply ht.congr'
    filter_upwards [] with x
    simp only [Pi.mul_apply, one_mul]
  have htop : Tendsto
      ((fun _ : ℝ => (1 : ℝ)) * deriv thetaLogAmplitude)
      atTop (nhds (0 : ℝ)) := by
    apply (tendsto_pow_mul_deriv_thetaLogAmplitude_atTop 0).congr'
    filter_upwards [] with x
    simp only [zero_add, pow_zero, one_mul, Pi.mul_apply]
  have hibp := integral_Ioi_mul_deriv_eq_deriv_mul
    hu hv huv' hu'v hzero htop
  simp only [Pi.mul_apply, one_mul, zero_mul, integral_zero, sub_zero] at hibp
  norm_num at hibp ⊢
  exact hibp

/-- Two integrations by parts for every polynomial degree at least two. -/
theorem integral_pow_add_two_mul_iteratedDeriv_two_thetaLogAmplitude (m : ℕ) :
    (∫ u in Ioi (0 : ℝ),
      u ^ (m + 2) * iteratedDeriv 2 thetaLogAmplitude u) =
      ((m : ℝ) + 2) * ((m : ℝ) + 1) *
        ∫ u in Ioi (0 : ℝ), u ^ m * thetaLogAmplitude u := by
  let p : ℝ → ℝ := fun u => u ^ (m + 2)
  let p' : ℝ → ℝ := fun u => ((m : ℝ) + 2) * u ^ (m + 1)
  let p'' : ℝ → ℝ := fun u => ((m : ℝ) + 2) * ((m : ℝ) + 1) * u ^ m
  have hp : ∀ x ∈ Ioi (0 : ℝ), HasDerivAt p (p' x) x := by
    intro x _hx
    simpa [p, p', Nat.cast_add, Nat.cast_ofNat] using
      (hasDerivAt_pow (m + 2) x)
  have hp' : ∀ x ∈ Ioi (0 : ℝ), HasDerivAt p' (p'' x) x := by
    intro x _hx
    simpa [p', p'', Nat.cast_add, Nat.cast_one, Nat.cast_ofNat, mul_assoc] using
      ((hasDerivAt_pow (m + 1) x).const_mul ((m + 2 : ℕ) : ℝ))
  have hA : ∀ x ∈ Ioi (0 : ℝ),
      HasDerivAt thetaLogAmplitude (deriv thetaLogAmplitude x) x := by
    intro x _hx
    exact (thetaLogAmplitude_contDiff_two.differentiable (by norm_num)) x |>.hasDerivAt
  have hA' : ∀ x ∈ Ioi (0 : ℝ),
      HasDerivAt (deriv thetaLogAmplitude)
        (iteratedDeriv 2 thetaLogAmplitude x) x := by
    intro x _hx
    have h := thetaLogAmplitude_contDiff_two.differentiable_deriv_two x
    rw [show iteratedDeriv 2 thetaLogAmplitude x =
        deriv (deriv thetaLogAmplitude) x by
      rw [show 2 = 1 + 1 by norm_num, iteratedDeriv_succ, iteratedDeriv_one]]
    exact h.hasDerivAt
  have hpA2 : IntegrableOn (p * fun x => iteratedDeriv 2 thetaLogAmplitude x)
      (Ioi 0) := by
    change IntegrableOn (fun x => x ^ (m + 2) *
      iteratedDeriv 2 thetaLogAmplitude x) (Ioi 0)
    exact integrableOn_pow_mul_iteratedDeriv_two_thetaLogAmplitude (m + 2)
  have hp'A' : IntegrableOn (p' * deriv thetaLogAmplitude) (Ioi 0) := by
    apply IntegrableOn.congr_fun
      ((integrableOn_pow_mul_deriv_thetaLogAmplitude (m + 1)).const_mul
        ((m : ℝ) + 2)) _ measurableSet_Ioi
    intro x _hx
    simp only [p', Pi.mul_apply]
    ring
  have hp'A : IntegrableOn (p' * thetaLogAmplitude) (Ioi 0) := by
    apply IntegrableOn.congr_fun
      ((integrableOn_pow_mul_thetaLogAmplitude (m + 1)).const_mul
        ((m : ℝ) + 2)) _ measurableSet_Ioi
    intro x _hx
    simp only [p', Pi.mul_apply]
    ring
  have hp''A : IntegrableOn (p'' * thetaLogAmplitude) (Ioi 0) := by
    apply IntegrableOn.congr_fun
      ((integrableOn_pow_mul_thetaLogAmplitude m).const_mul
        (((m : ℝ) + 2) * ((m : ℝ) + 1))) _ measurableSet_Ioi
    intro x _hx
    simp only [p'', Pi.mul_apply]
    ring
  have hpA'_zero : Tendsto (p * deriv thetaLogAmplitude)
      (nhdsWithin 0 (Ioi 0)) (nhds (0 : ℝ)) := by
    have hcont : ContinuousAt (p * deriv thetaLogAmplitude) 0 :=
      (continuousAt_id.pow (m + 2)).mul
        (thetaLogAmplitude_contDiff_two.continuous_deriv (by norm_num)).continuousAt
    simpa only [p, Pi.mul_apply, zero_pow (by omega : m + 2 ≠ 0), zero_mul] using
      hcont.tendsto.mono_left nhdsWithin_le_nhds
  have hpA'_top : Tendsto (p * deriv thetaLogAmplitude) atTop (nhds (0 : ℝ)) := by
    change Tendsto (fun x => x ^ (m + 2) * deriv thetaLogAmplitude x)
      atTop (nhds (0 : ℝ))
    exact tendsto_pow_mul_deriv_thetaLogAmplitude_atTop (m + 2)
  have hp'A_zero : Tendsto (p' * thetaLogAmplitude)
      (nhdsWithin 0 (Ioi 0)) (nhds (0 : ℝ)) := by
    have hcont : ContinuousAt (p' * thetaLogAmplitude) 0 := by
      exact ((continuousAt_const.mul (continuousAt_id.pow (m + 1))).mul
        thetaLogAmplitude_contDiff_two.continuous.continuousAt)
    have ht : Tendsto (p' * thetaLogAmplitude)
        (nhdsWithin 0 (Ioi 0))
        (nhds ((p' * thetaLogAmplitude) 0)) :=
      hcont.tendsto.mono_left nhdsWithin_le_nhds
    have hvalue : (p' * thetaLogAmplitude) 0 = 0 := by
      simp only [p', Pi.mul_apply, zero_pow (by omega : m + 1 ≠ 0), mul_zero,
        zero_mul]
    rw [hvalue] at ht
    exact ht
  have hp'A_top : Tendsto (p' * thetaLogAmplitude) atTop (nhds (0 : ℝ)) := by
    have h := (tendsto_pow_mul_thetaLogAmplitude_atTop (m + 1)).const_mul
      ((m : ℝ) + 2)
    simp only [mul_zero] at h
    apply h.congr'
    filter_upwards [] with x
    simp only [p', Pi.mul_apply]
    ring
  have hfirst := integral_Ioi_mul_deriv_eq_deriv_mul
    hp hA' hpA2 hp'A' hpA'_zero hpA'_top
  have hsecond := integral_Ioi_mul_deriv_eq_deriv_mul
    hp' hA hp'A' hp''A hp'A_zero hp'A_top
  rw [show (∫ u in Ioi (0 : ℝ), u ^ (m + 2) *
      iteratedDeriv 2 thetaLogAmplitude u) =
      ∫ u in Ioi (0 : ℝ), p u * iteratedDeriv 2 thetaLogAmplitude u by rfl]
  rw [hfirst, hsecond]
  simp only [p'', Pi.mul_apply, sub_zero, zero_sub, neg_zero, neg_neg]
  calc
    (∫ x in Ioi (0 : ℝ),
        ((m : ℝ) + 2) * ((m : ℝ) + 1) * x ^ m * thetaLogAmplitude x) =
        ∫ x in Ioi (0 : ℝ),
          (((m : ℝ) + 2) * ((m : ℝ) + 1)) *
            (x ^ m * thetaLogAmplitude x) := by
              apply integral_congr_ae
              filter_upwards [] with x
              ring
    _ = ((m : ℝ) + 2) * ((m : ℝ) + 1) *
        ∫ x in Ioi (0 : ℝ), x ^ m * thetaLogAmplitude x := by
          rw [integral_const_mul]

end

end Zeta23.Research.JensenWedge
