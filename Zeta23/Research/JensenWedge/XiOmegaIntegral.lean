import Zeta23.Research.JensenWedge.ThetaOmega
import Mathlib.Analysis.MellinInversion

/-!
# From the completed-zeta Mellin transform to the omega integral

This module carries out the logarithmic change of variables and prepares the
improper integrations by parts closing T1.
-/

namespace Zeta23.Research.JensenWedge

open Complex Filter Function MeasureTheory Set Topology Asymptotics
open scoped FourierTransform

noncomputable section

/-- Logarithmic form of a Mellin transform.  This is the first equality in
Mathlib's Mellin-to-Fourier calculation, isolated here for direct use. -/
theorem mellin_eq_logIntegral_neg (f : ℝ → ℂ) (s : ℂ) :
    mellin f s =
      ∫ u : ℝ, Complex.exp (-s * u) * f (Real.exp (-u)) := by
  rw [mellin_eq_fourier, Real.fourier_eq']
  apply integral_congr_ae
  filter_upwards [] with u
  simp only [Real.inner_apply, Complex.real_smul, smul_eq_mul]
  trans Complex.exp (-s.im * u * I) *
      ((Real.exp (-s.re * u) : ℂ) * f (Real.exp (-u)))
  · congr 1
    push_cast
    field_simp [Real.pi_ne_zero]
  · rw [show -s * (u : ℂ) =
        (-s.im * u * I) + ((-s.re * u : ℝ) : ℂ) by
      apply Complex.ext <;> simp]
    rw [Complex.exp_add, ← Complex.ofReal_exp]
    push_cast
    ring

/-- Exact whole-line logarithmic representation of Mathlib's pole-removed
completed Riemann zeta. -/
theorem completedRiemannZeta₀_eq_logIntegral (s : ℂ) :
    completedRiemannZeta₀ s =
      ∫ u : ℝ, Complex.exp (s * u) *
        riemannThetaModifiedKernel (Real.exp (2 * u)) := by
  rw [completedRiemannZeta₀_eq_mellin_riemannThetaModifiedKernel]
  rw [mellin_eq_logIntegral_neg]
  let g : ℝ → ℂ := fun x =>
    Complex.exp (-(s / 2) * x) *
      riemannThetaModifiedKernel (Real.exp (-x))
  have hscale := Measure.integral_comp_mul_left g (-2)
  change (∫ x : ℝ, g x) / 2 = _
  calc
    (∫ x : ℝ, g x) / 2 = ∫ u : ℝ, g (-2 * u) := by
      rw [hscale]
      norm_num [Complex.real_smul]
      ring
    _ = ∫ u : ℝ, Complex.exp (s * u) *
        riemannThetaModifiedKernel (Real.exp (2 * u)) := by
      apply integral_congr_ae
      filter_upwards [] with u
      unfold g
      rw [show -(s / 2) * ((-2 * u : ℝ) : ℂ) = s * (u : ℂ) by
        push_cast
        ring]
      rw [show -(-2 * u) = 2 * u by ring]

/-- The centered modified-theta amplitude occurring in the whole-line xi
integral. -/
def centeredModifiedThetaAmplitude (u : ℝ) : ℂ :=
  (Real.exp (u / 2) : ℂ) *
    riemannThetaModifiedKernel (Real.exp (2 * u))

/-- The completed zeta centered at one half is the bilateral Laplace
transform of the concrete modified-theta amplitude. -/
theorem completedRiemannZeta₀_centered_eq_bilateralLaplace (w : ℂ) :
    completedRiemannZeta₀ (1 / 2 + w) =
      ∫ u : ℝ, Complex.exp (w * u) * centeredModifiedThetaAmplitude u := by
  rw [completedRiemannZeta₀_eq_logIntegral]
  apply integral_congr_ae
  filter_upwards [] with u
  unfold centeredModifiedThetaAmplitude
  rw [Complex.ofReal_exp]
  rw [show (1 / 2 + w) * (u : ℂ) =
      w * (u : ℂ) + ((u / 2 : ℝ) : ℂ) by
    push_cast
    ring]
  rw [Complex.exp_add]
  ring

/-- The centered modified-theta amplitude is even, by the exact modular
symmetry of the modified Riemann kernel. -/
theorem centeredModifiedThetaAmplitude_even (u : ℝ) :
    centeredModifiedThetaAmplitude (-u) = centeredModifiedThetaAmplitude u := by
  unfold centeredModifiedThetaAmplitude
  have hmod := riemannThetaModifiedKernel_one_div (Real.exp_pos (2 * u))
  have hinv : 1 / Real.exp (2 * u) = Real.exp (2 * (-u)) := by
    rw [one_div, ← Real.exp_neg]
    congr 1
    ring
  rw [hinv] at hmod
  have hpow : Real.exp (2 * u) ^ (1 / 2 : ℝ) = Real.exp u := by
    rw [Real.rpow_def_of_pos (Real.exp_pos _), Real.log_exp]
    congr 1
    ring
  rw [hmod]
  rw [hpow]
  push_cast
  rw [← mul_assoc]
  rw [← Complex.exp_add]
  rw [show -(u : ℂ) / 2 + (u : ℂ) = (u : ℂ) / 2 by ring]

/-- On the positive half-line the modified amplitude is exactly twice the
paper's theta amplitude. -/
theorem centeredModifiedThetaAmplitude_eq_two_mul_thetaLogAmplitude
    {u : ℝ} (hu : 0 < u) :
    centeredModifiedThetaAmplitude u = 2 * (thetaLogAmplitude u : ℂ) := by
  unfold centeredModifiedThetaAmplitude thetaLogAmplitude
  rw [riemannThetaModifiedKernel_eq_two_mul_thetaTail]
  · push_cast
    ring
  · exact Real.one_lt_exp_iff.mpr (by linarith)

end

end Zeta23.Research.JensenWedge
