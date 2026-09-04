import Zeta23.Research.JensenWedge.FullThetaMoment
import Zeta23.Research.JensenWedge.XiOmegaCoefficients

/-!
# Exact theta-moment coefficient assembly

This file closes the exact normalization seam between the complex theta
moment localized in T3--T5 and the concrete centered-xi coefficients proved
in T1.  In particular, the change of variables `u = 2v`, the factor
`2^(2n+1)`, and the manuscript combination
`32 * choose (2m) 2 * F (2m-2) - F (2m)` are all checked in the kernel.
-/

namespace Zeta23.Research.JensenWedge

open Complex Filter Function MeasureTheory Set Topology

noncomputable section

/-- The all-mode contour integrand is the theta tail times its Mellin phase
on the positive real ray. -/
theorem fullThetaContourIntegrand_eq_thetaTail
    (s : ℂ) (u : ℝ) :
    fullThetaContourIntegrand s u =
      exp (s * log (u : ℂ) + (u : ℂ) / 4) *
        (riemannThetaTail (Real.exp u) : ℂ) := by
  let a : ℕ → ℂ := fun n =>
    exp (-((Real.pi : ℂ) * (((n + 1 : ℕ) : ℂ) ^ 2) * exp (u : ℂ)))
  have ht : 0 < Real.exp u := Real.exp_pos u
  have hsumR := hasSum_nat_riemannThetaTail ht
  have hsumC : HasSum (fun n : ℕ =>
      ((Real.exp (-Real.pi * (n + 1) ^ 2 * Real.exp u) : ℝ) : ℂ))
      (riemannThetaTail (Real.exp u) : ℂ) :=
    Complex.hasSum_ofReal.mpr hsumR
  have haEq (n : ℕ) : a n =
      ((Real.exp (-Real.pi * (n + 1) ^ 2 * Real.exp u) : ℝ) : ℂ) := by
    simp only [a, ofReal_exp, ofReal_neg, ofReal_mul, Complex.ofReal_pow]
    congr 1
    push_cast
    ring
  have hsumA : HasSum a (riemannThetaTail (Real.exp u) : ℂ) := by
    convert hsumC using 1
    funext n
    exact haEq n
  have hhead : a 0 + ∑' n : ℕ, a (n + 1) =
      (riemannThetaTail (Real.exp u) : ℂ) := by
    have hdecomp := hsumA.summable.sum_add_tsum_nat_add 1
    rw [Finset.sum_range_one, hsumA.tsum_eq] at hdecomp
    exact hdecomp
  have hlead : leadingIntegrand s (u : ℂ) =
      exp (s * log (u : ℂ) + (u : ℂ) / 4) * a 0 := by
    rw [leadingIntegrand_eq_exp_logIntegrand]
    unfold leadingLogIntegrand a
    rw [← exp_add]
    congr 1
    norm_num
    ring
  have hhigh (n : ℕ) : higherThetaMode n s (u : ℂ) =
      exp (s * log (u : ℂ) + (u : ℂ) / 4) * a (n + 1) := by
    rw [higherThetaMode_eq_fullMode, ← exp_add]
    congr 1
  unfold fullThetaContourIntegrand
  rw [hlead]
  simp_rw [hhigh]
  rw [tsum_mul_left, ← mul_add, hhead]

/-- At an even natural Mellin parameter, the substitution `u = 2v`
recovers the real theta logarithmic amplitude pointwise. -/
theorem fullThetaContourIntegrand_evenNat_two_mul
    (n : ℕ) {v : ℝ} (hv : 0 < v) :
    fullThetaContourIntegrand ((2 * n : ℕ) : ℂ) ((2 * v : ℝ) : ℂ) =
      (((2 * v) ^ (2 * n) * thetaLogAmplitude v : ℝ) : ℂ) := by
  rw [fullThetaContourIntegrand_eq_thetaTail]
  unfold thetaLogAmplitude
  have htwovne : ((2 * v : ℝ) : ℂ) ≠ 0 := by
    exact ofReal_ne_zero.mpr (mul_ne_zero (by norm_num) hv.ne')
  have hexplog : exp (((2 * n : ℕ) : ℂ) * log ((2 * v : ℝ) : ℂ)) =
      ((2 * v : ℝ) : ℂ) ^ (2 * n) := by
    rw [Complex.exp_nat_mul, Complex.exp_log htwovne]
  rw [Complex.exp_add, hexplog]
  push_cast
  rw [show (2 : ℂ) * (v : ℂ) / 4 = (v : ℂ) / 2 by ring]
  ring

/-- The exact `u = 2v` moment relation, including its Jacobian. -/
theorem fullThetaMoment_evenNat_eq_thetaMoment (n : ℕ) :
    fullThetaMoment ((2 * n : ℕ) : ℂ) =
      (2 : ℂ) ^ (2 * n + 1) *
        ((∫ v in Ioi (0 : ℝ),
          v ^ (2 * n) * thetaLogAmplitude v : ℝ) : ℂ) := by
  let g : ℝ → ℂ := fun u =>
    fullThetaContourIntegrand ((2 * n : ℕ) : ℂ) (u : ℂ)
  have hchange := integral_comp_mul_left_Ioi' g 0 (b := 2) (by norm_num)
  have hpoint : ∀ᵐ v ∂volume.restrict (Ioi (0 : ℝ)),
      g (2 * v) =
        (((2 * v) ^ (2 * n) * thetaLogAmplitude v : ℝ) : ℂ) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with v hv
    exact fullThetaContourIntegrand_evenNat_two_mul n hv
  have hintegral :
      (∫ v in Ioi (0 : ℝ), g (2 * v)) =
        ∫ v in Ioi (0 : ℝ),
          (((2 * v) ^ (2 * n) * thetaLogAmplitude v : ℝ) : ℂ) :=
    integral_congr_ae hpoint
  have hfactor : (fun v : ℝ =>
      (2 * v) ^ (2 * n) * thetaLogAmplitude v) =
      fun v : ℝ => 2 ^ (2 * n) *
        (v ^ (2 * n) * thetaLogAmplitude v) := by
    funext v
    rw [mul_pow]
    ring
  unfold fullThetaMoment
  change (2 : ℝ) • (∫ v in Ioi (0 : ℝ), g (2 * v)) = _ at hchange
  rw [mul_zero] at hchange
  rw [← hchange, hintegral, integral_complex_ofReal, hfactor,
    integral_const_mul]
  push_cast
  rw [Complex.real_smul]
  norm_num
  ring

/-- Denominator-free exact form of the manuscript's two-shift theta-moment
assembly for every positive centered-xi coefficient. -/
theorem centeredXiCoefficient_succ_thetaMomentAssembly (n : ℕ) :
    (2 : ℂ) ^ (2 * (n + 1) + 2) * centeredXiCoefficient (n + 1) =
      ((n + 1).factorial : ℂ) / ((2 * (n + 1)).factorial : ℂ) *
        (32 * (((2 * (n + 1)).choose 2 : ℕ) : ℂ) *
            fullThetaMoment ((2 * n : ℕ) : ℂ) -
          fullThetaMoment ((2 * (n + 1) : ℕ) : ℂ)) := by
  have hprevious := fullThetaMoment_evenNat_eq_thetaMoment n
  have hcurrent := fullThetaMoment_evenNat_eq_thetaMoment (n + 1)
  have hrecReal := eight_mul_integral_pow_omegaLogAmplitude_succ n
  have hrec := congrArg (fun x : ℝ => (x : ℂ)) hrecReal
  push_cast at hrec
  rw [centeredXiCoefficient_eq_omegaMoment,
    halfLineMoment_omegaLogAmplitude_eq_ofReal, hprevious, hcurrent,
    Nat.cast_choose_two]
  push_cast
  calc
    _ = (2 : ℂ) ^ (2 * (n + 1) + 2) *
        (((n + 1).factorial : ℂ) / ((2 * (n + 1)).factorial : ℂ) *
          (8 * ((∫ u in Ioi (0 : ℝ),
            u ^ (2 * (n + 1)) * omegaLogAmplitude u : ℝ) : ℂ))) := by
          ring
    _ = _ := by
      rw [hrec]
      norm_num
      ring

/-- Divided form of the exact manuscript assembly. -/
theorem centeredXiCoefficient_succ_eq_thetaMomentAssembly (n : ℕ) :
    centeredXiCoefficient (n + 1) =
      (((n + 1).factorial : ℂ) / ((2 * (n + 1)).factorial : ℂ) *
        (32 * (((2 * (n + 1)).choose 2 : ℕ) : ℂ) *
            fullThetaMoment ((2 * n : ℕ) : ℂ) -
          fullThetaMoment ((2 * (n + 1) : ℕ) : ℂ))) /
        (2 : ℂ) ^ (2 * (n + 1) + 2) := by
  apply (eq_div_iff (pow_ne_zero _ (by norm_num : (2 : ℂ) ≠ 0))).2
  simpa [mul_comm] using
    centeredXiCoefficient_succ_thetaMomentAssembly n

end

end Zeta23.Research.JensenWedge
