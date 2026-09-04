import Zeta23.Research.JensenWedge.ExactXiBranch

/-!
# Positivity of the Riemann-xi Jensen coefficients

The real logarithms in the exact parameter map require positivity, not just
nonvanishing of a complex continuation.  Here positivity is proved directly
from the theta-mode series on the manuscript half-line.
-/

namespace Zeta23.Research.JensenWedge

open Filter MeasureTheory Set

noncomputable section

/-- Every differentiated theta mode contributing to omega is positive once
`t ≥ 1`. -/
theorem riemannOmegaMode_pos_of_one_le
    (n : ℕ) {t : ℝ} (ht : 1 ≤ t) :
    0 < riemannOmegaMode n t := by
  have hn1 : (1 : ℝ) ≤ ((n + 1 : ℕ) : ℝ) := by
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Nat.succ_ne_zero n)
  have hn : (1 : ℝ) ≤ ((n + 1 : ℕ) : ℝ) ^ 2 := by
    nlinarith [sq_nonneg (((n + 1 : ℕ) : ℝ) - 1)]
  have hc : thetaTailCoeff n < -3 := by
    have hprod : 3 < Real.pi * ((n + 1 : ℕ) : ℝ) ^ 2 := by
      calc
        3 = 3 * 1 := by ring
        _ < Real.pi * 1 := mul_lt_mul_of_pos_right Real.pi_gt_three zero_lt_one
        _ ≤ Real.pi * ((n + 1 : ℕ) : ℝ) ^ 2 :=
          mul_le_mul_of_nonneg_left hn Real.pi_pos.le
    unfold thetaTailCoeff
    have hprod' : 3 < Real.pi * ((n : ℝ) + 1) ^ 2 := by
      simpa only [Nat.cast_add, Nat.cast_one] using hprod
    nlinarith
  have htpos : 0 < t := zero_lt_one.trans_le ht
  have hbracket :
      0 < 2 * t ^ 2 * thetaTailCoeff n ^ 2 +
        3 * t * thetaTailCoeff n := by
    rw [show 2 * t ^ 2 * thetaTailCoeff n ^ 2 +
        3 * t * thetaTailCoeff n =
      t * (-thetaTailCoeff n) * (2 * t * (-thetaTailCoeff n) - 3) by ring]
    have hcneg : 0 < -thetaTailCoeff n := by nlinarith
    have hlast : 0 < 2 * t * (-thetaTailCoeff n) - 3 := by nlinarith
    exact mul_pos (mul_pos htpos hcneg) hlast
  unfold riemannOmegaMode thetaTailTerm
  exact mul_pos (mul_pos (by norm_num) hbracket) (Real.exp_pos _)

/-- The omega-mode series is summable at every positive argument. -/
theorem summable_riemannOmegaMode {t : ℝ} (ht : 0 < t) :
    Summable (fun n : ℕ => riemannOmegaMode n t) := by
  have h2 := (summable_thetaTailD2_terms ht).mul_left (2 * t ^ 2)
  have h1 := (summable_thetaTailD1_terms ht).mul_left (3 * t)
  have hsum := (h2.add h1).mul_left (1 / 2 : ℝ)
  apply hsum.congr
  intro n
  unfold riemannOmegaMode
  ring

/-- The paper's omega kernel is strictly positive on `[1,∞)`. -/
theorem riemannOmega_pos_of_one_le {t : ℝ} (ht : 1 ≤ t) :
    0 < riemannOmega t := by
  have htpos : 0 < t := zero_lt_one.trans_le ht
  rw [riemannOmega_eq_tsum htpos]
  exact (summable_riemannOmegaMode htpos).tsum_pos
    (fun n => (riemannOmegaMode_pos_of_one_le n ht).le)
    0 (riemannOmegaMode_pos_of_one_le 0 ht)

/-- The logarithmic omega amplitude is positive on the full integration
half-line. -/
theorem omegaLogAmplitude_pos {u : ℝ} (hu : 0 ≤ u) :
    0 < omegaLogAmplitude u := by
  have ht : 1 ≤ Real.exp (2 * u) := Real.one_le_exp (by linarith)
  unfold omegaLogAmplitude
  exact mul_pos (Real.exp_pos _) (riemannOmega_pos_of_one_le ht)

/-- Every coefficient used by the exact xi logarithm is strictly positive.
This discharges the real-log branch condition directly from the defining
integral. -/
theorem riemannXiCoefficientReal_pos (n : ℕ) :
    0 < riemannXiCoefficientReal n := by
  let f : ℝ → ℝ := fun u => u ^ (2 * n) * omegaLogAmplitude u
  have hfint : IntegrableOn f (Ioi 0) := by
    simpa only [f] using integrableOn_pow_mul_omegaLogAmplitude (2 * n)
  have hsupport : Function.support f ∩ Ioi 0 = Ioi 0 := by
    rw [inter_eq_right]
    intro u hu
    exact (mul_pos (pow_pos hu (2 * n)) (omegaLogAmplitude_pos hu.le)).ne'
  have hnonneg : 0 ≤ᵐ[volume.restrict (Ioi 0)] f := by
    refine eventually_of_mem (self_mem_ae_restrict measurableSet_Ioi) ?_
    intro u hu
    exact (mul_pos (pow_pos hu (2 * n)) (omegaLogAmplitude_pos hu.le)).le
  have hintegral : 0 < ∫ u in Ioi (0 : ℝ), f u := by
    rw [setIntegral_pos_iff_support_of_nonneg_ae hnonneg hfint, hsupport]
    exact Measure.measure_Ioi_pos volume 0
  unfold riemannXiCoefficientReal
  have hfactorial : (0 : ℝ) < (n.factorial : ℝ) := by positivity
  have hdouble : (0 : ℝ) < ((2 * n).factorial : ℝ) := by positivity
  have hprefactor : 0 < 8 * (n.factorial : ℝ) / ((2 * n).factorial : ℝ) := by
    positivity
  simpa only [f] using mul_pos hprefactor hintegral

end

end Zeta23.Research.JensenWedge
