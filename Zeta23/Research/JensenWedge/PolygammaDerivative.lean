import Zeta23.Research.JensenWedge.PolygammaPairing
import Zeta23.Analytic.Stirling
import Mathlib.Analysis.Calculus.SmoothSeries

/-!
# Identifying the fifth-polygamma series

`PolygammaPairing` proves the quantitative estimate for the standard series
`120 * sum (z+k)^(-6)`.  This file closes the derivative-identification seam:
on `Re z > 1`, that series is exactly `iteratedDeriv 5 Complex.digamma z`.

There are two points requiring care.  First, differentiation of an infinite
series is justified locally uniformly on a right-half-plane ball.  Second,
the existing trigamma producer in `Zeta23.Analytic.Stirling` is stated only
off the integers.  We remove that artificial exclusion by approaching a
positive integer through noninteger right-half-plane points and using
holomorphic continuity on both sides.
-/

noncomputable section

namespace Zeta23.Research.JensenWedge

open Set Filter Topology

/-- One term of the inverse-power series. -/
def inversePowerTerm (p k : ℕ) (z : ℂ) : ℂ :=
  (z + (k : ℂ))⁻¹ ^ p

/-- The derivative expression produced directly by the power and inverse
rules, before normalizing the exponent. -/
def inversePowerTermDerivative (p k : ℕ) (z : ℂ) : ℂ :=
  (p : ℂ) * (z + (k : ℂ))⁻¹ ^ (p - 1) *
    (-1 / (z + (k : ℂ)) ^ 2)

/-- The inverse-power series. -/
def inversePowerSeries (p : ℕ) (z : ℂ) : ℂ :=
  ∑' k : ℕ, inversePowerTerm p k z

/-- Termwise complex derivative on the open right half-plane. -/
theorem hasDerivAt_inversePowerTerm (p k : ℕ) {z : ℂ} (hz : 0 < z.re) :
    HasDerivAt (inversePowerTerm p k) (inversePowerTermDerivative p k z) z := by
  have hne : z + (k : ℂ) ≠ 0 := by
    intro h
    have hre := congrArg Complex.re h
    simp at hre
    linarith
  have hbase : HasDerivAt (fun q : ℂ => q + (k : ℂ)) 1 z :=
    (hasDerivAt_id z).add_const (k : ℂ)
  exact (hbase.inv hne).pow p

/-- Algebraic normalization of the termwise derivative. -/
theorem inversePowerTermDerivative_eq (p k : ℕ) (hp : 1 ≤ p) {z : ℂ} :
    inversePowerTermDerivative p k z =
      -(p : ℂ) * inversePowerTerm (p + 1) k z := by
  unfold inversePowerTermDerivative inversePowerTerm
  rw [neg_div, one_div, ← inv_pow]
  calc
    (p : ℂ) * (z + (k : ℂ))⁻¹ ^ (p - 1) *
        -(z + (k : ℂ))⁻¹ ^ 2 =
      -(p : ℂ) * ((z + (k : ℂ))⁻¹ ^ (p - 1) *
        (z + (k : ℂ))⁻¹ ^ 2) := by ring
    _ = -(p : ℂ) * (z + (k : ℂ))⁻¹ ^ (p + 1) := by
      rw [← pow_add, show p - 1 + 2 = p + 1 by omega]

/-- Absolute convergence of the generic inverse-power series for exponent
strictly larger than one. -/
theorem summable_inversePowerSeries {z : ℂ} {p : ℕ} (hp : 1 < p)
    (hz : 1 ≤ z.re) :
    Summable (fun k : ℕ => inversePowerTerm p k z) := by
  have hmajor0 := summable_pow_div_add (1 : ℂ) p 1 hp
  have hmajor : Summable
      (fun k : ℕ => ‖(1 : ℂ) / ((k : ℂ) + (1 : ℂ)) ^ p‖) := by
    simpa only [Nat.cast_one] using hmajor0
  have hnorm : Summable (fun k : ℕ => ‖inversePowerTerm p k z‖) := by
    apply Summable.of_nonneg_of_le (fun _ => norm_nonneg _) _ hmajor
    intro k
    have hapos : 0 < ((1 + k : ℕ) : ℝ) := by positivity
    have hlower : ((1 + k : ℕ) : ℝ) ≤ ‖z + (k : ℂ)‖ := by
      calc
        ((1 + k : ℕ) : ℝ) ≤ z.re + k := by
          simpa [Nat.cast_add, add_comm] using add_le_add_right hz (k : ℝ)
        _ = (z + (k : ℂ)).re := by simp
        _ ≤ ‖z + (k : ℂ)‖ := Complex.re_le_norm _
    unfold inversePowerTerm
    rw [norm_pow, norm_inv, norm_div, norm_one, one_div]
    simp only [norm_pow]
    rw [inv_pow]
    have hinv := (inv_le_inv₀ (pow_pos (hapos.trans_le hlower) p)
      (pow_pos hapos p)).mpr (pow_le_pow_left₀ hapos.le hlower p)
    calc
      (‖z + (k : ℂ)‖ ^ p)⁻¹ ≤ (((1 + k : ℕ) : ℝ) ^ p)⁻¹ := hinv
      _ = (‖(k : ℂ) + (1 : ℂ)‖ ^ p)⁻¹ := by
        rw [show (k : ℂ) + (1 : ℂ) = ((k + 1 : ℕ) : ℂ) by norm_num,
          Complex.norm_natCast]
        norm_num [Nat.cast_add, add_comm]
  exact hnorm.of_norm

/-- Local uniform differentiation of the inverse-power series on
`Re z > 1`. -/
theorem hasDerivAt_inversePowerSeries {z : ℂ} {p : ℕ} (hp : 1 < p)
    (hz : 1 < z.re) :
    HasDerivAt (inversePowerSeries p)
      (-(p : ℂ) * inversePowerSeries (p + 1) z) z := by
  let radius : ℝ := z.re - 1
  let U : Set ℂ := Metric.ball z radius
  let u : ℕ → ℝ := fun k => p / (((k : ℝ) + 1) ^ (p + 1))
  have hr : 0 < radius := by dsimp [radius]; linarith
  have hzU : z ∈ U := Metric.mem_ball_self hr
  have hUopen : IsOpen U := Metric.isOpen_ball
  have hUpre : IsPreconnected U := (convex_ball z radius).isPreconnected
  have hUre {w : ℂ} (hw : w ∈ U) : 1 < w.re := by
    have hdist : ‖w - z‖ < radius := by
      simpa [U, dist_eq_norm] using hw
    have hre : |w.re - z.re| ≤ ‖w - z‖ := by
      simpa [Complex.sub_re] using Complex.abs_re_le_norm (w - z)
    dsimp [radius] at hdist
    have hlt := lt_of_le_of_lt hre hdist
    rw [abs_lt] at hlt
    linarith
  have hu : Summable u := by
    have h0 := summable_pow_div_add (1 : ℝ) (p + 1) 1 (by omega)
    have h1 : Summable
        (fun k : ℕ => ‖(1 : ℝ) / ((k : ℝ) + (1 : ℝ)) ^ (p + 1)‖) := by
      simpa only [Nat.cast_one] using h0
    have hbase : Summable
        (fun k : ℕ => 1 / (((k : ℝ) + 1) ^ (p + 1))) := by
      exact h1.congr (fun k => by
        rw [norm_div, norm_one, norm_pow, Real.norm_eq_abs,
          abs_of_nonneg (by positivity)])
    exact (hbase.mul_left (p : ℝ)).congr (fun k => by
      dsimp [u]
      ring)
  have hg : ∀ (k : ℕ) (w : ℂ), w ∈ U →
      HasDerivAt (inversePowerTerm p k) (inversePowerTermDerivative p k w) w := by
    intro k w hw
    exact hasDerivAt_inversePowerTerm p k (lt_trans zero_lt_one (hUre hw))
  have hbound : ∀ (k : ℕ) (w : ℂ), w ∈ U →
      ‖inversePowerTermDerivative p k w‖ ≤ u k := by
    intro k w hw
    have hwre := hUre hw
    have hlower : (1 + k : ℝ) ≤ ‖w + (k : ℂ)‖ := by
      calc
        (1 + k : ℝ) ≤ w.re + k := by linarith
        _ = (w + (k : ℂ)).re := by simp
        _ ≤ ‖w + (k : ℂ)‖ := Complex.re_le_norm _
    have hapos : 0 < (1 + k : ℝ) := by positivity
    rw [inversePowerTermDerivative_eq p k hp.le]
    dsimp [u, inversePowerTerm]
    rw [norm_mul, norm_neg, Complex.norm_natCast, norm_pow, norm_inv]
    have hinv : ‖w + (k : ℂ)‖⁻¹ ≤ (1 + k : ℝ)⁻¹ :=
      (inv_le_inv₀ (lt_of_lt_of_le hapos hlower) hapos).mpr hlower
    have hpow := pow_le_pow_left₀ (by positivity : 0 ≤ ‖w + (k : ℂ)‖⁻¹)
      hinv (p + 1)
    calc
      (p : ℝ) * ‖w + (k : ℂ)‖⁻¹ ^ (p + 1) ≤
          p * (1 + k : ℝ)⁻¹ ^ (p + 1) := by gcongr
      _ = p / (k + 1) ^ (p + 1) := by rw [inv_pow]; ring
  have hsumz := summable_inversePowerSeries hp hz.le
  have hraw := hasDerivAt_tsum_of_isPreconnected
    (g := fun k => inversePowerTerm p k)
    (g' := fun k w => inversePowerTermDerivative p k w)
    hu hUopen hUpre hg hbound hzU hsumz hzU
  have hcoeff : (∑' k : ℕ, inversePowerTermDerivative p k z) =
      -(p : ℂ) * inversePowerSeries (p + 1) z := by
    calc
      (∑' k : ℕ, inversePowerTermDerivative p k z) =
          ∑' k : ℕ, (-(p : ℂ) * inversePowerTerm (p + 1) k z) := by
            apply tsum_congr
            intro k
            exact inversePowerTermDerivative_eq p k hp.le
      _ = -(p : ℂ) * inversePowerSeries (p + 1) z := by
        unfold inversePowerSeries
        rw [tsum_mul_left]
  exact hraw.congr_deriv hcoeff

private theorem gamma_ne_neg_nat {z : ℂ} (hz : 0 < z.re) :
    ∀ m : ℕ, z ≠ -(m : ℂ) := by
  intro m h
  rw [h] at hz
  simp only [Complex.neg_re, Complex.natCast_re] at hz
  nlinarith [Nat.cast_nonneg (α := ℝ) m]

/-- The digamma function is analytic on the open right half-plane, including
positive integers. -/
theorem analyticAt_digamma_rightHalfPlane {z : ℂ} (hz : 0 < z.re) :
    AnalyticAt ℂ Complex.digamma z := by
  have hopen : IsOpen {w : ℂ | 0 < w.re} :=
    isOpen_lt continuous_const Complex.continuous_re
  have hGamma : AnalyticAt ℂ Complex.Gamma z := by
    rw [Complex.analyticAt_iff_eventually_differentiableAt]
    filter_upwards [hopen.mem_nhds hz] with w hw
    exact Complex.differentiableAt_Gamma w (gamma_ne_neg_nat hw)
  have hGamma_ne : Complex.Gamma z ≠ 0 :=
    Complex.Gamma_ne_zero (gamma_ne_neg_nat hz)
  have hderiv : AnalyticAt ℂ (deriv Complex.Gamma) z := hGamma.deriv
  exact (hderiv.div hGamma hGamma_ne).congr (by
    filter_upwards with w
    rw [Complex.digamma_def, logDeriv_apply]
    rfl)

/-- The trigamma series identity on the full right half-plane `Re z > 1`.
At a positive integer it follows by a noninteger approximation and
holomorphic continuity. -/
theorem deriv_digamma_eq_inversePowerSeries_two {z : ℂ} (hz : 1 < z.re) :
    deriv Complex.digamma z = inversePowerSeries 2 z := by
  by_cases hmem : z ∈ Complex.integerComplement
  · unfold inversePowerSeries inversePowerTerm
    simpa [one_div, inv_pow] using
      (Zeta23.Stirling.hasSum_trigamma hmem).tsum_eq.symm
  · have hz0 : 0 < z.re := lt_trans zero_lt_one hz
    have hzim : z.im = 0 := by
      have hrange : ∃ j : ℤ, (j : ℂ) = z := by
        simpa only [Complex.mem_integerComplement_iff, not_not] using hmem
      obtain ⟨j, hj⟩ := hrange
      simpa using (congrArg Complex.im hj).symm
    let u : ℕ → ℂ := fun n =>
      z + (((((n : ℝ) + 1)⁻¹ : ℝ) : ℂ) * (1 + Complex.I))
    have hu : Tendsto u atTop (𝓝 z) := by
      have hinv : Tendsto (fun n : ℕ => ((n : ℝ) + 1)⁻¹) atTop (𝓝 0) :=
        tendsto_inv_atTop_zero.comp
          (tendsto_atTop_add_const_right atTop (1 : ℝ) tendsto_natCast_atTop_atTop)
      have hcast : Tendsto
          (fun n : ℕ => ((((n : ℝ) + 1)⁻¹ : ℝ) : ℂ)) atTop (𝓝 0) := by
        simpa only [Complex.ofReal_zero] using hinv.ofReal
      simpa [u] using tendsto_const_nhds.add (hcast.mul_const (1 + Complex.I))
    have hure (n : ℕ) : 1 < (u n).re := by
      simp only [u, Complex.add_re, Complex.mul_re, Complex.ofReal_re,
        Complex.ofReal_im, Complex.one_re, Complex.I_re, zero_mul, add_zero, mul_one]
      have hinv : 0 ≤ ((n : ℝ) + 1)⁻¹ := inv_nonneg.mpr (by positivity)
      linarith
    have humem (n : ℕ) : u n ∈ Complex.integerComplement := by
      rw [Complex.mem_integerComplement_iff]
      rintro ⟨j, hj⟩
      have him := congrArg Complex.im hj
      have hpos : 0 < ((n : ℝ) + 1)⁻¹ := by positivity
      simp only [u, Complex.add_im, Complex.mul_im, Complex.ofReal_re,
        Complex.ofReal_im, Complex.I_im, Complex.one_im, zero_mul, mul_one,
        add_zero, hzim, zero_add, Complex.intCast_im] at him
      linarith
    have heq (n : ℕ) :
        deriv Complex.digamma (u n) = inversePowerSeries 2 (u n) := by
      unfold inversePowerSeries inversePowerTerm
      simpa [one_div, inv_pow] using
        (Zeta23.Stirling.hasSum_trigamma (humem n)).tsum_eq.symm
    have hleft : Tendsto (fun n => deriv Complex.digamma (u n)) atTop
        (𝓝 (deriv Complex.digamma z)) :=
      (analyticAt_digamma_rightHalfPlane hz0).deriv.continuousAt.tendsto.comp hu
    have hright : Tendsto (fun n => inversePowerSeries 2 (u n)) atTop
        (𝓝 (inversePowerSeries 2 z)) :=
      (hasDerivAt_inversePowerSeries (p := 2) (by norm_num) hz).continuousAt.tendsto.comp hu
    exact tendsto_nhds_unique hleft
      (hright.congr' (Filter.Eventually.of_forall fun n => (heq n).symm))

/-- Complete higher-polygamma tower on `Re z > 1`. -/
theorem iteratedDeriv_digamma_eq_inversePowerSeries (m : ℕ) {z : ℂ}
    (hz : 1 < z.re) :
    iteratedDeriv (m + 1) Complex.digamma z =
      ((-1 : ℂ) ^ m * ((m + 1).factorial : ℂ)) *
        inversePowerSeries (m + 2) z := by
  induction m generalizing z with
  | zero =>
      rw [zero_add, iteratedDeriv_succ, iteratedDeriv_zero]
      simpa using deriv_digamma_eq_inversePowerSeries_two hz
  | succ m ih =>
      let c : ℂ := (-1 : ℂ) ^ m * ((m + 1).factorial : ℂ)
      have hopen : IsOpen {w : ℂ | 1 < w.re} :=
        isOpen_lt continuous_const Complex.continuous_re
      have hevent :
          (fun w : ℂ => iteratedDeriv (m + 1) Complex.digamma w) =ᶠ[𝓝 z]
            (fun w : ℂ => c * inversePowerSeries (m + 2) w) := by
        filter_upwards [hopen.mem_nhds hz] with w hw
        exact ih hw
      have hs := hasDerivAt_inversePowerSeries (p := m + 2) (by omega) hz
      have hscaled := hs.const_mul c
      have hcoeff :
          c * (-((m + 2 : ℕ) : ℂ) * inversePowerSeries (m + 2 + 1) z) =
            ((-1 : ℂ) ^ (m + 1) * ((m + 2).factorial : ℂ)) *
              inversePowerSeries (m + 3) z := by
        have hfac : (((m + 2).factorial : ℕ) : ℂ) =
            ((m + 2 : ℕ) : ℂ) * (((m + 1).factorial : ℕ) : ℂ) := by
          rw [show m + 2 = (m + 1) + 1 by omega, Nat.factorial_succ]
          push_cast
          ring
        dsimp [c]
        rw [hfac, pow_succ]
        ring
      have hscaled' :
          HasDerivAt (fun w : ℂ => c * inversePowerSeries (m + 2) w)
            (((-1 : ℂ) ^ (m + 1) * ((m + 2).factorial : ℂ)) *
              inversePowerSeries (m + 3) z) z := by
        exact hscaled.congr_deriv hcoeff
      have hiter := hscaled'.congr_of_eventuallyEq hevent
      rw [show m + 1 + 1 = (m + 1) + 1 by omega, iteratedDeriv_succ]
      simpa [Nat.succ_eq_add_one] using hiter.deriv

/-- The standard fifth-polygamma series is exactly the fifth derivative of
digamma on the right half-plane used by the manuscript. -/
theorem iteratedDeriv_five_digamma_eq_polygammaFiveSeries {z : ℂ}
    (hz : 1 < z.re) :
    iteratedDeriv 5 Complex.digamma z = polygammaFiveSeries z := by
  have h := iteratedDeriv_digamma_eq_inversePowerSeries 4 hz
  unfold inversePowerSeries inversePowerTerm at h
  unfold polygammaFiveSeries
  norm_num at h ⊢
  exact h

/-- Direct paired fifth-polygamma estimate in the manuscript's derivative
notation. -/
theorem iteratedDeriv_five_digamma_pair_norm_le {z w : ℂ} {n : ℕ}
    (hn : 2 ≤ n) (hz : (n : ℝ) ≤ z.re) (hw : (n : ℝ) ≤ w.re) :
    ‖iteratedDeriv 5 Complex.digamma z - iteratedDeriv 5 Complex.digamma w‖ ≤
      120 * ‖z - w‖ / (((n - 1 : ℕ) : ℝ) ^ 6) := by
  have hz1 : 1 < z.re := lt_of_lt_of_le (by exact_mod_cast hn) hz
  have hw1 : 1 < w.re := lt_of_lt_of_le (by exact_mod_cast hn) hw
  rw [iteratedDeriv_five_digamma_eq_polygammaFiveSeries hz1,
    iteratedDeriv_five_digamma_eq_polygammaFiveSeries hw1]
  exact polygammaFiveSeries_pair_norm_le hn hz hw

end Zeta23.Research.JensenWedge
