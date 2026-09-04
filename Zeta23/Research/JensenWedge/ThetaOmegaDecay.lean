import Zeta23.Research.JensenWedge.ThetaOmega
import Mathlib.Analysis.Calculus.SmoothSeries

/-!
# Termwise theta derivatives and decay preparation

The improper integrations by parts in T1 require decay of the theta
amplitude and its first derivative.  This module first identifies the first
two derivatives of the concrete theta tail with their differentiated series.
Every exchange of derivative and infinite sum is justified by an explicit
summable majorant on a positive neighbourhood of the evaluation point.
-/

namespace Zeta23.Research.JensenWedge

open Complex Filter Function MeasureTheory Set Topology Asymptotics
open HurwitzZeta

noncomputable section

/-- The negative quadratic coefficient in the `n`th theta mode. -/
def thetaTailCoeff (n : ℕ) : ℝ := -Real.pi * (n + 1) ^ 2

/-- The `n`th one-sided theta mode. -/
def thetaTailTerm (n : ℕ) (t : ℝ) : ℝ :=
  Real.exp (thetaTailCoeff n * t)

/-- The first differentiated one-sided theta series. -/
def thetaTailD1 (t : ℝ) : ℝ :=
  ∑' n : ℕ, thetaTailTerm n t * thetaTailCoeff n

/-- The second differentiated one-sided theta series. -/
def thetaTailD2 (t : ℝ) : ℝ :=
  ∑' n : ℕ, thetaTailTerm n t * thetaTailCoeff n ^ 2

/-- The defining theta tail is the zeroth one-sided theta series. -/
theorem riemannThetaTail_eq_tsum {t : ℝ} (ht : 0 < t) :
    riemannThetaTail t =
      ∑' n : ℕ, thetaTailTerm n t := by
  simpa [thetaTailTerm, thetaTailCoeff] using
    (hasSum_nat_riemannThetaTail ht).tsum_eq.symm

/-- Termwise differentiation of the theta tail. -/
theorem hasDerivAt_riemannThetaTail_eq_thetaTailD1
    {t : ℝ} (ht : 0 < t) :
    HasDerivAt riemannThetaTail (thetaTailD1 t) t := by
  let term : ℕ → ℝ → ℝ := thetaTailTerm
  let term' : ℕ → ℝ → ℝ := fun n x =>
    thetaTailTerm n x * thetaTailCoeff n
  let bound : ℕ → ℝ := fun n =>
    Real.pi * HurwitzKernelBounds.f_nat 2 1 (t / 2) n
  have hhalf : 0 < t / 2 := by linarith
  have hbound : Summable bound := by
    exact (HurwitzKernelBounds.summable_f_nat 2 1 hhalf).mul_left Real.pi
  have hderiv : ∀ n x, x ∈ Ioi (t / 2) →
      HasDerivAt (term n) (term' n x) x := by
    intro n x _hx
    dsimp [term, term']
    have hlin : HasDerivAt
        (fun y : ℝ => thetaTailCoeff n * y) (thetaTailCoeff n) x := by
      simpa using (hasDerivAt_id x).const_mul (thetaTailCoeff n)
    change HasDerivAt (fun y : ℝ => Real.exp (thetaTailCoeff n * y))
      (Real.exp (thetaTailCoeff n * x) * thetaTailCoeff n) x
    exact (Real.hasDerivAt_exp (thetaTailCoeff n * x)).comp x hlin
  have hnorm : ∀ n x, x ∈ Ioi (t / 2) → ‖term' n x‖ ≤ bound n := by
    intro n x hx
    dsimp [term', bound, thetaTailTerm, thetaTailCoeff,
      HurwitzKernelBounds.f_nat]
    rw [abs_mul, abs_mul, abs_neg, abs_of_pos Real.pi_pos]
    rw [abs_of_pos (Real.exp_pos _), abs_of_nonneg (sq_nonneg _)]
    have hexp : Real.exp (-Real.pi * (n + 1) ^ 2 * x) ≤
        Real.exp (-Real.pi * (n + 1) ^ 2 * (t / 2)) :=
      Real.exp_monotone (mul_le_mul_of_nonpos_left hx.le
        (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr Real.pi_pos.le) (sq_nonneg _)))
    calc
      Real.exp (-Real.pi * (n + 1) ^ 2 * x) *
          (Real.pi * (n + 1) ^ 2) =
          Real.pi * (n + 1) ^ 2 * Real.exp (-Real.pi * (n + 1) ^ 2 * x) := by ring
      _ ≤
          Real.pi * (n + 1) ^ 2 *
            Real.exp (-Real.pi * (n + 1) ^ 2 * (t / 2)) :=
        mul_le_mul_of_nonneg_left hexp (by positivity)
      _ = Real.pi * ((n + 1) ^ 2 *
            Real.exp (-Real.pi * (n + 1) ^ 2 * (t / 2))) := by ring
  have hbase : Summable (fun n => term n t) := by
    simpa [term, thetaTailTerm, thetaTailCoeff] using
      (hasSum_nat_riemannThetaTail ht).summable
  have htmem : t ∈ Ioi (t / 2) := by
    change t / 2 < t
    exact div_lt_self ht (by norm_num)
  have hsum := hasDerivAt_tsum_of_isPreconnected hbound isOpen_Ioi
    (convex_Ioi (t / 2)).isPreconnected hderiv hnorm htmem hbase htmem
  have hlocal : ∀ᶠ x in 𝓝 t,
      riemannThetaTail x = ∑' n, term n x := by
    filter_upwards [Ioi_mem_nhds ht] with x hx
    exact riemannThetaTail_eq_tsum hx
  have hsum' := hsum.congr_of_eventuallyEq hlocal
  simpa [thetaTailD1, term', term] using hsum'

/-- The ordinary derivative is exactly the first differentiated series. -/
theorem deriv_riemannThetaTail_eq_thetaTailD1 {t : ℝ} (ht : 0 < t) :
    deriv riemannThetaTail t = thetaTailD1 t :=
  (hasDerivAt_riemannThetaTail_eq_thetaTailD1 ht).deriv

/-- Termwise differentiation of the first differentiated theta series. -/
theorem hasDerivAt_thetaTailD1_eq_thetaTailD2
    {t : ℝ} (ht : 0 < t) : HasDerivAt thetaTailD1 (thetaTailD2 t) t := by
  let term : ℕ → ℝ → ℝ := fun n x =>
    thetaTailTerm n x * thetaTailCoeff n
  let term' : ℕ → ℝ → ℝ := fun n x =>
    thetaTailTerm n x * thetaTailCoeff n ^ 2
  let bound : ℕ → ℝ := fun n =>
    Real.pi ^ 2 * HurwitzKernelBounds.f_nat 4 1 (t / 2) n
  have hhalf : 0 < t / 2 := by linarith
  have hbound : Summable bound := by
    exact (HurwitzKernelBounds.summable_f_nat 4 1 hhalf).mul_left (Real.pi ^ 2)
  have hderiv : ∀ n x, x ∈ Ioi (t / 2) →
      HasDerivAt (term n) (term' n x) x := by
    intro n x _hx
    dsimp [term, term']
    have hlin : HasDerivAt
        (fun y : ℝ => thetaTailCoeff n * y) (thetaTailCoeff n) x := by
      simpa using (hasDerivAt_id x).const_mul (thetaTailCoeff n)
    have hexp : HasDerivAt (thetaTailTerm n)
        (thetaTailTerm n x * thetaTailCoeff n) x := by
      change HasDerivAt (fun y : ℝ => Real.exp (thetaTailCoeff n * y))
        (Real.exp (thetaTailCoeff n * x) * thetaTailCoeff n) x
      exact (Real.hasDerivAt_exp (thetaTailCoeff n * x)).comp x hlin
    simpa [pow_two, mul_assoc] using hexp.mul_const (thetaTailCoeff n)
  have hnorm : ∀ n x, x ∈ Ioi (t / 2) → ‖term' n x‖ ≤ bound n := by
    intro n x hx
    dsimp [term', bound, thetaTailTerm, thetaTailCoeff,
      HurwitzKernelBounds.f_nat]
    rw [abs_mul, abs_pow, abs_mul, abs_neg, abs_of_pos Real.pi_pos]
    rw [abs_of_pos (Real.exp_pos _), abs_of_nonneg (sq_nonneg _)]
    have hexp : Real.exp (-Real.pi * (n + 1) ^ 2 * x) ≤
        Real.exp (-Real.pi * (n + 1) ^ 2 * (t / 2)) :=
      Real.exp_monotone (mul_le_mul_of_nonpos_left hx.le
        (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr Real.pi_pos.le) (sq_nonneg _)))
    calc
      Real.exp (-Real.pi * (n + 1) ^ 2 * x) *
          (Real.pi * (n + 1) ^ 2) ^ 2 =
        (Real.pi * (n + 1) ^ 2) ^ 2 *
          Real.exp (-Real.pi * (n + 1) ^ 2 * x) := by ring
      _ ≤
        (Real.pi * (n + 1) ^ 2) ^ 2 *
          Real.exp (-Real.pi * (n + 1) ^ 2 * (t / 2)) :=
        mul_le_mul_of_nonneg_left hexp (sq_nonneg _)
      _ = Real.pi ^ 2 * ((n + 1) ^ 4 *
          Real.exp (-Real.pi * (n + 1) ^ 2 * (t / 2))) := by ring
  have hbase : Summable (fun n => term n t) := by
    dsimp [term, thetaTailTerm, thetaTailCoeff]
    apply ((HurwitzKernelBounds.summable_f_nat 2 1 ht).mul_left (-Real.pi)).congr
    intro n
    simp [HurwitzKernelBounds.f_nat]
    ring
  have htmem : t ∈ Ioi (t / 2) := by
    change t / 2 < t
    exact div_lt_self ht (by norm_num)
  have hsum := hasDerivAt_tsum_of_isPreconnected hbound isOpen_Ioi
    (convex_Ioi (t / 2)).isPreconnected hderiv hnorm htmem hbase htmem
  change HasDerivAt (fun z => ∑' n : ℕ,
      thetaTailTerm n z * thetaTailCoeff n)
    (∑' n : ℕ, thetaTailTerm n t * thetaTailCoeff n ^ 2) t
  exact hsum

/-- The second derivative of the concrete theta tail is exactly the second
differentiated series. -/
theorem iteratedDeriv_two_riemannThetaTail_eq_thetaTailD2
    {t : ℝ} (ht : 0 < t) :
    iteratedDeriv 2 riemannThetaTail t = thetaTailD2 t := by
  rw [show 2 = 1 + 1 by norm_num, iteratedDeriv_succ, iteratedDeriv_one]
  have hfun : ∀ᶠ x in 𝓝 t, deriv riemannThetaTail x = thetaTailD1 x := by
    filter_upwards [Ioi_mem_nhds ht] with x hx
    exact deriv_riemannThetaTail_eq_thetaTailD1 hx
  rw [Filter.EventuallyEq.deriv_eq hfun]
  exact (hasDerivAt_thetaTailD1_eq_thetaTailD2 ht).deriv

/-- The `n`th positive-half-line omega mode. -/
def riemannOmegaMode (n : ℕ) (t : ℝ) : ℝ :=
  1 / 2 * (2 * t ^ 2 * thetaTailCoeff n ^ 2 +
    3 * t * thetaTailCoeff n) * thetaTailTerm n t

/-- Summability of the first differentiated series at every positive
argument. -/
theorem summable_thetaTailD1_terms {t : ℝ} (ht : 0 < t) :
    Summable (fun n : ℕ => thetaTailTerm n t * thetaTailCoeff n) := by
  apply ((HurwitzKernelBounds.summable_f_nat 2 1 ht).mul_left (-Real.pi)).congr
  intro n
  simp [HurwitzKernelBounds.f_nat, thetaTailTerm, thetaTailCoeff]
  ring

/-- Summability of the second differentiated series at every positive
argument. -/
theorem summable_thetaTailD2_terms {t : ℝ} (ht : 0 < t) :
    Summable (fun n : ℕ => thetaTailTerm n t * thetaTailCoeff n ^ 2) := by
  apply ((HurwitzKernelBounds.summable_f_nat 4 1 ht).mul_left
    (Real.pi ^ 2)).congr
  intro n
  simp [HurwitzKernelBounds.f_nat, thetaTailTerm, thetaTailCoeff]
  ring

/-- The omega kernel is the sum of the twice differentiated theta modes.
This identity supplies the exact series needed for tail bounds and Tonelli
arguments later in T1. -/
theorem riemannOmega_eq_tsum {t : ℝ} (ht : 0 < t) :
    riemannOmega t = ∑' n : ℕ, riemannOmegaMode n t := by
  rw [riemannOmega]
  rw [iteratedDeriv_two_riemannThetaTail_eq_thetaTailD2 ht]
  rw [deriv_riemannThetaTail_eq_thetaTailD1 ht]
  unfold thetaTailD1 thetaTailD2
  have h2 := (summable_thetaTailD2_terms ht).mul_left (2 * t ^ 2)
  have h1 := (summable_thetaTailD1_terms ht).mul_left (3 * t)
  rw [← tsum_mul_left]
  rw [← tsum_mul_left]
  rw [← h2.tsum_add h1]
  rw [← tsum_mul_left]
  congr 1
  funext n
  unfold riemannOmegaMode
  ring

/-- Concrete first derivative of the logarithmic theta amplitude in terms
of the differentiated theta series. -/
theorem deriv_thetaLogAmplitude_eq_thetaTailD1 (u : ℝ) :
    deriv thetaLogAmplitude u =
      Real.exp (u / 2) *
        (1 / 2 * riemannThetaTail (Real.exp (2 * u)) +
          2 * Real.exp (2 * u) * thetaTailD1 (Real.exp (2 * u))) := by
  have h := hasDerivAt_thetaLogAmplitude (u := u)
    (hasDerivAt_riemannThetaTail_eq_thetaTailD1 (Real.exp_pos _))
  exact h.deriv

/-! ## Uniform exponential bounds for differentiated mode sums -/

/-- A summable, `t`-independent majorant for the order-`k` mode sum. -/
def thetaModeMajorant (k : ℕ) (n : ℕ) : ℝ :=
  (n + 1) ^ k * Real.exp (-(Real.pi / 2 * (n + 1)))

theorem summable_thetaModeMajorant (k : ℕ) :
    Summable (thetaModeMajorant k) := by
  have h := Real.summable_pow_mul_exp_neg_nat_mul k (by positivity : 0 < Real.pi / 2)
  have hshift := (summable_nat_add_iff 1).mpr h
  change Summable (fun n : ℕ =>
    (n + 1 : ℝ) ^ k * Real.exp (-(Real.pi / 2 * (n + 1))))
  simpa only [Nat.cast_add, Nat.cast_one, neg_mul] using hshift

/-- Every polynomially weighted positive theta-mode sum decays at least as
`exp(-pi t/2)`.  This single bound covers the zeroth, first, and second
theta derivatives by taking `k=0,2,4`. -/
theorem hurwitzFNat_one_isBigO_exp (k : ℕ) :
    (fun t => HurwitzKernelBounds.F_nat k 1 t) =O[atTop]
      (fun t => Real.exp (-(Real.pi / 2) * t)) := by
  let B : ℝ := ∑' n : ℕ, thetaModeMajorant k n
  have hBnonneg : 0 ≤ B := by
    apply tsum_nonneg
    intro n
    unfold thetaModeMajorant
    positivity
  have htoB : (fun t => HurwitzKernelBounds.F_nat k 1 t) =O[atTop]
      (fun t => B * Real.exp (-(Real.pi / 2) * t)) := by
    apply Eventually.isBigO
    filter_upwards [eventually_ge_atTop (1 : ℝ)] with t ht
    have htpos : 0 < t := zero_lt_one.trans_le ht
    have hmode : ∀ n : ℕ,
        ‖HurwitzKernelBounds.f_nat k 1 t n‖ ≤
          thetaModeMajorant k n * Real.exp (-(Real.pi / 2) * t) := by
      intro n
      have hm : (1 : ℝ) ≤ n + 1 := by
        exact_mod_cast Nat.succ_le_succ (Nat.zero_le n)
      have hquad : ((n + 1 : ℝ) ^ 2) * t ≥ ((n + 1 : ℝ) + t) / 2 := by
        have hprod : 0 ≤ ((n + 1 : ℝ) - 1) * (t - 1) :=
          mul_nonneg (sub_nonneg.mpr hm) (sub_nonneg.mpr ht)
        have hsquare : 0 ≤ (n + 1 : ℝ) * ((n + 1 : ℝ) - 1) * t := by
          positivity
        nlinarith
      dsimp [HurwitzKernelBounds.f_nat, thetaModeMajorant]
      rw [abs_mul, abs_of_nonneg (by positivity), abs_of_pos (Real.exp_pos _)]
      calc
        (n + 1 : ℝ) ^ k * Real.exp (-Real.pi * (n + 1 : ℝ) ^ 2 * t) ≤
            (n + 1 : ℝ) ^ k *
              (Real.exp (-(Real.pi / 2 * (n + 1))) *
                Real.exp (-(Real.pi / 2) * t)) := by
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          rw [← Real.exp_add]
          apply Real.exp_monotone
          nlinarith [Real.pi_pos]
        _ = (n + 1 : ℝ) ^ k * Real.exp (-(Real.pi / 2 * (n + 1))) *
              Real.exp (-(Real.pi / 2) * t) := by ring
    have hmajorant : HasSum
        (fun n : ℕ => thetaModeMajorant k n *
          Real.exp (-(Real.pi / 2) * t))
        (B * Real.exp (-(Real.pi / 2) * t)) := by
      exact (summable_thetaModeMajorant k).hasSum.mul_right _
    have hbound := tsum_of_norm_bounded hmajorant hmode
    rw [HurwitzKernelBounds.F_nat, Real.norm_eq_abs]
    exact hbound
  exact htoB.trans ((isBigO_refl (fun t : ℝ =>
    Real.exp (-(Real.pi / 2) * t)) atTop).const_mul_left B)

/-- Exact identification of the first differentiated series with the
quadratically weighted positive mode sum. -/
theorem thetaTailD1_eq_neg_pi_mul_FNat (t : ℝ) :
    thetaTailD1 t = -Real.pi * HurwitzKernelBounds.F_nat 2 1 t := by
  unfold thetaTailD1 HurwitzKernelBounds.F_nat
  rw [← tsum_mul_left]
  congr 1
  funext n
  simp [thetaTailTerm, thetaTailCoeff, HurwitzKernelBounds.f_nat]
  ring

/-- Exact identification of the second differentiated series with the
quartically weighted positive mode sum. -/
theorem thetaTailD2_eq_pi_sq_mul_FNat (t : ℝ) :
    thetaTailD2 t = Real.pi ^ 2 * HurwitzKernelBounds.F_nat 4 1 t := by
  unfold thetaTailD2 HurwitzKernelBounds.F_nat
  rw [← tsum_mul_left]
  congr 1
  funext n
  simp [thetaTailTerm, thetaTailCoeff, HurwitzKernelBounds.f_nat]
  ring

/-- The undifferentiated theta tail is the zeroth positive mode sum. -/
theorem riemannThetaTail_eq_FNat_zero {t : ℝ} (ht : 0 < t) :
    riemannThetaTail t = HurwitzKernelBounds.F_nat 0 1 t := by
  rw [riemannThetaTail_eq_tsum ht]
  unfold HurwitzKernelBounds.F_nat
  congr 1
  funext n
  simp [thetaTailTerm, thetaTailCoeff, HurwitzKernelBounds.f_nat]

theorem thetaTailD1_isBigO_exp :
    thetaTailD1 =O[atTop] (fun t => Real.exp (-(Real.pi / 2) * t)) := by
  have h := (hurwitzFNat_one_isBigO_exp 2).const_mul_left (-Real.pi)
  exact h.congr' (Eventually.of_forall fun t =>
    (thetaTailD1_eq_neg_pi_mul_FNat t).symm) (Eventually.of_forall fun _ => rfl)

theorem thetaTailD2_isBigO_exp :
    thetaTailD2 =O[atTop] (fun t => Real.exp (-(Real.pi / 2) * t)) := by
  have h := (hurwitzFNat_one_isBigO_exp 4).const_mul_left (Real.pi ^ 2)
  exact h.congr' (Eventually.of_forall fun t =>
    (thetaTailD2_eq_pi_sq_mul_FNat t).symm) (Eventually.of_forall fun _ => rfl)

/-- After the logarithmic substitution `t = exp (2u)`, every differentiated
mode sum still beats an arbitrary fixed exponential prefactor. -/
theorem exp_mul_hurwitzFNat_exp_two_isBigO_exp_neg (q : ℝ) (k : ℕ) :
    (fun u => Real.exp (q * u) *
      HurwitzKernelBounds.F_nat k 1 (Real.exp (2 * u))) =O[atTop]
        (fun u => Real.exp (-u)) := by
  have hpow : (fun t => HurwitzKernelBounds.F_nat k 1 t) =O[atTop]
      (fun t : ℝ => t ^ (-((q + 1) / 2))) :=
    (hurwitzFNat_one_isBigO_exp k).trans
      (isLittleO_exp_neg_mul_rpow_atTop
        (by positivity : 0 < Real.pi / 2) (-((q + 1) / 2))).isBigO
  have hexp2 : Tendsto (fun u : ℝ => Real.exp (2 * u)) atTop atTop :=
    Real.tendsto_exp_atTop.comp
      (tendsto_id.const_mul_atTop (by norm_num : 0 < (2 : ℝ)))
  have hcomp := hpow.comp_tendsto hexp2
  have hmul := (isBigO_refl (fun u : ℝ => Real.exp (q * u)) atTop).mul hcomp
  refine hmul.congr' (Eventually.of_forall fun _ => rfl) ?_
  filter_upwards [] with u
  dsimp only [Function.comp_apply]
  rw [Real.rpow_def_of_pos (Real.exp_pos _), Real.log_exp, ← Real.exp_add]
  congr 1
  ring

/-- The preceding arbitrary-prefactor estimate at the paper's basic
`exp (u/2)` normalization. -/
theorem exp_half_mul_hurwitzFNat_exp_two_isBigO_exp_neg (k : ℕ) :
    (fun u => Real.exp (u / 2) *
      HurwitzKernelBounds.F_nat k 1 (Real.exp (2 * u))) =O[atTop]
        (fun u => Real.exp (-u)) := by
  convert exp_mul_hurwitzFNat_exp_two_isBigO_exp_neg (1 / 2) k using 1
  funext u
  congr 2
  ring

/-! ## Decay of the logarithmic theta amplitude -/

/-- Exact second derivative of `A(u)` in terms of the three positive mode
sums needed below. -/
theorem iteratedDeriv_two_thetaLogAmplitude_eq_modeSums (u : ℝ) :
    iteratedDeriv 2 thetaLogAmplitude u =
      Real.exp (u / 2) *
        (1 / 4 * HurwitzKernelBounds.F_nat 0 1 (Real.exp (2 * u)) -
          6 * Real.pi * Real.exp (2 * u) *
            HurwitzKernelBounds.F_nat 2 1 (Real.exp (2 * u)) +
          4 * Real.pi ^ 2 * Real.exp (2 * u) ^ 2 *
            HurwitzKernelBounds.F_nat 4 1 (Real.exp (2 * u))) := by
  have hfirst : deriv thetaLogAmplitude =
      fun x => Real.exp (x / 2) *
        (1 / 2 * riemannThetaTail (Real.exp (2 * x)) +
          2 * Real.exp (2 * x) * deriv riemannThetaTail (Real.exp (2 * x))) := by
    funext x
    exact (hasDerivAt_thetaLogAmplitude (u := x)
      (riemannThetaTail_differentiableAt (Real.exp_pos _)).hasDerivAt).deriv
  have hsecond := hasDerivAt_thetaLogAmplitude_first
    (u := u) (riemannThetaTail_differentiableAt (Real.exp_pos _)).hasDerivAt
      (deriv_riemannThetaTail_differentiableAt (Real.exp_pos _)).hasDerivAt
  rw [show iteratedDeriv 2 thetaLogAmplitude u =
      deriv (deriv thetaLogAmplitude) u by
    rw [show 2 = 1 + 1 by norm_num, iteratedDeriv_succ, iteratedDeriv_one]]
  rw [hfirst, hsecond.deriv]
  rw [deriv_riemannThetaTail_eq_thetaTailD1 (Real.exp_pos _)]
  have hD2 :=
    iteratedDeriv_two_riemannThetaTail_eq_thetaTailD2 (Real.exp_pos (2 * u))
  rw [show iteratedDeriv 2 riemannThetaTail (Real.exp (2 * u)) =
      deriv (deriv riemannThetaTail) (Real.exp (2 * u)) by
    rw [show 2 = 1 + 1 by norm_num, iteratedDeriv_succ, iteratedDeriv_one]] at hD2
  rw [hD2]
  rw [riemannThetaTail_eq_FNat_zero (Real.exp_pos _)]
  rw [thetaTailD1_eq_neg_pi_mul_FNat, thetaTailD2_eq_pi_sq_mul_FNat]
  ring

theorem thetaLogAmplitude_isBigO_exp_neg :
    thetaLogAmplitude =O[atTop] (fun u => Real.exp (-u)) := by
  refine (exp_half_mul_hurwitzFNat_exp_two_isBigO_exp_neg 0).congr'
    (Eventually.of_forall fun u => ?_) (Eventually.of_forall fun _ => rfl)
  unfold thetaLogAmplitude
  rw [riemannThetaTail_eq_FNat_zero (Real.exp_pos _)]

theorem deriv_thetaLogAmplitude_isBigO_exp_neg :
    (deriv thetaLogAmplitude) =O[atTop] (fun u => Real.exp (-u)) := by
  have h0 :=
    (exp_mul_hurwitzFNat_exp_two_isBigO_exp_neg (1 / 2) 0).const_mul_left (1 / 2)
  have h2 :=
    (exp_mul_hurwitzFNat_exp_two_isBigO_exp_neg (5 / 2) 2).const_mul_left
      (-2 * Real.pi)
  have hsum := h0.add h2
  refine hsum.congr' (Eventually.of_forall fun u => ?_)
    (Eventually.of_forall fun _ => rfl)
  rw [deriv_thetaLogAmplitude_eq_thetaTailD1]
  rw [riemannThetaTail_eq_FNat_zero (Real.exp_pos _)]
  rw [thetaTailD1_eq_neg_pi_mul_FNat]
  dsimp only
  rw [show Real.exp (u / 2) = Real.exp ((1 / 2) * u) by congr 1; ring]
  rw [show Real.exp ((5 / 2) * u) =
      Real.exp ((1 / 2) * u) * Real.exp (2 * u) by
    rw [← Real.exp_add]; congr 1; ring]
  ring

theorem iteratedDeriv_two_thetaLogAmplitude_isBigO_exp_neg :
    (fun u => iteratedDeriv 2 thetaLogAmplitude u) =O[atTop]
      (fun u => Real.exp (-u)) := by
  have h0 :=
    (exp_mul_hurwitzFNat_exp_two_isBigO_exp_neg (1 / 2) 0).const_mul_left (1 / 4)
  have h2 :=
    (exp_mul_hurwitzFNat_exp_two_isBigO_exp_neg (5 / 2) 2).const_mul_left
      (-6 * Real.pi)
  have h4 :=
    (exp_mul_hurwitzFNat_exp_two_isBigO_exp_neg (9 / 2) 4).const_mul_left
      (4 * Real.pi ^ 2)
  have hsum := (h0.add h2).add h4
  refine hsum.congr' (Eventually.of_forall fun u => ?_)
    (Eventually.of_forall fun _ => rfl)
  change _ = iteratedDeriv 2 thetaLogAmplitude u
  rw [iteratedDeriv_two_thetaLogAmplitude_eq_modeSums]
  dsimp only
  rw [show Real.exp (u / 2) = Real.exp ((1 / 2) * u) by congr 1; ring]
  rw [show Real.exp ((5 / 2) * u) =
      Real.exp ((1 / 2) * u) * Real.exp (2 * u) by
    rw [← Real.exp_add]; congr 1; ring]
  rw [show Real.exp ((9 / 2) * u) =
      Real.exp ((1 / 2) * u) * Real.exp (2 * u) ^ 2 by
    rw [pow_two, ← Real.exp_add, ← Real.exp_add]
    congr 1
    ring]
  ring

/-- The pulled-back theta amplitude is globally twice continuously
differentiable; the positive-domain condition for theta is discharged by
positivity of the exponential substitution. -/
theorem thetaLogAmplitude_contDiff_two : ContDiff ℝ 2 thetaLogAmplitude := by
  unfold thetaLogAmplitude
  have hhalf : ContDiff ℝ 2 (fun u : ℝ => Real.exp (u / 2)) :=
    Real.contDiff_exp.comp (contDiff_id.div_const 2)
  have htwo : ContDiff ℝ 2 (fun u : ℝ => Real.exp (2 * u)) :=
    Real.contDiff_exp.comp (contDiff_const.mul contDiff_id)
  have htheta : ContDiff ℝ 2
      (fun u : ℝ => riemannThetaTail (Real.exp (2 * u))) := by
    have hcomp := riemannThetaTail_contDiffOn.comp (s := Set.univ)
      htwo.contDiffOn (fun u _ => Real.exp_pos (2 * u))
    change ContDiff ℝ 2 (riemannThetaTail ∘ fun u : ℝ => Real.exp (2 * u))
    simpa only [contDiffOn_univ] using hcomp
  exact hhalf.mul htheta

/-- Polynomial weights consume only half of the available exponential
decay. -/
theorem pow_mul_isBigO_exp_neg_half_of_isBigO_exp_neg
    {f : ℝ → ℝ} (hf : f =O[atTop] (fun u => Real.exp (-u))) (m : ℕ) :
    (fun u => u ^ m * f u) =O[atTop] (fun u => Real.exp (-(1 / 2) * u)) := by
  have hpow :=
    (isLittleO_pow_exp_pos_mul_atTop m (by norm_num : 0 < (1 / 2 : ℝ))).isBigO
  have hmul := hpow.mul hf
  refine hmul.congr' (Eventually.of_forall fun _ => rfl) ?_
  filter_upwards [] with u
  rw [← Real.exp_add]
  congr 1
  ring

/-- A continuous function with the established exponential tail remains
integrable after multiplication by any fixed polynomial. -/
theorem integrableOn_pow_mul_of_isBigO_exp_neg
    {f : ℝ → ℝ} (hfcont : Continuous f)
    (hf : f =O[atTop] (fun u => Real.exp (-u))) (m : ℕ) :
    IntegrableOn (fun u => u ^ m * f u) (Ioi 0) := by
  apply integrable_of_isBigO_exp_neg (by norm_num : 0 < (1 / 2 : ℝ))
  · exact ((continuous_id.pow m).mul hfcont).continuousOn
  · exact pow_mul_isBigO_exp_neg_half_of_isBigO_exp_neg hf m

/-- The same weighted products vanish at the infinite endpoint. -/
theorem tendsto_pow_mul_zero_of_isBigO_exp_neg
    {f : ℝ → ℝ} (hf : f =O[atTop] (fun u => Real.exp (-u))) (m : ℕ) :
    Tendsto (fun u => u ^ m * f u) atTop (nhds 0) := by
  apply (pow_mul_isBigO_exp_neg_half_of_isBigO_exp_neg hf m).trans_tendsto
  exact Real.tendsto_exp_atBot.comp
    (tendsto_id.const_mul_atTop_of_neg (by norm_num : (-(1 / 2 : ℝ)) < 0))

theorem integrableOn_pow_mul_thetaLogAmplitude (m : ℕ) :
    IntegrableOn (fun u => u ^ m * thetaLogAmplitude u) (Ioi 0) :=
  integrableOn_pow_mul_of_isBigO_exp_neg
    thetaLogAmplitude_contDiff_two.continuous thetaLogAmplitude_isBigO_exp_neg m

theorem integrableOn_pow_mul_deriv_thetaLogAmplitude (m : ℕ) :
    IntegrableOn (fun u => u ^ m * deriv thetaLogAmplitude u) (Ioi 0) :=
  integrableOn_pow_mul_of_isBigO_exp_neg
    (thetaLogAmplitude_contDiff_two.continuous_deriv (by norm_num))
    deriv_thetaLogAmplitude_isBigO_exp_neg m

theorem integrableOn_pow_mul_iteratedDeriv_two_thetaLogAmplitude (m : ℕ) :
    IntegrableOn (fun u => u ^ m * iteratedDeriv 2 thetaLogAmplitude u) (Ioi 0) :=
  integrableOn_pow_mul_of_isBigO_exp_neg
    (thetaLogAmplitude_contDiff_two.continuous_iteratedDeriv 2 (by norm_num))
    iteratedDeriv_two_thetaLogAmplitude_isBigO_exp_neg m

theorem tendsto_pow_mul_thetaLogAmplitude_atTop (m : ℕ) :
    Tendsto (fun u => u ^ m * thetaLogAmplitude u) atTop (nhds 0) :=
  tendsto_pow_mul_zero_of_isBigO_exp_neg thetaLogAmplitude_isBigO_exp_neg m

theorem tendsto_pow_mul_deriv_thetaLogAmplitude_atTop (m : ℕ) :
    Tendsto (fun u => u ^ m * deriv thetaLogAmplitude u) atTop (nhds 0) :=
  tendsto_pow_mul_zero_of_isBigO_exp_neg deriv_thetaLogAmplitude_isBigO_exp_neg m

end

end Zeta23.Research.JensenWedge
