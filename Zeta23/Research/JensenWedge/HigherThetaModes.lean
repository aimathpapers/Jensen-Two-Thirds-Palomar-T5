import Zeta23.Research.JensenWedge.LeadingT3Assembly

/-!
# Higher theta modes on the legal saddle strip

This module defines every mode above the leading theta term, proves the exact
quadratic gap, and sums the resulting geometric majorant.  The conclusion is
a pointwise estimate for the entire infinite higher-mode sum throughout the
legal horizontal strip; no finite truncation is used.
-/

namespace Zeta23.Research.JensenWedge

open Complex Filter Function MeasureTheory Set Topology

noncomputable section

def higherThetaGap (n : ℕ) : ℕ := (n + 2) ^ 2 - 1

def higherThetaScalarFactor (q : ℝ) (n : ℕ) : ℝ :=
  Real.exp (-(higherThetaGap n : ℝ) * q)

def higherThetaComplexFactor (n : ℕ) (u : ℂ) : ℂ :=
  exp (-((Real.pi : ℂ) * (higherThetaGap n : ℂ) * exp u))

def higherThetaMode (n : ℕ) (s u : ℂ) : ℂ :=
  leadingIntegrand s u * higherThetaComplexFactor n u

theorem higherThetaGap_ge_three_mul (n : ℕ) :
    3 * (n + 1) ≤ higherThetaGap n := by
  unfold higherThetaGap
  apply Nat.le_sub_of_add_le
  nlinarith [Nat.zero_le (n * n)]

theorem higherThetaComplexFactor_norm (n : ℕ) (u : ℂ) :
    ‖higherThetaComplexFactor n u‖ =
      higherThetaScalarFactor ((Real.pi) * (exp u).re) n := by
  rw [higherThetaComplexFactor, Complex.norm_exp]
  unfold higherThetaScalarFactor
  congr 1
  simp only [neg_re, mul_re, mul_im, ofReal_re, ofReal_im, natCast_re, natCast_im,
    zero_mul, sub_zero]
  ring

theorem higherThetaScalarFactor_le_geometric
    {q : ℝ} (hq : 0 ≤ q) (n : ℕ) :
    higherThetaScalarFactor q n ≤ (Real.exp (-3 * q)) ^ (n + 1) := by
  rw [← Real.exp_nat_mul]
  apply Real.exp_monotone
  have hgap : (3 : ℝ) * (n + 1) ≤ higherThetaGap n := by
    exact_mod_cast higherThetaGap_ge_three_mul n
  push_cast at hgap ⊢
  have hmul := mul_nonneg hq (sub_nonneg.mpr hgap)
  nlinarith

theorem summable_higherThetaScalarFactor {q : ℝ} (hq : 0 < q) :
    Summable (higherThetaScalarFactor q) := by
  let r := Real.exp (-3 * q)
  have hr0 : 0 ≤ r := (Real.exp_pos _).le
  have hr1 : r < 1 := by
    dsimp [r]
    rw [Real.exp_lt_one_iff]
    linarith
  have hgeo : Summable (fun n : ℕ => r ^ (n + 1)) := by
    exact (summable_nat_add_iff 1).mpr
      (summable_geometric_of_lt_one hr0 hr1)
  apply Summable.of_nonneg_of_le
  · intro n
    exact (Real.exp_pos _).le
  · intro n
    simpa only [r] using higherThetaScalarFactor_le_geometric hq.le n
  · exact hgeo

theorem higherThetaScalarFactor_tsum_le_geometric
    {q : ℝ} (hq : 0 < q) :
    (∑' n : ℕ, higherThetaScalarFactor q n) ≤
      Real.exp (-3 * q) * (1 - Real.exp (-3 * q))⁻¹ := by
  let r := Real.exp (-3 * q)
  have hr0 : 0 ≤ r := (Real.exp_pos _).le
  have hr1 : r < 1 := by
    dsimp [r]
    rw [Real.exp_lt_one_iff]
    linarith
  have hgeo0 := summable_geometric_of_lt_one hr0 hr1
  have hgeo : Summable (fun n : ℕ => r ^ (n + 1)) :=
    (summable_nat_add_iff 1).mpr hgeo0
  calc
    (∑' n : ℕ, higherThetaScalarFactor q n) ≤
        ∑' n : ℕ, r ^ (n + 1) :=
      (summable_higherThetaScalarFactor hq).tsum_le_tsum
        (fun n => by
          simpa only [r] using higherThetaScalarFactor_le_geometric hq.le n) hgeo
    _ = ∑' n : ℕ, r * r ^ n := by
      congr 1
      funext n
      rw [pow_succ]
      ring
    _ = r * (1 - r)⁻¹ := by
      rw [tsum_mul_left, tsum_geometric_of_lt_one hr0 hr1]
    _ = _ := by simp only [r]

theorem exp_neg_three_mul_le_half {q : ℝ} (hq : 1 ≤ q) :
    Real.exp (-3 * q) ≤ 1 / 2 := by
  rw [show -3 * q = -(3 * q) by ring, Real.exp_neg]
  have hexpPos : 0 < Real.exp (3 * q) := Real.exp_pos _
  apply (inv_le_comm₀ hexpPos (by norm_num : (0 : ℝ) < 1 / 2)).2
  norm_num
  exact (by
    have hlower := Real.add_one_le_exp (3 * q)
    linarith : (2 : ℝ) ≤ Real.exp (3 * q))

theorem higherThetaScalarFactor_tsum_le_two_exp
    {q : ℝ} (hq : 1 ≤ q) :
    (∑' n : ℕ, higherThetaScalarFactor q n) ≤
      2 * Real.exp (-3 * q) := by
  let r := Real.exp (-3 * q)
  have hr0 : 0 ≤ r := (Real.exp_pos _).le
  have hrHalf : r ≤ 1 / 2 := by
    simpa only [r] using exp_neg_three_mul_le_half hq
  have hdenomPos : 0 < 1 - r := by linarith
  have hinv : (1 - r)⁻¹ ≤ 2 := by
    apply (inv_le_comm₀ hdenomPos (by norm_num : (0 : ℝ) < 2)).2
    norm_num
    linarith
  calc
    (∑' n : ℕ, higherThetaScalarFactor q n) ≤
        r * (1 - r)⁻¹ := by
      simpa only [r] using higherThetaScalarFactor_tsum_le_geometric
        (lt_of_lt_of_le zero_lt_one hq)
    _ ≤ r * 2 := mul_le_mul_of_nonneg_left hinv hr0
    _ = 2 * Real.exp (-3 * q) := by simp only [r]; ring

theorem higherThetaMode_eq_fullMode (n : ℕ) (s u : ℂ) :
    higherThetaMode n s u =
      exp (s * log u + u / 4 -
        (Real.pi : ℂ) * ((n + 2 : ℕ) : ℂ) ^ 2 * exp u) := by
  rw [higherThetaMode, leadingIntegrand_eq_exp_logIntegrand,
    higherThetaComplexFactor, ← exp_add]
  congr 1
  unfold leadingLogIntegrand higherThetaGap
  push_cast
  rw [Nat.cast_sub (Nat.one_le_pow 2 (n + 2) (by omega))]
  push_cast
  ring

theorem summable_higherThetaComplexFactor
    {u : ℂ} (hq : 0 < Real.pi * (exp u).re) :
    Summable (fun n : ℕ => higherThetaComplexFactor n u) := by
  rw [← summable_norm_iff]
  simpa only [higherThetaComplexFactor_norm] using
    summable_higherThetaScalarFactor hq

theorem summable_higherThetaMode
    {s u : ℂ} (hq : 0 < Real.pi * (exp u).re) :
    Summable (fun n : ℕ => higherThetaMode n s u) := by
  exact (summable_higherThetaComplexFactor hq).mul_left (leadingIntegrand s u)

theorem higherThetaMode_tsum_norm_le
    {s u : ℂ} (hq : 1 ≤ Real.pi * (exp u).re) :
    ‖∑' n : ℕ, higherThetaMode n s u‖ ≤
      2 * ‖leadingIntegrand s u‖ *
        Real.exp (-3 * (Real.pi * (exp u).re)) := by
  let q : ℝ := Real.pi * (exp u).re
  have hqpos : 0 < q := lt_of_lt_of_le zero_lt_one hq
  have hsumNorm : Summable (fun n : ℕ => ‖higherThetaMode n s u‖) := by
    have hfacNorm : Summable (fun n : ℕ => ‖higherThetaComplexFactor n u‖) := by
      simpa only [higherThetaComplexFactor_norm, q] using
        summable_higherThetaScalarFactor hqpos
    simpa only [higherThetaMode, norm_mul] using
      hfacNorm.mul_left ‖leadingIntegrand s u‖
  calc
    ‖∑' n : ℕ, higherThetaMode n s u‖ ≤
        ∑' n : ℕ, ‖higherThetaMode n s u‖ :=
      norm_tsum_le_tsum_norm hsumNorm
    _ = ‖leadingIntegrand s u‖ *
        (∑' n : ℕ, higherThetaScalarFactor q n) := by
      simp only [higherThetaMode, norm_mul, higherThetaComplexFactor_norm, q,
        tsum_mul_left]
    _ ≤ ‖leadingIntegrand s u‖ *
        (2 * Real.exp (-3 * q)) := by
      gcongr
      exact higherThetaScalarFactor_tsum_le_two_exp hq
    _ = 2 * ‖leadingIntegrand s u‖ *
        Real.exp (-3 * (Real.pi * (exp u).re)) := by
      simp only [q]
      ring

def fullThetaContourIntegrand (s u : ℂ) : ℂ :=
  leadingIntegrand s u + ∑' n : ℕ, higherThetaMode n s u

theorem thetaStrip_modeParameter_ge_one
    {u : ℂ} (hre : 1 ≤ u.re) (him : |u.im| ≤ 1 / 20) :
    1 ≤ Real.pi * (exp u).re := by
  have hcoslt : 99 / 100 < Real.cos u.im := by
    calc
      99 / 100 < 1 - u.im ^ 2 / 2 := by
        nlinarith [sq_abs u.im, abs_nonneg u.im]
      _ ≤ Real.cos u.im := Real.one_sub_sq_div_two_le_cos
  have hcos : 99 / 100 ≤ Real.cos u.im := hcoslt.le
  have hexp : 2 ≤ Real.exp u.re := by
    calc
      2 ≤ u.re + 1 := by linarith
      _ ≤ Real.exp u.re := Real.add_one_le_exp _
  rw [Complex.exp_re]
  calc
    (1 : ℝ) ≤ 3 * (2 * (99 / 100 : ℝ)) := by norm_num
    _ ≤ Real.pi * (Real.exp u.re * Real.cos u.im) := by
      gcongr
      exact Real.pi_gt_three.le

theorem fullThetaContourIntegrand_sub_leading_norm_le
    {s u : ℂ} (hre : 1 ≤ u.re) (him : |u.im| ≤ 1 / 20) :
    ‖fullThetaContourIntegrand s u - leadingIntegrand s u‖ ≤
      2 * ‖leadingIntegrand s u‖ *
        Real.exp (-3 * (Real.pi * (exp u).re)) := by
  rw [fullThetaContourIntegrand]
  simp only [add_sub_cancel_left]
  exact higherThetaMode_tsum_norm_le
    (thetaStrip_modeParameter_ge_one hre him)

end

end Zeta23.Research.JensenWedge
