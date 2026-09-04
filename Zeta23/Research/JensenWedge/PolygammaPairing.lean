import Zeta23.Research.JensenWedge.XiLogError
import Mathlib.Analysis.PSeries
import Mathlib.Analysis.SumIntegralComparisons
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals

/-!
# Paired fifth-polygamma series bounds

The sixth logarithmic residual in the manuscript contains two differences of
fifth polygamma terms.  This file isolates the quantitative analytic core of
that pairing.  It defines the standard absolutely convergent series

`120 * sum_{k >= 0} (z+k)^(-6)`

and proves a finite-`n`, right-half-plane Lipschitz estimate with the exact
scale needed by the residual argument.  The proof is entirely kernel checked:
it combines an algebraic inverse-power estimate with Mathlib's integral test
for the seventh-power tail.  No numerical evaluation is used.

Identification of this series with the fifth derivative of `Complex.digamma`
is deliberately a separate subsequent seam; the theorem here does not hide
that remaining derivative-identification obligation.
-/

noncomputable section

namespace Zeta23.Research.JensenWedge

open Set MeasureTheory

/-- A complex line segment whose endpoints lie to the right of `a` stays to
the right of `a`.  This is the domain-containment fact used when pairing
polygamma values by a segment argument. -/
theorem lineSegment_re_lower {z w : ℂ} {a t : ℝ}
    (hz : a ≤ z.re) (hw : a ≤ w.re) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    a ≤ (z + (t : ℂ) * (w - z)).re := by
  simp only [Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.sub_re,
    Complex.ofReal_im, Complex.sub_im, zero_mul, sub_zero]
  nlinarith

/-- Absolute convergence of the real seventh-power tail at an integer
translate. -/
theorem shiftedSeventhPowerTail_summable (n : ℕ) :
    Summable (fun k : ℕ => 1 / (((n + k : ℕ) : ℝ) ^ 7)) := by
  have h := summable_pow_div_add (1 : ℝ) 7 n (by norm_num)
  exact h.congr (fun k => by
    rw [norm_div, norm_one, norm_pow, Real.norm_eq_abs,
      abs_of_nonneg (by positivity)]
    norm_num [Nat.cast_add, add_comm, one_div])

/-- Integral-test bound preserving the decisive sixth inverse power:
`sum_{k >= 0} (n+k)^(-7) <= 1 / (6 (n-1)^6)` for `n >= 2`. -/
theorem shiftedSeventhPowerTail_le {n : ℕ} (hn : 2 ≤ n) :
    (∑' k : ℕ, 1 / (((n + k : ℕ) : ℝ) ^ 7)) ≤
      1 / (6 * (((n - 1 : ℕ) : ℝ) ^ 6)) := by
  let f : ℝ → ℝ := fun x => x ^ (-7 : ℝ)
  have hNpos : 0 < ((n - 1 : ℕ) : ℝ) := by
    exact_mod_cast Nat.sub_pos_of_lt (by omega : 1 < n)
  have hanti : AntitoneOn f (Ici ((n - 1 : ℕ) : ℝ)) := by
    intro x hx y _hy hxy
    dsimp [f]
    exact Real.rpow_le_rpow_of_nonpos (hNpos.trans_le hx) hxy (by norm_num)
  have hint : IntegrableOn f (Ioi ((n - 1 : ℕ) : ℝ)) :=
    integrableOn_Ioi_rpow_of_lt (by norm_num) hNpos
  have hnonneg : ∀ t ∈ Ioi ((n - 1 : ℕ) : ℝ), 0 ≤ f t := by
    intro t ht
    exact Real.rpow_nonneg (le_of_lt (hNpos.trans ht)) _
  have hbound := hanti.tsum_comp_add_le_integral (n - 1) hint hnonneg
  rw [integral_Ioi_rpow_of_lt (by norm_num) hNpos] at hbound
  norm_num [f] at hbound ⊢
  have hn1 : 1 ≤ n := by omega
  convert hbound using 1
  · congr 1
    funext k
    congr 2
    rw [Nat.cast_sub hn1]
    ring
  · field_simp

/-- Degree-six power differences are Lipschitz on a norm ball. -/
theorem norm_pow_six_sub_pow_six_le {x y : ℂ} {b : ℝ} (hb : 0 ≤ b)
    (hx : ‖x‖ ≤ b) (hy : ‖y‖ ≤ b) :
    ‖x ^ 6 - y ^ 6‖ ≤ 6 * b ^ 5 * ‖x - y‖ := by
  have hid : x ^ 6 - y ^ 6 =
      (x - y) * (x ^ 5 + x ^ 4 * y + x ^ 3 * y ^ 2 +
        x ^ 2 * y ^ 3 + x * y ^ 4 + y ^ 5) := by ring
  rw [hid, norm_mul]
  have hmonomial (i j : ℕ) (hij : i + j = 5) :
      ‖x ^ i * y ^ j‖ ≤ b ^ 5 := by
    rw [norm_mul, norm_pow, norm_pow]
    calc
      ‖x‖ ^ i * ‖y‖ ^ j ≤ b ^ i * b ^ j :=
        mul_le_mul (pow_le_pow_left₀ (norm_nonneg _) hx i)
          (pow_le_pow_left₀ (norm_nonneg _) hy j)
          (pow_nonneg (norm_nonneg _) _) (pow_nonneg hb _)
      _ = b ^ (i + j) := (pow_add b i j).symm
      _ = b ^ 5 := by rw [hij]
  have h1 : ‖x ^ 5‖ ≤ b ^ 5 := by simpa using hmonomial 5 0 rfl
  have h2 : ‖x ^ 4 * y‖ ≤ b ^ 5 := by simpa using hmonomial 4 1 rfl
  have h3 : ‖x ^ 3 * y ^ 2‖ ≤ b ^ 5 := hmonomial 3 2 rfl
  have h4 : ‖x ^ 2 * y ^ 3‖ ≤ b ^ 5 := hmonomial 2 3 rfl
  have h5 : ‖x * y ^ 4‖ ≤ b ^ 5 := by simpa using hmonomial 1 4 rfl
  have h6 : ‖y ^ 5‖ ≤ b ^ 5 := by simpa using hmonomial 0 5 rfl
  have hsum :
      ‖x ^ 5 + x ^ 4 * y + x ^ 3 * y ^ 2 +
        x ^ 2 * y ^ 3 + x * y ^ 4 + y ^ 5‖ ≤ 6 * b ^ 5 := by
    calc
      _ ≤ (b ^ 5 + b ^ 5 + b ^ 5 + b ^ 5 + b ^ 5) + b ^ 5 := by
        apply norm_add_le_of_le
        · apply norm_add_le_of_le
          · apply norm_add_le_of_le
            · apply norm_add_le_of_le
              · exact norm_add_le_of_le h1 h2
              · exact h3
            · exact h4
          · exact h5
        · exact h6
      _ = 6 * b ^ 5 := by ring
  calc
    ‖x - y‖ * _ ≤ ‖x - y‖ * (6 * b ^ 5) :=
      mul_le_mul_of_nonneg_left hsum (norm_nonneg _)
    _ = 6 * b ^ 5 * ‖x - y‖ := by ring

/-- Reciprocal subtraction on a set bounded away from zero. -/
theorem norm_inv_sub_inv_le {u v : ℂ} {a : ℝ} (ha : 0 < a)
    (hu : a ≤ ‖u‖) (hv : a ≤ ‖v‖) :
    ‖u⁻¹ - v⁻¹‖ ≤ ‖u - v‖ / a ^ 2 := by
  have hu0 : u ≠ 0 := by
    intro h
    subst u
    simpa using (ha.trans_le hu)
  have hv0 : v ≠ 0 := by
    intro h
    subst v
    simpa using (ha.trans_le hv)
  have hid : u⁻¹ - v⁻¹ = -(u - v) / (u * v) := by
    field_simp
    ring
  rw [hid, norm_div, norm_neg, norm_mul]
  have hden : a ^ 2 ≤ ‖u‖ * ‖v‖ := by
    rw [pow_two]
    exact mul_le_mul hu hv ha.le (norm_nonneg _)
  exact div_le_div_of_nonneg_left (norm_nonneg _) (pow_pos ha 2) hden

/-- Sixth inverse powers have the seventh-power denominator expected from
one differentiation. -/
theorem norm_inv_pow_six_sub_inv_pow_six_le {u v : ℂ} {a : ℝ} (ha : 0 < a)
    (hu : a ≤ ‖u‖) (hv : a ≤ ‖v‖) :
    ‖u⁻¹ ^ 6 - v⁻¹ ^ 6‖ ≤ 6 * ‖u - v‖ / a ^ 7 := by
  have hiu : ‖u⁻¹‖ ≤ 1 / a := by
    rw [norm_inv]
    simpa [one_div] using one_div_le_one_div_of_le ha hu
  have hiv : ‖v⁻¹‖ ≤ 1 / a := by
    rw [norm_inv]
    simpa [one_div] using one_div_le_one_div_of_le ha hv
  have hb : 0 ≤ 1 / a := (div_pos zero_lt_one ha).le
  have hp := norm_pow_six_sub_pow_six_le hb hiu hiv
  have hd := norm_inv_sub_inv_le ha hu hv
  calc
    ‖u⁻¹ ^ 6 - v⁻¹ ^ 6‖ ≤ 6 * (1 / a) ^ 5 * ‖u⁻¹ - v⁻¹‖ := hp
    _ ≤ 6 * (1 / a) ^ 5 * (‖u - v‖ / a ^ 2) := by gcongr
    _ = 6 * ‖u - v‖ / a ^ 7 := by field_simp

/-- Absolute convergence of the sixth inverse-power series on an
integer-anchored right half-plane. -/
theorem summable_invPowSix_rightOfNat {z : ℂ} {n : ℕ} (hn : 2 ≤ n)
    (hz : (n : ℝ) ≤ z.re) :
    Summable (fun k : ℕ => (z + (k : ℂ))⁻¹ ^ 6) := by
  have hmajor := summable_pow_div_add (1 : ℂ) 6 n (by norm_num)
  have hnorm : Summable (fun k : ℕ => ‖(z + (k : ℂ))⁻¹ ^ 6‖) := by
    apply Summable.of_nonneg_of_le (fun _ => norm_nonneg _) _ hmajor
    intro k
    have hapos : 0 < ((n + k : ℕ) : ℝ) := by positivity
    have hlower : ((n + k : ℕ) : ℝ) ≤ ‖z + (k : ℂ)‖ := by
      calc
        ((n + k : ℕ) : ℝ) ≤ z.re + k := by
          simpa [Nat.cast_add, add_comm] using add_le_add_right hz (k : ℝ)
        _ = (z + (k : ℂ)).re := by simp
        _ ≤ ‖z + (k : ℂ)‖ := Complex.re_le_norm _
    rw [norm_pow, norm_inv, norm_div, norm_one, one_div]
    simp only [norm_pow]
    rw [inv_pow]
    have hinv := (inv_le_inv₀ (pow_pos (hapos.trans_le hlower) 6)
      (pow_pos hapos 6)).mpr (pow_le_pow_left₀ hapos.le hlower 6)
    calc
      (‖z + (k : ℂ)‖ ^ 6)⁻¹ ≤ (((n + k : ℕ) : ℝ) ^ 6)⁻¹ := hinv
      _ = (‖(k : ℂ) + (n : ℂ)‖ ^ 6)⁻¹ := by
        rw [← Nat.cast_add, Complex.norm_natCast]
        norm_num [Nat.cast_add, add_comm]
  exact hnorm.of_norm

/-- The absolutely convergent series representation of the fifth
polygamma on the right half-plane. -/
def polygammaFiveSeries (z : ℂ) : ℂ :=
  120 * ∑' k : ℕ, (z + (k : ℂ))⁻¹ ^ 6

/-- Pairing two fifth-polygamma series gains one inverse power.  The constant
`120` is exact and the estimate is uniform in the imaginary parts. -/
theorem polygammaFiveSeries_pair_norm_le {z w : ℂ} {n : ℕ} (hn : 2 ≤ n)
    (hz : (n : ℝ) ≤ z.re) (hw : (n : ℝ) ≤ w.re) :
    ‖polygammaFiveSeries z - polygammaFiveSeries w‖ ≤
      120 * ‖z - w‖ / (((n - 1 : ℕ) : ℝ) ^ 6) := by
  have hsz := summable_invPowSix_rightOfNat hn hz
  have hsw := summable_invPowSix_rightOfNat hn hw
  have hsdiff := hsz.sub hsw
  have hsdiffNorm := hsdiff.norm
  have htail := shiftedSeventhPowerTail_summable n
  have hmajor : Summable
      (fun k : ℕ => 6 * ‖z - w‖ / (((n + k : ℕ) : ℝ) ^ 7)) := by
    exact (htail.mul_left (6 * ‖z - w‖)).congr (fun k => by ring)
  have hterm (k : ℕ) :
      ‖(z + (k : ℂ))⁻¹ ^ 6 - (w + (k : ℂ))⁻¹ ^ 6‖ ≤
        6 * ‖z - w‖ / (((n + k : ℕ) : ℝ) ^ 7) := by
    have hapos : 0 < ((n + k : ℕ) : ℝ) := by positivity
    have hzlower : ((n + k : ℕ) : ℝ) ≤ ‖z + (k : ℂ)‖ := by
      calc
        ((n + k : ℕ) : ℝ) ≤ z.re + k := by
          simpa [Nat.cast_add, add_comm] using add_le_add_right hz (k : ℝ)
        _ = (z + (k : ℂ)).re := by simp
        _ ≤ ‖z + (k : ℂ)‖ := Complex.re_le_norm _
    have hwlower : ((n + k : ℕ) : ℝ) ≤ ‖w + (k : ℂ)‖ := by
      calc
        ((n + k : ℕ) : ℝ) ≤ w.re + k := by
          simpa [Nat.cast_add, add_comm] using add_le_add_right hw (k : ℝ)
        _ = (w + (k : ℂ)).re := by simp
        _ ≤ ‖w + (k : ℂ)‖ := Complex.re_le_norm _
    have h := norm_inv_pow_six_sub_inv_pow_six_le hapos hzlower hwlower
    simpa only [add_sub_add_right_eq_sub] using h
  have htsum :
      (∑' k : ℕ,
        ‖(z + (k : ℂ))⁻¹ ^ 6 - (w + (k : ℂ))⁻¹ ^ 6‖) ≤
        ∑' k : ℕ, 6 * ‖z - w‖ / (((n + k : ℕ) : ℝ) ^ 7) :=
    hsdiffNorm.tsum_le_tsum hterm hmajor
  have hnorm :
      ‖∑' k : ℕ,
        ((z + (k : ℂ))⁻¹ ^ 6 - (w + (k : ℂ))⁻¹ ^ 6)‖ ≤
        ∑' k : ℕ, 6 * ‖z - w‖ / (((n + k : ℕ) : ℝ) ^ 7) :=
    (norm_tsum_le_tsum_norm hsdiffNorm).trans htsum
  have htailBound := shiftedSeventhPowerTail_le hn
  rw [hsz.tsum_sub hsw] at hnorm
  unfold polygammaFiveSeries
  rw [← mul_sub]
  rw [norm_mul, Complex.norm_ofNat]
  have hmajorEq :
      (∑' k : ℕ, 6 * ‖z - w‖ / (((n + k : ℕ) : ℝ) ^ 7)) =
        (6 * ‖z - w‖) *
          (∑' k : ℕ, 1 / (((n + k : ℕ) : ℝ) ^ 7)) := by
    rw [← tsum_mul_left]
    apply tsum_congr
    intro k
    ring
  calc
    (120 : ℝ) * ‖(∑' k : ℕ, (z + (k : ℂ))⁻¹ ^ 6) -
        ∑' k : ℕ, (w + (k : ℂ))⁻¹ ^ 6‖
        ≤ 120 * (∑' k : ℕ,
          6 * ‖z - w‖ / (((n + k : ℕ) : ℝ) ^ 7)) := by gcongr
    _ = 120 * (6 * ‖z - w‖) *
        (∑' k : ℕ, 1 / (((n + k : ℕ) : ℝ) ^ 7)) := by
          rw [hmajorEq]
          ring
    _ ≤ 120 * (6 * ‖z - w‖) *
        (1 / (6 * (((n - 1 : ℕ) : ℝ) ^ 6))) :=
          mul_le_mul_of_nonneg_left htailBound (by positivity)
    _ = 120 * ‖z - w‖ / (((n - 1 : ℕ) : ℝ) ^ 6) := by
      have hn1base : 0 < ((n - 1 : ℕ) : ℝ) := by
        exact_mod_cast Nat.sub_pos_of_lt (by omega : 1 < n)
      have hn1pos : 0 < (((n - 1 : ℕ) : ℝ) ^ 6) := pow_pos hn1base 6
      field_simp [ne_of_gt hn1pos]

end Zeta23.Research.JensenWedge
