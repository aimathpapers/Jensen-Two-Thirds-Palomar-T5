import Zeta23.Research.JensenWedge.PolygammaDerivative
import Mathlib.Analysis.SumIntegralComparisons
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals

/-!
# Exact sixth-residual assembly

This module puts the manuscript's six-term logarithmic residual into the
pairing order required for the two decisive fifth-polygamma differences.  It
also supplies the one-term fifth-polygamma tail needed for the distant `A`
parameter and combines these estimates with the uniform complex Cauchy bound
for the logarithmic xi error.

The remaining moving-saddle input is deliberately explicit as `mainSix`.
No equality between that input and the exact sixth derivative of the
manuscript auxiliary main is postulated here; that identification and its
`H₆` bound form the next formalization seam.
-/

noncomputable section

namespace Zeta23.Research.JensenWedge

open Set MeasureTheory

/-- Absolute convergence of the real sixth-power tail at an integer
translate. -/
theorem shiftedSixthPowerTail_summable (n : ℕ) :
    Summable (fun k : ℕ => 1 / (((n + k : ℕ) : ℝ) ^ 6)) := by
  have h := summable_pow_div_add (1 : ℝ) 6 n (by norm_num)
  exact h.congr (fun k => by
    rw [norm_div, norm_one, norm_pow, Real.norm_eq_abs,
      abs_of_nonneg (by positivity)]
    norm_num [Nat.cast_add, add_comm, one_div])

/-- Integral-test estimate for the single fifth-polygamma tail. -/
theorem shiftedSixthPowerTail_le {n : ℕ} (hn : 2 ≤ n) :
    (∑' k : ℕ, 1 / (((n + k : ℕ) : ℝ) ^ 6)) ≤
      1 / (5 * (((n - 1 : ℕ) : ℝ) ^ 5)) := by
  let f : ℝ → ℝ := fun x => x ^ (-6 : ℝ)
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

/-- A single fifth-polygamma series is `O((n-1)^-5)` on the right
half-plane. -/
theorem polygammaFiveSeries_norm_le {z : ℂ} {n : ℕ} (hn : 2 ≤ n)
    (hz : (n : ℝ) ≤ z.re) :
    ‖polygammaFiveSeries z‖ ≤
      24 / (((n - 1 : ℕ) : ℝ) ^ 5) := by
  have hsz := summable_invPowSix_rightOfNat hn hz
  have hszNorm := hsz.norm
  have htail := shiftedSixthPowerTail_summable n
  have hterm (k : ℕ) :
      ‖(z + (k : ℂ))⁻¹ ^ 6‖ ≤ 1 / (((n + k : ℕ) : ℝ) ^ 6) := by
    have hapos : 0 < ((n + k : ℕ) : ℝ) := by positivity
    have hlower : ((n + k : ℕ) : ℝ) ≤ ‖z + (k : ℂ)‖ := by
      calc
        ((n + k : ℕ) : ℝ) ≤ z.re + k := by
          simpa [Nat.cast_add, add_comm] using add_le_add_right hz (k : ℝ)
        _ = (z + (k : ℂ)).re := by simp
        _ ≤ ‖z + (k : ℂ)‖ := Complex.re_le_norm _
    rw [norm_pow, norm_inv, one_div]
    rw [inv_pow]
    exact (inv_le_inv₀ (pow_pos (hapos.trans_le hlower) 6)
      (pow_pos hapos 6)).mpr (pow_le_pow_left₀ hapos.le hlower 6)
  have htsum :
      (∑' k : ℕ, ‖(z + (k : ℂ))⁻¹ ^ 6‖) ≤
        ∑' k : ℕ, 1 / (((n + k : ℕ) : ℝ) ^ 6) :=
    hszNorm.tsum_le_tsum hterm htail
  have hnorm :
      ‖∑' k : ℕ, (z + (k : ℂ))⁻¹ ^ 6‖ ≤
        ∑' k : ℕ, 1 / (((n + k : ℕ) : ℝ) ^ 6) :=
    (norm_tsum_le_tsum_norm hszNorm).trans htsum
  have htailBound := shiftedSixthPowerTail_le hn
  unfold polygammaFiveSeries
  rw [norm_mul, Complex.norm_ofNat]
  calc
    (120 : ℝ) * ‖∑' k : ℕ, (z + (k : ℂ))⁻¹ ^ 6‖ ≤
        120 * (∑' k : ℕ, 1 / (((n + k : ℕ) : ℝ) ^ 6)) := by
      gcongr
    _ ≤ 120 * (1 / (5 * (((n - 1 : ℕ) : ℝ) ^ 5))) := by
      gcongr
    _ = 24 / (((n - 1 : ℕ) : ℝ) ^ 5) := by
      have hbase : 0 < ((n - 1 : ℕ) : ℝ) := by
        exact_mod_cast Nat.sub_pos_of_lt (by omega : 1 < n)
      field_simp [ne_of_gt (pow_pos hbase 5)] <;> norm_num

/-- The single-term tail in the manuscript's derivative notation. -/
theorem iteratedDeriv_five_digamma_norm_le {z : ℂ} {n : ℕ}
    (hn : 2 ≤ n) (hz : (n : ℝ) ≤ z.re) :
    ‖iteratedDeriv 5 Complex.digamma z‖ ≤
      24 / (((n - 1 : ℕ) : ℝ) ^ 5) := by
  have hz1 : 1 < z.re := lt_of_lt_of_le (by exact_mod_cast hn) hz
  rw [iteratedDeriv_five_digamma_eq_polygammaFiveSeries hz1]
  exact polygammaFiveSeries_norm_le hn hz

/-- The exact displayed sixth residual, with the sixth derivative of
`h = Log M` supplied as the explicit value `hSix`. -/
def manuscriptSixthResidualValue
    (hSix : ℂ) (n : ℕ) (A B C D z : ℂ) : ℂ :=
  hSix + iteratedDeriv 5 Complex.digamma (B + z) -
    iteratedDeriv 5 Complex.digamma ((n : ℂ) + 1 / 2 + z) -
    iteratedDeriv 5 Complex.digamma (A + z) +
    iteratedDeriv 5 Complex.digamma (D + z) -
    iteratedDeriv 5 Complex.digamma (C + z)

/-- Exact regrouping of the residual into its two paired differences and
the distant `A` tail. -/
theorem manuscriptSixthResidualValue_eq_paired
    (hSix : ℂ) (n : ℕ) (A B C D z : ℂ) :
    manuscriptSixthResidualValue hSix n A B C D z =
      hSix +
        (iteratedDeriv 5 Complex.digamma (B + z) -
          iteratedDeriv 5 Complex.digamma (C + z)) +
        (iteratedDeriv 5 Complex.digamma (D + z) -
          iteratedDeriv 5 Complex.digamma ((n : ℂ) + 1 / 2 + z)) -
        iteratedDeriv 5 Complex.digamma (A + z) := by
  unfold manuscriptSixthResidualValue
  ring

/-- Quantitative residual assembly from one `h⁽⁶⁾` bound, the two
paired parameter displacements, and the distant `A` tail. -/
theorem manuscriptSixthResidualValue_norm_le
    {hSix A B C D z : ℂ} {n m : ℕ} {H : ℝ}
    (hm : 2 ≤ m)
    (hh : ‖hSix‖ ≤ H)
    (hB : (m : ℝ) ≤ (B + z).re)
    (hC : (m : ℝ) ≤ (C + z).re)
    (hD : (m : ℝ) ≤ (D + z).re)
    (hhalf : (m : ℝ) ≤ ((n : ℂ) + 1 / 2 + z).re)
    (hA : (m : ℝ) ≤ (A + z).re) :
    ‖manuscriptSixthResidualValue hSix n A B C D z‖ ≤
      H + 120 * ‖B - C‖ / (((m - 1 : ℕ) : ℝ) ^ 6) +
        120 * ‖D - ((n : ℂ) + 1 / 2)‖ /
          (((m - 1 : ℕ) : ℝ) ^ 6) +
        24 / (((m - 1 : ℕ) : ℝ) ^ 5) := by
  have hBC := iteratedDeriv_five_digamma_pair_norm_le hm hB hC
  have hDhalf := iteratedDeriv_five_digamma_pair_norm_le hm hD hhalf
  have hAtail := iteratedDeriv_five_digamma_norm_le hm hA
  have hBC' :
      ‖iteratedDeriv 5 Complex.digamma (B + z) -
          iteratedDeriv 5 Complex.digamma (C + z)‖ ≤
        120 * ‖B - C‖ / (((m - 1 : ℕ) : ℝ) ^ 6) := by
    simpa only [add_sub_add_right_eq_sub] using hBC
  have hDhalf' :
      ‖iteratedDeriv 5 Complex.digamma (D + z) -
          iteratedDeriv 5 Complex.digamma ((n : ℂ) + 1 / 2 + z)‖ ≤
        120 * ‖D - ((n : ℂ) + 1 / 2)‖ /
          (((m - 1 : ℕ) : ℝ) ^ 6) := by
    simpa only [add_sub_add_right_eq_sub] using hDhalf
  rw [manuscriptSixthResidualValue_eq_paired]
  calc
    ‖hSix +
          (iteratedDeriv 5 Complex.digamma (B + z) -
            iteratedDeriv 5 Complex.digamma (C + z)) +
          (iteratedDeriv 5 Complex.digamma (D + z) -
            iteratedDeriv 5 Complex.digamma ((n : ℂ) + 1 / 2 + z)) -
          iteratedDeriv 5 Complex.digamma (A + z)‖ ≤
        ((‖hSix‖ +
            ‖iteratedDeriv 5 Complex.digamma (B + z) -
              iteratedDeriv 5 Complex.digamma (C + z)‖) +
          ‖iteratedDeriv 5 Complex.digamma (D + z) -
            iteratedDeriv 5 Complex.digamma ((n : ℂ) + 1 / 2 + z)‖) +
          ‖iteratedDeriv 5 Complex.digamma (A + z)‖ := by
      exact (norm_sub_le _ _).trans
        (add_le_add
          ((norm_add_le _ _).trans
            (add_le_add (norm_add_le _ _) (le_refl _)))
          (le_refl _))
    _ ≤
        ((H + 120 * ‖B - C‖ / (((m - 1 : ℕ) : ℝ) ^ 6)) +
          120 * ‖D - ((n : ℂ) + 1 / 2)‖ /
            (((m - 1 : ℕ) : ℝ) ^ 6)) +
          24 / (((m - 1 : ℕ) : ℝ) ^ 5) := by
      gcongr

/-- Sharper residual assembly with a separate integer anchor for the distant
`A` parameter.  This retains the logarithmic gain which is lost if all five
polygamma arguments are bounded using the common `n/4` anchor. -/
theorem manuscriptSixthResidualValue_norm_le_separateA
    {hSix A B C D z : ℂ} {n m mA : ℕ} {H : ℝ}
    (hm : 2 ≤ m) (hmA : 2 ≤ mA)
    (hh : ‖hSix‖ ≤ H)
    (hB : (m : ℝ) ≤ (B + z).re)
    (hC : (m : ℝ) ≤ (C + z).re)
    (hD : (m : ℝ) ≤ (D + z).re)
    (hhalf : (m : ℝ) ≤ ((n : ℂ) + 1 / 2 + z).re)
    (hA : (mA : ℝ) ≤ (A + z).re) :
    ‖manuscriptSixthResidualValue hSix n A B C D z‖ ≤
      H + 120 * ‖B - C‖ / (((m - 1 : ℕ) : ℝ) ^ 6) +
        120 * ‖D - ((n : ℂ) + 1 / 2)‖ /
          (((m - 1 : ℕ) : ℝ) ^ 6) +
        24 / (((mA - 1 : ℕ) : ℝ) ^ 5) := by
  have hBC := iteratedDeriv_five_digamma_pair_norm_le hm hB hC
  have hDhalf := iteratedDeriv_five_digamma_pair_norm_le hm hD hhalf
  have hAtail := iteratedDeriv_five_digamma_norm_le hmA hA
  have hBC' :
      ‖iteratedDeriv 5 Complex.digamma (B + z) -
          iteratedDeriv 5 Complex.digamma (C + z)‖ ≤
        120 * ‖B - C‖ / (((m - 1 : ℕ) : ℝ) ^ 6) := by
    simpa only [add_sub_add_right_eq_sub] using hBC
  have hDhalf' :
      ‖iteratedDeriv 5 Complex.digamma (D + z) -
          iteratedDeriv 5 Complex.digamma ((n : ℂ) + 1 / 2 + z)‖ ≤
        120 * ‖D - ((n : ℂ) + 1 / 2)‖ /
          (((m - 1 : ℕ) : ℝ) ^ 6) := by
    simpa only [add_sub_add_right_eq_sub] using hDhalf
  rw [manuscriptSixthResidualValue_eq_paired]
  calc
    ‖hSix +
          (iteratedDeriv 5 Complex.digamma (B + z) -
            iteratedDeriv 5 Complex.digamma (C + z)) +
          (iteratedDeriv 5 Complex.digamma (D + z) -
            iteratedDeriv 5 Complex.digamma ((n : ℂ) + 1 / 2 + z)) -
          iteratedDeriv 5 Complex.digamma (A + z)‖ ≤
        ((‖hSix‖ +
            ‖iteratedDeriv 5 Complex.digamma (B + z) -
              iteratedDeriv 5 Complex.digamma (C + z)‖) +
          ‖iteratedDeriv 5 Complex.digamma (D + z) -
            iteratedDeriv 5 Complex.digamma ((n : ℂ) + 1 / 2 + z)‖) +
          ‖iteratedDeriv 5 Complex.digamma (A + z)‖ := by
      exact (norm_sub_le _ _).trans
        (add_le_add
          ((norm_add_le _ _).trans
            (add_le_add (norm_add_le _ _) (le_refl _)))
          (le_refl _))
    _ ≤
        ((H + 120 * ‖B - C‖ / (((m - 1 : ℕ) : ℝ) ^ 6)) +
          120 * ‖D - ((n : ℂ) + 1 / 2)‖ /
            (((m - 1 : ℕ) : ℝ) ^ 6)) +
          24 / (((mA - 1 : ℕ) : ℝ) ^ 5) := by
      gcongr

/-- The part of `h⁽⁶⁾` already produced by the formal xi theorem: a
moving-saddle main value plus the actual sixth derivative of the logarithmic
relative error. -/
def manuscriptXiSixthLogDecomposition (mainSix z : ℂ) : ℂ :=
  mainSix + iteratedDeriv 6 manuscriptXiLogRelativeError z

/-- Uniform bound for the already-identified logarithmic-error part of
`h⁽⁶⁾` on the complex half-disc. -/
theorem manuscriptXiSixthLogDecomposition_norm_le
    {x : ℝ} (hx : Real.exp (leanSaddleCutoff + 2) < x)
    {z mainSix : ℂ} {Hmain : ℝ}
    (hz : z ∈ Metric.closedBall (x : ℂ) (manuscriptInteriorCauchyRadius x))
    (hmain : ‖mainSix‖ ≤ Hmain) :
    ‖manuscriptXiSixthLogDecomposition mainSix z‖ ≤
      Hmain + Nat.factorial 6 * ((3 / 2 : ℝ) * manuscriptCauchyEpsilon x) /
        manuscriptInteriorCauchyRadius x ^ 6 := by
  have herr := manuscriptXiLogRelativeError_derivatives_through_six_on_half_disc
    hx hz 6 (by norm_num)
  unfold manuscriptXiSixthLogDecomposition
  exact (norm_add_le _ _).trans (add_le_add hmain herr)

/-- End-to-end residual inequality for the part of the manuscript chain now
identified with the actual xi logarithmic error.  Only the moving-saddle
sixth derivative remains as the explicit `mainSix` input. -/
theorem manuscriptSixthResidualValue_of_xiDecomposition_norm_le
    {x : ℝ} (hx : Real.exp (leanSaddleCutoff + 2) < x)
    {z mainSix A B C D : ℂ} {n m : ℕ} {Hmain : ℝ}
    (hz : (n : ℂ) + z ∈
      Metric.closedBall (x : ℂ) (manuscriptInteriorCauchyRadius x))
    (hmain : ‖mainSix‖ ≤ Hmain)
    (hm : 2 ≤ m)
    (hB : (m : ℝ) ≤ (B + z).re)
    (hC : (m : ℝ) ≤ (C + z).re)
    (hD : (m : ℝ) ≤ (D + z).re)
    (hhalf : (m : ℝ) ≤ ((n : ℂ) + 1 / 2 + z).re)
    (hA : (m : ℝ) ≤ (A + z).re) :
    ‖manuscriptSixthResidualValue
        (manuscriptXiSixthLogDecomposition mainSix ((n : ℂ) + z))
          n A B C D z‖ ≤
      (Hmain + Nat.factorial 6 *
        ((3 / 2 : ℝ) * manuscriptCauchyEpsilon x) /
          manuscriptInteriorCauchyRadius x ^ 6) +
        120 * ‖B - C‖ / (((m - 1 : ℕ) : ℝ) ^ 6) +
        120 * ‖D - ((n : ℂ) + 1 / 2)‖ /
          (((m - 1 : ℕ) : ℝ) ^ 6) +
        24 / (((m - 1 : ℕ) : ℝ) ^ 5) := by
  apply manuscriptSixthResidualValue_norm_le hm
    (manuscriptXiSixthLogDecomposition_norm_le hx hz hmain)
    hB hC hD hhalf hA

end Zeta23.Research.JensenWedge
