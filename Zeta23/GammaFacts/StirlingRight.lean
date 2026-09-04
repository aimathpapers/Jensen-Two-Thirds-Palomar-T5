import Zeta23.GammaFacts.StirlingVert

/-!
# Effective digamma Stirling bound in the right half-plane

This module reuses the exact unit-interval Euler--Maclaurin identities from
`StirlingVert`, but controls every denominator by its real part.  It proves a
uniform `O((Re w)^{-2})` remainder for `digamma w` at the noninteger points of
the remote right half-plane.  The `integerComplement` hypothesis reflects the
scope of the repository's partial-fraction-series producer; it is sufficient
for the line-segment transport used by the sectorial Gamma theorem.
-/

noncomputable section

namespace Zeta23
namespace StirlingRight

open Complex Filter Topology MeasureTheory intervalIntegral Set
open StirlingVert

theorem re_add_le_norm_add {w : ℂ} (x : ℝ) :
    w.re + x ≤ ‖(x : ℂ) + w‖ := by
  have h := Complex.re_le_norm ((x : ℂ) + w)
  simpa [add_comm] using h

theorem norm_eps_le_re {w : ℂ} (hw : 0 < w.re) {m : ℝ} (hm : 0 ≤ m) :
    ‖eps w m‖ ≤ 1 / (3 * ‖(m : ℂ) + w‖ ^ 2 * (w.re + m)) := by
  have hmw := add_ne_zero hw hm
  have hM : 0 < ‖(m : ℂ) + w‖ := norm_pos_iff.mpr hmw
  have hR : 0 < w.re + m := by linarith
  unfold eps
  calc ‖∫ x in m..(m + 1), ((x - m : ℝ) : ℂ) ^ 2 /
          (((m : ℂ) + w) ^ 2 * ((x : ℂ) + w))‖
      ≤ ∫ x in m..(m + 1), ‖((x - m : ℝ) : ℂ) ^ 2 /
          (((m : ℂ) + w) ^ 2 * ((x : ℂ) + w))‖ :=
        intervalIntegral.norm_integral_le_integral_norm (by linarith)
    _ ≤ ∫ x in m..(m + 1), (x - m) ^ 2 /
          (‖(m : ℂ) + w‖ ^ 2 * (w.re + m)) := by
        apply intervalIntegral.integral_mono_on (by linarith)
        · refine (ContinuousOn.intervalIntegrable ?_).norm
          apply ContinuousOn.div (by fun_prop) (by fun_prop)
          intro x hx
          rw [uIcc_of_le (by linarith)] at hx
          exact mul_ne_zero (pow_ne_zero _ hmw) (add_ne_zero hw (by linarith [hx.1]))
        · exact (by fun_prop : Continuous fun x : ℝ =>
              (x - m) ^ 2 / (‖(m : ℂ) + w‖ ^ 2 * (w.re + m)))
            |>.intervalIntegrable _ _
        · intro x hx
          have hxw : w.re + m ≤ ‖(x : ℂ) + w‖ := by
            have := re_add_le_norm_add (w := w) x
            linarith [hx.1]
          rw [norm_div, norm_mul, norm_pow, norm_pow, Complex.norm_real, Real.norm_eq_abs,
            sq_abs]
          apply div_le_div_of_nonneg_left (sq_nonneg _) (by positivity)
          exact mul_le_mul_of_nonneg_left hxw (by positivity)
    _ = 1 / (3 * ‖(m : ℂ) + w‖ ^ 2 * (w.re + m)) := by
        rw [intervalIntegral.integral_div,
          intervalIntegral.integral_comp_sub_right (fun u : ℝ => u ^ 2) m]
        simp only [sub_self, add_sub_cancel_left, integral_pow]
        norm_num
        field_simp

section Seq

variable {w : ℂ}

theorem norm_rho_le_re (hw : 0 < w.re) (n : ℕ) :
    ‖rho w n‖ ≤
      1 / (‖(n : ℂ) + 1 + w‖ ^ 2 * (w.re + (n : ℝ) + 2)) := by
  have hR : 0 < w.re + (n : ℝ) + 2 := by positivity
  have hn2 : w.re + (n : ℝ) + 2 ≤ ‖(n : ℂ) + 2 + w‖ := by
    have := re_add_le_norm_add (w := w) ((n : ℝ) + 2)
    convert this using 1 <;> push_cast <;> ring
  unfold rho
  rw [norm_div, norm_one, norm_mul, norm_pow]
  apply div_le_div_of_nonneg_left zero_le_one (mul_pos (sq_pos_of_pos (by
    exact norm_pos_iff.mpr (natp1_ne_zero hw n))) hR)
  exact mul_le_mul_of_nonneg_left hn2 (by positivity)

theorem norm_eps_natp1_le_re (hw : 0 < w.re) (n : ℕ) :
    ‖eps w ((n : ℝ) + 1)‖ ≤
      1 / (3 * ‖(n : ℂ) + 1 + w‖ ^ 2 * (w.re + (n : ℝ) + 1)) := by
  have h := norm_eps_le_re hw (m := (n : ℝ) + 1) (by positivity)
  convert h using 1
  all_goals push_cast; ring

theorem inv_norm_sq_le_telescope_re (hw : 0 < w.re) (n : ℕ) :
    1 / ‖(n : ℂ) + 1 + w‖ ^ 2 ≤
      1 / ((n : ℝ) + w.re) - 1 / ((n : ℝ) + 1 + w.re) := by
  have hnorm : (n : ℝ) + 1 + w.re ≤ ‖(n : ℂ) + 1 + w‖ := by
    have := re_add_le_norm_add (w := w) ((n : ℝ) + 1)
    convert this using 1 <;> push_cast <;> ring
  have h0 : 0 < (n : ℝ) + w.re := by positivity
  have h1 : 0 < (n : ℝ) + 1 + w.re := by positivity
  have hsq : ((n : ℝ) + w.re) * ((n : ℝ) + 1 + w.re) ≤
      ‖(n : ℂ) + 1 + w‖ ^ 2 := by
    have hleft : (n : ℝ) + w.re ≤ ‖(n : ℂ) + 1 + w‖ := by linarith
    nlinarith [norm_nonneg ((n : ℂ) + 1 + w)]
  rw [show 1 / ((n : ℝ) + w.re) - 1 / ((n : ℝ) + 1 + w.re) =
      1 / (((n : ℝ) + w.re) * ((n : ℝ) + 1 + w.re)) by field_simp; ring]
  exact div_le_div_of_nonneg_left zero_le_one (mul_pos h0 h1) hsq

theorem sum_inv_norm_sq_le_re (hw : 0 < w.re) (N : ℕ) :
    ∑ n ∈ Finset.range N, 1 / ‖(n : ℂ) + 1 + w‖ ^ 2 ≤ 1 / w.re := by
  calc
    ∑ n ∈ Finset.range N, 1 / ‖(n : ℂ) + 1 + w‖ ^ 2
        ≤ ∑ n ∈ Finset.range N,
            (1 / ((n : ℝ) + w.re) - 1 / ((n : ℝ) + 1 + w.re)) :=
      Finset.sum_le_sum fun n _ => inv_norm_sq_le_telescope_re hw n
    _ = 1 / w.re - 1 / ((N : ℝ) + w.re) := by
      rw [Finset.sum_congr rfl (fun (i : ℕ) _ => by
        rw [show ((i : ℝ) + 1 + w.re) = (((i + 1 : ℕ) : ℝ) + w.re) by
          push_cast; ring]),
        Finset.sum_range_sub' (fun n : ℕ => 1 / ((n : ℝ) + w.re)) N]
      push_cast
      ring
    _ ≤ 1 / w.re := by
      have : 0 ≤ 1 / ((N : ℝ) + w.re) := by positivity
      linarith

theorem tsum_inv_norm_sq_le_re (hw : 0 < w.re) :
    ∑' n : ℕ, 1 / ‖(n : ℂ) + 1 + w‖ ^ 2 ≤ 1 / w.re :=
  Real.tsum_le_of_sum_range_le (fun n => by positivity) (sum_inv_norm_sq_le_re hw)

theorem norm_rho_le_re_majorant (hw : 0 < w.re) (n : ℕ) :
    ‖rho w n‖ ≤ (1 / w.re) * (1 / ‖(n : ℂ) + 1 + w‖ ^ 2) := by
  have hnorm : 0 < ‖(n : ℂ) + 1 + w‖ := norm_pos_iff.mpr (natp1_ne_zero hw n)
  calc
    ‖rho w n‖ ≤
        1 / (‖(n : ℂ) + 1 + w‖ ^ 2 * (w.re + (n : ℝ) + 2)) :=
      norm_rho_le_re hw n
    _ ≤ 1 / (‖(n : ℂ) + 1 + w‖ ^ 2 * w.re) := by
      apply one_div_le_one_div_of_le (mul_pos (sq_pos_of_pos hnorm) hw)
      have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
      have hs : 0 ≤ ‖(n : ℂ) + 1 + w‖ ^ 2 := sq_nonneg _
      nlinarith
    _ = (1 / w.re) * (1 / ‖(n : ℂ) + 1 + w‖ ^ 2) := by ring

theorem norm_eps_le_re_majorant (hw : 0 < w.re) (n : ℕ) :
    ‖eps w ((n : ℝ) + 1)‖ ≤
      (1 / (3 * w.re)) * (1 / ‖(n : ℂ) + 1 + w‖ ^ 2) := by
  have hnorm : 0 < ‖(n : ℂ) + 1 + w‖ := norm_pos_iff.mpr (natp1_ne_zero hw n)
  calc
    ‖eps w ((n : ℝ) + 1)‖ ≤
        1 / (3 * ‖(n : ℂ) + 1 + w‖ ^ 2 * (w.re + (n : ℝ) + 1)) :=
      norm_eps_natp1_le_re hw n
    _ ≤ 1 / (3 * ‖(n : ℂ) + 1 + w‖ ^ 2 * w.re) := by
      apply one_div_le_one_div_of_le (by positivity)
      have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
      have hs : 0 ≤ ‖(n : ℂ) + 1 + w‖ ^ 2 := sq_nonneg _
      nlinarith
    _ = (1 / (3 * w.re)) * (1 / ‖(n : ℂ) + 1 + w‖ ^ 2) := by ring

theorem summable_rho_re (hw : 0 < w.re) : Summable (rho w) := by
  refine Summable.of_norm_bounded ((summable_inv_norm_sq hw).mul_left (1 / w.re)) fun n => ?_
  exact norm_rho_le_re_majorant hw n

theorem summable_eps_re (hw : 0 < w.re) :
    Summable (fun n : ℕ => eps w ((n : ℝ) + 1)) := by
  refine Summable.of_norm_bounded
    ((summable_inv_norm_sq hw).mul_left (1 / (3 * w.re))) fun n => ?_
  exact norm_eps_le_re_majorant hw n

theorem summable_norm_rho_re (hw : 0 < w.re) : Summable (fun n => ‖rho w n‖) := by
  exact (summable_rho_re hw).norm

theorem summable_norm_eps_re (hw : 0 < w.re) :
    Summable (fun n : ℕ => ‖eps w ((n : ℝ) + 1)‖) := by
  exact (summable_eps_re hw).norm

theorem norm_tsum_rho_le_re (hw : 0 < w.re) :
    ‖∑' n, rho w n‖ ≤ 1 / w.re ^ 2 := by
  calc
    ‖∑' n, rho w n‖ ≤ ∑' n, ‖rho w n‖ :=
      norm_tsum_le_tsum_norm (summable_norm_rho_re hw)
    _ ≤ ∑' n : ℕ, (1 / w.re) *
        (1 / ‖(n : ℂ) + 1 + w‖ ^ 2) := by
      refine Summable.tsum_le_tsum (fun n => ?_) (summable_norm_rho_re hw)
        ((summable_inv_norm_sq hw).mul_left _)
      exact norm_rho_le_re_majorant hw n
    _ = (1 / w.re) * ∑' n : ℕ,
        1 / ‖(n : ℂ) + 1 + w‖ ^ 2 := tsum_mul_left
    _ ≤ (1 / w.re) * (1 / w.re) := by gcongr; exact tsum_inv_norm_sq_le_re hw
    _ = 1 / w.re ^ 2 := by ring

theorem norm_tsum_eps_le_re (hw : 0 < w.re) :
    ‖∑' n : ℕ, eps w ((n : ℝ) + 1)‖ ≤ (1 / 3) / w.re ^ 2 := by
  calc
    ‖∑' n : ℕ, eps w ((n : ℝ) + 1)‖ ≤
        ∑' n : ℕ, ‖eps w ((n : ℝ) + 1)‖ :=
      norm_tsum_le_tsum_norm (summable_norm_eps_re hw)
    _ ≤ ∑' n : ℕ, (1 / (3 * w.re)) *
        (1 / ‖(n : ℂ) + 1 + w‖ ^ 2) := by
      refine Summable.tsum_le_tsum (fun n => ?_) (summable_norm_eps_re hw)
        ((summable_inv_norm_sq hw).mul_left _)
      exact norm_eps_le_re_majorant hw n
    _ = (1 / (3 * w.re)) * ∑' n : ℕ,
        1 / ‖(n : ℂ) + 1 + w‖ ^ 2 := tsum_mul_left
    _ ≤ (1 / (3 * w.re)) * (1 / w.re) := by
      gcongr
      exact tsum_inv_norm_sq_le_re hw
    _ = (1 / 3) / w.re ^ 2 := by ring

/-- The exact digamma identity, with convergence controlled by the real part. -/
theorem digamma_eq_re (hw : 0 < w.re) (hmem : w ∈ Complex.integerComplement) :
    Complex.digamma w = Complex.log (1 + w) - 1 / w - (1 / 2 : ℂ) * (1 + w)⁻¹
      - (1 / 2 : ℂ) * (∑' n, rho w n) + ∑' n : ℕ, eps w ((n : ℝ) + 1) := by
  have hL := (Zeta23.DigammaSeries.hasSum_digamma_series hmem).tendsto_sum_nat
  have hR : Tendsto
      (fun N : ℕ => ∑ n ∈ Finset.range N,
        (1 / ((n : ℂ) + 1) - 1 / (w + n + 1))) atTop
      (𝓝 ((Real.eulerMascheroniConstant : ℂ) + Complex.log (1 + w)
        - (1 / 2 : ℂ) * ((1 + w)⁻¹ - 0 + ∑' n, rho w n)
        + ∑' n : ℕ, eps w ((n : ℝ) + 1))) := by
    have e : ∀ N : ℕ, ∑ n ∈ Finset.range N,
        (1 / ((n : ℂ) + 1) - 1 / (w + n + 1)) =
        ((∑ n ∈ Finset.range N, 1 / ((n : ℂ) + 1)) -
          Complex.log ((N : ℂ) + 1 + w)) + Complex.log (1 + w)
          - (1 / 2 : ℂ) * ((1 + w)⁻¹ - ((N : ℂ) + 1 + w)⁻¹
            + ∑ n ∈ Finset.range N, rho w n)
          + ∑ n ∈ Finset.range N, eps w ((n : ℝ) + 1) := by
      intro N
      rw [partial_sum_eq hw N]
      push_cast
      ring
    simp_rw [e]
    refine (((tendsto_harmonic_sub_clog hw).add tendsto_const_nhds).sub
      (((tendsto_const_nhds.sub (tendsto_inv_natp1 hw)).add
        (summable_rho_re hw).hasSum.tendsto_sum_nat).const_mul _)).add
      (summable_eps_re hw).hasSum.tendsto_sum_nat
  have h := tendsto_nhds_unique hL hR
  rw [sub_zero] at h
  linear_combination h

theorem norm_eps_zero_le_re (hw : 0 < w.re) :
    ‖eps w 0‖ ≤ (1 / 3) / w.re ^ 3 := by
  have h := norm_eps_le_re hw (m := 0) le_rfl
  have hwn : w.re ≤ ‖w‖ := Complex.re_le_norm w
  simp only [Complex.ofReal_zero, zero_add, add_zero] at h
  calc
    ‖eps w 0‖ ≤ 1 / (3 * ‖w‖ ^ 2 * w.re) := h
    _ ≤ 1 / (3 * w.re ^ 2 * w.re) := by
      apply one_div_le_one_div_of_le (by positivity)
      have hs : w.re ^ 2 ≤ ‖w‖ ^ 2 := by nlinarith [sq_nonneg (‖w‖ - w.re)]
      nlinarith
    _ = (1 / 3) / w.re ^ 3 := by ring

/-- Effective Stirling estimate for digamma in the remote right half-plane.
The integer points are excluded only because the repository's underlying
partial-fraction producer is currently stated on `integerComplement`. -/
theorem digamma_stirling_re
    (hw : 1 ≤ w.re) (hmem : w ∈ Complex.integerComplement) :
    ‖Complex.digamma w - Complex.log w + (1 / 2 : ℂ) / w‖ ≤
      2 / w.re ^ 2 := by
  have hw0 : 0 < w.re := lt_of_lt_of_le zero_lt_one hw
  have hwne : w ≠ 0 := fun h => by rw [h] at hw0; simp at hw0
  have h1w : 1 + w ≠ 0 := fun h => by
    have := congrArg Complex.re h
    simp at this
    linarith
  have hident := digamma_eq_re hw0 hmem
  have hlog := log_one_add_sub_log hw0
  have key : Complex.digamma w - Complex.log w + (1 / 2 : ℂ) / w =
      -(1 / 2 : ℂ) / (w ^ 2 * (1 + w)) + eps w 0
        - (1 / 2 : ℂ) * (∑' n, rho w n)
        + ∑' n : ℕ, eps w ((n : ℝ) + 1) := by
    rw [hident, show Complex.log (1 + w) =
      Complex.log w + (w⁻¹ - (1 / 2 : ℂ) / w ^ 2 + eps w 0) by
        rw [← hlog]
        ring]
    field_simp
    ring
  rw [key]
  have hnormw : w.re ≤ ‖w‖ := Complex.re_le_norm w
  have hnorm1w : 1 + w.re ≤ ‖1 + w‖ := by
    have := Complex.re_le_norm (1 + w)
    simpa using this
  have b1 : ‖-(1 / 2 : ℂ) / (w ^ 2 * (1 + w))‖ ≤
      (1 / 2) / w.re ^ 2 := by
    rw [norm_div, norm_neg, norm_mul, norm_pow]
    norm_num
    apply div_le_div_of_nonneg_left (by norm_num) (by positivity)
    have hsq : w.re ^ 2 ≤ ‖w‖ ^ 2 := by
      nlinarith [sq_nonneg (‖w‖ - w.re)]
    have hOne : 1 ≤ ‖1 + w‖ := by linarith
    nlinarith [norm_nonneg w, norm_nonneg (1 + w)]
  have b2 : ‖eps w 0‖ ≤ (1 / 3) / w.re ^ 2 := by
    refine le_trans (norm_eps_zero_le_re hw0) ?_
    apply div_le_div_of_nonneg_left (by norm_num) (by positivity)
    nlinarith [sq_nonneg w.re]
  have b3 : ‖(1 / 2 : ℂ) * ∑' n, rho w n‖ ≤ (1 / 2) / w.re ^ 2 := by
    rw [norm_mul, show ‖(1 / 2 : ℂ)‖ = 1 / 2 by norm_num]
    calc
      (1 / 2 : ℝ) * ‖∑' n, rho w n‖ ≤
          (1 / 2) * (1 / w.re ^ 2) := by
        gcongr
        exact norm_tsum_rho_le_re hw0
      _ = (1 / 2) / w.re ^ 2 := by ring
  have b4 : ‖∑' n : ℕ, eps w ((n : ℝ) + 1)‖ ≤ (1 / 3) / w.re ^ 2 :=
    norm_tsum_eps_le_re hw0
  calc
    ‖-(1 / 2 : ℂ) / (w ^ 2 * (1 + w)) + eps w 0 -
        (1 / 2 : ℂ) * ∑' n, rho w n +
        ∑' n : ℕ, eps w ((n : ℝ) + 1)‖ ≤
        ‖-(1 / 2 : ℂ) / (w ^ 2 * (1 + w))‖ + ‖eps w 0‖ +
          ‖(1 / 2 : ℂ) * ∑' n, rho w n‖ +
          ‖∑' n : ℕ, eps w ((n : ℝ) + 1)‖ := by
      have hA := norm_add_le
        (-(1 / 2 : ℂ) / (w ^ 2 * (1 + w)) + eps w 0 -
          (1 / 2 : ℂ) * ∑' n, rho w n)
        (∑' n : ℕ, eps w ((n : ℝ) + 1))
      have hB := norm_sub_le
        (-(1 / 2 : ℂ) / (w ^ 2 * (1 + w)) + eps w 0)
        ((1 / 2 : ℂ) * ∑' n, rho w n)
      have hC := norm_add_le (-(1 / 2 : ℂ) / (w ^ 2 * (1 + w))) (eps w 0)
      linarith
    _ ≤ (1 / 2) / w.re ^ 2 + (1 / 3) / w.re ^ 2 +
        (1 / 2) / w.re ^ 2 + (1 / 3) / w.re ^ 2 := by gcongr
    _ ≤ 2 / w.re ^ 2 := by
      have hpos : 0 < w.re ^ 2 := by positivity
      rw [show (1 / 2) / w.re ^ 2 + (1 / 3) / w.re ^ 2 +
          (1 / 2) / w.re ^ 2 + (1 / 3) / w.re ^ 2 =
          (5 / 3) / w.re ^ 2 by ring]
      apply div_le_div_of_nonneg_right _ hpos.le
      norm_num

/-- The digamma function is holomorphic on the open right half-plane.  This
removes the artificial integer exclusion inherited from the partial-fraction
producer when its estimates are extended by continuity. -/
theorem differentiableAt_digamma_re (hw : 0 < w.re) :
    DifferentiableAt ℂ Complex.digamma w := by
  have hzero : ∀ m : ℕ, w ≠ -(m : ℂ) := by
    intro m h
    rw [h] at hw
    simp only [Complex.neg_re, Complex.natCast_re] at hw
    nlinarith [Nat.cast_nonneg (α := ℝ) m]
  have hopen : IsOpen {z : ℂ | 0 < z.re} :=
    isOpen_lt continuous_const Complex.continuous_re
  have hGamma : AnalyticAt ℂ Complex.Gamma w := by
    rw [Complex.analyticAt_iff_eventually_differentiableAt]
    filter_upwards [hopen.mem_nhds hw] with z hz
    exact Complex.differentiableAt_Gamma z fun m hzm ↦ by
      rw [hzm] at hz
      simp only [Complex.neg_re, Complex.natCast_re] at hz
      nlinarith [Nat.cast_nonneg (α := ℝ) m]
  have hGamma_ne : Complex.Gamma w ≠ 0 := Complex.Gamma_ne_zero hzero
  have hpsi : AnalyticAt ℂ Complex.digamma w := by
    have hderiv : AnalyticAt ℂ (deriv Complex.Gamma) w := hGamma.deriv
    exact (hderiv.div hGamma hGamma_ne).congr (by
      filter_upwards with z
      rw [Complex.digamma_def, logDeriv_apply]
      rfl)
  exact hpsi.differentiableAt

/-- The right-half-plane Stirling bound has no exceptional positive integer
points.  At an integer excluded by the underlying series theorem, approach
from the upper-right direction and pass to the limit by holomorphicity. -/
theorem digamma_stirling_re_all (hw : 1 ≤ w.re) :
    ‖Complex.digamma w - Complex.log w + (1 / 2 : ℂ) / w‖ ≤
      2 / w.re ^ 2 := by
  by_cases hmem : w ∈ Complex.integerComplement
  · exact digamma_stirling_re hw hmem
  · have hw0 : 0 < w.re := lt_of_lt_of_le zero_lt_one hw
    have hwne : w ≠ 0 := fun h ↦ by rw [h] at hw0; simp at hw0
    let u : ℕ → ℂ := fun n ↦
      w + (((((n : ℝ) + 1)⁻¹ : ℝ) : ℂ) * (1 + Complex.I))
    have hu_tendsto : Tendsto u atTop (𝓝 w) := by
      have hnat : Tendsto (fun n : ℕ ↦ ((n : ℝ) + 1)⁻¹) atTop (𝓝 0) := by
        exact tendsto_inv_atTop_zero.comp
          (tendsto_atTop_add_const_right atTop (1 : ℝ) tendsto_natCast_atTop_atTop)
      have hc : Tendsto (fun n : ℕ ↦ ((((n : ℝ) + 1)⁻¹ : ℝ) : ℂ))
          atTop (𝓝 0) := by
        simpa only [Complex.ofReal_zero] using hnat.ofReal
      simpa [u] using tendsto_const_nhds.add (hc.mul_const (1 + Complex.I))
    have hu_re (n : ℕ) : 1 ≤ (u n).re := by
      simp only [u, Complex.add_re, Complex.mul_re, Complex.ofReal_re,
        Complex.ofReal_im, Complex.one_re, Complex.I_re, zero_mul, add_zero, mul_one]
      have hinv : 0 ≤ ((n : ℝ) + 1)⁻¹ := inv_nonneg.mpr (by positivity)
      linarith
    have hw_im : w.im = 0 := by
      have hw_range : ∃ j : ℤ, (j : ℂ) = w := by
        simpa only [Complex.mem_integerComplement_iff, not_not] using hmem
      obtain ⟨j, hj⟩ := hw_range
      simpa using (congrArg Complex.im hj).symm
    have hu_mem (n : ℕ) : u n ∈ Complex.integerComplement := by
      rw [Complex.mem_integerComplement_iff]
      rintro ⟨k, hk⟩
      have him := congrArg Complex.im hk
      have hpos : 0 < ((n : ℝ) + 1)⁻¹ := by positivity
      simp only [u, Complex.add_im, Complex.mul_im, Complex.ofReal_re,
        Complex.ofReal_im, Complex.I_im, Complex.one_im, zero_mul, mul_one,
        add_zero, hw_im, zero_add,
        Complex.intCast_im] at him
      linarith
    have hbound (n : ℕ) :
        ‖Complex.digamma (u n) - Complex.log (u n) + (1 / 2 : ℂ) / u n‖ ≤
          2 / (u n).re ^ 2 :=
      digamma_stirling_re (hu_re n) (hu_mem n)
    have hleft : Tendsto
        (fun n ↦ ‖Complex.digamma (u n) - Complex.log (u n) + (1 / 2 : ℂ) / u n‖)
        atTop (𝓝 ‖Complex.digamma w - Complex.log w + (1 / 2 : ℂ) / w‖) := by
      have hres : ContinuousAt
          (fun z : ℂ ↦ Complex.digamma z - Complex.log z + (1 / 2 : ℂ) / z) w :=
        ((differentiableAt_digamma_re hw0).continuousAt.sub
          (continuousAt_clog (Complex.mem_slitPlane_iff.mpr (Or.inl hw0)))).add
          (continuousAt_const.div continuousAt_id hwne)
      exact hres.norm.tendsto.comp hu_tendsto
    have hright : Tendsto (fun n ↦ 2 / (u n).re ^ 2) atTop
        (𝓝 (2 / w.re ^ 2)) := by
      have hre : Tendsto (fun n ↦ (u n).re) atTop (𝓝 w.re) :=
        Complex.continuous_re.continuousAt.tendsto.comp hu_tendsto
      exact tendsto_const_nhds.div (hre.pow 2) (by positivity)
    exact le_of_tendsto_of_tendsto hleft hright (Eventually.of_forall hbound)

end Seq

end StirlingRight
end Zeta23
