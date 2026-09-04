import Zeta23.Research.JensenWedge.ManuscriptCoefficientMain
import Zeta23.GammaFacts.StirlingRight

/-!
# Bounds for the manuscript-main correction

This module estimates the three exact factors in `manuscriptMainCorrection`.
The elementary reindexing factor is treated by the same exact one-step
logarithm expansion used in the independently developed Gamma/Stirling
library; the other factors use the checked saddle box and curvature bounds.
-/

namespace Zeta23.Research.JensenWedge

open Complex Set

noncomputable section

/-- A single exponential character for the elementary factor `R_N`. -/
def coefficientReindexLogError (N : ℂ) : ℂ :=
  2 + log (N + 1) + (N + 1 / 2) * log N -
    (N + 3 / 2) * log (N + 2)

theorem coefficientReindexCorrection_eq_exp_logError
    {N : ℂ} (hNre : 0 < N.re) :
    coefficientReindexCorrection N = exp (coefficientReindexLogError N) := by
  have hN1ne : N + 1 ≠ 0 := by
    intro h
    have := congrArg Complex.re h
    norm_num at this
    linarith
  unfold coefficientReindexCorrection
  calc
    exp 2 * (N + 1) *
        exp ((N + 1 / 2) * log N - (N + 3 / 2) * log (N + 2)) =
      exp 2 * exp (log (N + 1)) *
        exp ((N + 1 / 2) * log N -
          (N + 3 / 2) * log (N + 2)) := by
            rw [exp_log hN1ne]
    _ = exp (2 + log (N + 1) +
        ((N + 1 / 2) * log N -
          (N + 3 / 2) * log (N + 2))) := by
            rw [Complex.exp_add, Complex.exp_add]
    _ = exp (coefficientReindexLogError N) := by
            congr 1
            unfold coefficientReindexLogError
            ring

/-- Exact second-order expansion of the logarithm of `R_N`. -/
theorem coefficientReindexLogError_eq_rational_eps
    {N : ℂ} (hNre : 0 < N.re) :
    coefficientReindexLogError N =
      1 / (4 * N ^ 2) + 1 / (4 * (N + 1) ^ 2) -
        (N + 1 / 2) * Zeta23.StirlingVert.eps N 0 -
        (N + 3 / 2) * Zeta23.StirlingVert.eps (N + 1) 0 := by
  have hN1re : 0 < (N + 1).re := by simp; linarith
  have hNne : N ≠ 0 := by
    intro h
    rw [h] at hNre
    simp at hNre
  have hN1ne : N + 1 ≠ 0 := by
    intro h
    have := congrArg Complex.re h
    norm_num at this
    linarith
  have hlog0 := Zeta23.StirlingVert.log_one_add_sub_log hNre
  have hlog1 := Zeta23.StirlingVert.log_one_add_sub_log hN1re
  have hN1 : log (N + 1) = log N +
      (N⁻¹ - (1 / 2 : ℂ) / N ^ 2 + Zeta23.StirlingVert.eps N 0) := by
    rw [← hlog0]
    ring
  have hN2 : log (N + 2) = log (N + 1) +
      ((N + 1)⁻¹ - (1 / 2 : ℂ) / (N + 1) ^ 2 +
        Zeta23.StirlingVert.eps (N + 1) 0) := by
    have hlog1' : log (N + 2) - log (N + 1) =
        (N + 1)⁻¹ - (1 / 2 : ℂ) / (N + 1) ^ 2 +
          Zeta23.StirlingVert.eps (N + 1) 0 := by
      convert hlog1 using 1 <;> ring
    rw [← hlog1']
    ring
  rw [coefficientReindexLogError, hN2, hN1]
  field_simp [hNne, hN1ne]
  ring

/-- On the fixed narrow sector the real part controls the full norm. -/
theorem leanSaddleSector_norm_le_two_re
    {s : ℂ} (hs : s ∈ leanSaddleSector) :
    ‖s‖ ≤ 2 * s.re := by
  have harg : |s.arg| ≤ 1 / 100 := by
    simpa only [saddleProofAngle] using hs.2.le
  have hargSq : s.arg ^ 2 ≤ (1 / 100 : ℝ) ^ 2 := by
    rw [sq_le_sq]
    simpa using harg
  have hcosBase := Real.one_sub_sq_div_two_le_cos (x := s.arg)
  have hcos : 1 / 2 ≤ Real.cos s.arg := by
    calc
      (1 / 2 : ℝ) ≤ 1 - s.arg ^ 2 / 2 := by nlinarith
      _ ≤ Real.cos s.arg := hcosBase
  have hid := Complex.norm_mul_cos_arg s
  have hnorm := norm_nonneg s
  nlinarith

/-- The exact logarithm of `R_N` has a uniform quadratic bound. -/
theorem coefficientReindexLogError_norm_le
    {N : ℂ} (hN : N ∈ leanSaddleSector) :
    ‖coefficientReindexLogError N‖ ≤ 16 / ‖N‖ ^ 2 := by
  let r : ℝ := N.re
  have hr : 0 < r := by
    simpa only [r] using leanSaddleSector_re_pos hN
  have hrOne : 1 ≤ r := by
    have hlarge := leanSaddleSector_parameterNorm_ge_fiveHundredBillion hN
    have hupper := leanSaddleSector_norm_le_two_re hN
    nlinarith
  have hNupper : ‖N‖ ≤ 2 * r := by
    simpa only [r] using leanSaddleSector_norm_le_two_re hN
  have hNlower : r ≤ ‖N‖ := by
    simpa only [r] using Complex.re_le_norm N
  have hNpos : 0 < ‖N‖ := lt_of_lt_of_le hr hNlower
  have hN1lower : r ≤ ‖N + 1‖ := by
    have h := Complex.re_le_norm (N + 1)
    simp only [add_re, one_re] at h
    dsimp only [r]
    linarith
  have hN1re : 0 < (N + 1).re := by simp; linarith
  have hNhalf : ‖N + 1 / 2‖ ≤ 3 * r := by
    calc
      ‖N + 1 / 2‖ ≤ ‖N‖ + ‖(1 / 2 : ℂ)‖ := norm_add_le _ _
      _ ≤ 2 * r + 1 / 2 := by norm_num; linarith
      _ ≤ 3 * r := by linarith
  have hNthreeHalf : ‖N + 3 / 2‖ ≤ 4 * r := by
    calc
      ‖N + 3 / 2‖ ≤ ‖N‖ + ‖(3 / 2 : ℂ)‖ := norm_add_le _ _
      _ ≤ 2 * r + 3 / 2 := by norm_num; linarith
      _ ≤ 4 * r := by linarith
  have hrat0 : ‖1 / (4 * N ^ 2)‖ ≤ 1 / (4 * r ^ 2) := by
    rw [norm_div, norm_one, norm_mul, norm_pow]
    norm_num
    rw [inv_le_inv₀ (sq_pos_of_pos hNpos) (sq_pos_of_pos hr)]
    exact pow_le_pow_left₀ hr.le hNlower 2
  have hrat1 : ‖1 / (4 * (N + 1) ^ 2)‖ ≤ 1 / (4 * r ^ 2) := by
    rw [norm_div, norm_one, norm_mul, norm_pow]
    norm_num
    have hN1pos : 0 < ‖N + 1‖ := lt_of_lt_of_le hr hN1lower
    rw [inv_le_inv₀ (sq_pos_of_pos hN1pos) (sq_pos_of_pos hr)]
    exact pow_le_pow_left₀ hr.le hN1lower 2
  have heps0 := Zeta23.StirlingRight.norm_eps_zero_le_re
    (w := N) (by simpa only [r] using hr)
  have heps1base := Zeta23.StirlingRight.norm_eps_zero_le_re hN1re
  have heps1 : ‖Zeta23.StirlingVert.eps (N + 1) 0‖ ≤
      (1 / 3) / r ^ 3 := by
    refine heps1base.trans ?_
    simp only [add_re, one_re]
    apply div_le_div_of_nonneg_left (by norm_num) (by positivity)
    have : r ≤ N.re + 1 := by dsimp only [r]; linarith
    gcongr
  have hterm0 : ‖(N + 1 / 2) * Zeta23.StirlingVert.eps N 0‖ ≤
      1 / r ^ 2 := by
    rw [norm_mul]
    calc
      ‖N + 1 / 2‖ * ‖Zeta23.StirlingVert.eps N 0‖ ≤
          (3 * r) * ((1 / 3) / r ^ 3) := by gcongr
      _ = 1 / r ^ 2 := by field_simp
  have hterm1 : ‖(N + 3 / 2) * Zeta23.StirlingVert.eps (N + 1) 0‖ ≤
      2 / r ^ 2 := by
    rw [norm_mul]
    calc
      ‖N + 3 / 2‖ * ‖Zeta23.StirlingVert.eps (N + 1) 0‖ ≤
          (4 * r) * ((1 / 3) / r ^ 3) := by gcongr
      _ ≤ 2 / r ^ 2 := by
        field_simp
        nlinarith [sq_pos_of_pos hr]
  rw [coefficientReindexLogError_eq_rational_eps
    (by simpa only [r] using hr)]
  have hraw :
      ‖1 / (4 * N ^ 2) + 1 / (4 * (N + 1) ^ 2) -
          (N + 1 / 2) * Zeta23.StirlingVert.eps N 0 -
          (N + 3 / 2) * Zeta23.StirlingVert.eps (N + 1) 0‖ ≤
        4 / r ^ 2 := by
    calc
      _ ≤ ‖1 / (4 * N ^ 2)‖ + ‖1 / (4 * (N + 1) ^ 2)‖ +
          ‖(N + 1 / 2) * Zeta23.StirlingVert.eps N 0‖ +
          ‖(N + 3 / 2) * Zeta23.StirlingVert.eps (N + 1) 0‖ := by
            calc
              _ ≤ ‖1 / (4 * N ^ 2) + 1 / (4 * (N + 1) ^ 2) -
                    (N + 1 / 2) * Zeta23.StirlingVert.eps N 0‖ +
                  ‖(N + 3 / 2) * Zeta23.StirlingVert.eps (N + 1) 0‖ :=
                norm_sub_le _ _
              _ ≤ (‖1 / (4 * N ^ 2) + 1 / (4 * (N + 1) ^ 2)‖ +
                    ‖(N + 1 / 2) * Zeta23.StirlingVert.eps N 0‖) +
                  ‖(N + 3 / 2) * Zeta23.StirlingVert.eps (N + 1) 0‖ := by
                gcongr
                exact norm_sub_le _ _
              _ ≤ _ := by
                gcongr
                exact norm_add_le _ _
      _ ≤ 1 / (4 * r ^ 2) + 1 / (4 * r ^ 2) +
          1 / r ^ 2 + 2 / r ^ 2 := by gcongr
      _ ≤ 4 / r ^ 2 := by
        field_simp
        nlinarith [sq_pos_of_pos hr]
  refine hraw.trans ?_
  rw [div_le_div_iff₀ (sq_pos_of_pos hr) (sq_pos_of_pos
    (norm_pos_iff.mpr (leanSaddleSector_quantitative hN).parameter_ne_zero))]
  nlinarith [sq_nonneg (‖N‖ - 2 * r)]

theorem coefficientReindexCorrection_sub_one_norm_le
    {N : ℂ} (hN : N ∈ leanSaddleSector) :
    ‖coefficientReindexCorrection N - 1‖ ≤ Real.log ‖N‖ / ‖N‖ := by
  have hNre := leanSaddleSector_re_pos hN
  have hNlarge := leanSaddleSector_parameterNorm_ge_fiveHundredBillion hN
  have hNpos : 0 < ‖N‖ := by linarith
  have hlogOne : 1 ≤ Real.log ‖N‖ := by
    have h := leanSaddleSector_log_re_gt hN
    rw [Complex.log_re] at h
    linarith
  have hE := coefficientReindexLogError_norm_le hN
  have hEone : ‖coefficientReindexLogError N‖ ≤ 1 := by
    calc
      ‖coefficientReindexLogError N‖ ≤ 16 / ‖N‖ ^ 2 := hE
      _ ≤ 1 := by
        apply (div_le_one (sq_pos_of_pos hNpos)).2
        nlinarith [sq_pos_of_pos hNpos]
  rw [coefficientReindexCorrection_eq_exp_logError hNre]
  calc
    ‖exp (coefficientReindexLogError N) - 1‖ ≤
        2 * ‖coefficientReindexLogError N‖ :=
      Complex.norm_exp_sub_one_le hEone
    _ ≤ 2 * (16 / ‖N‖ ^ 2) := by gcongr
    _ ≤ Real.log ‖N‖ / ‖N‖ := by
      field_simp
      nlinarith

private theorem real_log_le_eighth_add_six
    {x : ℝ} (hx : 0 < x) : Real.log x ≤ x / 8 + 6 := by
  have height : (8 : ℝ) ≠ 0 := by norm_num
  have hxdiv : x / 8 ≠ 0 := div_ne_zero hx.ne' height
  have hfactor : x = 8 * (x / 8) := by field_simp
  rw [hfactor, Real.log_mul height hxdiv]
  nlinarith [Real.log_le_sub_one_of_pos (show (0 : ℝ) < 8 by norm_num),
    Real.log_le_sub_one_of_pos (div_pos hx (by norm_num : (0 : ℝ) < 8))]

theorem coefficientGaussianCorrection_sub_one_norm_le
    {N : ℂ} (hN : N ∈ leanSaddleSector) :
    ‖coefficientGaussianCorrection N - 1‖ ≤
      4 * Real.log ‖N‖ / ‖N‖ := by
  let L : ℂ := quantitativeSaddleBranch N
  let K : ℂ := leadingCurvature N L
  have hNlarge := leanSaddleSector_parameterNorm_ge_fiveHundredBillion hN
  have hNpos : 0 < ‖N‖ := by linarith
  have hlogpos : 0 < Real.log ‖N‖ := by
    have h := leanSaddleSector_log_re_gt hN
    rw [Complex.log_re] at h
    linarith
  have hKre : 0 < K.re := by
    simpa only [K, L] using quantitativeSaddleBranch_curvature_re_pos hN
  have hKne : K ≠ 0 := by
    intro h
    rw [h] at hKre
    simp at hKre
  have hcurv := quantitativeSaddleBranch_curvature_inv_le_log_div_norm hN
  have hz : ‖1 / (2 * K)‖ ≤ 2 * Real.log ‖N‖ / ‖N‖ := by
    rw [norm_div, norm_one, norm_mul]
    norm_num
    have hcurv' : 1 / ‖K‖ ≤ 4 * Real.log ‖N‖ / ‖N‖ := by
      simpa only [K, L] using hcurv
    calc
      ‖K‖⁻¹ * (1 / 2) = (1 / 2) * (1 / ‖K‖) := by
        rw [one_div]
        ring
      _ ≤ (1 / 2) * (4 * Real.log ‖N‖ / ‖N‖) := by gcongr
      _ = 2 * Real.log ‖N‖ / ‖N‖ := by ring
  have hzOne : ‖1 / (2 * K)‖ ≤ 1 := by
    refine hz.trans ?_
    apply (div_le_one hNpos).2
    have hlogUpper := real_log_le_eighth_add_six hNpos
    nlinarith
  change ‖exp (1 / (2 * K)) - 1‖ ≤
    4 * Real.log ‖N‖ / ‖N‖
  calc
    ‖exp (1 / (2 * K)) - 1‖ ≤ 2 * ‖1 / (2 * K)‖ :=
      Complex.norm_exp_sub_one_le hzOne
    _ ≤ 2 * (2 * Real.log ‖N‖ / ‖N‖) := by gcongr
    _ = 4 * Real.log ‖N‖ / ‖N‖ := by ring

/-- The exact two-shift multiplier itself is separated from zero. -/
theorem coefficientMomentMultiplier_norm_lower
    {N : ℂ} (hN : N ∈ leanSaddleSector) :
    9 * ‖N‖ ^ 2 ≤ ‖coefficientMomentMultiplier N‖ := by
  have hlarge := leanSaddleSector_parameterNorm_ge_fiveHundredBillion hN
  have hplus2 : 3 / 4 * ‖N‖ ≤ ‖N + 2‖ := by
    have htri : ‖N‖ ≤ ‖N + 2‖ + 2 := by
      calc
        ‖N‖ = ‖(N + 2) - 2‖ := by ring_nf
        _ ≤ ‖N + 2‖ + ‖(2 : ℂ)‖ := norm_sub_le _ _
        _ = ‖N + 2‖ + 2 := by norm_num
    nlinarith
  have hplus1 : 3 / 4 * ‖N‖ ≤ ‖N + 1‖ := by
    have htri : ‖N‖ ≤ ‖N + 1‖ + 1 := by
      calc
        ‖N‖ = ‖(N + 1) - 1‖ := by ring_nf
        _ ≤ ‖N + 1‖ + ‖(1 : ℂ)‖ := norm_sub_le _ _
        _ = ‖N + 1‖ + 1 := by norm_num
    nlinarith
  unfold coefficientMomentMultiplier
  rw [norm_mul, norm_mul]
  norm_num
  nlinarith [mul_le_mul hplus2 hplus1
    (mul_nonneg (by norm_num) (norm_nonneg N)) (norm_nonneg (N + 2))]

theorem coefficientCancellationCorrection_sub_one_norm_le
    {N : ℂ} (hN : N ∈ leanSaddleSector) :
    ‖coefficientCancellationCorrection N - 1‖ ≤
      Real.log ‖N‖ / ‖N‖ := by
  let L : ℂ := quantitativeSaddleBranch N
  let c : ℂ := coefficientMomentMultiplier N
  have hNlarge := leanSaddleSector_parameterNorm_ge_fiveHundredBillion hN
  have hNpos : 0 < ‖N‖ := by linarith
  have hlogpos : 0 < Real.log ‖N‖ := by
    have h := leanSaddleSector_log_re_gt hN
    rw [Complex.log_re] at h
    linarith
  have hlogUpper : Real.log ‖N‖ ≤ ‖N‖ := by
    have hbase := Real.log_le_sub_one_of_pos hNpos
    linarith
  have hL := quantitativeSaddleBranch_norm_le_two_log_norm hN
  have hc := coefficientMomentMultiplier_norm_lower hN
  have hcpos : 0 < ‖c‖ := by
    dsimp only [c]
    nlinarith [sq_pos_of_pos hNpos]
  change ‖(1 - L ^ 2 / c) - 1‖ ≤ Real.log ‖N‖ / ‖N‖
  have hnorm : ‖(1 - L ^ 2 / c) - 1‖ = ‖L‖ ^ 2 / ‖c‖ := by
    rw [show (1 - L ^ 2 / c) - 1 = -(L ^ 2 / c) by ring,
      norm_neg, norm_div, norm_pow]
  rw [hnorm]
  calc
    ‖L‖ ^ 2 / ‖c‖ ≤
        (2 * Real.log ‖N‖) ^ 2 / (9 * ‖N‖ ^ 2) := by
      apply div_le_div₀ (sq_nonneg _)
        (pow_le_pow_left₀ (norm_nonneg L) hL 2) (by positivity) hc
    _ ≤ Real.log ‖N‖ / ‖N‖ := by
      rw [div_le_div_iff₀ (by positivity : 0 < 9 * ‖N‖ ^ 2) hNpos]
      have hfour : 4 * Real.log ‖N‖ ≤ 9 * ‖N‖ := by nlinarith
      have hprod := mul_le_mul_of_nonneg_right hfour
        (mul_nonneg hlogpos.le hNpos.le)
      nlinarith

/-- The product of the three suppressed factors is uniformly near one. -/
theorem manuscriptMainCorrection_sub_one_norm_le
    {M : ℂ} (hM : M ∈ leanXiCoefficientSector) :
    let N := coefficientMellinParameter M
    ‖manuscriptMainCorrection M - 1‖ ≤
      20 * Real.log ‖N‖ / ‖N‖ := by
  let N : ℂ := coefficientMellinParameter M
  let R : ℂ := coefficientReindexCorrection N
  let G : ℂ := coefficientGaussianCorrection N
  let C : ℂ := coefficientCancellationCorrection N
  let q : ℝ := Real.log ‖N‖ / ‖N‖
  have hN : N ∈ leanSaddleSector :=
    leanTwoShiftAdmissible_base (leanCoefficientSector_admissible hM.2)
  have hNlarge := leanSaddleSector_parameterNorm_ge_fiveHundredBillion hN
  have hNpos : 0 < ‖N‖ := by linarith
  have hlogpos : 0 < Real.log ‖N‖ := by
    have h := leanSaddleSector_log_re_gt hN
    rw [Complex.log_re] at h
    linarith
  have hqnonneg : 0 ≤ q := div_nonneg hlogpos.le hNpos.le
  have hqone : q ≤ 1 := by
    apply (div_le_one hNpos).2
    nlinarith [Real.log_le_sub_one_of_pos hNpos]
  have hR : ‖R - 1‖ ≤ q := by
    simpa only [R, q] using coefficientReindexCorrection_sub_one_norm_le hN
  have hG : ‖G - 1‖ ≤ 4 * q := by
    dsimp only [G, q]
    convert coefficientGaussianCorrection_sub_one_norm_le hN using 1 <;> ring
  have hC : ‖C - 1‖ ≤ q := by
    simpa only [C, q] using coefficientCancellationCorrection_sub_one_norm_le hN
  have hGnorm : ‖G‖ ≤ 5 := by
    have htri : ‖G‖ ≤ ‖G - 1‖ + 1 := by
      calc
        ‖G‖ = ‖(G - 1) + 1‖ := by ring_nf
        _ ≤ ‖G - 1‖ + ‖(1 : ℂ)‖ := norm_add_le _ _
        _ = ‖G - 1‖ + 1 := by norm_num
    linarith
  have hCnorm : ‖C‖ ≤ 2 := by
    have htri : ‖C‖ ≤ ‖C - 1‖ + 1 := by
      calc
        ‖C‖ = ‖(C - 1) + 1‖ := by ring_nf
        _ ≤ ‖C - 1‖ + ‖(1 : ℂ)‖ := norm_add_le _ _
        _ = ‖C - 1‖ + 1 := by norm_num
    linarith
  dsimp only [manuscriptMainCorrection]
  change ‖R * G * C - 1‖ ≤ 20 * Real.log ‖N‖ / ‖N‖
  have hright : 20 * Real.log ‖N‖ / ‖N‖ = 20 * q := by
    dsimp only [q]
    ring
  rw [hright]
  have hid : R * G * C - 1 = (R - 1) * G * C + (G - 1) * C + (C - 1) := by
    ring
  rw [hid]
  calc
    ‖(R - 1) * G * C + (G - 1) * C + (C - 1)‖ ≤
        ‖(R - 1) * G * C‖ + ‖(G - 1) * C‖ + ‖C - 1‖ := by
      calc
        _ ≤ ‖(R - 1) * G * C + (G - 1) * C‖ + ‖C - 1‖ :=
          norm_add_le _ _
        _ ≤ _ := by gcongr; exact norm_add_le _ _
    _ = (‖R - 1‖ * ‖G‖ * ‖C‖) +
        (‖G - 1‖ * ‖C‖) + ‖C - 1‖ := by rw [norm_mul, norm_mul, norm_mul]
    _ ≤ (q * 5 * 2) + ((4 * q) * 2) + q := by gcongr
    _ ≤ 20 * q := by nlinarith

end

end Zeta23.Research.JensenWedge
