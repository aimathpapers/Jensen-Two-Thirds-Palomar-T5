import Zeta23.Research.JensenWedge.XiNaturalMainIntervalBudgets
import Zeta23.Research.JensenWedge.SixthResidualRate
import Zeta23.Research.JensenWedge.MovingSaddleDerivativeIdentification

/-!
# Explicit cutoff and the lower xi positive branch

Step 4 reduced the analytic estimates to seven scalar endpoint inequalities.
This file discharges all seven from one deliberately enormous cutoff,
`ceil (exp (10^15)) + 1`, and feeds the resulting exact xi certificate into
the positive-parameter branch theorem.

The four lower derivatives of the displayed saddle logarithm are supplied by
the kernel-checked recurrence in `MovingSaddleDerivativeIdentification`.
Thus the explicit branch constructed here has no external symbolic-algebra
premise.
-/

namespace Zeta23.Research.JensenWedge

open Complex Set

noncomputable section

/-- Logarithm of the explicit Step-5 coefficient cutoff. -/
def xiNaturalExplicitLogCutoff : ℝ := 1000000000000000

/-- First natural number strictly above `exp (10^15)`. -/
noncomputable def xiNaturalExplicitCutoffIndex : ℕ :=
  ⌈Real.exp xiNaturalExplicitLogCutoff⌉₊ + 1

/-- The displayed cutoff index really lies strictly beyond the real
exponential defining it. -/
theorem exp_explicitLogCutoff_lt_cutoffIndex :
    Real.exp xiNaturalExplicitLogCutoff <
      (xiNaturalExplicitCutoffIndex : ℝ) := by
  unfold xiNaturalExplicitCutoffIndex
  have hceil := Nat.le_ceil (Real.exp xiNaturalExplicitLogCutoff)
  push_cast
  linarith

theorem exp_explicitLogCutoff_lt_of_cutoffIndex_le
    {n : ℕ} (hn : xiNaturalExplicitCutoffIndex ≤ n) :
    Real.exp xiNaturalExplicitLogCutoff < (n : ℝ) := by
  exact exp_explicitLogCutoff_lt_cutoffIndex.trans_le (by exact_mod_cast hn)

/-- The explicit exponential cutoff dominates the fixed power used in all
subsequent elementary logarithm estimates. -/
theorem ten_pow_oneSixty_le_exp_explicitLogCutoff :
    (10 : ℝ) ^ 160 ≤ Real.exp xiNaturalExplicitLogCutoff := by
  have hpow := Real.pow_div_factorial_le_exp xiNaturalExplicitLogCutoff
    (by norm_num [xiNaturalExplicitLogCutoff] :
      (0 : ℝ) ≤ xiNaturalExplicitLogCutoff) 12
  apply le_trans ?_ hpow
  norm_num [xiNaturalExplicitLogCutoff, Nat.factorial]

private theorem real_log_le_four_sqrt_div_ten_pow_forty
    {x : ℝ} (hx : 0 < x) (hlarge : (10 : ℝ) ^ 160 ≤ x) :
    Real.log x ≤ 4 * Real.sqrt x / (10 : ℝ) ^ 40 := by
  have hsqrtpos : 0 < Real.sqrt x := Real.sqrt_pos.2 hx
  have hsqrtlarge : (10 : ℝ) ^ 80 ≤ Real.sqrt x := by
    apply Real.le_sqrt_of_sq_le
    calc
      ((10 : ℝ) ^ 80) ^ 2 = (10 : ℝ) ^ 160 := by ring
      _ ≤ x := hlarge
  have hlog := real_log_le_two_mul_div_ten_pow_forty_of_large
    hsqrtpos hsqrtlarge
  calc
    Real.log x = 2 * Real.log (Real.sqrt x) := by
      rw [Real.log_sqrt hx.le]
      ring
    _ ≤ 2 * (2 * Real.sqrt x / (10 : ℝ) ^ 40) := by gcongr
    _ = 4 * Real.sqrt x / (10 : ℝ) ^ 40 := by ring

private theorem explicitCutoff_basic_bounds
    {n : ℕ} (hn : xiNaturalExplicitCutoffIndex ≤ n) :
    let x : ℝ := n
    let N : ℝ := xiNaturalMellinCenter n
    (10 : ℝ) ^ 160 ≤ x ∧
      x ≤ N ∧ N ≤ 2 * x ∧ N + 10 ≤ 3 * x ∧
      0 < x ∧ 0 < N := by
  let x : ℝ := n
  let N : ℝ := xiNaturalMellinCenter n
  have hexp := exp_explicitLogCutoff_lt_of_cutoffIndex_le hn
  have hxlarge : (10 : ℝ) ^ 160 ≤ x :=
    ten_pow_oneSixty_le_exp_explicitLogCutoff.trans hexp.le
  have hx8 : (8 : ℝ) ≤ x := hxlarge.trans' (by norm_num)
  have hNdef : N = 2 * x - 2 := by
    simp only [N, x, xiNaturalMellinCenter]
  have hxpos : 0 < x := by positivity
  have hNpos : 0 < N := by rw [hNdef]; linarith
  refine ⟨hxlarge, ?_, ?_, ?_, hxpos, hNpos⟩
  · simp only [xiNaturalMellinCenter]
    linarith
  · simp only [xiNaturalMellinCenter]
    linarith
  · simp only [xiNaturalMellinCenter]
    linarith

private theorem explicitCutoff_log_and_scale_bounds
    {n : ℕ} (hn : xiNaturalExplicitCutoffIndex ≤ n) :
    let x : ℝ := n
    let N : ℝ := xiNaturalMellinCenter n
    xiNaturalExplicitLogCutoff < Real.log N ∧
      Real.log (N + 10) ≤ Real.log (3 * x) ∧
      Real.log N ≤ 4 * Real.sqrt N / (10 : ℝ) ^ 40 ∧
      Real.log (3 * x) ≤ 4 * Real.sqrt (3 * x) / (10 : ℝ) ^ 40 ∧
      Real.sqrt N ≤ Real.sqrt (3 * x) ∧
      Real.sqrt (3 * x) ≤ x ∧
      xiNaturalSaddleScale n ≤
        8 * Real.sqrt (3 * x) / (10 : ℝ) ^ 40 := by
  let x : ℝ := n
  let N : ℝ := xiNaturalMellinCenter n
  rcases explicitCutoff_basic_bounds hn with
    ⟨hxlarge, hxN, hN2x, hNten3x, hxpos, hNpos⟩
  have hexp := exp_explicitLogCutoff_lt_of_cutoffIndex_le hn
  have hlogLower : xiNaturalExplicitLogCutoff < Real.log N := by
    apply (Real.lt_log_iff_exp_lt hNpos).2
    exact hexp.trans_le hxN
  have hthreepos : 0 < 3 * x := by positivity
  have hlogMono : Real.log (N + 10) ≤ Real.log (3 * x) := by
    exact Real.log_le_log (by linarith) hNten3x
  have hNlarge : (10 : ℝ) ^ 160 ≤ N := hxlarge.trans hxN
  have hthreeLarge : (10 : ℝ) ^ 160 ≤ 3 * x :=
    hxlarge.trans (by nlinarith)
  have hlogN := real_log_le_four_sqrt_div_ten_pow_forty hNpos hNlarge
  have hlogThree := real_log_le_four_sqrt_div_ten_pow_forty
    hthreepos hthreeLarge
  have hsqrtN : Real.sqrt N ≤ Real.sqrt (3 * x) := by
    apply Real.sqrt_le_sqrt
    linarith
  have hsqrtThree : Real.sqrt (3 * x) ≤ x := by
    rw [Real.sqrt_le_iff]
    constructor
    · exact hxpos.le
    · nlinarith [hxlarge.trans' (by norm_num : (3 : ℝ) ≤ (10 : ℝ) ^ 160)]
  have hremote : Real.exp (leanSaddleCutoff + 2) < N := by
    have hcut : leanSaddleCutoff + 2 < xiNaturalExplicitLogCutoff := by
      norm_num [leanSaddleCutoff, xiNaturalExplicitLogCutoff]
    exact (Real.exp_lt_exp.mpr hcut).trans (hexp.trans_le hxN)
  have hsector : (N : ℂ) ∈ leanSaddleSector := by
    have hNnorm : ‖(N : ℂ)‖ = N := by
      rw [norm_real, Real.norm_eq_abs, abs_of_pos hNpos]
    constructor
    · rw [hNnorm]
      exact (Real.exp_lt_exp.mpr (by norm_num)).trans hremote
    · rw [arg_ofReal_of_nonneg hNpos.le]
      norm_num [saddleProofAngle]
  have hbranch := quantitativeSaddleBranch_norm_le_two_log_norm hsector
  have hreal := quantitativeSaddleBranch_ofReal_eq_re hNpos hsector
  have hre : 0 < (quantitativeSaddleBranch (N : ℂ)).re := by
    linarith [quantitativeSaddleBranch_re_gt hsector]
  have hscaleLog : xiNaturalSaddleScale n ≤ 2 * Real.log N := by
    rw [hreal, norm_real, Real.norm_eq_abs, abs_of_pos hre] at hbranch
    simpa only [xiNaturalSaddleScale, N, norm_real, Real.norm_eq_abs,
      abs_of_pos hNpos] using hbranch
  have hscale : xiNaturalSaddleScale n ≤
      8 * Real.sqrt (3 * x) / (10 : ℝ) ^ 40 := by
    calc
      xiNaturalSaddleScale n ≤ 2 * Real.log N := hscaleLog
      _ ≤ 2 * (4 * Real.sqrt N / (10 : ℝ) ^ 40) := by gcongr
      _ ≤ 2 * (4 * Real.sqrt (3 * x) / (10 : ℝ) ^ 40) := by gcongr
      _ = 8 * Real.sqrt (3 * x) / (10 : ℝ) ^ 40 := by ring
  exact ⟨hlogLower, hlogMono, hlogN, hlogThree, hsqrtN,
    hsqrtThree, hscale⟩

/-- All seven Step-4 endpoint conditions follow from the single explicit
coefficient cutoff. -/
theorem xiNaturalSaddleIntervalConditions_of_explicitCutoff
    {n : ℕ} (hn : xiNaturalExplicitCutoffIndex ≤ n) :
    XiNaturalSaddleIntervalConditions n := by
  let x : ℝ := n
  let N : ℝ := xiNaturalMellinCenter n
  rcases explicitCutoff_basic_bounds hn with
    ⟨hxlarge, hxN, hN2x, hNten3x, hxpos, hNpos⟩
  rcases explicitCutoff_log_and_scale_bounds hn with
    ⟨hlogLower, hlogMono, hlogN, hlogThree, hsqrtN,
      hsqrtThree, hscale⟩
  have hexp := exp_explicitLogCutoff_lt_of_cutoffIndex_le hn
  have hcoefficientRemote : Real.exp (leanSaddleCutoff + 2) < x := by
    exact (Real.exp_lt_exp.mpr (by
      norm_num [leanSaddleCutoff, xiNaturalExplicitLogCutoff])).trans hexp
  have hcenterRemote : Real.exp (leanSaddleCutoff + 2) < N :=
    hcoefficientRemote.trans_le hxN
  have hlogNpos : 0 < Real.log N :=
    (by norm_num [xiNaturalExplicitLogCutoff] :
      (0 : ℝ) < xiNaturalExplicitLogCutoff).trans hlogLower
  have hthreepos : 0 < 3 * x := by positivity
  have hlogThreeNonneg : 0 ≤ Real.log (3 * x) := by
    exact Real.log_nonneg (by
      have : (1 : ℝ) ≤ x := hxlarge.trans' (by norm_num)
      nlinarith)
  have hsqrtSq : Real.sqrt (3 * x) ^ 2 = 3 * x :=
    Real.sq_sqrt (by positivity)
  refine {
    coefficient_center_in_remote_sector := by simpa only [x] using hcoefficientRemote
    center_in_remote_sector := by simpa only [N] using hcenterRemote
    inverse_rate := ?_
    sigma_rate := ?_
    ratio_rate := ?_
    correction_rate := ?_
    log_error_rate := ?_
  }
  · calc
      2 / Real.log N ≤ 2 / xiNaturalExplicitLogCutoff := by
        exact div_le_div_of_nonneg_left (by norm_num)
          (by norm_num [xiNaturalExplicitLogCutoff]) hlogLower.le
      _ ≤ saddleFinalLimitRadius := by
        norm_num [xiNaturalExplicitLogCutoff, saddleFinalLimitRadius]
  · calc
      2 * Real.log (N + 10) / N ≤
          2 * Real.log (3 * x) / N := by
        exact div_le_div_of_nonneg_right
          (mul_le_mul_of_nonneg_left hlogMono (by norm_num)) hNpos.le
      _ ≤ 2 * Real.log (3 * x) / x := by
        exact div_le_div_of_nonneg_left
          (mul_nonneg (by norm_num) hlogThreeNonneg) hxpos hxN
      _ ≤ 2 * (4 * Real.sqrt (3 * x) / (10 : ℝ) ^ 40) / x := by
        gcongr
      _ ≤ 2 * (4 * x / (10 : ℝ) ^ 40) / x := by gcongr
      _ = 8 / (10 : ℝ) ^ 40 := by
        apply (div_eq_iff hxpos.ne').2
        ring
      _ ≤ saddleFinalLimitRadius := by
        norm_num [saddleFinalLimitRadius]
  · have hNhuge : (10 : ℝ) ^ 160 ≤ N := hxlarge.trans hxN
    have hlogOne : 1 ≤ Real.log N := by
      exact hlogLower.le.trans' (by
        norm_num [xiNaturalExplicitLogCutoff])
    have hinvN : 1 / N ≤ 1 / (10 : ℝ) ^ 160 := by
      exact one_div_le_one_div_of_le (by positivity) hNhuge
    have hfraction : 320 / (9 * N * Real.log N) ≤ 320 / (9 * N) := by
      apply div_le_div_of_nonneg_left (by norm_num) (by positivity)
      nlinarith
    calc
      16 * (320 / (9 * N * Real.log N)) + 128 / N ≤
          16 * (320 / (9 * N)) + 128 / N := by
        nlinarith
      _ = (16 * (320 / 9) + 128) * (1 / N) := by ring
      _ ≤ (16 * (320 / 9) + 128) * (1 / (10 : ℝ) ^ 160) := by
        gcongr
      _ ≤ xiNaturalSaddleRatioError := by
        norm_num [xiNaturalSaddleRatioError]
  · calc
      xiNaturalCorrectionScale * xiNaturalSaddleScale n *
            Real.log (3 * x) / x ≤
          xiNaturalCorrectionScale *
            (8 * Real.sqrt (3 * x) / (10 : ℝ) ^ 40) *
            (4 * Real.sqrt (3 * x) / (10 : ℝ) ^ 40) / x := by
        gcongr <;> norm_num [xiNaturalCorrectionScale] <;> positivity
      _ = xiNaturalCorrectionScale * 96 / (10 : ℝ) ^ 80 := by
        rw [show (10 : ℝ) ^ 80 = (10 : ℝ) ^ 40 * (10 : ℝ) ^ 40 by ring]
        calc
          _ = xiNaturalCorrectionScale * 32 *
                (Real.sqrt (3 * x) ^ 2) /
                ((10 : ℝ) ^ 40 * (10 : ℝ) ^ 40) / x := by ring
          _ = _ := by
            rw [hsqrtSq]
            apply (div_eq_iff hxpos.ne').2
            ring
      _ ≤ xiNaturalCorrectionBudget := by
        norm_num [xiNaturalCorrectionScale, xiNaturalCorrectionBudget]
  · have hC : 0 ≤ 100 * fullThetaMomentErrorCoefficient := by
      norm_num [fullThetaMomentErrorCoefficient, Nat.factorial]
    unfold naturalXiCauchyEpsilon
    calc
      xiNaturalLogErrorScale * xiNaturalSaddleScale n *
            ((100 * fullThetaMomentErrorCoefficient) * Real.log (3 * x) / x) / x ≤
          xiNaturalLogErrorScale *
            (8 * Real.sqrt (3 * x) / (10 : ℝ) ^ 40) *
            ((100 * fullThetaMomentErrorCoefficient) *
              (4 * Real.sqrt (3 * x) / (10 : ℝ) ^ 40) / x) / x := by
        gcongr <;> norm_num [xiNaturalLogErrorScale,
          fullThetaMomentErrorCoefficient, Nat.factorial] <;> positivity
      _ = (xiNaturalLogErrorScale *
            (100 * fullThetaMomentErrorCoefficient) * 96 /
              (10 : ℝ) ^ 80) / x := by
        rw [show (10 : ℝ) ^ 80 = (10 : ℝ) ^ 40 * (10 : ℝ) ^ 40 by ring]
        calc
          _ = (xiNaturalLogErrorScale *
                (100 * fullThetaMomentErrorCoefficient) * 32 *
                (Real.sqrt (3 * x) ^ 2) /
                ((10 : ℝ) ^ 40 * (10 : ℝ) ^ 40) / x) / x := by ring
          _ = _ := by
            rw [hsqrtSq]
            field_simp [hxpos.ne']
            ring
      _ ≤ xiNaturalLogErrorScale *
            (100 * fullThetaMomentErrorCoefficient) * 96 /
              (10 : ℝ) ^ 80 := by
        apply div_le_self
        · norm_num [xiNaturalLogErrorScale,
            fullThetaMomentErrorCoefficient, Nat.factorial]
        · exact hxlarge.trans' (by norm_num)
      _ ≤ xiNaturalLogErrorBudget := by
        norm_num [xiNaturalLogErrorScale, xiNaturalLogErrorBudget,
          fullThetaMomentErrorCoefficient, Nat.factorial]

/-- The four exact lower moving-saddle identities, uniformly on the six-sample
interval used by the xi coefficient certificate. -/
def XiNaturalLowerIdentificationCertificate (n : ℕ) : Prop :=
  ∀ y : ℝ, y ∈ Icc (n : ℝ) ((n : ℝ) + 5) →
    ManuscriptG0LowerIdentification ((2 * y - 2 : ℝ) : ℂ)

/-- The explicit interval conditions place every sample in the sector where
the kernel derivative identification applies. -/
theorem xiNaturalLowerIdentificationCertificate_of_explicitCutoff
    {n : ℕ} (hn : xiNaturalExplicitCutoffIndex ≤ n) :
    XiNaturalLowerIdentificationCertificate n := by
  intro y hy
  exact manuscriptG0LowerIdentification_of_mem_sector
    ((xiNaturalSaddleIntervalConditions_of_explicitCutoff hn).interval_mellin_mem_sector hy)

/-- At and beyond the explicit cutoff, the exact xi saddle interval
certificate has no remaining symbolic or scalar endpoint hypotheses. -/
theorem exactXiSaddleIntervalCertificate_of_explicitCutoff
    {n : ℕ} (hn : xiNaturalExplicitCutoffIndex ≤ n) :
    ExactXiSaddleIntervalCertificate n (xiNaturalSaddleScale n)
      xiNaturalCertificateBudget :=
  (xiNaturalSaddleIntervalConditions_of_explicitCutoff hn).exactCertificate
    (xiNaturalLowerIdentificationCertificate_of_explicitCutoff hn)

/-- The real saddle scale is at least half of the displayed logarithmic
cutoff.  This is the quantitative lower bound used by the final contraction
budgets. -/
theorem explicitLogCutoff_half_le_xiNaturalSaddleScale
    {n : ℕ} (hn : xiNaturalExplicitCutoffIndex ≤ n) :
    xiNaturalExplicitLogCutoff / 2 ≤ xiNaturalSaddleScale n := by
  let C := xiNaturalSaddleIntervalConditions_of_explicitCutoff hn
  have hlower := quantitativeSaddleBranch_norm_lower_half_realLog
    C.center_mellin_mem_sector
  have hscaleCast := C.saddleScale_cast
  have hscalePos := C.saddleScale_pos
  rw [← hscaleCast] at hlower
  simp only [norm_real, Real.norm_eq_abs, abs_of_pos C.center_pos,
    abs_of_pos hscalePos] at hlower
  have hlog : xiNaturalExplicitLogCutoff <
      Real.log (xiNaturalMellinCenter n) := by
    exact (explicitCutoff_log_and_scale_bounds hn).1
  linarith

/-- The two small parameters consumed by the exact xi contraction are
bounded by fixed rationals at the explicit cutoff. -/
theorem explicitCutoff_xiNatural_branch_scales
    {n : ℕ} (hn : xiNaturalExplicitCutoffIndex ≤ n) :
    1 / xiNaturalSaddleScale n ≤ 1 / (500000000000000 : ℝ) ∧
      xiNaturalSaddleScale n / (n : ℝ) ≤ 8 / (10 : ℝ) ^ 40 ∧
      1 / (n : ℝ) ≤ 1 / (10 : ℝ) ^ 160 := by
  let C := xiNaturalSaddleIntervalConditions_of_explicitCutoff hn
  have hLpos := C.saddleScale_pos
  have hLlower := explicitLogCutoff_half_le_xiNaturalSaddleScale hn
  have hinvL : 1 / xiNaturalSaddleScale n ≤
      1 / (500000000000000 : ℝ) := by
    apply one_div_le_one_div_of_le (by norm_num)
    norm_num [xiNaturalExplicitLogCutoff] at hLlower
    exact hLlower
  let x : ℝ := n
  rcases explicitCutoff_basic_bounds hn with
    ⟨hxlarge, _hxN, _hN2x, _hNten3x, hxpos, _hNpos⟩
  rcases explicitCutoff_log_and_scale_bounds hn with
    ⟨_hlogLower, _hlogMono, _hlogN, _hlogThree, _hsqrtN,
      hsqrtThree, hscale⟩
  have hLdiv : xiNaturalSaddleScale n / x ≤ 8 / (10 : ℝ) ^ 40 := by
    calc
      xiNaturalSaddleScale n / x ≤
          (8 * Real.sqrt (3 * x) / (10 : ℝ) ^ 40) / x := by
        exact div_le_div_of_nonneg_right hscale hxpos.le
      _ ≤ (8 * x / (10 : ℝ) ^ 40) / x := by gcongr
      _ = 8 / (10 : ℝ) ^ 40 := by
        apply (div_eq_iff hxpos.ne').2
        ring
  have hinvN : 1 / x ≤ 1 / (10 : ℝ) ^ 160 := by
    exact one_div_le_one_div_of_le (by positivity) hxlarge
  exact ⟨hinvL, by simpa only [x] using hLdiv,
    by simpa only [x] using hinvN⟩

/-- Beyond the explicit cutoff, the kernel derivative-identification theorem
produces the locally unique positive parameter branch for the exact
normalized xi map.  No external symbolic or asymptotic side condition remains
implicit. -/
noncomputable def exactXiPositiveParameterBranch_of_explicitCutoff
    {n : ℕ} (hn : xiNaturalExplicitCutoffIndex ≤ n) :
    PositiveParameterBranch
      (exactXiParameterMap n (xiNaturalSaddleScale n)) := by
  let C := xiNaturalSaddleIntervalConditions_of_explicitCutoff hn
  have hnpos : 0 < n := C.n_pos
  have hLpos := C.saddleScale_pos
  have hLlower := explicitLogCutoff_half_le_xiNaturalSaddleScale hn
  have hL : 1 ≤ xiNaturalSaddleScale n := by
    have : (1 : ℝ) ≤ xiNaturalExplicitLogCutoff / 2 := by
      norm_num [xiNaturalExplicitLogCutoff]
    exact this.trans hLlower
  rcases explicitCutoff_xiNatural_branch_scales hn with
    ⟨hinvL, hLdiv, hinvN⟩
  have hjacobian :
      1 / xiNaturalSaddleScale n + 1 / (n : ℝ) ≤
        1 / 100000000 := by
    calc
      1 / xiNaturalSaddleScale n + 1 / (n : ℝ) ≤
          1 / (500000000000000 : ℝ) + 1 / (10 : ℝ) ^ 160 :=
        add_le_add hinvL hinvN
      _ ≤ 1 / 100000000 := by norm_num
  have hquotient :
      (1 / (n : ℝ)) / (1 / xiNaturalSaddleScale n) =
        xiNaturalSaddleScale n / (n : ℝ) := by
    field_simp [hLpos.ne', (show (n : ℝ) ≠ 0 by positivity)]
  have hresidual :
      10000 * (1 / xiNaturalSaddleScale n +
          (1 / (n : ℝ)) / (1 / xiNaturalSaddleScale n)) +
          xiNaturalCertificateBudget ≤
        (3 / 608) * branchInnerRadius := by
    rw [hquotient]
    calc
      10000 * (1 / xiNaturalSaddleScale n +
          xiNaturalSaddleScale n / (n : ℝ)) +
          xiNaturalCertificateBudget ≤
        10000 * (1 / (500000000000000 : ℝ) +
          8 / (10 : ℝ) ^ 40) + xiNaturalCertificateBudget := by
            gcongr
      _ ≤ (3 / 608) * branchInnerRadius := by
        norm_num [xiNaturalCertificateBudget, xiNaturalSaddleBudget,
          xiNaturalCorrectionBudget, xiNaturalLogErrorBudget,
          branchInnerRadius]
  exact exactXi_positiveParameterBranch hnpos hL
    (exactXiSaddleIntervalCertificate_of_explicitCutoff hn)
    hjacobian hresidual

end

end Zeta23.Research.JensenWedge
