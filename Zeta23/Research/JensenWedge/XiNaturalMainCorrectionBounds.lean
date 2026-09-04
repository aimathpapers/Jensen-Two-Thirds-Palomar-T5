import Zeta23.Research.JensenWedge.XiNaturalMainLowerForwardDifferences
import Zeta23.Research.JensenWedge.LeadingEndpointConnector

/-!
# Explicit correction to the lower natural-main saddle tower

The lower derivatives used by the xi interval certificate have one dominant
piece: the derivatives of `manuscriptSaddleG0 (2*M-2)`.  This file isolates
the remaining holomorphic function and bounds it on proportional Cauchy
discs.  The lower-order rational identities consumed here are represented by
the named `ManuscriptG0LowerIdentification` record.  The downstream
`MovingSaddleDerivativeIdentification` module constructs that record in Lean
from the displayed saddle equation and reduced numerator recurrence.
-/

namespace Zeta23.Research.JensenWedge

open Complex Set

noncomputable section

/-- The denominator in `G0` is curvature times the square of the selected
saddle.  This identity is exact and is useful both for nonvanishing and size
bounds. -/
theorem manuscriptSaddleQ_eq_curvature_mul_sq
    {N : ℂ} (hN : N ∈ leanSaddleSector) :
    manuscriptSaddleQ N =
      leadingCurvature N (quantitativeSaddleBranch N) *
        quantitativeSaddleBranch N ^ 2 := by
  have hNne := (leanSaddleSector_quantitative hN).parameter_ne_zero
  have hLne := (quantitativeSaddleBranch_scaled_bounds
    (leanSaddleSector_quantitative hN)).1
  rw [leadingCurvature_eq_paper hLne]
  unfold manuscriptSaddleQ
  field_simp [hNne, hLne]
  ring

/-- The `G0` logarithmic denominator stays in the open right half-plane on
the fixed sector, so its principal logarithm is genuinely holomorphic. -/
theorem manuscriptSaddleQ_re_pos
    {N : ℂ} (hN : N ∈ leanSaddleSector) :
    0 < (manuscriptSaddleQ N).re := by
  let L : ℂ := quantitativeSaddleBranch N
  let K : ℂ := leadingCurvature N L
  have hLre : 1000 < L.re := by
    simpa only [L] using quantitativeSaddleBranch_re_gt hN
  have hLim : |L.im| < 1 / 20 := by
    simpa only [L] using quantitativeSaddleBranch_im_abs_lt hN
  have hK := quantitativeSaddleBranch_curvature_strong_bounds hN
  have hKim : |K.im| ≤ 2 * K.re :=
    (Complex.abs_im_le_norm K).trans hK.2
  have hcross : |K.im * (2 * L.re * L.im)| ≤
      (2 * K.re) * (L.re / 10) := by
    have htwenty : |L.im| ≤ 1 / 20 := hLim.le
    have hKnonneg : 0 ≤ K.re := by linarith [hK.1]
    have hLnonneg : 0 ≤ L.re := by linarith
    calc
      |K.im * (2 * L.re * L.im)| =
          |K.im| * 2 * L.re * |L.im| := by
        rw [abs_mul, abs_mul, abs_mul,
          abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2),
          abs_of_pos (lt_trans (by norm_num) hLre)]
        ring
      _ ≤ (2 * K.re) * 2 * L.re * (1 / 20) := by
        gcongr
      _ = (2 * K.re) * (L.re / 10) := by ring
  have hreLower :
      K.re * (L.re ^ 2 - L.im ^ 2) -
          K.im * (2 * L.re * L.im) ≥
        K.re * (L.re ^ 2 - (1 / 20 : ℝ) ^ 2) -
          (2 * K.re) * (L.re / 10) := by
    have himsq : L.im ^ 2 ≤ (1 / 20 : ℝ) ^ 2 := by
      rw [sq_le_sq]
      simpa only [abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 20)] using hLim.le
    have hcross' : K.im * (2 * L.re * L.im) ≤
        (2 * K.re) * (L.re / 10) :=
      (le_abs_self _).trans hcross
    nlinarith [hK.1]
  have hinner : 0 <
      L.re ^ 2 - (1 / 20 : ℝ) ^ 2 - 2 * (L.re / 10) := by
    nlinarith [sq_nonneg (L.re - 1000)]
  have hlowerPos : 0 <
      K.re * (L.re ^ 2 - (1 / 20 : ℝ) ^ 2) -
        (2 * K.re) * (L.re / 10) := by
    have := mul_pos (by linarith [hK.1] : 0 < K.re) hinner
    nlinarith
  have hformula : (K * L ^ 2).re =
      K.re * (L.re ^ 2 - L.im ^ 2) -
        K.im * (2 * L.re * L.im) := by
    simp only [pow_two, mul_re, mul_im]
    ring
  rw [manuscriptSaddleQ_eq_curvature_mul_sq hN]
  change 0 < (K * L ^ 2).re
  rw [hformula]
  exact hlowerPos.trans_le hreLower

theorem manuscriptSaddleQ_ne_zero
    {N : ℂ} (hN : N ∈ leanSaddleSector) :
    manuscriptSaddleQ N ≠ 0 := by
  intro hzero
  have hpos := manuscriptSaddleQ_re_pos hN
  rw [hzero] at hpos
  simp at hpos

/-- The displayed `G0` is holomorphic at every point of the saddle sector;
in particular the named lower-derivative CAS equalities concern ordinary
complex derivatives of a branch-fixed function. -/
theorem differentiableAt_manuscriptSaddleG0
    {N : ℂ} (hN : N ∈ leanSaddleSector) :
    DifferentiableAt ℂ manuscriptSaddleG0 N := by
  let L : ℂ := quantitativeSaddleBranch N
  have hL := (hasDerivAt_quantitativeSaddleBranch hN).differentiableAt
  have hlogL : DifferentiableAt ℂ (fun z => log (quantitativeSaddleBranch z)) N :=
    (Complex.differentiableAt_log (Complex.mem_slitPlane_iff.mpr
      (Or.inl (by
        have := quantitativeSaddleBranch_re_gt hN
        linarith)))).comp N hL
  have hQ : DifferentiableAt ℂ manuscriptSaddleQ N := by
    unfold manuscriptSaddleQ
    fun_prop
  have hlogQ : DifferentiableAt ℂ (fun z => log (manuscriptSaddleQ z)) N :=
    (Complex.differentiableAt_log (Complex.mem_slitPlane_iff.mpr
      (Or.inl (manuscriptSaddleQ_re_pos hN)))).comp N hQ
  have hLne := (quantitativeSaddleBranch_scaled_bounds
    (leanSaddleSector_quantitative hN)).1
  unfold manuscriptSaddleG0
  exact ((((differentiableAt_id.add_const 1).mul hlogL).add
    (hL.div_const 4)).sub
      (differentiableAt_id.div hL hLne)).sub
        (hlogQ.div_const 2)

theorem differentiableOn_manuscriptSaddleG0 :
    DifferentiableOn ℂ manuscriptSaddleG0 leanSaddleSector := by
  intro N hN
  exact (differentiableAt_manuscriptSaddleG0 hN).differentiableWithinAt

/-- Remove the affine dyadic term and the moving-saddle logarithm from the
explicit natural main.  All derivatives of order at least two of the affine
term vanish, so this function is exactly the lower-order correction. -/
def xiNaturalMainSaddleRemainder (M : ℂ) : ℂ :=
  complexXiNaturalAuxiliaryLogMain M -
      manuscriptSaddleG0 (coefficientMellinParameter M) +
    coefficientMellinParameter M * log 2

theorem differentiableAt_xiNaturalMainSaddleRemainder
    {M : ℂ} (hM : M ∈ leanXiCoefficientSector) :
    DifferentiableAt ℂ xiNaturalMainSaddleRemainder M := by
  have hN : coefficientMellinParameter M ∈ leanSaddleSector :=
    leanTwoShiftAdmissible_base (leanCoefficientSector_admissible hM.2)
  have hNdiff : DifferentiableAt ℂ coefficientMellinParameter M :=
    differentiableAt_coefficientMellinParameter M
  unfold xiNaturalMainSaddleRemainder
  exact ((differentiableAt_complexXiNaturalAuxiliaryLogMain hM).sub
    ((differentiableAt_manuscriptSaddleG0 hN).comp M hNdiff)).add
      (hNdiff.mul_const (log 2))

theorem differentiableOn_xiNaturalMainSaddleRemainder :
    DifferentiableOn ℂ xiNaturalMainSaddleRemainder leanXiCoefficientSector := by
  intro M hM
  exact (differentiableAt_xiNaturalMainSaddleRemainder hM).differentiableWithinAt

/-- Exact cancellation identity exposing that the remainder has only
logarithmic size.  The potentially large `N*log L` and `N*log 2` terms have
cancelled before any norm estimate is taken. -/
theorem xiNaturalMainSaddleRemainder_eq
    {M : ℂ} (hM : M ∈ leanXiCoefficientSector) :
    let N := coefficientMellinParameter M
    let L := quantitativeSaddleBranch N
    let K := leadingCurvature N L
    xiNaturalMainSaddleRemainder M =
      -4 * log 2 - log L + 3 / 4 +
        (1 / 2) * log ((2 * Real.pi : ℂ) / K) + 1 / (2 * K) +
          log (manuscriptSaddleQ N) / 2 + complexXiNaturalTwoShiftLog M := by
  let N : ℂ := coefficientMellinParameter M
  let L : ℂ := quantitativeSaddleBranch N
  let K : ℂ := leadingCurvature N L
  have hN : N ∈ leanSaddleSector :=
    leanTwoShiftAdmissible_base (leanCoefficientSector_admissible hM.2)
  have hLne := (quantitativeSaddleBranch_scaled_bounds
    (leanSaddleSector_quantitative hN)).1
  have hroot : sectorialSaddleEquation N L = 0 := by
    simpa only [L] using
      (quantitativeSaddleBranch_spec (leanSaddleSector_quantitative hN)).2.1
  have hstationary : (Real.pi : ℂ) * exp L = N / L - 3 / 4 := by
    have hmap : L * ((Real.pi : ℂ) * exp L + 3 / 4) = N := by
      exact eq_of_sub_eq_zero (by
        simpa only [sectorialSaddleEquation, saddleParameterMap] using hroot)
    rw [eq_sub_iff_add_eq]
    apply (eq_div_iff hLne).2
    calc
      ((Real.pi : ℂ) * exp L + 3 / 4) * L =
          L * ((Real.pi : ℂ) * exp L + 3 / 4) := by ring
      _ = N := hmap
  have hNM : N = 2 * M - 2 := by rfl
  unfold xiNaturalMainSaddleRemainder complexXiNaturalAuxiliaryLogMain
    saddleMomentLogMain saddleLeadingLog leadingLogIntegrand
    manuscriptSaddleG0
  rw [saddleCurvatureAlong_eq hN]
  simp only [N, L, K] at hstationary ⊢
  rw [hstationary]
  dsimp only [coefficientMellinParameter] at hNM ⊢
  ring

/-- A branch-independent norm estimate for the principal complex logarithm. -/
theorem norm_log_le_abs_realLog_add_pi (z : ℂ) :
    ‖log z‖ ≤ |Real.log ‖z‖| + Real.pi := by
  calc
    ‖log z‖ ≤ |(log z).re| + |(log z).im| :=
      Complex.norm_le_abs_re_add_abs_im _
    _ = |Real.log ‖z‖| + |z.arg| := by
      rw [Complex.log_re, Complex.log_im]
    _ ≤ |Real.log ‖z‖| + Real.pi := by
      gcongr
      exact Complex.abs_arg_le_pi z

private theorem norm_log_le_realLog_add_pi
    {z : ℂ} (hz : 1 ≤ ‖z‖) :
    ‖log z‖ ≤ Real.log ‖z‖ + Real.pi := by
  simpa only [abs_of_nonneg (Real.log_nonneg hz)] using
    norm_log_le_abs_realLog_add_pi z

private theorem shifted_log_norm_le_three_log
    {N : ℂ} (hN : N ∈ leanSaddleSector) {a : ℝ}
    (ha0 : 0 ≤ a) (ha2 : a ≤ 2) :
    ‖log (N + (a : ℂ))‖ ≤ 3 * Real.log ‖N‖ := by
  have hNpos : 0 < ‖N‖ := norm_pos_iff.mpr
    (leanSaddleSector_quantitative hN).parameter_ne_zero
  have hell : 1000000 < Real.log ‖N‖ := by
    simpa only [Complex.log_re] using leanSaddleSector_log_re_gt hN
  have hNhuge : 4 < ‖N‖ := by
    have hlarge := leanSaddleSector_parameterNorm_ge_fiveHundredBillion hN
    linarith
  have hNreLarge : 2 < N.re := by
    have hnormRe := leanSaddleSector_norm_le_two_re hN
    nlinarith
  have hshiftLower : 1 ≤ ‖N + (a : ℂ)‖ := by
    have hre := Complex.re_le_norm (N + (a : ℂ))
    simp only [add_re, ofReal_re] at hre
    linarith
  have hshiftUpper : ‖N + (a : ℂ)‖ ≤ 2 * ‖N‖ := by
    calc
      ‖N + (a : ℂ)‖ ≤ ‖N‖ + ‖(a : ℂ)‖ := norm_add_le _ _
      _ = ‖N‖ + a := by rw [norm_real, Real.norm_eq_abs, abs_of_nonneg ha0]
      _ ≤ 2 * ‖N‖ := by linarith
  have hlogUpper : Real.log ‖N + (a : ℂ)‖ ≤
      Real.log (2 * ‖N‖) :=
    Real.log_le_log (lt_of_lt_of_le (by norm_num) hshiftLower) hshiftUpper
  have hlogTwo : Real.log (2 : ℝ) ≤ Real.log ‖N‖ := by
    exact Real.log_le_log (by norm_num) (by linarith)
  have hpi : Real.pi ≤ Real.log ‖N‖ := by
    linarith [Real.pi_lt_four]
  calc
    ‖log (N + (a : ℂ))‖ ≤ Real.log ‖N + (a : ℂ)‖ + Real.pi :=
      norm_log_le_realLog_add_pi hshiftLower
    _ ≤ Real.log (2 * ‖N‖) + Real.pi := by gcongr
    _ = Real.log 2 + Real.log ‖N‖ + Real.pi := by
      rw [Real.log_mul (by norm_num) hNpos.ne']
    _ ≤ 3 * Real.log ‖N‖ := by linarith

private theorem norm_seven_term_sum_le
    (a b c d e f g : ℂ) :
    ‖a + b + c + d + e + f + g‖ ≤
      ‖a‖ + ‖b‖ + ‖c‖ + ‖d‖ + ‖e‖ + ‖f‖ + ‖g‖ := by
  calc
    ‖a + b + c + d + e + f + g‖ ≤ ‖a + b + c + d + e + f‖ + ‖g‖ :=
      norm_add_le _ _
    _ ≤ (‖a + b + c + d + e‖ + ‖f‖) + ‖g‖ := by gcongr; exact norm_add_le _ _
    _ ≤ ((‖a + b + c + d‖ + ‖e‖) + ‖f‖) + ‖g‖ := by
      gcongr; exact norm_add_le _ _
    _ ≤ (((‖a + b + c‖ + ‖d‖) + ‖e‖) + ‖f‖) + ‖g‖ := by
      gcongr; exact norm_add_le _ _
    _ ≤ ((((‖a + b‖ + ‖c‖) + ‖d‖) + ‖e‖) + ‖f‖) + ‖g‖ := by
      gcongr; exact norm_add_le _ _
    _ ≤ (((((‖a‖ + ‖b‖) + ‖c‖) + ‖d‖) + ‖e‖) + ‖f‖) + ‖g‖ := by
      gcongr; exact norm_add_le _ _
    _ = ‖a‖ + ‖b‖ + ‖c‖ + ‖d‖ + ‖e‖ + ‖f‖ + ‖g‖ := by ring

/-- The exposed remainder is uniformly of logarithmic size on the entire
paired coefficient sector.  The constant `40` is deliberately generous. -/
theorem xiNaturalMainSaddleRemainder_norm_le
    {M : ℂ} (hM : M ∈ leanXiCoefficientSector) :
    ‖xiNaturalMainSaddleRemainder M‖ ≤
      40 * Real.log ‖coefficientMellinParameter M‖ := by
  let N : ℂ := coefficientMellinParameter M
  let L : ℂ := quantitativeSaddleBranch N
  let K : ℂ := leadingCurvature N L
  let Q : ℂ := manuscriptSaddleQ N
  have hN : N ∈ leanSaddleSector :=
    leanTwoShiftAdmissible_base (leanCoefficientSector_admissible hM.2)
  have hNne := (leanSaddleSector_quantitative hN).parameter_ne_zero
  have hNpos : 0 < ‖N‖ := norm_pos_iff.mpr hNne
  have hell : 1000000 < Real.log ‖N‖ := by
    simpa only [Complex.log_re] using leanSaddleSector_log_re_gt hN
  have hpi : Real.pi ≤ Real.log ‖N‖ := by
    linarith [Real.pi_lt_four]
  have hLre : 1000 < L.re := by
    simpa only [L] using quantitativeSaddleBranch_re_gt hN
  have hLlower : 1 ≤ ‖L‖ := by
    have := Complex.re_le_norm L
    linarith
  have hLupper : ‖L‖ ≤ 2 * Real.log ‖N‖ := by
    simpa only [L] using quantitativeSaddleBranch_norm_le_two_log_norm hN
  have hlogLreal : Real.log ‖L‖ ≤ 2 * Real.log ‖N‖ := by
    have := Real.log_le_sub_one_of_pos (lt_of_lt_of_le (by norm_num) hLlower)
    linarith
  have hlogLnonneg : 0 ≤ Real.log ‖L‖ := Real.log_nonneg hLlower
  have hlogL : ‖log L‖ ≤ 3 * Real.log ‖N‖ := by
    exact (norm_log_le_realLog_add_pi hLlower).trans (by linarith)
  have hKlower : 4000 ≤ ‖K‖ := by
    simpa only [K, L] using quantitativeSaddleBranch_curvature_norm_ge_fourThousand hN
  have hKpos : 0 < ‖K‖ := by linarith
  have hKupper : ‖K‖ ≤ ‖N‖ := by
    simpa only [K, L] using quantitativeSaddleBranch_curvature_norm_le_parameter_norm hN
  have hlogKnonneg : 0 ≤ Real.log ‖K‖ := Real.log_nonneg (by linarith)
  have hlogKupper : Real.log ‖K‖ ≤ Real.log ‖N‖ :=
    Real.log_le_log hKpos hKupper
  have htwoPiPos : 0 < (2 * Real.pi : ℝ) := mul_pos (by norm_num) Real.pi_pos
  have hlogTwoPiNonneg : 0 ≤ Real.log (2 * Real.pi) := by
    apply Real.log_nonneg
    nlinarith [Real.pi_gt_three]
  have hlogTwoPiUpper : Real.log (2 * Real.pi) ≤ Real.log ‖N‖ := by
    have hraw := Real.log_le_sub_one_of_pos htwoPiPos
    nlinarith [Real.pi_lt_four]
  have hlogQuotientReal :
      |Real.log ‖((2 * Real.pi : ℂ) / K)‖| ≤ 2 * Real.log ‖N‖ := by
    rw [norm_div, norm_mul, norm_real, Real.norm_eq_abs,
      abs_of_pos Real.pi_pos]
    norm_num only [Complex.norm_ofNat]
    rw [Real.log_div htwoPiPos.ne' hKpos.ne']
    calc
      |Real.log (2 * Real.pi) - Real.log ‖K‖| ≤
          |Real.log (2 * Real.pi)| + |Real.log ‖K‖| := abs_sub _ _
      _ = Real.log (2 * Real.pi) + Real.log ‖K‖ := by
        rw [abs_of_nonneg hlogTwoPiNonneg, abs_of_nonneg hlogKnonneg]
      _ ≤ 2 * Real.log ‖N‖ := by linarith
  have hlogQuotient : ‖log ((2 * Real.pi : ℂ) / K)‖ ≤
      3 * Real.log ‖N‖ :=
    (norm_log_le_abs_realLog_add_pi _).trans (by linarith)
  have hinvK : ‖1 / (2 * K)‖ ≤ Real.log ‖N‖ := by
    have : 1 / (2 * ‖K‖) ≤ 1 := by
      apply (div_le_one (by positivity)).2
      linarith
    calc
      ‖1 / (2 * K)‖ = 1 / (2 * ‖K‖) := by
        rw [norm_div, norm_one, norm_mul]
        norm_num
      _ ≤ 1 := this
      _ ≤ Real.log ‖N‖ := by linarith
  have hQeq : Q = K * L ^ 2 := by
    simpa only [Q, K, L] using manuscriptSaddleQ_eq_curvature_mul_sq hN
  have hQlower : 1 ≤ ‖Q‖ := by
    rw [hQeq, norm_mul, norm_pow]
    nlinarith
  have hlogQreal : Real.log ‖Q‖ ≤ 5 * Real.log ‖N‖ := by
    rw [hQeq, norm_mul, norm_pow,
      Real.log_mul hKpos.ne' (pow_ne_zero 2 (by positivity : ‖L‖ ≠ 0)),
      Real.log_pow]
    norm_num only [Nat.cast_ofNat]
    calc
      Real.log ‖K‖ + 2 * Real.log ‖L‖ ≤
          Real.log ‖N‖ + 2 * (2 * Real.log ‖N‖) := by
        gcongr
      _ = 5 * Real.log ‖N‖ := by ring
  have hlogQ : ‖log Q‖ ≤ 6 * Real.log ‖N‖ :=
    (norm_log_le_realLog_add_pi hQlower).trans (by linarith)
  have hshiftOne : ‖log (N + 1)‖ ≤ 3 * Real.log ‖N‖ := by
    simpa only [ofReal_one] using shifted_log_norm_le_three_log hN
      (by norm_num : (0 : ℝ) ≤ 1) (by norm_num : (1 : ℝ) ≤ 2)
  have hshiftTwo : ‖log (N + 2)‖ ≤ 3 * Real.log ‖N‖ := by
    simpa only [ofReal_ofNat] using shifted_log_norm_le_three_log hN
      (by norm_num : (0 : ℝ) ≤ 2) (by norm_num : (2 : ℝ) ≤ 2)
  let C : ℂ := coefficientCancellationCorrection N
  have hC : ‖C - 1‖ ≤ 1 / 2 := by
    simpa only [C, N] using coefficientCancellationCorrection_norm_sub_one_le_half hM
  have hlogC : ‖log C‖ ≤ Real.log ‖N‖ := by
    have hraw : ‖log C‖ ≤ (3 / 2 : ℝ) * ‖C - 1‖ := by
      have := Complex.norm_log_one_add_half_le_self (z := C - 1) hC
      convert this using 1 <;> ring
    exact hraw.trans (by nlinarith)
  have hlog16 : ‖log (16 : ℂ)‖ ≤ Real.log ‖N‖ := by
    calc
      ‖log (16 : ℂ)‖ ≤ |Real.log ‖(16 : ℂ)‖| + Real.pi :=
        norm_log_le_abs_realLog_add_pi _
      _ = Real.log 16 + Real.pi := by
        norm_num only [Complex.norm_ofNat]
        rw [abs_of_nonneg (Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 16))]
      _ ≤ Real.log ‖N‖ := by
        have := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 16)
        nlinarith [Real.pi_lt_four]
  have htwoShift : ‖complexXiNaturalTwoShiftLog M‖ ≤
      8 * Real.log ‖N‖ := by
    unfold complexXiNaturalTwoShiftLog
    change ‖log 16 + log (N + 2) + log (N + 1) + log C‖ ≤ _
    calc
      _ ≤ ‖log (16 : ℂ)‖ + ‖log (N + 2)‖ + ‖log (N + 1)‖ + ‖log C‖ := by
        calc
          _ ≤ ‖log 16 + log (N + 2) + log (N + 1)‖ + ‖log C‖ := norm_add_le _ _
          _ ≤ (‖log 16 + log (N + 2)‖ + ‖log (N + 1)‖) + ‖log C‖ := by
            gcongr; exact norm_add_le _ _
          _ ≤ ((‖log (16 : ℂ)‖ + ‖log (N + 2)‖) + ‖log (N + 1)‖) + ‖log C‖ := by
            gcongr; exact norm_add_le _ _
      _ ≤ 8 * Real.log ‖N‖ := by linarith
  rw [xiNaturalMainSaddleRemainder_eq hM]
  change ‖-4 * log 2 + (-log L) + 3 / 4 +
      (1 / 2) * log ((2 * Real.pi : ℂ) / K) + 1 / (2 * K) +
        log Q / 2 + complexXiNaturalTwoShiftLog M‖ ≤ _
  calc
    _ ≤ ‖-4 * log 2‖ + ‖-log L‖ + ‖(3 / 4 : ℂ)‖ +
        ‖(1 / 2) * log ((2 * Real.pi : ℂ) / K)‖ + ‖1 / (2 * K)‖ +
          ‖log Q / 2‖ + ‖complexXiNaturalTwoShiftLog M‖ :=
      norm_seven_term_sum_le _ _ _ _ _ _ _
    _ ≤ 40 * Real.log ‖N‖ := by
      have hlog2 : ‖log (2 : ℂ)‖ ≤ Real.log ‖N‖ := by
        calc
          ‖log (2 : ℂ)‖ ≤ |Real.log ‖(2 : ℂ)‖| + Real.pi :=
            norm_log_le_abs_realLog_add_pi _
          _ = Real.log 2 + Real.pi := by
            norm_num only [Complex.norm_ofNat]
            rw [abs_of_nonneg (Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 2))]
          _ ≤ Real.log ‖N‖ := by
            have := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
            nlinarith [Real.pi_lt_four]
      have hterm0 : ‖-4 * log (2 : ℂ)‖ ≤ 4 * Real.log ‖N‖ := by
        rw [norm_mul]
        norm_num
        gcongr
      have hterm2 : ‖(3 / 4 : ℂ)‖ ≤ Real.log ‖N‖ := by
        norm_num
        linarith
      have hterm3 : ‖(1 / 2 : ℂ) * log ((2 * Real.pi : ℂ) / K)‖ ≤
          2 * Real.log ‖N‖ := by
        rw [norm_mul]
        norm_num
        nlinarith
      have hterm5 : ‖log Q / 2‖ ≤ 3 * Real.log ‖N‖ := by
        rw [norm_div]
        norm_num
        nlinarith
      have hneglogL : ‖-log L‖ ≤ 3 * Real.log ‖N‖ := by
        simpa only [norm_neg] using hlogL
      nlinarith

/-- Cauchy transport of the explicit logarithmic-size remainder.  The proof
is uniform in the derivative order; the named sixth-order surface is the one
needed by the concrete xi multiplier closure. -/
theorem xiNaturalMainSaddleRemainder_derivatives_through_six_on_half_disc
    {x : ℝ} (hx : Real.exp (leanSaddleCutoff + 2) < x)
    {z : ℂ}
    (hz : z ∈ Metric.closedBall (x : ℂ) (manuscriptInteriorCauchyRadius x)) :
    ∀ j ≤ 6,
      ‖iteratedDeriv j xiNaturalMainSaddleRemainder z‖ ≤
        j.factorial * (40 * Real.log (3 * x)) /
          manuscriptInteriorCauchyRadius x ^ j := by
  have hxpos : 0 < x := (manuscriptCauchy_large_properties hx).2.2.2
  have hradius : 0 < manuscriptInteriorCauchyRadius x := by
    unfold manuscriptInteriorCauchyRadius
    positivity
  let D : Set ℂ := Metric.closedBall z (manuscriptInteriorCauchyRadius x)
  have hDinner : D ⊆ Metric.closedBall (x : ℂ) (manuscriptCauchyRadius x) :=
    manuscriptInterior_closedBall_subset_manuscriptDisc hz
  have hDsector : D ⊆ leanXiCoefficientSector :=
    hDinner.trans (manuscriptCauchy_closedBall_subset_sector hx)
  have hdiff : DifferentiableOn ℂ xiNaturalMainSaddleRemainder D :=
    differentiableOn_xiNaturalMainSaddleRemainder.mono hDsector
  have hdisc : DiffContOnCl ℂ xiNaturalMainSaddleRemainder
      (Metric.ball z (manuscriptInteriorCauchyRadius x)) :=
    hdiff.diffContOnCl_ball Subset.rfl
  intro j _hj
  apply Complex.norm_iteratedDeriv_le_of_forall_mem_sphere_norm_le
    j hradius hdisc
  intro w hw
  have hwD : w ∈ D := Metric.sphere_subset_closedBall hw
  have hNbound := manuscriptCauchy_shifted_norm_bounds hx (hDinner hwD)
  have hNpos : 0 < ‖coefficientMellinParameter w‖ :=
    hxpos.trans_le hNbound.1
  have hlogUpper : Real.log ‖coefficientMellinParameter w‖ ≤
      Real.log (3 * x) :=
    Real.log_le_log hNpos hNbound.2
  calc
    ‖xiNaturalMainSaddleRemainder w‖ ≤
        40 * Real.log ‖coefficientMellinParameter w‖ :=
      xiNaturalMainSaddleRemainder_norm_le (hDsector hwD)
    _ ≤ 40 * Real.log (3 * x) := by gcongr

/-- Backward-compatible lower-order projection of the sixth-order Cauchy
transport theorem. -/
theorem xiNaturalMainSaddleRemainder_derivatives_through_five_on_half_disc
    {x : ℝ} (hx : Real.exp (leanSaddleCutoff + 2) < x)
    {z : ℂ}
    (hz : z ∈ Metric.closedBall (x : ℂ) (manuscriptInteriorCauchyRadius x)) :
    ∀ j ≤ 5,
      ‖iteratedDeriv j xiNaturalMainSaddleRemainder z‖ ≤
        j.factorial * (40 * Real.log (3 * x)) /
          manuscriptInteriorCauchyRadius x ^ j := by
  intro j hj
  exact xiNaturalMainSaddleRemainder_derivatives_through_six_on_half_disc
    hx hz j (by omega)

theorem xiNaturalMainSaddleRemainder_analyticOnNhd :
    AnalyticOnNhd ℂ xiNaturalMainSaddleRemainder leanXiCoefficientSector :=
  differentiableOn_xiNaturalMainSaddleRemainder.analyticOnNhd
    isOpen_leanXiCoefficientSector

theorem manuscriptSaddleG0_analyticOnNhd :
    AnalyticOnNhd ℂ manuscriptSaddleG0 leanSaddleSector :=
  differentiableOn_manuscriptSaddleG0.analyticOnNhd isOpen_leanSaddleSector

theorem hasDerivAt_iteratedDeriv_manuscriptSaddleG0
    (s : ℕ) {N : ℂ} (hN : N ∈ leanSaddleSector) :
    HasDerivAt (iteratedDeriv s manuscriptSaddleG0)
      (iteratedDeriv (s + 1) manuscriptSaddleG0 N) N := by
  have h := (manuscriptSaddleG0_analyticOnNhd.iterated_deriv s) N hN
  rw [iteratedDeriv_succ, iteratedDeriv_eq_iterate]
  exact h.differentiableAt.hasDerivAt

/-- Local affine-chain rule for every derivative of `G0`.  It is proved on
the open coefficient sector, avoiding any unjustified global smoothness
claim about the branch outside its certified domain. -/
theorem iteratedDeriv_manuscriptSaddleG0_comp_coefficientMellinParameter
    (q : ℕ) {M : ℂ} (hM : M ∈ leanXiCoefficientSector) :
    iteratedDeriv q
        (fun z => manuscriptSaddleG0 (coefficientMellinParameter z)) M =
      2 ^ q * iteratedDeriv q manuscriptSaddleG0
        (coefficientMellinParameter M) := by
  have hall : Set.EqOn
      (iteratedDeriv q
        (fun z => manuscriptSaddleG0 (coefficientMellinParameter z)))
      (fun z => 2 ^ q * iteratedDeriv q manuscriptSaddleG0
        (coefficientMellinParameter z)) leanXiCoefficientSector := by
    induction q with
    | zero =>
        intro z _hz
        simp only [iteratedDeriv_zero, pow_zero, one_mul]
    | succ q ih =>
        intro z hz
        have hN : coefficientMellinParameter z ∈ leanSaddleSector :=
          leanTwoShiftAdmissible_base (leanCoefficientSector_admissible hz.2)
        have heq : iteratedDeriv q
            (fun w => manuscriptSaddleG0 (coefficientMellinParameter w)) =ᶠ[nhds z]
            (fun w => 2 ^ q * iteratedDeriv q manuscriptSaddleG0
              (coefficientMellinParameter w)) := by
          filter_upwards [isOpen_leanXiCoefficientSector.mem_nhds hz] with w hw
          exact ih hw
        have hNderiv : HasDerivAt coefficientMellinParameter 2 z := by
          unfold coefficientMellinParameter
          change HasDerivAt (fun w : ℂ => (2 : ℂ) * w - (2 : ℂ)) (2 : ℂ) z
          simpa only [id_eq, mul_one] using
            (((hasDerivAt_id z).const_mul (2 : ℂ)).sub_const (2 : ℂ))
        have hright : HasDerivAt
            (fun w => 2 ^ q * iteratedDeriv q manuscriptSaddleG0
              (coefficientMellinParameter w))
            (2 ^ q * (iteratedDeriv (q + 1) manuscriptSaddleG0
              (coefficientMellinParameter z) * 2)) z := by
          exact ((hasDerivAt_iteratedDeriv_manuscriptSaddleG0 q hN).comp z
            hNderiv).const_mul (2 ^ q)
        rw [iteratedDeriv_succ, heq.deriv_eq, hright.deriv]
        ring
  exact hall hM

private theorem iteratedDeriv_affine_dyadic_eq_zero
    (q : ℕ) (hq : 2 ≤ q) (M : ℂ) :
    iteratedDeriv q
      (fun z => coefficientMellinParameter z * log 2) M = 0 := by
  have hq0 : q ≠ 0 := by omega
  have hq1 : q ≠ 1 := by omega
  have hcoeff : iteratedDeriv q coefficientMellinParameter M = 0 := by
    unfold coefficientMellinParameter
    change iteratedDeriv q
      ((fun z : ℂ => (2 : ℂ) * z) - (fun _z : ℂ => (2 : ℂ))) M = 0
    have hlin : ContDiffAt ℂ q (fun z : ℂ => (2 : ℂ) * z) M := by fun_prop
    have hconst : ContDiffAt ℂ q (fun _z : ℂ => (2 : ℂ)) M := by fun_prop
    rw [iteratedDeriv_sub hlin hconst, iteratedDeriv_const_mul_field,
      iteratedDeriv_const]
    simp only [iteratedDeriv_fun_id, hq0, hq1, if_false, mul_zero, sub_zero]
  rw [iteratedDeriv_mul_const_field, hcoeff, zero_mul]

/-- At every order at least two, the remainder derivative is exactly the
natural-main derivative minus the affine-chain derivative of `G0`. -/
theorem iteratedDeriv_xiNaturalMainSaddleRemainder_eq
    (q : ℕ) (hq : 2 ≤ q) {M : ℂ} (hM : M ∈ leanXiCoefficientSector) :
    iteratedDeriv q xiNaturalMainSaddleRemainder M =
      iteratedDeriv q complexXiNaturalAuxiliaryLogMain M -
        2 ^ q * iteratedDeriv q manuscriptSaddleG0
          (coefficientMellinParameter M) := by
  have hN : coefficientMellinParameter M ∈ leanSaddleSector :=
    leanTwoShiftAdmissible_base (leanCoefficientSector_admissible hM.2)
  have hmain : ContDiffAt ℂ q complexXiNaturalAuxiliaryLogMain M :=
    (complexXiNaturalAuxiliaryLogMain_analyticOnNhd M hM).contDiffAt
  have hNanalytic : AnalyticAt ℂ coefficientMellinParameter M := by
    unfold coefficientMellinParameter
    fun_prop
  have hgcomp : ContDiffAt ℂ q
      (fun z => manuscriptSaddleG0 (coefficientMellinParameter z)) M :=
    ((manuscriptSaddleG0_analyticOnNhd
      (coefficientMellinParameter M) hN).comp hNanalytic).contDiffAt
  have haffine : ContDiffAt ℂ q
      (fun z => coefficientMellinParameter z * log 2) M := by
    unfold coefficientMellinParameter
    fun_prop
  unfold xiNaturalMainSaddleRemainder
  change iteratedDeriv q
      ((complexXiNaturalAuxiliaryLogMain -
          fun z => manuscriptSaddleG0 (coefficientMellinParameter z)) +
        fun z => coefficientMellinParameter z * log 2) M = _
  have hsum := iteratedDeriv_add (x := M) (hmain.sub hgcomp) haffine
  have hsub := iteratedDeriv_sub (x := M) hmain hgcomp
  calc
    iteratedDeriv q
        ((complexXiNaturalAuxiliaryLogMain -
            fun z => manuscriptSaddleG0 (coefficientMellinParameter z)) +
          fun z => coefficientMellinParameter z * log 2) M =
        iteratedDeriv q
            (complexXiNaturalAuxiliaryLogMain -
              fun z => manuscriptSaddleG0 (coefficientMellinParameter z)) M +
          iteratedDeriv q
            (fun z => coefficientMellinParameter z * log 2) M := hsum
    _ = (iteratedDeriv q complexXiNaturalAuxiliaryLogMain M -
          iteratedDeriv q
            (fun z => manuscriptSaddleG0 (coefficientMellinParameter z)) M) +
          iteratedDeriv q
            (fun z => coefficientMellinParameter z * log 2) M := by rw [hsub]
    _ = _ := by
      rw [iteratedDeriv_manuscriptSaddleG0_comp_coefficientMellinParameter q hM,
        iteratedDeriv_affine_dyadic_eq_zero q hq]
      ring

theorem xiNaturalMainCorrectionTwo_eq_remainder
    {M : ℂ} (hM : M ∈ leanXiCoefficientSector)
    (I : ManuscriptG0LowerIdentification (coefficientMellinParameter M)) :
    xiNaturalMainCorrectionTwo M =
      iteratedDeriv 2 xiNaturalMainSaddleRemainder M := by
  rw [iteratedDeriv_xiNaturalMainSaddleRemainder_eq 2 (by norm_num) hM,
    I.orderTwo]
  unfold xiNaturalMainCorrectionTwo xiNaturalMainSaddleTwo
  ring

theorem xiNaturalMainCorrectionThree_eq_remainder
    {M : ℂ} (hM : M ∈ leanXiCoefficientSector)
    (I : ManuscriptG0LowerIdentification (coefficientMellinParameter M)) :
    xiNaturalMainCorrectionThree M =
      iteratedDeriv 3 xiNaturalMainSaddleRemainder M := by
  rw [iteratedDeriv_xiNaturalMainSaddleRemainder_eq 3 (by norm_num) hM,
    I.orderThree]
  unfold xiNaturalMainCorrectionThree xiNaturalMainSaddleThree
  ring

theorem xiNaturalMainCorrectionFour_eq_remainder
    {M : ℂ} (hM : M ∈ leanXiCoefficientSector)
    (I : ManuscriptG0LowerIdentification (coefficientMellinParameter M)) :
    xiNaturalMainCorrectionFour M =
      iteratedDeriv 4 xiNaturalMainSaddleRemainder M := by
  rw [iteratedDeriv_xiNaturalMainSaddleRemainder_eq 4 (by norm_num) hM,
    I.orderFour]
  unfold xiNaturalMainCorrectionFour xiNaturalMainSaddleFour
  ring

theorem xiNaturalMainCorrectionFive_eq_remainder
    {M : ℂ} (hM : M ∈ leanXiCoefficientSector)
    (I : ManuscriptG0LowerIdentification (coefficientMellinParameter M)) :
    xiNaturalMainCorrectionFive M =
      iteratedDeriv 5 xiNaturalMainSaddleRemainder M := by
  rw [iteratedDeriv_xiNaturalMainSaddleRemainder_eq 5 (by norm_num) hM,
    I.orderFive]
  unfold xiNaturalMainCorrectionFive xiNaturalMainSaddleFive
  ring

end

end Zeta23.Research.JensenWedge
