import Zeta23.Research.JensenWedge.GammaRatioStirling

/-!
# Holomorphic-parameter coefficient assembly

The paper continues the positive-integer centered-xi coefficient formula by
replacing the factorial quotient by a Gamma quotient and the even theta
moments by their complex Mellin parameters.  This file defines that exact
continuation and first checks the normalization seam: at every positive
integer it is literally the centered-xi coefficient already proved in T1.

No asymptotic estimate is used in this normalization theorem.  The later
sections of this file assemble the T3--T5 moment, two-shift, and complex
Gamma estimates on the fixed sector.
-/

namespace Zeta23.Research.JensenWedge

open Complex Set

noncomputable section

/-- The Mellin parameter `N = 2M - 2` used in the coefficient theorem. -/
def coefficientMellinParameter (M : ℂ) : ℂ :=
  2 * M - 2

/-- The polynomial coefficient `16 (N+2) (N+1)` multiplying the lower
theta moment. -/
def coefficientMomentMultiplier (N : ℂ) : ℂ :=
  16 * (N + 2) * (N + 1)

/-- Holomorphic continuation of the dyadic factor `2^(-2M-2)`. -/
def coefficientDyadicScale (M : ℂ) : ℂ :=
  exp (-(2 * M + 2) * log 2)

/-- The exact complex-parameter continuation of the centered-xi coefficient
identity.  Its agreement with the actual coefficients at positive integers
is proved below. -/
def complexXiCoefficientMoment (M : ℂ) : ℂ :=
  let N := coefficientMellinParameter M
  complexFactorialRatio M * coefficientDyadicScale M *
    (coefficientMomentMultiplier N * fullThetaMoment N -
      fullThetaMoment (N + 2))

theorem coefficientMellinParameter_nat_succ (n : ℕ) :
    coefficientMellinParameter ((n + 1 : ℕ) : ℂ) = ((2 * n : ℕ) : ℂ) := by
  unfold coefficientMellinParameter
  push_cast
  ring

theorem coefficientMomentMultiplier_evenNat (n : ℕ) :
    coefficientMomentMultiplier ((2 * n : ℕ) : ℂ) =
      32 * ((((2 * (n + 1)).choose 2 : ℕ) : ℂ)) := by
  unfold coefficientMomentMultiplier
  rw [Nat.cast_choose_two]
  push_cast
  ring

theorem coefficientDyadicScale_natCast (M : ℕ) :
    coefficientDyadicScale (M : ℂ) =
      1 / (2 : ℂ) ^ (2 * M + 2) := by
  unfold coefficientDyadicScale
  have htwo : (2 : ℂ) ≠ 0 := by norm_num
  have hlog : exp (log (2 : ℂ)) = 2 := Complex.exp_log htwo
  rw [show -(2 * (M : ℂ) + 2) * log 2 =
      -(((2 * M + 2 : ℕ) : ℂ) * log 2) by push_cast; ring]
  rw [Complex.exp_neg, Complex.exp_nat_mul, hlog]
  simp only [one_div]

/-- Exact normalization seam: the complex moment continuation specializes to
the T1 centered-xi coefficient at every positive integer. -/
theorem complexXiCoefficientMoment_nat_succ (n : ℕ) :
    complexXiCoefficientMoment ((n + 1 : ℕ) : ℂ) =
      centeredXiCoefficient (n + 1) := by
  rw [complexXiCoefficientMoment]
  simp only [coefficientMellinParameter_nat_succ,
    coefficientMomentMultiplier_evenNat,
    coefficientDyadicScale_natCast]
  rw [complexFactorialRatio_natCast]
  have hratio :
      (((((n + 1).factorial : ℝ) /
          ((2 * (n + 1)).factorial : ℝ)) : ℂ)) =
        ((n + 1).factorial : ℂ) /
          ((2 * (n + 1)).factorial : ℂ) := by
    push_cast
    rfl
  rw [hratio]
  have h := centeredXiCoefficient_succ_eq_thetaMomentAssembly n
  rw [h]
  have hs2 : ((2 * n : ℕ) : ℂ) + 2 = ((2 * (n + 1) : ℕ) : ℂ) := by
    push_cast
    ring
  rw [hs2]
  ring

/-! ## Exact relative-error assembly -/

/-- Coefficient parameters for which both the Gamma factor and the shifted
Mellin parameter lie in their proved fixed sectors. -/
def leanXiCoefficientSector : Set ℂ :=
  {M | M ∈ leanCoefficientSector ∧
    coefficientMellinParameter M ∈ leanCoefficientSector}

/-- The moment/two-shift relative error at `N=2M-2`. -/
def complexXiMomentRelativeError (M : ℂ) : ℂ :=
  let N := coefficientMellinParameter M
  twoShiftRelativeError (coefficientMomentMultiplier N)
    (quantitativeSaddleBranch N)
    (fullThetaMomentRelativeError N)
    (fullThetaMomentRelativeError (N + 2))
    (saddleMainTwoShiftRelativeError N)

/-- The coefficient main before the harmless elementary simplification used
in the displayed manuscript formula. -/
def complexXiCoefficientMain (M : ℂ) : ℂ :=
  let N := coefficientMellinParameter M
  complexFactorialRatioMain M * coefficientDyadicScale M *
    saddleMomentMain N *
      (coefficientMomentMultiplier N - quantitativeSaddleBranch N ^ 2)

/-- Product-rule combination of the Gamma and moment relative errors. -/
def complexXiCoefficientRelativeError (M : ℂ) : ℂ :=
  let gammaError := complexFactorialRatioCorrection M - 1
  let momentError := complexXiMomentRelativeError M
  gammaError + momentError + gammaError * momentError

theorem complexFactorialRatio_exact_factorization (M : ℂ) :
    complexFactorialRatio M = complexFactorialRatioMain M *
      (1 + (complexFactorialRatioCorrection M - 1)) := by
  rw [show 1 + (complexFactorialRatioCorrection M - 1) =
    complexFactorialRatioCorrection M by ring]
  unfold complexFactorialRatioCorrection
  field_simp [complexFactorialRatioMain_ne_zero]

/-- Exact assembly of all analytic factors.  The only hypotheses are the
concrete fixed-sector memberships proved for the individual components. -/
theorem complexXiCoefficientMoment_factorization_of_ne_zero
    {M : ℂ} (hM : M ∈ leanXiCoefficientSector)
    (hdenomInput :
      coefficientMomentMultiplier (coefficientMellinParameter M) -
        quantitativeSaddleBranch (coefficientMellinParameter M) ^ 2 ≠ 0) :
    complexXiCoefficientMoment M = complexXiCoefficientMain M *
      (1 + complexXiCoefficientRelativeError M) := by
  let N : ℂ := coefficientMellinParameter M
  let c : ℂ := coefficientMomentMultiplier N
  let L : ℂ := quantitativeSaddleBranch N
  let gammaError : ℂ := complexFactorialRatioCorrection M - 1
  let momentError : ℂ := complexXiMomentRelativeError M
  have hNcoef : N ∈ leanCoefficientSector := hM.2
  have hNadm := leanCoefficientSector_admissible hNcoef
  have hN : N ∈ leanSaddleSector := leanTwoShiftAdmissible_base hNadm
  have hN2 : N + 2 ∈ leanSaddleSector := by
    simpa using (hNadm 1 (by constructor <;> norm_num)).1
  have hdenom : c - L ^ 2 ≠ 0 := by
    simpa only [c, L, N] using hdenomInput
  have hratio : saddleMomentMain (N + 2) =
      saddleMomentMain N * L ^ 2 *
        (1 + saddleMainTwoShiftRelativeError N) := by
    simpa only [L] using saddleMomentMain_fixedSector_twoShift_factorization hNcoef
  have hmoment := fullThetaTwoShiftAssembly
    (scale := complexFactorialRatio M * coefficientDyadicScale M)
    (coefficient := c) (saddleScale := L)
    (ratioError := saddleMainTwoShiftRelativeError N)
    hN hN2 hdenom hratio
  have hgamma := complexFactorialRatio_exact_factorization M
  change complexFactorialRatio M * coefficientDyadicScale M *
      (c * fullThetaMoment N - fullThetaMoment (N + 2)) =
    (complexFactorialRatioMain M * coefficientDyadicScale M *
      saddleMomentMain N * (c - L ^ 2)) *
      (1 + (gammaError + momentError + gammaError * momentError))
  have hmoment' :
      complexFactorialRatio M * coefficientDyadicScale M *
          (c * fullThetaMoment N - fullThetaMoment (N + 2)) =
        (complexFactorialRatio M * coefficientDyadicScale M *
          saddleMomentMain N * (c - L ^ 2)) * (1 + momentError) := by
    simpa only [momentError, complexXiMomentRelativeError, N, c, L] using hmoment
  rw [hmoment', hgamma]
  ring

/-! ## Fixed-sector size estimates -/

/-- The selected saddle has the expected logarithmic size, with a deliberately
generous rational constant. -/
theorem quantitativeSaddleBranch_norm_le_two_log_norm
    {s : ℂ} (hs : s ∈ leanSaddleSector) :
    ‖quantitativeSaddleBranch s‖ ≤ 2 * Real.log ‖s‖ := by
  let L : ℂ := quantitativeSaddleBranch s
  let C : ℂ := saddleComparisonCenter s
  have hq := leanSaddleSector_quantitative hs
  have hdist : ‖L - C‖ ≤ 11 / 750 := by
    simpa only [L, C, dist_eq] using quantitativeSaddleBranch_dist_center_le hq
  have hcenter : ‖C‖ ≤ ‖log s‖ + ‖log s‖ / 100 := by
    change ‖log s - log (log s) - log (Real.pi : ℂ)‖ ≤ _
    have hshape : log s - log (log s) - log (Real.pi : ℂ) =
        log s - (log (log s) + log (Real.pi : ℂ)) := by ring
    rw [hshape]
    exact (norm_sub_le _ _).trans
      (add_le_add_right hq.logCorrection_le ‖log s‖)
  have hL : ‖L‖ ≤ ‖C‖ + 11 / 750 := by
    calc
      ‖L‖ = ‖(L - C) + C‖ := by ring_nf
      _ ≤ ‖L - C‖ + ‖C‖ := norm_add_le _ _
      _ ≤ ‖C‖ + 11 / 750 := by linarith
  have hlog := leanSaddleSector_log_norm_le_re_add hs
  have hlogre := leanSaddleSector_log_re_gt hs
  rw [Complex.log_re] at hlog hlogre
  change ‖L‖ ≤ 2 * Real.log ‖s‖
  nlinarith

/-- The inverse curvature has the manuscript scale `log |s| / |s|`. -/
theorem quantitativeSaddleBranch_curvature_inv_le_log_div_norm
    {s : ℂ} (hs : s ∈ leanSaddleSector) :
    1 / ‖leadingCurvature s (quantitativeSaddleBranch s)‖ ≤
      4 * Real.log ‖s‖ / ‖s‖ := by
  let L : ℂ := quantitativeSaddleBranch s
  let K : ℂ := leadingCurvature s L
  let a : ℂ := 1 + 1 / L - (3 / 4) * (L / s)
  have hq := leanSaddleSector_quantitative hs
  have hbounds := quantitativeSaddleBranch_scaled_bounds hq
  have hsne := hq.parameter_ne_zero
  have hLne := hbounds.1
  have ha : 9 / 16 ≤ ‖a‖ := by
    exact saddle_scaled_factor_norm_lower hbounds.2.1 hbounds.2.2
  have hKfactor : K = (s / L) * a := by
    exact leadingCurvature_factor hsne hLne
  have hLupper : ‖L‖ ≤ 2 * Real.log ‖s‖ := by
    simpa only [L] using quantitativeSaddleBranch_norm_le_two_log_norm hs
  have hspos : 0 < ‖s‖ := norm_pos_iff.mpr hsne
  have hKpos : 0 < ‖K‖ := by
    have hKne : K ≠ 0 := by
      rw [hKfactor]
      exact mul_ne_zero (div_ne_zero hsne hLne)
        (saddle_scaled_factor_ne_zero hbounds.2.1 hbounds.2.2)
    exact norm_pos_iff.mpr hKne
  have hlogpos : 0 < Real.log ‖s‖ := by
    have h := leanSaddleSector_log_re_gt hs
    rw [Complex.log_re] at h
    linarith
  have hbasic : (9 / 16 : ℝ) * ‖s‖ ≤ ‖K‖ * ‖L‖ := by
    rw [hKfactor, norm_mul, norm_div]
    have hLpos : 0 < ‖L‖ := norm_pos_iff.mpr hLne
    calc
      (9 / 16 : ℝ) * ‖s‖ ≤ ‖a‖ * ‖s‖ := by
        exact mul_le_mul_of_nonneg_right ha (norm_nonneg s)
      _ = ‖s‖ / ‖L‖ * ‖a‖ * ‖L‖ := by
        field_simp
  have hscaled : ‖s‖ ≤ 4 * Real.log ‖s‖ * ‖K‖ := by
    have hupper : ‖K‖ * ‖L‖ ≤ ‖K‖ * (2 * Real.log ‖s‖) := by
      gcongr
    nlinarith
  change 1 / ‖K‖ ≤ 4 * Real.log ‖s‖ / ‖s‖
  rw [div_le_div_iff₀ hKpos hspos]
  nlinarith

/-- The same curvature estimate at the shifted point, expressed at the base
parameter. -/
theorem quantitativeSaddleBranch_shift_curvature_inv_le_log_div_norm
    {s : ℂ} (hs : s ∈ leanCoefficientSector) :
    1 / ‖leadingCurvature (s + 2) (quantitativeSaddleBranch (s + 2))‖ ≤
      16 * Real.log ‖s‖ / ‖s‖ := by
  have hadm := leanCoefficientSector_admissible hs
  have hs0 : s ∈ leanSaddleSector := leanTwoShiftAdmissible_base hadm
  have hs2 : s + 2 ∈ leanSaddleSector := by
    simpa using (hadm 1 (by constructor <;> norm_num)).1
  have hcompare : ‖s‖ ≤ 2 * ‖s + 2‖ := by
    simpa using (hadm 1 (by constructor <;> norm_num)).2
  have hslarge := leanSaddleSector_parameterNorm_ge_fiveHundredBillion hs0
  have hspos : 0 < ‖s‖ := by linarith
  have hs2pos : 0 < ‖s + 2‖ := by nlinarith
  have hupper : ‖s + 2‖ ≤ 2 * ‖s‖ := by
    calc
      ‖s + 2‖ ≤ ‖s‖ + ‖(2 : ℂ)‖ := norm_add_le _ _
      _ ≤ 2 * ‖s‖ := by norm_num; nlinarith
  have hlogpos : 0 < Real.log ‖s‖ := by
    have h := leanSaddleSector_log_re_gt hs0
    rw [Complex.log_re] at h
    linarith
  have hlog2pos : 0 < Real.log ‖s + 2‖ := by
    have h := leanSaddleSector_log_re_gt hs2
    rw [Complex.log_re] at h
    linarith
  have hlogUpper : Real.log ‖s + 2‖ ≤ 2 * Real.log ‖s‖ := by
    have hmono : Real.log ‖s + 2‖ ≤ Real.log (2 * ‖s‖) :=
      Real.log_le_log hs2pos hupper
    have hlogTwo : Real.log 2 ≤ Real.log ‖s‖ := by
      apply Real.log_le_log (by norm_num)
      linarith
    rw [Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) hspos.ne'] at hmono
    linarith
  have hcurv := quantitativeSaddleBranch_curvature_inv_le_log_div_norm hs2
  calc
    1 / ‖leadingCurvature (s + 2) (quantitativeSaddleBranch (s + 2))‖ ≤
        4 * Real.log ‖s + 2‖ / ‖s + 2‖ := hcurv
    _ ≤ 8 * Real.log ‖s‖ / ‖s + 2‖ := by
      apply div_le_div_of_nonneg_right _ hs2pos.le
      nlinarith
    _ ≤ 16 * Real.log ‖s‖ / ‖s‖ := by
      rw [div_le_div_iff₀ hs2pos hspos]
      have hmul := mul_le_mul_of_nonneg_left hcompare
        (mul_nonneg (by norm_num : (0 : ℝ) ≤ 8) hlogpos.le)
      nlinarith

/-- The polynomial coefficient is at most quadratic on the remote sector. -/
theorem coefficientMomentMultiplier_norm_le
    {s : ℂ} (hs : s ∈ leanSaddleSector) :
    ‖coefficientMomentMultiplier s‖ ≤ 96 * ‖s‖ ^ 2 := by
  have hslarge := leanSaddleSector_parameterNorm_ge_fiveHundredBillion hs
  have hsone : 1 ≤ ‖s‖ := by linarith
  unfold coefficientMomentMultiplier
  rw [norm_mul, norm_mul]
  norm_num
  have h2 : ‖s + 2‖ ≤ 3 * ‖s‖ := by
    calc
      ‖s + 2‖ ≤ ‖s‖ + ‖(2 : ℂ)‖ := norm_add_le _ _
      _ ≤ 3 * ‖s‖ := by norm_num; nlinarith
  have h1 : ‖s + 1‖ ≤ 2 * ‖s‖ := by
    calc
      ‖s + 1‖ ≤ ‖s‖ + ‖(1 : ℂ)‖ := norm_add_le _ _
      _ ≤ 2 * ‖s‖ := by norm_num; nlinarith
  nlinarith [mul_le_mul h2 h1 (norm_nonneg (s + 1))
    (mul_nonneg (by norm_num) (norm_nonneg s))]

/-- The exact cancellation denominator is uniformly separated from zero. -/
theorem coefficientMomentMultiplier_sub_saddle_sq_norm_lower
    {s : ℂ} (hs : s ∈ leanSaddleSector) :
    8 * ‖s‖ ^ 2 ≤
      ‖coefficientMomentMultiplier s - quantitativeSaddleBranch s ^ 2‖ := by
  let L : ℂ := quantitativeSaddleBranch s
  have hslarge := leanSaddleSector_parameterNorm_ge_fiveHundredBillion hs
  have hq := leanSaddleSector_quantitative hs
  have hbounds := quantitativeSaddleBranch_scaled_bounds hq
  have hspos : 0 < ‖s‖ := norm_pos_iff.mpr hq.parameter_ne_zero
  have hplus2 : 3 / 4 * ‖s‖ ≤ ‖s + 2‖ := by
    have htri : ‖s‖ ≤ ‖s + 2‖ + 2 := by
      calc
        ‖s‖ = ‖(s + 2) - 2‖ := by ring_nf
        _ ≤ ‖s + 2‖ + ‖(2 : ℂ)‖ := norm_sub_le _ _
        _ = ‖s + 2‖ + 2 := by norm_num
    nlinarith
  have hplus1 : 3 / 4 * ‖s‖ ≤ ‖s + 1‖ := by
    have htri : ‖s‖ ≤ ‖s + 1‖ + 1 := by
      calc
        ‖s‖ = ‖(s + 1) - 1‖ := by ring_nf
        _ ≤ ‖s + 1‖ + ‖(1 : ℂ)‖ := norm_sub_le _ _
        _ = ‖s + 1‖ + 1 := by norm_num
    nlinarith
  have hcoeff : 9 * ‖s‖ ^ 2 ≤ ‖coefficientMomentMultiplier s‖ := by
    unfold coefficientMomentMultiplier
    rw [norm_mul, norm_mul]
    norm_num
    nlinarith [mul_le_mul hplus2 hplus1
      (mul_nonneg (by norm_num) (norm_nonneg s)) (norm_nonneg (s + 2))]
  have hL : ‖L‖ ≤ (7 / 50 : ℝ) * ‖s‖ := by
    have hsigma : ‖L / s‖ ≤ 7 / 50 := by
      simpa only [L] using hbounds.2.2
    rw [norm_div] at hsigma
    exact (div_le_iff₀ hspos).mp hsigma
  have hLsq : ‖L ^ 2‖ ≤ ‖s‖ ^ 2 := by
    rw [norm_pow]
    have hLleS : ‖L‖ ≤ ‖s‖ := by
      exact hL.trans (by nlinarith [norm_nonneg s])
    exact pow_le_pow_left₀ (norm_nonneg L) hLleS 2
  have htri : ‖coefficientMomentMultiplier s‖ ≤
      ‖coefficientMomentMultiplier s - L ^ 2‖ + ‖L ^ 2‖ := by
    calc
      ‖coefficientMomentMultiplier s‖ =
          ‖(coefficientMomentMultiplier s - L ^ 2) + L ^ 2‖ := by ring_nf
      _ ≤ _ := norm_add_le _ _
  change 8 * ‖s‖ ^ 2 ≤
    ‖coefficientMomentMultiplier s - L ^ 2‖
  nlinarith

theorem coefficientMomentMultiplier_sub_saddle_sq_ne_zero
    {s : ℂ} (hs : s ∈ leanSaddleSector) :
    coefficientMomentMultiplier s - quantitativeSaddleBranch s ^ 2 ≠ 0 := by
  intro hzero
  have hlower := coefficientMomentMultiplier_sub_saddle_sq_norm_lower hs
  rw [hzero, norm_zero] at hlower
  have hspos : 0 < ‖s‖ := norm_pos_iff.mpr
    (leanSaddleSector_quantitative hs).parameter_ne_zero
  nlinarith [sq_pos_of_pos hspos]

/-- Concrete fixed-sector form of the exact coefficient factorization. -/
theorem complexXiCoefficientMoment_factorization
    {M : ℂ} (hM : M ∈ leanXiCoefficientSector) :
    complexXiCoefficientMoment M = complexXiCoefficientMain M *
      (1 + complexXiCoefficientRelativeError M) := by
  apply complexXiCoefficientMoment_factorization_of_ne_zero hM
  exact coefficientMomentMultiplier_sub_saddle_sq_ne_zero
    (leanTwoShiftAdmissible_base
      (leanCoefficientSector_admissible hM.2))

/-- The complete moment/two-shift error has the required logarithmic rate. -/
theorem complexXiMomentRelativeError_norm_le
    {M : ℂ} (hM : M ∈ leanXiCoefficientSector) :
    let N := coefficientMellinParameter M
    ‖complexXiMomentRelativeError M‖ ≤
      (100 * fullThetaMomentErrorCoefficient) * Real.log ‖N‖ / ‖N‖ := by
  let N : ℂ := coefficientMellinParameter M
  let L : ℂ := quantitativeSaddleBranch N
  let K : ℂ := leadingCurvature N L
  let K2 : ℂ := leadingCurvature (N + 2) (quantitativeSaddleBranch (N + 2))
  let C : ℝ := fullThetaMomentErrorCoefficient
  have hNcoef : N ∈ leanCoefficientSector := hM.2
  have hNadm := leanCoefficientSector_admissible hNcoef
  have hN : N ∈ leanSaddleSector := leanTwoShiftAdmissible_base hNadm
  have hN2 : N + 2 ∈ leanSaddleSector := by
    simpa using (hNadm 1 (by constructor <;> norm_num)).1
  have hNpos : 0 < ‖N‖ := norm_pos_iff.mpr
    (leanSaddleSector_quantitative hN).parameter_ne_zero
  have hNlarge := leanSaddleSector_parameterNorm_ge_fiveHundredBillion hN
  have hlogpos : 0 < Real.log ‖N‖ := by
    have h := leanSaddleSector_log_re_gt hN
    rw [Complex.log_re] at h
    linarith
  have hC : 1 ≤ C := by
    norm_num [C, fullThetaMomentErrorCoefficient]
  have hlogone : 1 ≤ Real.log ‖N‖ := by
    have h := leanSaddleSector_log_re_gt hN
    rw [Complex.log_re] at h
    linarith
  have hClog : 1 ≤ C * Real.log ‖N‖ := by
    simpa using mul_le_mul hC hlogone (by norm_num : (0 : ℝ) ≤ 1)
      (by linarith : (0 : ℝ) ≤ C)
  have hcoeff : ‖coefficientMomentMultiplier N‖ ≤ 96 * ‖N‖ ^ 2 :=
    coefficientMomentMultiplier_norm_le hN
  have hLsq : ‖L‖ ^ 2 ≤ ‖N‖ ^ 2 := by
    have hbounds := quantitativeSaddleBranch_scaled_bounds
      (leanSaddleSector_quantitative hN)
    have hsigma : ‖L / N‖ ≤ 7 / 50 := by
      simpa only [L] using hbounds.2.2
    rw [norm_div] at hsigma
    have hL : ‖L‖ ≤ (7 / 50 : ℝ) * ‖N‖ :=
      (div_le_iff₀ hNpos).mp hsigma
    have hLle : ‖L‖ ≤ ‖N‖ := hL.trans (by nlinarith [norm_nonneg N])
    exact pow_le_pow_left₀ (norm_nonneg L) hLle 2
  have he0 : C / ‖K‖ ≤ 4 * C * Real.log ‖N‖ / ‖N‖ := by
    have hcurv := quantitativeSaddleBranch_curvature_inv_le_log_div_norm hN
    have hcurv' : ‖K‖⁻¹ ≤ 4 * Real.log ‖N‖ / ‖N‖ := by
      simpa only [K, L, one_div] using hcurv
    rw [div_eq_mul_inv]
    calc
      C * ‖K‖⁻¹ ≤ C * (4 * Real.log ‖N‖ / ‖N‖) := by gcongr
      _ = 4 * C * Real.log ‖N‖ / ‖N‖ := by ring
  have he2 : C / ‖K2‖ ≤ 16 * C * Real.log ‖N‖ / ‖N‖ := by
    have hcurv := quantitativeSaddleBranch_shift_curvature_inv_le_log_div_norm hNcoef
    have hcurv' : ‖K2‖⁻¹ ≤ 16 * Real.log ‖N‖ / ‖N‖ := by
      simpa only [K2, one_div] using hcurv
    rw [div_eq_mul_inv]
    calc
      C * ‖K2‖⁻¹ ≤ C * (16 * Real.log ‖N‖ / ‖N‖) := by gcongr
      _ = 16 * C * Real.log ‖N‖ / ‖N‖ := by ring
  have heratio : 52 / ‖N‖ ≤ 52 * C * Real.log ‖N‖ / ‖N‖ := by
    apply div_le_div_of_nonneg_right _ hNpos.le
    nlinarith
  have heratioOne : 52 / ‖N‖ ≤ 1 := by
    exact (div_le_one hNpos).2 (by linarith)
  have hcross :
      (52 / ‖N‖) * (C / ‖K2‖) ≤
        16 * C * Real.log ‖N‖ / ‖N‖ := by
    calc
      (52 / ‖N‖) * (C / ‖K2‖) ≤ 1 * (C / ‖K2‖) := by
        gcongr
      _ ≤ 16 * C * Real.log ‖N‖ / ‖N‖ := by simpa using he2
  have hbracket :
      52 / ‖N‖ + C / ‖K2‖ + (52 / ‖N‖) * (C / ‖K2‖) ≤
        84 * C * Real.log ‖N‖ / ‖N‖ := by
    calc
      52 / ‖N‖ + C / ‖K2‖ + (52 / ‖N‖) * (C / ‖K2‖) ≤
          (52 * C * Real.log ‖N‖ / ‖N‖) +
            (16 * C * Real.log ‖N‖ / ‖N‖) +
            (16 * C * Real.log ‖N‖ / ‖N‖) := by
        exact add_le_add (add_le_add heratio he2) hcross
      _ = 84 * C * Real.log ‖N‖ / ‖N‖ := by ring
  have hfirst :
      ‖coefficientMomentMultiplier N‖ * (C / ‖K‖) ≤
        384 * C * Real.log ‖N‖ * ‖N‖ := by
    calc
      ‖coefficientMomentMultiplier N‖ * (C / ‖K‖) ≤
          (96 * ‖N‖ ^ 2) *
            (4 * C * Real.log ‖N‖ / ‖N‖) := by gcongr
      _ = 384 * C * Real.log ‖N‖ * ‖N‖ := by
        field_simp
        ring
  have hsecond :
      ‖L‖ ^ 2 *
          (52 / ‖N‖ + C / ‖K2‖ + (52 / ‖N‖) * (C / ‖K2‖)) ≤
        84 * C * Real.log ‖N‖ * ‖N‖ := by
    calc
      ‖L‖ ^ 2 *
          (52 / ‖N‖ + C / ‖K2‖ + (52 / ‖N‖) * (C / ‖K2‖)) ≤
          ‖N‖ ^ 2 * (84 * C * Real.log ‖N‖ / ‖N‖) := by gcongr
      _ = 84 * C * Real.log ‖N‖ * ‖N‖ := by
        field_simp
  have hraw := fullThetaTwoShiftRelativeError_norm_le
    (s := N) (coefficient := coefficientMomentMultiplier N)
    (saddleScale := L) (ratioError := saddleMainTwoShiftRelativeError N)
    (epsilonRatio := 52 / ‖N‖) (denominatorFloor := 8 * ‖N‖ ^ 2)
    hN hN2 (saddleMainTwoShiftRelativeError_fixedSector hNcoef)
    (coefficientMomentMultiplier_sub_saddle_sq_norm_lower hN)
    (mul_pos (by norm_num) (sq_pos_of_pos hNpos))
  change ‖complexXiMomentRelativeError M‖ ≤
    (100 * C) * Real.log ‖N‖ / ‖N‖
  have hraw' : ‖complexXiMomentRelativeError M‖ ≤
      (‖coefficientMomentMultiplier N‖ * (C / ‖K‖) +
        ‖L‖ ^ 2 *
          (52 / ‖N‖ + C / ‖K2‖ + (52 / ‖N‖) * (C / ‖K2‖))) /
        (8 * ‖N‖ ^ 2) := by
    simpa only [complexXiMomentRelativeError, N, L, K, K2, C] using hraw
  refine hraw'.trans ?_
  apply (div_le_iff₀ (mul_pos (by norm_num) (sq_pos_of_pos hNpos))).2
  calc
    ‖coefficientMomentMultiplier N‖ * (C / ‖K‖) +
        ‖L‖ ^ 2 *
          (52 / ‖N‖ + C / ‖K2‖ + (52 / ‖N‖) * (C / ‖K2‖)) ≤
      384 * C * Real.log ‖N‖ * ‖N‖ +
        84 * C * Real.log ‖N‖ * ‖N‖ := add_le_add hfirst hsecond
    _ ≤ ((100 * C) * Real.log ‖N‖ / ‖N‖) *
        (8 * ‖N‖ ^ 2) := by
      field_simp
      nlinarith [mul_pos hlogpos hNpos]

theorem norm_complexFactorialRatioCorrection_sub_one_fixedSector
    {M : ℂ} (hM : M ∈ leanCoefficientSector) :
    ‖complexFactorialRatioCorrection M - 1‖ ≤ 1 / ‖M‖ := by
  obtain ⟨error, heq, herr⟩ :=
    complexFactorialRatio_relative_error_fixedSector hM
  have hmain := complexFactorialRatioMain_ne_zero M
  have hcorr : complexFactorialRatioCorrection M = 1 + error := by
    unfold complexFactorialRatioCorrection
    rw [heq]
    field_simp
  rw [hcorr]
  simpa using herr

def complexXiCoefficientErrorCoefficient : ℝ :=
  203 * fullThetaMomentErrorCoefficient

/-- Concrete coefficient theorem in the normalization of the exact complex
moment continuation. -/
theorem complexXiCoefficientRelativeError_norm_le
    {M : ℂ} (hM : M ∈ leanXiCoefficientSector) :
    let N := coefficientMellinParameter M
    ‖complexXiCoefficientRelativeError M‖ ≤
      complexXiCoefficientErrorCoefficient * Real.log ‖N‖ / ‖N‖ := by
  let N : ℂ := coefficientMellinParameter M
  let gammaError : ℂ := complexFactorialRatioCorrection M - 1
  let momentError : ℂ := complexXiMomentRelativeError M
  let C : ℝ := fullThetaMomentErrorCoefficient
  have hMouter : M ∈ leanSaddleSector :=
    leanTwoShiftAdmissible_base (leanCoefficientSector_admissible hM.1)
  have hNcoef : N ∈ leanCoefficientSector := hM.2
  have hN : N ∈ leanSaddleSector :=
    leanTwoShiftAdmissible_base (leanCoefficientSector_admissible hNcoef)
  have hMpos : 0 < ‖M‖ := norm_pos_iff.mpr
    (leanSaddleSector_quantitative hMouter).parameter_ne_zero
  have hNpos : 0 < ‖N‖ := norm_pos_iff.mpr
    (leanSaddleSector_quantitative hN).parameter_ne_zero
  have hMlarge := leanSaddleSector_parameterNorm_ge_fiveHundredBillion hMouter
  have hlogone : 1 ≤ Real.log ‖N‖ := by
    have h := leanSaddleSector_log_re_gt hN
    rw [Complex.log_re] at h
    linarith
  have hC : 1 ≤ C := by
    norm_num [C, fullThetaMomentErrorCoefficient]
  have hNM : ‖N‖ ≤ 3 * ‖M‖ := by
    change ‖2 * M - 2‖ ≤ 3 * ‖M‖
    calc
      ‖2 * M - 2‖ ≤ ‖2 * M‖ + ‖(2 : ℂ)‖ := norm_sub_le _ _
      _ = 2 * ‖M‖ + 2 := by norm_num [norm_mul]
      _ ≤ 3 * ‖M‖ := by nlinarith
  have hgamma : ‖gammaError‖ ≤ 3 * Real.log ‖N‖ / ‖N‖ := by
    have hbase := norm_complexFactorialRatioCorrection_sub_one_fixedSector hM.1
    have hcompare : 1 / ‖M‖ ≤ 3 / ‖N‖ := by
      rw [div_le_div_iff₀ hMpos hNpos]
      simpa using hNM
    calc
      ‖gammaError‖ ≤ 1 / ‖M‖ := by simpa only [gammaError] using hbase
      _ ≤ 3 / ‖N‖ := hcompare
      _ ≤ 3 * Real.log ‖N‖ / ‖N‖ := by
        apply div_le_div_of_nonneg_right _ hNpos.le
        nlinarith
  have hgammaOne : ‖gammaError‖ ≤ 1 := by
    have hbase := norm_complexFactorialRatioCorrection_sub_one_fixedSector hM.1
    calc
      ‖gammaError‖ ≤ 1 / ‖M‖ := by simpa only [gammaError] using hbase
      _ ≤ 1 := (div_le_one hMpos).2 (by linarith)
  have hmoment : ‖momentError‖ ≤
      (100 * C) * Real.log ‖N‖ / ‖N‖ := by
    simpa only [momentError, N, C] using complexXiMomentRelativeError_norm_le hM
  change ‖gammaError + momentError + gammaError * momentError‖ ≤
    (203 * C) * Real.log ‖N‖ / ‖N‖
  have hprod : ‖gammaError * momentError‖ ≤
      (100 * C) * Real.log ‖N‖ / ‖N‖ := by
    rw [norm_mul]
    calc
      ‖gammaError‖ * ‖momentError‖ ≤
          1 * ((100 * C) * Real.log ‖N‖ / ‖N‖) := by gcongr
      _ = (100 * C) * Real.log ‖N‖ / ‖N‖ := by ring
  calc
    ‖gammaError + momentError + gammaError * momentError‖ ≤
        ‖gammaError‖ + ‖momentError‖ + ‖gammaError * momentError‖ := by
      calc
        _ ≤ ‖gammaError + momentError‖ + ‖gammaError * momentError‖ :=
          norm_add_le _ _
        _ ≤ ‖gammaError‖ + ‖momentError‖ +
            ‖gammaError * momentError‖ := by
          gcongr
          exact norm_add_le _ _
    _ ≤ 3 * Real.log ‖N‖ / ‖N‖ +
        (100 * C) * Real.log ‖N‖ / ‖N‖ +
        (100 * C) * Real.log ‖N‖ / ‖N‖ := by
      exact add_le_add (add_le_add hgamma hmoment) hprod
    _ ≤ (203 * C) * Real.log ‖N‖ / ‖N‖ := by
      have hClog : 0 ≤ C * Real.log ‖N‖ :=
        mul_nonneg (by linarith) (by linarith)
      field_simp
      nlinarith

theorem complexXiCoefficientMain_ne_zero
    {M : ℂ} (hM : M ∈ leanXiCoefficientSector) :
    complexXiCoefficientMain M ≠ 0 := by
  let N : ℂ := coefficientMellinParameter M
  have hN : N ∈ leanSaddleSector :=
    leanTwoShiftAdmissible_base (leanCoefficientSector_admissible hM.2)
  have hdyadic : coefficientDyadicScale M ≠ 0 := by
    unfold coefficientDyadicScale
    exact exp_ne_zero _
  have hmoment : saddleMomentMain N ≠ 0 := saddleMomentMain_ne_zero hN
  have hdenom := coefficientMomentMultiplier_sub_saddle_sq_ne_zero hN
  exact mul_ne_zero (mul_ne_zero
    (mul_ne_zero (complexFactorialRatioMain_ne_zero M) hdyadic) hmoment) hdenom

/-- T5 in one exported statement: exact factorization, nonzero main, and a
uniform logarithmic relative-error bound on the fixed coefficient sector. -/
theorem complexXiCoefficient_sector_asymptotic
    {M : ℂ} (hM : M ∈ leanXiCoefficientSector) :
    let N := coefficientMellinParameter M
    complexXiCoefficientMain M ≠ 0 ∧
      complexXiCoefficientMoment M = complexXiCoefficientMain M *
        (1 + complexXiCoefficientRelativeError M) ∧
      ‖complexXiCoefficientRelativeError M‖ ≤
        complexXiCoefficientErrorCoefficient * Real.log ‖N‖ / ‖N‖ := by
  exact ⟨complexXiCoefficientMain_ne_zero hM,
    complexXiCoefficientMoment_factorization hM,
    complexXiCoefficientRelativeError_norm_le hM⟩

end

end Zeta23.Research.JensenWedge
