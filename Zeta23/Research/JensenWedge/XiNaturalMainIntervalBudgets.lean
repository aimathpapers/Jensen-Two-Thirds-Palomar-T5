import Zeta23.Research.JensenWedge.XiNaturalMainLowerForwardDifferences
import Zeta23.Research.JensenWedge.PositiveRealSaddle
import Zeta23.Research.JensenWedge.XiNaturalMainCorrectionBounds
import Zeta23.Research.JensenWedge.ExactXiBranch

/-!
# Effective interval budgets for the lower xi coordinates

This file begins the concrete Step-4 instantiation.  It replaces asymptotic
notation by exact scalar inequalities at the left endpoint, proves that those
inequalities hold uniformly on all six real samples, and compares the moving
saddle at `2y-2` with the manuscript scale at `2n-2`.

The cutoff is intentionally enormous.  Effectivity, rather than numerical
usefulness, is the purpose of this certificate.
-/

namespace Zeta23.Research.JensenWedge

open Complex Set

noncomputable section

/-- Real Mellin parameter at the left coefficient node. -/
def xiNaturalMellinCenter (n : ℕ) : ℝ := 2 * (n : ℝ) - 2

/-- The manuscript scale `L_(2n-2)`, returned as a real number. -/
def xiNaturalSaddleScale (n : ℕ) : ℝ :=
  (quantitativeSaddleBranch (xiNaturalMellinCenter n : ℂ)).re

/-- Common relative budget for the change of saddle scale on `n <= y <= n+5`. -/
def xiNaturalSaddleRatioError : ℝ := 1 / 1000000000000

/-- Final normalized saddle contribution budget. -/
def xiNaturalSaddleBudget : ℝ := 1 / 10000000000

/-- Deliberately small final budget for the explicit natural-main correction. -/
def xiNaturalCorrectionBudget : ℝ := 1 / 10000000000

/-- Largest of the four normalized Cauchy constants (the order-five one). -/
def xiNaturalCorrectionScale : ℝ := 25600000000000000000

/-- Final normalized budget for the holomorphic natural-log error. -/
def xiNaturalLogErrorBudget : ℝ := 1 / 10000000000

/-- Largest normalized Cauchy multiplier for error orders two through five. -/
def xiNaturalLogErrorScale : ℝ := 960000000000000000

/-- Total error budget after adding the saddle, explicit correction, and
holomorphic logarithmic-error contributions. -/
def xiNaturalCertificateBudget : ℝ :=
  xiNaturalSaddleBudget + xiNaturalCorrectionBudget + xiNaturalLogErrorBudget

/-- Exact endpoint inequalities used by the saddle half of Step 4. -/
structure XiNaturalSaddleIntervalConditions (n : ℕ) : Prop where
  coefficient_center_in_remote_sector :
    Real.exp (leanSaddleCutoff + 2) < (n : ℝ)
  center_in_remote_sector :
    Real.exp (leanSaddleCutoff + 2) < xiNaturalMellinCenter n
  inverse_rate :
    2 / Real.log (xiNaturalMellinCenter n) ≤ saddleFinalLimitRadius
  sigma_rate :
    2 * Real.log (xiNaturalMellinCenter n + 10) /
        xiNaturalMellinCenter n ≤ saddleFinalLimitRadius
  ratio_rate :
    16 * (320 /
        (9 * xiNaturalMellinCenter n * Real.log (xiNaturalMellinCenter n))) +
      128 / xiNaturalMellinCenter n ≤ xiNaturalSaddleRatioError
  correction_rate :
    xiNaturalCorrectionScale * xiNaturalSaddleScale n *
        Real.log (3 * (n : ℝ)) / (n : ℝ) ≤ xiNaturalCorrectionBudget
  log_error_rate :
    xiNaturalLogErrorScale * xiNaturalSaddleScale n *
        naturalXiCauchyEpsilon (n : ℝ) / (n : ℝ) ≤ xiNaturalLogErrorBudget

theorem XiNaturalSaddleIntervalConditions.center_pos
    {n : ℕ} (C : XiNaturalSaddleIntervalConditions n) :
    0 < xiNaturalMellinCenter n :=
  (Real.exp_pos _).trans C.center_in_remote_sector

theorem XiNaturalSaddleIntervalConditions.n_pos
    {n : ℕ} (C : XiNaturalSaddleIntervalConditions n) : 0 < n := by
  have hc := C.center_pos
  unfold xiNaturalMellinCenter at hc
  exact_mod_cast (show (0 : ℝ) < n by linarith)

private theorem ofReal_mem_leanSaddleSector_of_remote_ge
    {a x : ℝ} (ha : Real.exp (leanSaddleCutoff + 2) < a) (hax : a ≤ x) :
    (x : ℂ) ∈ leanSaddleSector := by
  have hx : 0 < x := (Real.exp_pos _).trans (ha.trans_le hax)
  constructor
  · rw [norm_real, Real.norm_eq_abs, abs_of_pos hx]
    exact (show Real.exp leanSaddleCutoff <
        Real.exp (leanSaddleCutoff + 2) by
      exact Real.exp_lt_exp.mpr (by linarith)).trans (ha.trans_le hax)
  · rw [arg_ofReal_of_nonneg hx.le]
    norm_num [saddleProofAngle]

private theorem xiNatural_interval_mellin_bounds
    {n : ℕ} {y : ℝ} (hy : y ∈ Icc (n : ℝ) ((n : ℝ) + 5)) :
    xiNaturalMellinCenter n ≤ 2 * y - 2 ∧
      2 * y - 2 ≤ xiNaturalMellinCenter n + 10 := by
  constructor <;> unfold xiNaturalMellinCenter <;> linarith [hy.1, hy.2]

theorem XiNaturalSaddleIntervalConditions.interval_mellin_mem_sector
    {n : ℕ} (C : XiNaturalSaddleIntervalConditions n) {y : ℝ}
    (hy : y ∈ Icc (n : ℝ) ((n : ℝ) + 5)) :
    ((2 * y - 2 : ℝ) : ℂ) ∈ leanSaddleSector :=
  ofReal_mem_leanSaddleSector_of_remote_ge C.center_in_remote_sector
    (xiNatural_interval_mellin_bounds hy).1

theorem XiNaturalSaddleIntervalConditions.center_mellin_mem_sector
    {n : ℕ} (C : XiNaturalSaddleIntervalConditions n) :
    (xiNaturalMellinCenter n : ℂ) ∈ leanSaddleSector :=
  ofReal_mem_leanSaddleSector_of_remote_ge C.center_in_remote_sector le_rfl

theorem XiNaturalSaddleIntervalConditions.interval_coefficient_mem_sector
    {n : ℕ} (C : XiNaturalSaddleIntervalConditions n) {y : ℝ}
    (hy : y ∈ Icc (n : ℝ) ((n : ℝ) + 5)) :
    (y : ℂ) ∈ leanXiCoefficientSector := by
  have hyInner := nat_five_interval_mem_manuscriptInteriorDisc
    C.coefficient_center_in_remote_sector hy
  have hnpos : (0 : ℝ) < n :=
    (Real.exp_pos _).trans C.coefficient_center_in_remote_sector
  apply manuscriptCauchy_closedBall_subset_sector
    C.coefficient_center_in_remote_sector
  rw [Metric.mem_closedBall] at hyInner ⊢
  exact hyInner.trans (by
    unfold manuscriptInteriorCauchyRadius manuscriptCauchyRadius
    linarith)

private theorem real_log_mono_of_interval
    {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    Real.log a ≤ Real.log b := Real.log_le_log ha hab

theorem XiNaturalSaddleIntervalConditions.interval_reduced_rates
    {n : ℕ} (C : XiNaturalSaddleIntervalConditions n) {y : ℝ}
    (hy : y ∈ Icc (n : ℝ) ((n : ℝ) + 5)) :
    2 / Real.log (2 * y - 2) ≤ saddleFinalLimitRadius ∧
      2 * Real.log (2 * y - 2) / (2 * y - 2) ≤
        saddleFinalLimitRadius := by
  have hb := xiNatural_interval_mellin_bounds hy
  have ha : 0 < xiNaturalMellinCenter n := C.center_pos
  have hyN : 0 < 2 * y - 2 := ha.trans_le hb.1
  have hlogA : 0 < Real.log (xiNaturalMellinCenter n) := by
    have hcut : 1 < Real.exp (leanSaddleCutoff + 2) := by
      rw [← Real.exp_zero]
      exact Real.exp_lt_exp.mpr (by norm_num [leanSaddleCutoff])
    exact Real.log_pos (hcut.trans C.center_in_remote_sector)
  have hlogY : Real.log (xiNaturalMellinCenter n) ≤ Real.log (2 * y - 2) :=
    real_log_mono_of_interval ha hb.1
  constructor
  · exact (div_le_div_of_nonneg_left (by norm_num) hlogA hlogY).trans
      C.inverse_rate
  · have hlogUpper : Real.log (2 * y - 2) ≤
        Real.log (xiNaturalMellinCenter n + 10) :=
      real_log_mono_of_interval hyN hb.2
    have hlogNonneg : 0 ≤ Real.log (2 * y - 2) := hlogA.le.trans hlogY
    calc
      2 * Real.log (2 * y - 2) / (2 * y - 2) ≤
          2 * Real.log (xiNaturalMellinCenter n + 10) / (2 * y - 2) := by
        exact div_le_div_of_nonneg_right
          (mul_le_mul_of_nonneg_left hlogUpper (by norm_num)) hyN.le
      _ ≤ 2 * Real.log (xiNaturalMellinCenter n + 10) /
          xiNaturalMellinCenter n := by
        have hlogUpperNonneg : 0 ≤
            2 * Real.log (xiNaturalMellinCenter n + 10) := by
          have hmono : Real.log (xiNaturalMellinCenter n) ≤
              Real.log (xiNaturalMellinCenter n + 10) :=
            Real.log_le_log ha (by linarith)
          nlinarith [hlogA]
        exact div_le_div_of_nonneg_left hlogUpperNonneg ha hb.1
      _ ≤ saddleFinalLimitRadius := C.sigma_rate

private theorem branch_norm_sub_le_on_positive_interval
    {a b : ℝ} (haRemote : Real.exp (leanSaddleCutoff + 2) < a)
    (hab : a ≤ b) :
    ‖quantitativeSaddleBranch (b : ℂ) -
        quantitativeSaddleBranch (a : ℂ)‖ ≤
      (16 / (9 * a)) * (b - a) := by
  have ha : 0 < a := (Real.exp_pos _).trans haRemote
  let f : ℝ → ℂ := fun x => quantitativeSaddleBranch (x : ℂ)
  let f' : ℝ → ℂ := fun x =>
    quantitativeSaddleBranch (x : ℂ) /
      sectorialSaddleCurvature (x : ℂ)
        (quantitativeSaddleBranch (x : ℂ))
  have hderiv : ∀ x ∈ Icc a b, HasDerivAt f (f' x) x := by
    intro x hx
    have hs := ofReal_mem_leanSaddleSector_of_remote_ge haRemote hx.1
    simpa only [f, f'] using (hasDerivAt_quantitativeSaddleBranch hs).comp_ofReal
  have hbound : ∀ x ∈ Icc a b, ‖f' x‖ ≤ 16 / (9 * a) := by
    intro x hx
    have hxpos : 0 < x := ha.trans_le hx.1
    have hs := ofReal_mem_leanSaddleSector_of_remote_ge haRemote hx.1
    have hpoint := branchDeriv_mul_parameterNorm_le hs
    rw [norm_real, Real.norm_eq_abs, abs_of_pos hxpos] at hpoint
    have hmul : ‖f' x‖ * a ≤ 16 / 9 := by
      calc
        ‖f' x‖ * a ≤ ‖f' x‖ * x :=
          mul_le_mul_of_nonneg_left hx.1 (norm_nonneg _)
        _ ≤ 16 / 9 := by simpa only [f'] using hpoint
    apply (le_div_iff₀ (show 0 < 9 * a by positivity)).2
    nlinarith
  simpa only [f] using
    norm_sub_le_mul_of_hasDerivAt_le hab hderiv hbound

private theorem XiNaturalSaddleIntervalConditions.branch_ratio_sub_one_norm_le
    {n : ℕ} (C : XiNaturalSaddleIntervalConditions n) {y : ℝ}
    (hy : y ∈ Icc (n : ℝ) ((n : ℝ) + 5)) :
    ‖quantitativeSaddleBranch (xiNaturalMellinCenter n : ℂ) /
          quantitativeSaddleBranch ((2 * y - 2 : ℝ) : ℂ) - 1‖ ≤
      320 / (9 * xiNaturalMellinCenter n *
        Real.log (xiNaturalMellinCenter n)) := by
  let a := xiNaturalMellinCenter n
  let b := 2 * y - 2
  let La := quantitativeSaddleBranch (a : ℂ)
  let Lb := quantitativeSaddleBranch (b : ℂ)
  have hbnds := xiNatural_interval_mellin_bounds hy
  have ha : 0 < a := C.center_pos
  have hb : 0 < b := ha.trans_le hbnds.1
  have hsectorB : (b : ℂ) ∈ leanSaddleSector := by
    simpa only [b] using C.interval_mellin_mem_sector hy
  have hlogA : 0 < Real.log a := by
    have hcut : 1 < Real.exp (leanSaddleCutoff + 2) := by
      rw [← Real.exp_zero]
      exact Real.exp_lt_exp.mpr (by norm_num [leanSaddleCutoff])
    exact Real.log_pos (hcut.trans C.center_in_remote_sector)
  have hvariation : ‖Lb - La‖ ≤ 160 / (9 * a) := by
    have hraw := branch_norm_sub_le_on_positive_interval
      C.center_in_remote_sector hbnds.1
    calc
      ‖Lb - La‖ ≤ (16 / (9 * a)) * (b - a) := by
        simpa only [La, Lb, a, b] using hraw
      _ ≤ (16 / (9 * a)) * 10 := by
        gcongr
        dsimp only [a, b]
        linarith [hbnds.2]
      _ = 160 / (9 * a) := by ring
  have hLbLower : Real.log a / 2 ≤ ‖Lb‖ := by
    have hlogMono : Real.log a ≤ Real.log b := Real.log_le_log ha hbnds.1
    have hbNorm : ‖(b : ℂ)‖ = b := by
      rw [norm_real, Real.norm_eq_abs, abs_of_pos hb]
    have hbranch := quantitativeSaddleBranch_norm_lower_half_realLog hsectorB
    rw [hbNorm] at hbranch
    exact (div_le_div_of_nonneg_right hlogMono (by norm_num)).trans
      (by simpa only [Lb] using hbranch)
  have hLbpos : 0 < ‖Lb‖ := (by positivity : 0 < Real.log a / 2).trans_le hLbLower
  have hshape : La / Lb - 1 = (La - Lb) / Lb := by
    have hne : Lb ≠ 0 := norm_pos_iff.mp hLbpos
    field_simp [hne]
  rw [hshape, norm_div]
  have hvariation' : ‖La - Lb‖ ≤ 160 / (9 * a) := by
    simpa only [norm_sub_rev] using hvariation
  calc
    ‖La - Lb‖ / ‖Lb‖ ≤ (160 / (9 * a)) / (Real.log a / 2) := by
      exact div_le_div₀ (by positivity) hvariation' (by positivity) hLbLower
    _ = 320 / (9 * a * Real.log a) := by field_simp; ring

private theorem XiNaturalSaddleIntervalConditions.parameter_ratio_sub_one_norm_le
    {n : ℕ} (C : XiNaturalSaddleIntervalConditions n) {y : ℝ}
    (hy : y ∈ Icc (n : ℝ) ((n : ℝ) + 5)) :
    ‖(((2 * (n : ℝ)) / (2 * y - 2) : ℝ) : ℂ) - 1‖ ≤
      8 / xiNaturalMellinCenter n := by
  have hbnds := xiNatural_interval_mellin_bounds hy
  have ha : 0 < xiNaturalMellinCenter n := C.center_pos
  have hb : 0 < 2 * y - 2 := ha.trans_le hbnds.1
  have hcast : ((((2 * (n : ℝ)) / (2 * y - 2) : ℝ) : ℂ) - 1) =
      ((((2 * (n : ℝ)) / (2 * y - 2) - 1 : ℝ) : ℂ)) := by
    push_cast
    rfl
  rw [hcast]
  rw [norm_real, Real.norm_eq_abs]
  have hshape : (2 * (n : ℝ)) / (2 * y - 2) - 1 =
      (2 * (n : ℝ) - (2 * y - 2)) / (2 * y - 2) := by
    rw [show (1 : ℝ) = (2 * y - 2) / (2 * y - 2) by
      exact (div_self hb.ne').symm]
    exact (sub_div _ _ _).symm
  rw [hshape, abs_div, abs_of_pos hb]
  have hnum : |2 * (n : ℝ) - (2 * y - 2)| ≤ 8 := by
    rw [abs_le]
    constructor <;> linarith [hy.1, hy.2]
  exact div_le_div₀ (by norm_num) hnum ha hbnds.1

private theorem norm_pow_sub_one_le_two
    {a : ℂ} {delta : ℝ} (hdelta : 0 ≤ delta)
    (ha : ‖a‖ ≤ 2) (hsub : ‖a - 1‖ ≤ delta) (k : ℕ) :
    ‖a ^ k - 1‖ ≤ ((2 : ℝ) ^ k - 1) * delta := by
  induction k with
  | zero => simp
  | succ k ih =>
      have hshape : a ^ (k + 1) - 1 = a * (a ^ k - 1) + (a - 1) := by ring
      rw [hshape]
      calc
        ‖a * (a ^ k - 1) + (a - 1)‖ ≤
            ‖a‖ * ‖a ^ k - 1‖ + ‖a - 1‖ := by
          simpa only [norm_mul] using norm_add_le (a * (a ^ k - 1)) (a - 1)
        _ ≤ 2 * (((2 : ℝ) ^ k - 1) * delta) + delta := by gcongr
        _ = ((2 : ℝ) ^ (k + 1) - 1) * delta := by ring

private theorem norm_pow_mul_sub_one_le
    {a b : ℂ} {deltaA deltaB : ℝ}
    (hdeltaA : 0 ≤ deltaA) (hdeltaB : 0 ≤ deltaB)
    (ha : ‖a‖ ≤ 2) (hsubA : ‖a - 1‖ ≤ deltaA)
    (hsubB : ‖b - 1‖ ≤ deltaB) {k : ℕ} (hk : k ≤ 4) :
    ‖a ^ k * b - 1‖ ≤ 16 * deltaB + 15 * deltaA := by
  have hpowNorm : ‖a ^ k‖ ≤ 16 := by
    rw [norm_pow]
    calc
      ‖a‖ ^ k ≤ (2 : ℝ) ^ k := pow_le_pow_left₀ (norm_nonneg a) ha k
      _ ≤ (2 : ℝ) ^ 4 := pow_le_pow_right₀ (by norm_num) hk
      _ = 16 := by norm_num
  have hpowSub := norm_pow_sub_one_le_two hdeltaA ha hsubA k
  have hcoef : (2 : ℝ) ^ k - 1 ≤ 15 := by
    have hp : (2 : ℝ) ^ k ≤ (2 : ℝ) ^ 4 :=
      pow_le_pow_right₀ (by norm_num) hk
    norm_num at hp ⊢
    linarith
  have hshape : a ^ k * b - 1 = a ^ k * (b - 1) + (a ^ k - 1) := by ring
  rw [hshape]
  calc
    ‖a ^ k * (b - 1) + (a ^ k - 1)‖ ≤
        ‖a ^ k‖ * ‖b - 1‖ + ‖a ^ k - 1‖ := by
      simpa only [norm_mul] using norm_add_le (a ^ k * (b - 1)) (a ^ k - 1)
    _ ≤ 16 * deltaB + (((2 : ℝ) ^ k - 1) * deltaA) := by gcongr
    _ ≤ 16 * deltaB + 15 * deltaA := by gcongr

private theorem XiNaturalSaddleIntervalConditions.combined_ratio_norm_le
    {n : ℕ} (C : XiNaturalSaddleIntervalConditions n) {y : ℝ}
    (hy : y ∈ Icc (n : ℝ) ((n : ℝ) + 5)) {k : ℕ} (hk : k ≤ 4) :
    ‖(((2 * (n : ℝ)) / (2 * y - 2) : ℝ) : ℂ) ^ k *
        (quantitativeSaddleBranch (xiNaturalMellinCenter n : ℂ) /
          quantitativeSaddleBranch ((2 * y - 2 : ℝ) : ℂ)) - 1‖ ≤
      xiNaturalSaddleRatioError := by
  let a : ℂ := (((2 * (n : ℝ)) / (2 * y - 2) : ℝ) : ℂ)
  let b : ℂ := quantitativeSaddleBranch (xiNaturalMellinCenter n : ℂ) /
    quantitativeSaddleBranch ((2 * y - 2 : ℝ) : ℂ)
  let deltaA : ℝ := 8 / xiNaturalMellinCenter n
  let deltaB : ℝ := 320 / (9 * xiNaturalMellinCenter n *
    Real.log (xiNaturalMellinCenter n))
  have hcenter := C.center_pos
  have hlog : 0 < Real.log (xiNaturalMellinCenter n) := by
    have hcut : 1 < Real.exp (leanSaddleCutoff + 2) := by
      rw [← Real.exp_zero]
      exact Real.exp_lt_exp.mpr (by norm_num [leanSaddleCutoff])
    exact Real.log_pos (hcut.trans C.center_in_remote_sector)
  have hA := C.parameter_ratio_sub_one_norm_le hy
  have hB := C.branch_ratio_sub_one_norm_le hy
  have haNorm : ‖a‖ ≤ 2 := by
    have := norm_add_le (a - 1) 1
    have hdeltaSmall : deltaA ≤ 1 := by
      have hcenterHuge : (8 : ℝ) ≤ xiNaturalMellinCenter n := by
        have hcut : (8 : ℝ) < Real.exp (leanSaddleCutoff + 2) := by
          have hpow := Real.pow_div_factorial_le_exp (leanSaddleCutoff + 2)
            (by norm_num [leanSaddleCutoff] : (0 : ℝ) ≤ leanSaddleCutoff + 2) 1
          norm_num [leanSaddleCutoff] at hpow ⊢
          linarith
        exact (hcut.trans C.center_in_remote_sector).le
      have : 8 / xiNaturalMellinCenter n ≤ 1 :=
        (div_le_one₀ hcenter).2 hcenterHuge
      simpa only [deltaA] using this
    calc
      ‖a‖ = ‖(a - 1) + 1‖ := by congr 1 <;> ring
      _ ≤ ‖a - 1‖ + ‖(1 : ℂ)‖ := norm_add_le _ _
      _ ≤ deltaA + 1 := by simpa only [norm_one] using add_le_add hA le_rfl
      _ ≤ 2 := by linarith
  have hraw := norm_pow_mul_sub_one_le
    (show 0 ≤ deltaA by positivity) (show 0 ≤ deltaB by positivity)
    haNorm (by simpa only [a, deltaA] using hA)
    (by simpa only [b, deltaB] using hB) hk
  calc
    ‖a ^ k * b - 1‖ ≤ 16 * deltaB + 15 * deltaA := hraw
    _ ≤ 16 * deltaB + 16 * deltaA := by
      exact add_le_add le_rfl
        (mul_le_mul_of_nonneg_right (by norm_num) (by positivity))
    _ = 16 * (320 / (9 * xiNaturalMellinCenter n *
          Real.log (xiNaturalMellinCenter n))) +
        128 / xiNaturalMellinCenter n := by
      simp only [deltaA, deltaB]
      ring
    _ ≤ xiNaturalSaddleRatioError := C.ratio_rate

theorem XiNaturalSaddleIntervalConditions.saddleScale_pos
    {n : ℕ} (C : XiNaturalSaddleIntervalConditions n) :
    0 < xiNaturalSaddleScale n := by
  have hs := C.center_mellin_mem_sector
  have hreal := quantitativeSaddleBranch_ofReal_eq_re C.center_pos hs
  have hre := quantitativeSaddleBranch_re_gt hs
  simpa only [xiNaturalSaddleScale] using
    (show 0 < (quantitativeSaddleBranch
      (xiNaturalMellinCenter n : ℂ)).re by linarith)

theorem XiNaturalSaddleIntervalConditions.saddleScale_cast
    {n : ℕ} (C : XiNaturalSaddleIntervalConditions n) :
    (xiNaturalSaddleScale n : ℂ) =
      quantitativeSaddleBranch (xiNaturalMellinCenter n : ℂ) := by
  exact (quantitativeSaddleBranch_ofReal_eq_re C.center_pos
    C.center_mellin_mem_sector).symm

private theorem normalized_product_sub_le
    {R H c : ℂ} {delta eta : ℝ}
    (hdelta : 0 ≤ delta) (hR : ‖R - 1‖ ≤ delta)
    (hH : ‖H - c‖ ≤ eta) :
    ‖R * H - c‖ ≤ (1 + delta) * eta + ‖c‖ * delta := by
  have hRnorm : ‖R‖ ≤ 1 + delta := by
    calc
      ‖R‖ = ‖(R - 1) + 1‖ := by congr 1 <;> ring
      _ ≤ ‖R - 1‖ + ‖(1 : ℂ)‖ := norm_add_le _ _
      _ ≤ delta + 1 := by simpa only [norm_one] using add_le_add hR le_rfl
      _ = 1 + delta := by ring
  have hshape : R * H - c = R * (H - c) + (R - 1) * c := by ring
  rw [hshape]
  calc
    ‖R * (H - c) + (R - 1) * c‖ ≤
        ‖R‖ * ‖H - c‖ + ‖R - 1‖ * ‖c‖ := by
      simpa only [norm_mul] using norm_add_le (R * (H - c)) ((R - 1) * c)
    _ ≤ (1 + delta) * eta + delta * ‖c‖ := by gcongr
    _ = (1 + delta) * eta + ‖c‖ * delta := by ring

private theorem XiNaturalSaddleIntervalConditions.interval_final_reduced_limits
    {n : ℕ} (C : XiNaturalSaddleIntervalConditions n) {y : ℝ}
    (hy : y ∈ Icc (n : ℝ) ((n : ℝ) + 5)) :
    let N : ℂ := ((2 * y - 2 : ℝ) : ℂ)
    ‖saddleH2 (manuscriptSaddleR N) (manuscriptSaddleSigma N) - 1‖ ≤
        saddleFinalLimitError ∧
    ‖saddleH3 (manuscriptSaddleR N) (manuscriptSaddleSigma N) - (-1)‖ ≤
        saddleFinalLimitError ∧
    ‖saddleH4 (manuscriptSaddleR N) (manuscriptSaddleSigma N) - 2‖ ≤
        saddleFinalLimitError ∧
    ‖saddleH5 (manuscriptSaddleR N) (manuscriptSaddleSigma N) - (-6)‖ ≤
        saddleFinalLimitError := by
  let N : ℂ := ((2 * y - 2 : ℝ) : ℂ)
  have hs : N ∈ leanSaddleSector := by
    simpa only [N] using C.interval_mellin_mem_sector hy
  rcases C.interval_reduced_rates hy with ⟨hr, hsigma⟩
  have hnorm : ‖N‖ = 2 * y - 2 := by
    have hpos : 0 < 2 * y - 2 := C.center_pos.trans_le
      (xiNatural_interval_mellin_bounds hy).1
    simp only [N, norm_real, Real.norm_eq_abs, abs_of_pos hpos]
  have hr' : 2 / Real.log ‖N‖ ≤ saddleFinalLimitRadius := by
    simpa only [hnorm] using hr
  have hsigma' : 2 * Real.log ‖N‖ / ‖N‖ ≤ saddleFinalLimitRadius := by
    simpa only [hnorm] using hsigma
  rcases manuscriptSaddle_lower_reduced_limits_final hs hr' hsigma' with
    ⟨h2, h3, h4, h5⟩
  constructor
  · exact h2.le
  constructor
  · rw [sub_neg_eq_add]
    exact h3.le
  constructor
  · exact h4.le
  · rw [sub_neg_eq_add]
    exact h5.le

private theorem XiNaturalSaddleIntervalConditions.scaled_saddle_two_eq
    {n : ℕ} (C : XiNaturalSaddleIntervalConditions n) {y : ℝ}
    (hy : y ∈ Icc (n : ℝ) ((n : ℝ) + 5)) :
    (-((n : ℝ) * xiNaturalSaddleScale n) : ℂ) *
        xiNaturalMainSaddleTwo (y : ℂ) =
      -2 *
        (((((2 * (n : ℝ)) / (2 * y - 2) : ℝ) : ℂ) ^ 1) *
          (quantitativeSaddleBranch (xiNaturalMellinCenter n : ℂ) /
            quantitativeSaddleBranch ((2 * y - 2 : ℝ) : ℂ))) *
        saddleH2 (manuscriptSaddleR ((2 * y - 2 : ℝ) : ℂ))
          (manuscriptSaddleSigma ((2 * y - 2 : ℝ) : ℂ)) := by
  have hNpos : 0 < 2 * y - 2 := C.center_pos.trans_le
    (xiNatural_interval_mellin_bounds hy).1
  have hNne : (((2 * y - 2 : ℝ) : ℂ)) ≠ 0 := ofReal_ne_zero.mpr hNpos.ne'
  have hs := C.interval_mellin_mem_sector hy
  have hLne := (quantitativeSaddleBranch_scaled_bounds
    (leanSaddleSector_quantitative hs)).1
  push_cast
  rw [C.saddleScale_cast]
  unfold xiNaturalMainSaddleTwo manuscriptSaddleMainTwo
    coefficientMellinParameter
  push_cast
  field_simp [hNne, hLne]
  ring

private theorem XiNaturalSaddleIntervalConditions.scaled_saddle_three_eq
    {n : ℕ} (C : XiNaturalSaddleIntervalConditions n) {y : ℝ}
    (hy : y ∈ Icc (n : ℝ) ((n : ℝ) + 5)) :
    ((((n : ℝ) ^ 2 * xiNaturalSaddleScale n / 2 : ℝ) : ℂ)) *
        xiNaturalMainSaddleThree (y : ℂ) =
      (((((2 * (n : ℝ)) / (2 * y - 2) : ℝ) : ℂ) ^ 2) *
        (quantitativeSaddleBranch (xiNaturalMellinCenter n : ℂ) /
          quantitativeSaddleBranch ((2 * y - 2 : ℝ) : ℂ))) *
        saddleH3 (manuscriptSaddleR ((2 * y - 2 : ℝ) : ℂ))
          (manuscriptSaddleSigma ((2 * y - 2 : ℝ) : ℂ)) := by
  have hNpos : 0 < 2 * y - 2 := C.center_pos.trans_le
    (xiNatural_interval_mellin_bounds hy).1
  have hNne : (((2 * y - 2 : ℝ) : ℂ)) ≠ 0 := ofReal_ne_zero.mpr hNpos.ne'
  have hs := C.interval_mellin_mem_sector hy
  have hLne := (quantitativeSaddleBranch_scaled_bounds
    (leanSaddleSector_quantitative hs)).1
  push_cast
  rw [C.saddleScale_cast]
  unfold xiNaturalMainSaddleThree manuscriptSaddleMainThree
    coefficientMellinParameter
  push_cast
  field_simp [hNne, hLne]
  ring

private theorem XiNaturalSaddleIntervalConditions.scaled_saddle_four_eq
    {n : ℕ} (C : XiNaturalSaddleIntervalConditions n) {y : ℝ}
    (hy : y ∈ Icc (n : ℝ) ((n : ℝ) + 5)) :
    (-((n : ℝ) ^ 3 * xiNaturalSaddleScale n / 2 : ℝ) : ℂ) *
        xiNaturalMainSaddleFour (y : ℂ) =
      -(((((2 * (n : ℝ)) / (2 * y - 2) : ℝ) : ℂ) ^ 3) *
        (quantitativeSaddleBranch (xiNaturalMellinCenter n : ℂ) /
          quantitativeSaddleBranch ((2 * y - 2 : ℝ) : ℂ))) *
        saddleH4 (manuscriptSaddleR ((2 * y - 2 : ℝ) : ℂ))
          (manuscriptSaddleSigma ((2 * y - 2 : ℝ) : ℂ)) := by
  have hNpos : 0 < 2 * y - 2 := C.center_pos.trans_le
    (xiNatural_interval_mellin_bounds hy).1
  have hNne : (((2 * y - 2 : ℝ) : ℂ)) ≠ 0 := ofReal_ne_zero.mpr hNpos.ne'
  have hs := C.interval_mellin_mem_sector hy
  have hLne := (quantitativeSaddleBranch_scaled_bounds
    (leanSaddleSector_quantitative hs)).1
  push_cast
  rw [C.saddleScale_cast]
  unfold xiNaturalMainSaddleFour manuscriptSaddleMainFour
    coefficientMellinParameter
  push_cast
  field_simp [hNne, hLne]
  ring

private theorem XiNaturalSaddleIntervalConditions.scaled_saddle_five_eq
    {n : ℕ} (C : XiNaturalSaddleIntervalConditions n) {y : ℝ}
    (hy : y ∈ Icc (n : ℝ) ((n : ℝ) + 5)) :
    ((((n : ℝ) ^ 4 * xiNaturalSaddleScale n / 6 : ℝ) : ℂ)) *
        xiNaturalMainSaddleFive (y : ℂ) =
      (1 / 3) *
        (((((2 * (n : ℝ)) / (2 * y - 2) : ℝ) : ℂ) ^ 4) *
          (quantitativeSaddleBranch (xiNaturalMellinCenter n : ℂ) /
            quantitativeSaddleBranch ((2 * y - 2 : ℝ) : ℂ))) *
        saddleH5 (manuscriptSaddleR ((2 * y - 2 : ℝ) : ℂ))
          (manuscriptSaddleSigma ((2 * y - 2 : ℝ) : ℂ)) := by
  have hNpos : 0 < 2 * y - 2 := C.center_pos.trans_le
    (xiNatural_interval_mellin_bounds hy).1
  have hNne : (((2 * y - 2 : ℝ) : ℂ)) ≠ 0 := ofReal_ne_zero.mpr hNpos.ne'
  have hs := C.interval_mellin_mem_sector hy
  have hLne := (quantitativeSaddleBranch_scaled_bounds
    (leanSaddleSector_quantitative hs)).1
  push_cast
  rw [C.saddleScale_cast]
  unfold xiNaturalMainSaddleFive manuscriptSaddleMainFive
    coefficientMellinParameter
  push_cast
  field_simp [hNne, hLne]
  ring

/-- The endpoint conditions construct all four saddle fields of the
primitive pointwise certificate with the exact manuscript signs and scales. -/
theorem XiNaturalSaddleIntervalConditions.saddle_bounds
    {n : ℕ} (C : XiNaturalSaddleIntervalConditions n) :
    (∀ y : ℝ, y ∈ Icc (n : ℝ) ((n : ℝ) + 5) →
      ‖(-((n : ℝ) * xiNaturalSaddleScale n) : ℂ) *
          xiNaturalMainSaddleTwo (y : ℂ) - (-2)‖ ≤ xiNaturalSaddleBudget) ∧
    (∀ y : ℝ, y ∈ Icc (n : ℝ) ((n : ℝ) + 5) →
      ‖((((n : ℝ) ^ 2 * xiNaturalSaddleScale n / 2 : ℝ) : ℂ)) *
          xiNaturalMainSaddleThree (y : ℂ) - (-1)‖ ≤ xiNaturalSaddleBudget) ∧
    (∀ y : ℝ, y ∈ Icc (n : ℝ) ((n : ℝ) + 5) →
      ‖(-((n : ℝ) ^ 3 * xiNaturalSaddleScale n / 2 : ℝ) : ℂ) *
          xiNaturalMainSaddleFour (y : ℂ) - (-2)‖ ≤ xiNaturalSaddleBudget) ∧
    (∀ y : ℝ, y ∈ Icc (n : ℝ) ((n : ℝ) + 5) →
      ‖((((n : ℝ) ^ 4 * xiNaturalSaddleScale n / 6 : ℝ) : ℂ)) *
          xiNaturalMainSaddleFive (y : ℂ) - (-2)‖ ≤ xiNaturalSaddleBudget) := by
  have hdelta : 0 ≤ xiNaturalSaddleRatioError := by
    norm_num [xiNaturalSaddleRatioError]
  have hnumeric2 :
      2 * ((1 + xiNaturalSaddleRatioError) * saddleFinalLimitError +
        xiNaturalSaddleRatioError) ≤ xiNaturalSaddleBudget := by
    norm_num [xiNaturalSaddleRatioError, saddleFinalLimitError,
      xiNaturalSaddleBudget]
  have hnumeric3 :
      (1 + xiNaturalSaddleRatioError) * saddleFinalLimitError +
        xiNaturalSaddleRatioError ≤ xiNaturalSaddleBudget := by
    norm_num [xiNaturalSaddleRatioError, saddleFinalLimitError,
      xiNaturalSaddleBudget]
  have hnumeric4 :
      (1 + xiNaturalSaddleRatioError) * saddleFinalLimitError +
        2 * xiNaturalSaddleRatioError ≤ xiNaturalSaddleBudget := by
    norm_num [xiNaturalSaddleRatioError, saddleFinalLimitError,
      xiNaturalSaddleBudget]
  have hnumeric5 :
      (1 / 3 : ℝ) * ((1 + xiNaturalSaddleRatioError) * saddleFinalLimitError +
        6 * xiNaturalSaddleRatioError) ≤ xiNaturalSaddleBudget := by
    norm_num [xiNaturalSaddleRatioError, saddleFinalLimitError,
      xiNaturalSaddleBudget]
  constructor
  · intro y hy
    let R : ℂ := ((((2 * (n : ℝ)) / (2 * y - 2) : ℝ) : ℂ) ^ 1) *
      (quantitativeSaddleBranch (xiNaturalMellinCenter n : ℂ) /
        quantitativeSaddleBranch ((2 * y - 2 : ℝ) : ℂ))
    let H : ℂ := saddleH2 (manuscriptSaddleR ((2 * y - 2 : ℝ) : ℂ))
      (manuscriptSaddleSigma ((2 * y - 2 : ℝ) : ℂ))
    have hR : ‖R - 1‖ ≤ xiNaturalSaddleRatioError := by
      simpa only [R] using C.combined_ratio_norm_le hy (by norm_num : 1 ≤ 4)
    have hH := (C.interval_final_reduced_limits hy).1
    have hp := normalized_product_sub_le hdelta hR hH
    change ‖R * H - 1‖ ≤
      (1 + xiNaturalSaddleRatioError) * saddleFinalLimitError +
        ‖(1 : ℂ)‖ * xiNaturalSaddleRatioError at hp
    norm_num at hp
    rw [C.scaled_saddle_two_eq hy]
    change ‖-2 * R * H - (-2)‖ ≤ xiNaturalSaddleBudget
    calc
      ‖-2 * R * H - (-2)‖ = 2 * ‖R * H - 1‖ := by
        rw [show -2 * R * H - (-2) = (-2) * (R * H - 1) by ring,
          norm_mul]
        norm_num
      _ ≤ 2 * ((1 + xiNaturalSaddleRatioError) * saddleFinalLimitError +
          xiNaturalSaddleRatioError) := by gcongr
      _ ≤ xiNaturalSaddleBudget := hnumeric2
  constructor
  · intro y hy
    let R : ℂ := ((((2 * (n : ℝ)) / (2 * y - 2) : ℝ) : ℂ) ^ 2) *
      (quantitativeSaddleBranch (xiNaturalMellinCenter n : ℂ) /
        quantitativeSaddleBranch ((2 * y - 2 : ℝ) : ℂ))
    let H : ℂ := saddleH3 (manuscriptSaddleR ((2 * y - 2 : ℝ) : ℂ))
      (manuscriptSaddleSigma ((2 * y - 2 : ℝ) : ℂ))
    have hR : ‖R - 1‖ ≤ xiNaturalSaddleRatioError := by
      simpa only [R] using C.combined_ratio_norm_le hy (by norm_num : 2 ≤ 4)
    have hH := (C.interval_final_reduced_limits hy).2.1
    have hp := normalized_product_sub_le hdelta hR hH
    have hp' : ‖R * H - (-1)‖ ≤
        (1 + xiNaturalSaddleRatioError) * saddleFinalLimitError +
          xiNaturalSaddleRatioError := by
      change ‖R * H - (-1)‖ ≤
        (1 + xiNaturalSaddleRatioError) * saddleFinalLimitError +
          ‖(-1 : ℂ)‖ * xiNaturalSaddleRatioError at hp
      norm_num at hp
      rw [sub_neg_eq_add]
      exact hp
    rw [C.scaled_saddle_three_eq hy]
    change ‖R * H - (-1)‖ ≤ xiNaturalSaddleBudget
    exact hp'.trans hnumeric3
  constructor
  · intro y hy
    let R : ℂ := ((((2 * (n : ℝ)) / (2 * y - 2) : ℝ) : ℂ) ^ 3) *
      (quantitativeSaddleBranch (xiNaturalMellinCenter n : ℂ) /
        quantitativeSaddleBranch ((2 * y - 2 : ℝ) : ℂ))
    let H : ℂ := saddleH4 (manuscriptSaddleR ((2 * y - 2 : ℝ) : ℂ))
      (manuscriptSaddleSigma ((2 * y - 2 : ℝ) : ℂ))
    have hR : ‖R - 1‖ ≤ xiNaturalSaddleRatioError := by
      simpa only [R] using C.combined_ratio_norm_le hy (by norm_num : 3 ≤ 4)
    have hH := (C.interval_final_reduced_limits hy).2.2.1
    have hp := normalized_product_sub_le hdelta hR hH
    have hp' : ‖R * H - 2‖ ≤
        (1 + xiNaturalSaddleRatioError) * saddleFinalLimitError +
          2 * xiNaturalSaddleRatioError := by
      norm_num only [norm_ofNat] at hp
      simpa only [H] using hp
    rw [C.scaled_saddle_four_eq hy]
    change ‖-R * H - (-2)‖ ≤ xiNaturalSaddleBudget
    calc
      ‖-R * H - (-2)‖ = ‖R * H - 2‖ := by
        rw [show -R * H - (-2) = -(R * H - 2) by ring, norm_neg]
      _ ≤ (1 + xiNaturalSaddleRatioError) * saddleFinalLimitError +
          2 * xiNaturalSaddleRatioError := hp'
      _ ≤ xiNaturalSaddleBudget := hnumeric4
  · intro y hy
    let R : ℂ := ((((2 * (n : ℝ)) / (2 * y - 2) : ℝ) : ℂ) ^ 4) *
      (quantitativeSaddleBranch (xiNaturalMellinCenter n : ℂ) /
        quantitativeSaddleBranch ((2 * y - 2 : ℝ) : ℂ))
    let H : ℂ := saddleH5 (manuscriptSaddleR ((2 * y - 2 : ℝ) : ℂ))
      (manuscriptSaddleSigma ((2 * y - 2 : ℝ) : ℂ))
    have hR : ‖R - 1‖ ≤ xiNaturalSaddleRatioError := by
      simpa only [R] using C.combined_ratio_norm_le hy (by norm_num : 4 ≤ 4)
    have hH := (C.interval_final_reduced_limits hy).2.2.2
    have hp := normalized_product_sub_le hdelta hR hH
    have hp' : ‖R * H - (-6)‖ ≤
        (1 + xiNaturalSaddleRatioError) * saddleFinalLimitError +
          6 * xiNaturalSaddleRatioError := by
      norm_num only [norm_neg, norm_ofNat] at hp
      simpa only [H] using hp
    rw [C.scaled_saddle_five_eq hy]
    change ‖(1 / 3 : ℂ) * R * H - (-2)‖ ≤ xiNaturalSaddleBudget
    calc
      ‖(1 / 3 : ℂ) * R * H - (-2)‖ =
          (1 / 3 : ℝ) * ‖R * H - (-6)‖ := by
        rw [show (1 / 3 : ℂ) * R * H - (-2) =
          (1 / 3 : ℂ) * (R * H - (-6)) by ring, norm_mul]
        norm_num
      _ ≤ (1 / 3 : ℝ) *
          ((1 + xiNaturalSaddleRatioError) * saddleFinalLimitError +
            6 * xiNaturalSaddleRatioError) := by gcongr
      _ ≤ xiNaturalSaddleBudget := hnumeric5

/-- The logarithmic-size remainder and the single worst-order endpoint rate
construct all four normalized natural-main correction fields. -/
theorem XiNaturalSaddleIntervalConditions.correction_bounds
    {n : ℕ} (C : XiNaturalSaddleIntervalConditions n)
    (I : ∀ y : ℝ, y ∈ Icc (n : ℝ) ((n : ℝ) + 5) →
      ManuscriptG0LowerIdentification ((2 * y - 2 : ℝ) : ℂ)) :
    (∀ y : ℝ, y ∈ Icc (n : ℝ) ((n : ℝ) + 5) →
      ‖(-((n : ℝ) * xiNaturalSaddleScale n) : ℂ) *
          xiNaturalMainCorrectionTwo (y : ℂ)‖ ≤ xiNaturalCorrectionBudget) ∧
    (∀ y : ℝ, y ∈ Icc (n : ℝ) ((n : ℝ) + 5) →
      ‖((((n : ℝ) ^ 2 * xiNaturalSaddleScale n / 2 : ℝ) : ℂ)) *
          xiNaturalMainCorrectionThree (y : ℂ)‖ ≤ xiNaturalCorrectionBudget) ∧
    (∀ y : ℝ, y ∈ Icc (n : ℝ) ((n : ℝ) + 5) →
      ‖(-((n : ℝ) ^ 3 * xiNaturalSaddleScale n / 2 : ℝ) : ℂ) *
          xiNaturalMainCorrectionFour (y : ℂ)‖ ≤ xiNaturalCorrectionBudget) ∧
    (∀ y : ℝ, y ∈ Icc (n : ℝ) ((n : ℝ) + 5) →
      ‖((((n : ℝ) ^ 4 * xiNaturalSaddleScale n / 6 : ℝ) : ℂ)) *
          xiNaturalMainCorrectionFive (y : ℂ)‖ ≤ xiNaturalCorrectionBudget) := by
  have hnpos : (0 : ℝ) < n := by exact_mod_cast C.n_pos
  have hnOne : (1 : ℝ) ≤ n := by exact_mod_cast C.n_pos
  have hLpos : 0 < xiNaturalSaddleScale n := C.saddleScale_pos
  have hrpos : 0 < manuscriptInteriorCauchyRadius (n : ℝ) := by
    unfold manuscriptInteriorCauchyRadius
    positivity
  have hinner : ∀ y : ℝ, y ∈ Icc (n : ℝ) ((n : ℝ) + 5) →
      (y : ℂ) ∈ Metric.closedBall (n : ℂ)
        (manuscriptInteriorCauchyRadius (n : ℝ)) := by
    intro y hy
    exact nat_five_interval_mem_manuscriptInteriorDisc
      C.coefficient_center_in_remote_sector hy
  have hderiv : ∀ (q : ℕ), q ≤ 5 → ∀ y : ℝ,
      y ∈ Icc (n : ℝ) ((n : ℝ) + 5) →
      ‖iteratedDeriv q xiNaturalMainSaddleRemainder (y : ℂ)‖ ≤
        q.factorial * (40 * Real.log (3 * (n : ℝ))) /
          manuscriptInteriorCauchyRadius (n : ℝ) ^ q := by
    intro q hq y hy
    exact xiNaturalMainSaddleRemainder_derivatives_through_five_on_half_disc
      C.coefficient_center_in_remote_sector (hinner y hy) q hq
  have hscale : ∀ {A : ℝ}, 0 ≤ A → A ≤ xiNaturalCorrectionScale →
      A * xiNaturalSaddleScale n * Real.log (3 * (n : ℝ)) / (n : ℝ) ≤
        xiNaturalCorrectionBudget := by
    intro A hA hAmax
    exact (div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right hAmax hLpos.le)
        (by
          apply Real.log_nonneg
          have : (1 : ℝ) ≤ 3 * n := by nlinarith
          exact this)) hnpos.le).trans C.correction_rate
  constructor
  · intro y hy
    have hyM := C.interval_coefficient_mem_sector hy
    have hI : ManuscriptG0LowerIdentification
        (coefficientMellinParameter (y : ℂ)) := by
      simpa only [coefficientMellinParameter, ofReal_mul, ofReal_ofNat,
        ofReal_sub] using I y hy
    rw [xiNaturalMainCorrectionTwo_eq_remainder hyM hI, norm_mul]
    have hb := hderiv 2 (by norm_num) y hy
    have hnormScale : ‖(-((n : ℝ) * xiNaturalSaddleScale n) : ℂ)‖ =
        (n : ℝ) * xiNaturalSaddleScale n := by
      push_cast
      simp only [norm_neg, norm_mul, Complex.norm_natCast, norm_real, Real.norm_eq_abs,
        abs_of_pos hnpos, abs_of_pos hLpos]
    rw [hnormScale]
    calc
      (n : ℝ) * xiNaturalSaddleScale n *
          ‖iteratedDeriv 2 xiNaturalMainSaddleRemainder (y : ℂ)‖ ≤
        (n : ℝ) * xiNaturalSaddleScale n *
          ((2 : ℕ).factorial * (40 * Real.log (3 * (n : ℝ))) /
            manuscriptInteriorCauchyRadius (n : ℝ) ^ 2) := by gcongr
      _ = 320000000 * xiNaturalSaddleScale n *
          Real.log (3 * (n : ℝ)) / (n : ℝ) := by
        unfold manuscriptInteriorCauchyRadius
        field_simp [hnpos.ne']
        ring
      _ ≤ xiNaturalCorrectionBudget := hscale (by norm_num)
        (by norm_num [xiNaturalCorrectionScale])
  constructor
  · intro y hy
    have hyM := C.interval_coefficient_mem_sector hy
    have hI : ManuscriptG0LowerIdentification
        (coefficientMellinParameter (y : ℂ)) := by
      simpa only [coefficientMellinParameter, ofReal_mul, ofReal_ofNat,
        ofReal_sub] using I y hy
    rw [xiNaturalMainCorrectionThree_eq_remainder hyM hI, norm_mul]
    have hb := hderiv 3 (by norm_num) y hy
    have hnormScale :
        ‖((((n : ℝ) ^ 2 * xiNaturalSaddleScale n / 2 : ℝ) : ℂ))‖ =
          (n : ℝ) ^ 2 * xiNaturalSaddleScale n / 2 := by
      rw [norm_real, Real.norm_eq_abs, abs_of_pos (by positivity)]
    rw [hnormScale]
    calc
      ((n : ℝ) ^ 2 * xiNaturalSaddleScale n / 2) *
          ‖iteratedDeriv 3 xiNaturalMainSaddleRemainder (y : ℂ)‖ ≤
        ((n : ℝ) ^ 2 * xiNaturalSaddleScale n / 2) *
          ((3 : ℕ).factorial * (40 * Real.log (3 * (n : ℝ))) /
            manuscriptInteriorCauchyRadius (n : ℝ) ^ 3) := by gcongr
      _ = 960000000000 * xiNaturalSaddleScale n *
          Real.log (3 * (n : ℝ)) / (n : ℝ) := by
        unfold manuscriptInteriorCauchyRadius
        field_simp [hnpos.ne']
        ring
      _ ≤ xiNaturalCorrectionBudget := hscale (by norm_num)
        (by norm_num [xiNaturalCorrectionScale])
  constructor
  · intro y hy
    have hyM := C.interval_coefficient_mem_sector hy
    have hI : ManuscriptG0LowerIdentification
        (coefficientMellinParameter (y : ℂ)) := by
      simpa only [coefficientMellinParameter, ofReal_mul, ofReal_ofNat,
        ofReal_sub] using I y hy
    rw [xiNaturalMainCorrectionFour_eq_remainder hyM hI, norm_mul]
    have hb := hderiv 4 (by norm_num) y hy
    have hnormScale :
        ‖(-((n : ℝ) ^ 3 * xiNaturalSaddleScale n / 2 : ℝ) : ℂ)‖ =
          (n : ℝ) ^ 3 * xiNaturalSaddleScale n / 2 := by
      rw [norm_neg, norm_real, Real.norm_eq_abs, abs_of_pos (by positivity)]
    rw [hnormScale]
    calc
      ((n : ℝ) ^ 3 * xiNaturalSaddleScale n / 2) *
          ‖iteratedDeriv 4 xiNaturalMainSaddleRemainder (y : ℂ)‖ ≤
        ((n : ℝ) ^ 3 * xiNaturalSaddleScale n / 2) *
          ((4 : ℕ).factorial * (40 * Real.log (3 * (n : ℝ))) /
            manuscriptInteriorCauchyRadius (n : ℝ) ^ 4) := by gcongr
      _ = 7680000000000000 * xiNaturalSaddleScale n *
          Real.log (3 * (n : ℝ)) / (n : ℝ) := by
        unfold manuscriptInteriorCauchyRadius
        field_simp [hnpos.ne']
        ring
      _ ≤ xiNaturalCorrectionBudget := hscale (by norm_num)
        (by norm_num [xiNaturalCorrectionScale])
  · intro y hy
    have hyM := C.interval_coefficient_mem_sector hy
    have hI : ManuscriptG0LowerIdentification
        (coefficientMellinParameter (y : ℂ)) := by
      simpa only [coefficientMellinParameter, ofReal_mul, ofReal_ofNat,
        ofReal_sub] using I y hy
    rw [xiNaturalMainCorrectionFive_eq_remainder hyM hI, norm_mul]
    have hb := hderiv 5 (by norm_num) y hy
    have hnormScale :
        ‖((((n : ℝ) ^ 4 * xiNaturalSaddleScale n / 6 : ℝ) : ℂ))‖ =
          (n : ℝ) ^ 4 * xiNaturalSaddleScale n / 6 := by
      rw [norm_real, Real.norm_eq_abs, abs_of_pos (by positivity)]
    rw [hnormScale]
    calc
      ((n : ℝ) ^ 4 * xiNaturalSaddleScale n / 6) *
          ‖iteratedDeriv 5 xiNaturalMainSaddleRemainder (y : ℂ)‖ ≤
        ((n : ℝ) ^ 4 * xiNaturalSaddleScale n / 6) *
          ((5 : ℕ).factorial * (40 * Real.log (3 * (n : ℝ))) /
            manuscriptInteriorCauchyRadius (n : ℝ) ^ 5) := by gcongr
      _ = xiNaturalCorrectionScale * xiNaturalSaddleScale n *
          Real.log (3 * (n : ℝ)) / (n : ℝ) := by
        unfold manuscriptInteriorCauchyRadius xiNaturalCorrectionScale
        field_simp [hnpos.ne']
        ring
      _ ≤ xiNaturalCorrectionBudget := C.correction_rate

/-- Fully constructed primitive pointwise certificate.  Its only supplied
non-Lean input is the already disclosed four-equality CAS identification at
each real point; every analytic and numerical budget is kernel checked. -/
theorem XiNaturalSaddleIntervalConditions.pointwiseCertificate
    {n : ℕ} (C : XiNaturalSaddleIntervalConditions n)
    (I : ∀ y : ℝ, y ∈ Icc (n : ℝ) ((n : ℝ) + 5) →
      ManuscriptG0LowerIdentification ((2 * y - 2 : ℝ) : ℂ)) :
    XiNaturalMainLowerPointwiseCertificate n (xiNaturalSaddleScale n)
      xiNaturalSaddleBudget xiNaturalCorrectionBudget := by
  rcases C.saddle_bounds with ⟨hs2, hs3, hs4, hs5⟩
  rcases C.correction_bounds I with ⟨hc2, hc3, hc4, hc5⟩
  exact {
    saddleError_nonneg := by norm_num [xiNaturalSaddleBudget]
    correctionError_nonneg := by norm_num [xiNaturalCorrectionBudget]
    interval_mem_sector := fun y hy => C.interval_coefficient_mem_sector hy
    saddleTwo := hs2
    saddleThree := hs3
    saddleFour := hs4
    saddleFive := hs5
    correctionTwo := hc2
    correctionThree := hc3
    correctionFour := hc4
    correctionFive := hc5
  }

/-- All four normalized forward differences of the exact natural-log error
fit the single worst-order endpoint budget. -/
theorem XiNaturalSaddleIntervalConditions.logError_scaled_bounds
    {n : ℕ} (C : XiNaturalSaddleIntervalConditions n) :
    ‖(-((n : ℝ) * xiNaturalSaddleScale n) : ℂ) *
        complexForwardDiff 2 complexXiNaturalAuxiliaryLogError (n : ℂ)‖ ≤
      xiNaturalLogErrorBudget ∧
    ‖((((n : ℝ) ^ 2 * xiNaturalSaddleScale n / 2 : ℝ) : ℂ)) *
        complexForwardDiff 3 complexXiNaturalAuxiliaryLogError (n : ℂ)‖ ≤
      xiNaturalLogErrorBudget ∧
    ‖(-((n : ℝ) ^ 3 * xiNaturalSaddleScale n / 2 : ℝ) : ℂ) *
        complexForwardDiff 4 complexXiNaturalAuxiliaryLogError (n : ℂ)‖ ≤
      xiNaturalLogErrorBudget ∧
    ‖((((n : ℝ) ^ 4 * xiNaturalSaddleScale n / 6 : ℝ) : ℂ)) *
        complexForwardDiff 5 complexXiNaturalAuxiliaryLogError (n : ℂ)‖ ≤
      xiNaturalLogErrorBudget := by
  have hnpos : (0 : ℝ) < n := by exact_mod_cast C.n_pos
  have hLpos := C.saddleScale_pos
  have hepsNonneg : 0 ≤ naturalXiCauchyEpsilon (n : ℝ) := by
    unfold naturalXiCauchyEpsilon
    have hlog : 0 ≤ Real.log (3 * (n : ℝ)) := by
      apply Real.log_nonneg
      have hnOne : (1 : ℝ) ≤ n := by exact_mod_cast C.n_pos
      nlinarith
    have hconstant : 0 ≤ 100 * fullThetaMomentErrorCoefficient := by
      norm_num [fullThetaMomentErrorCoefficient]
    positivity
  have hscale : ∀ {A : ℝ}, 0 ≤ A → A ≤ xiNaturalLogErrorScale →
      A * xiNaturalSaddleScale n * naturalXiCauchyEpsilon (n : ℝ) /
          (n : ℝ) ≤ xiNaturalLogErrorBudget := by
    intro A hA hAmax
    exact (div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right hAmax hLpos.le) hepsNonneg)
      hnpos.le).trans C.log_error_rate
  rcases complexXiNaturalAuxiliaryLogError_certificate_bounds
    C.coefficient_center_in_remote_sector with ⟨h2, h3, h4, h5⟩
  constructor
  · rw [norm_mul]
    have hnormScale : ‖(-((n : ℝ) * xiNaturalSaddleScale n) : ℂ)‖ =
        (n : ℝ) * xiNaturalSaddleScale n := by
      push_cast
      simp only [norm_neg, norm_mul, Complex.norm_natCast, norm_real,
        Real.norm_eq_abs, abs_of_pos hLpos]
    rw [hnormScale]
    calc
      (n : ℝ) * xiNaturalSaddleScale n *
          ‖complexForwardDiff 2 complexXiNaturalAuxiliaryLogError (n : ℂ)‖ ≤
        (n : ℝ) * xiNaturalSaddleScale n *
          ((2 : ℕ).factorial * ((3 / 2 : ℝ) *
              naturalXiCauchyEpsilon (n : ℝ)) /
            manuscriptInteriorCauchyRadius (n : ℝ) ^ 2) := by gcongr
      _ = 12000000 * xiNaturalSaddleScale n *
          naturalXiCauchyEpsilon (n : ℝ) / (n : ℝ) := by
        unfold manuscriptInteriorCauchyRadius
        field_simp [hnpos.ne']
        ring
      _ ≤ xiNaturalLogErrorBudget := hscale (by norm_num)
        (by norm_num [xiNaturalLogErrorScale])
  constructor
  · rw [norm_mul]
    have hnormScale :
        ‖((((n : ℝ) ^ 2 * xiNaturalSaddleScale n / 2 : ℝ) : ℂ))‖ =
          (n : ℝ) ^ 2 * xiNaturalSaddleScale n / 2 := by
      rw [norm_real, Real.norm_eq_abs, abs_of_pos (by positivity)]
    rw [hnormScale]
    calc
      ((n : ℝ) ^ 2 * xiNaturalSaddleScale n / 2) *
          ‖complexForwardDiff 3 complexXiNaturalAuxiliaryLogError (n : ℂ)‖ ≤
        ((n : ℝ) ^ 2 * xiNaturalSaddleScale n / 2) *
          ((3 : ℕ).factorial * ((3 / 2 : ℝ) *
              naturalXiCauchyEpsilon (n : ℝ)) /
            manuscriptInteriorCauchyRadius (n : ℝ) ^ 3) := by gcongr
      _ = 36000000000 * xiNaturalSaddleScale n *
          naturalXiCauchyEpsilon (n : ℝ) / (n : ℝ) := by
        unfold manuscriptInteriorCauchyRadius
        field_simp [hnpos.ne']
        ring
      _ ≤ xiNaturalLogErrorBudget := hscale (by norm_num)
        (by norm_num [xiNaturalLogErrorScale])
  constructor
  · rw [norm_mul]
    have hnormScale :
        ‖(-((n : ℝ) ^ 3 * xiNaturalSaddleScale n / 2 : ℝ) : ℂ)‖ =
          (n : ℝ) ^ 3 * xiNaturalSaddleScale n / 2 := by
      rw [norm_neg, norm_real, Real.norm_eq_abs, abs_of_pos (by positivity)]
    rw [hnormScale]
    calc
      ((n : ℝ) ^ 3 * xiNaturalSaddleScale n / 2) *
          ‖complexForwardDiff 4 complexXiNaturalAuxiliaryLogError (n : ℂ)‖ ≤
        ((n : ℝ) ^ 3 * xiNaturalSaddleScale n / 2) *
          ((4 : ℕ).factorial * ((3 / 2 : ℝ) *
              naturalXiCauchyEpsilon (n : ℝ)) /
            manuscriptInteriorCauchyRadius (n : ℝ) ^ 4) := by gcongr
      _ = 288000000000000 * xiNaturalSaddleScale n *
          naturalXiCauchyEpsilon (n : ℝ) / (n : ℝ) := by
        unfold manuscriptInteriorCauchyRadius
        field_simp [hnpos.ne']
        ring
      _ ≤ xiNaturalLogErrorBudget := hscale (by norm_num)
        (by norm_num [xiNaturalLogErrorScale])
  · rw [norm_mul]
    have hnormScale :
        ‖((((n : ℝ) ^ 4 * xiNaturalSaddleScale n / 6 : ℝ) : ℂ))‖ =
          (n : ℝ) ^ 4 * xiNaturalSaddleScale n / 6 := by
      rw [norm_real, Real.norm_eq_abs, abs_of_pos (by positivity)]
    rw [hnormScale]
    calc
      ((n : ℝ) ^ 4 * xiNaturalSaddleScale n / 6) *
          ‖complexForwardDiff 5 complexXiNaturalAuxiliaryLogError (n : ℂ)‖ ≤
        ((n : ℝ) ^ 4 * xiNaturalSaddleScale n / 6) *
          ((5 : ℕ).factorial * ((3 / 2 : ℝ) *
              naturalXiCauchyEpsilon (n : ℝ)) /
            manuscriptInteriorCauchyRadius (n : ℝ) ^ 5) := by gcongr
      _ = xiNaturalLogErrorScale * xiNaturalSaddleScale n *
          naturalXiCauchyEpsilon (n : ℝ) / (n : ℝ) := by
        unfold manuscriptInteriorCauchyRadius xiNaturalLogErrorScale
        field_simp [hnpos.ne']
        ring
      _ ≤ xiNaturalLogErrorBudget := C.log_error_rate

private theorem norm_scaled_sum_add_le
    (a u v c : ℂ) {eu ev : ℝ}
    (hu : ‖a * u + c‖ ≤ eu) (hv : ‖a * v‖ ≤ ev) :
    ‖a * (u + v) + c‖ ≤ eu + ev := by
  calc
    ‖a * (u + v) + c‖ = ‖(a * u + c) + a * v‖ := by ring
    _ ≤ ‖a * u + c‖ + ‖a * v‖ := norm_add_le _ _
    _ ≤ eu + ev := add_le_add hu hv

/-- The exact real xi finite differences satisfy the four normalized
interval inequalities required by `ExactXiSaddleIntervalCertificate`.

The sole non-kernel input remains the disclosed four-equality identification
of the explicit lower-order tower.  All propagation from that interface,
including the natural-main correction and the holomorphic logarithmic error,
is checked here by Lean. -/
theorem XiNaturalSaddleIntervalConditions.exactCertificate
    {n : ℕ} (C : XiNaturalSaddleIntervalConditions n)
    (I : ∀ y : ℝ, y ∈ Icc (n : ℝ) ((n : ℝ) + 5) →
      ManuscriptG0LowerIdentification ((2 * y - 2 : ℝ) : ℂ)) :
    ExactXiSaddleIntervalCertificate n (xiNaturalSaddleScale n)
      xiNaturalCertificateBudget := by
  have hm := (C.pointwiseCertificate I).derivativeBounds.forwardDiff_bounds
  have he := C.logError_scaled_bounds
  have hd := ofReal_exactXiAuxiliarySecondDiff_forwardDiffs_decomposition
    C.coefficient_center_in_remote_sector
  refine {
    epsilon_nonneg := by
      norm_num [xiNaturalCertificateBudget, xiNaturalSaddleBudget,
        xiNaturalCorrectionBudget, xiNaturalLogErrorBudget]
    orderTwo := ?_
    orderThree := ?_
    orderFour := ?_
    orderFive := ?_
  }
  · have hcomplex :
        ‖(-((n : ℝ) * xiNaturalSaddleScale n) : ℂ) *
              (((natForwardDiff0 (exactXiAuxiliarySecondDiff n) : ℝ) : ℂ)) + 2‖ ≤
            xiNaturalCertificateBudget := by
      rw [hd.1]
      have h := norm_scaled_sum_add_le
        (-((n : ℝ) * xiNaturalSaddleScale n) : ℂ)
        (complexForwardDiff 2 complexXiNaturalAuxiliaryLogMain (n : ℂ))
        (complexForwardDiff 2 complexXiNaturalAuxiliaryLogError (n : ℂ)) 2
        hm.1 he.1
      simpa [xiNaturalCertificateBudget, add_assoc] using h
    rw [← Real.norm_eq_abs, ← Complex.norm_real]
    convert hcomplex using 1 <;> push_cast <;> ring
  · have hcomplex :
        ‖((((n : ℝ) ^ 2 * xiNaturalSaddleScale n / 2 : ℝ) : ℂ)) *
              (((natForwardDiff1 (exactXiAuxiliarySecondDiff n) : ℝ) : ℂ)) + 1‖ ≤
            xiNaturalCertificateBudget := by
      rw [hd.2.1]
      have h := norm_scaled_sum_add_le
        ((((n : ℝ) ^ 2 * xiNaturalSaddleScale n / 2 : ℝ) : ℂ))
        (complexForwardDiff 3 complexXiNaturalAuxiliaryLogMain (n : ℂ))
        (complexForwardDiff 3 complexXiNaturalAuxiliaryLogError (n : ℂ)) 1
        hm.2.1 he.2.1
      simpa [xiNaturalCertificateBudget, add_assoc] using h
    rw [← Real.norm_eq_abs, ← Complex.norm_real]
    convert hcomplex using 1 <;> push_cast <;> ring
  · have hcomplex :
        ‖(-((n : ℝ) ^ 3 * xiNaturalSaddleScale n / 2 : ℝ) : ℂ) *
              (((natForwardDiff2 (exactXiAuxiliarySecondDiff n) : ℝ) : ℂ)) + 2‖ ≤
            xiNaturalCertificateBudget := by
      rw [hd.2.2.1]
      have h := norm_scaled_sum_add_le
        (-((n : ℝ) ^ 3 * xiNaturalSaddleScale n / 2 : ℝ) : ℂ)
        (complexForwardDiff 4 complexXiNaturalAuxiliaryLogMain (n : ℂ))
        (complexForwardDiff 4 complexXiNaturalAuxiliaryLogError (n : ℂ)) 2
        hm.2.2.1 he.2.2.1
      simpa [xiNaturalCertificateBudget, add_assoc] using h
    rw [← Real.norm_eq_abs, ← Complex.norm_real]
    convert hcomplex using 1 <;> push_cast <;> ring
  · have hcomplex :
        ‖((((n : ℝ) ^ 4 * xiNaturalSaddleScale n / 6 : ℝ) : ℂ)) *
              (((natForwardDiff3 (exactXiAuxiliarySecondDiff n) : ℝ) : ℂ)) + 2‖ ≤
            xiNaturalCertificateBudget := by
      rw [hd.2.2.2]
      have h := norm_scaled_sum_add_le
        ((((n : ℝ) ^ 4 * xiNaturalSaddleScale n / 6 : ℝ) : ℂ))
        (complexForwardDiff 5 complexXiNaturalAuxiliaryLogMain (n : ℂ))
        (complexForwardDiff 5 complexXiNaturalAuxiliaryLogError (n : ℂ)) 2
        hm.2.2.2 he.2.2.2
      simpa [xiNaturalCertificateBudget, add_assoc] using h
    rw [← Real.norm_eq_abs, ← Complex.norm_real]
    convert hcomplex using 1 <;> push_cast <;> ring

end

end Zeta23.Research.JensenWedge
