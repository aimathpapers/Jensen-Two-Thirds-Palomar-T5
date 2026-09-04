import Zeta23.Research.JensenWedge.XiNaturalConcreteMultiplierBound

/-!
# Explicit wedge specialization of the concrete xi multiplier

This module chooses deliberately conservative exact constants, derives all
disc and parameter containments from the two-thirds wedge, and specializes
the Hermite--Genocchi estimate to the paper's thickened coefficient-index
interval.  The resulting strict `‖c_F - 1‖ < 1` bound has no remaining
analytic hypothesis.
-/

open Complex Metric Set

noncomputable section

namespace Zeta23.Research.JensenWedge

def xiNaturalMultiplierScaleConstant : ℝ := 20000000

def xiNaturalMultiplierDegreeCap : ℕ := 1200000000000000

def xiNaturalMultiplierGeometryWedgeConstant : ℝ :=
  2 * (xiNaturalMultiplierDegreeCap : ℝ) ^ 3

def xiNaturalMultiplierRadius
    (n d : ℕ) (L : ℝ) (y : BranchPoint) : ℝ :=
  (d : ℝ) + 8192 *
    Real.sqrt (residualParameterB y n (1 / L) * d)

theorem twoThirdsWedge_n_ge_multiplierDegreeCap_mul_degree
    {K : ℝ} (hK : xiNaturalMultiplierGeometryWedgeConstant ≤ K)
    {n d : ℕ} (hn : 0 < n) (hW : TwoThirdsWedge K n d) :
    xiNaturalMultiplierDegreeCap * d ≤ n := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hnOne : (1 : ℝ) ≤ n := by exact_mod_cast (Nat.one_le_iff_ne_zero.mpr hn.ne')
  have hlog : Real.log ((n : ℝ) + 2) ≤ 2 * n := by
    have hbase := Real.log_le_sub_one_of_pos
      (show (0 : ℝ) < (n : ℝ) + 2 by positivity)
    nlinarith
  have hd3 : 0 ≤ (d : ℝ) ^ 3 := by positivity
  have hKlower : xiNaturalMultiplierGeometryWedgeConstant * (d : ℝ) ^ 3 ≤
      K * (d : ℝ) ^ 3 := mul_le_mul_of_nonneg_right hK hd3
  have hcube : (((xiNaturalMultiplierDegreeCap : ℕ) : ℝ) * d) ^ 3 ≤
      (n : ℝ) ^ 3 := by
    unfold TwoThirdsWedge at hW
    dsimp [xiNaturalMultiplierGeometryWedgeConstant] at hKlower
    nlinarith [mul_le_mul_of_nonneg_left hlog (sq_nonneg (n : ℝ))]
  have hlinear : (((xiNaturalMultiplierDegreeCap : ℕ) : ℝ) * d) ≤ n := by
    exact le_of_pow_le_pow_left₀ (by norm_num : (3 : ℕ) ≠ 0) hnR.le hcube
  exact_mod_cast hlinear

theorem multiplierScale_small_of_degree_cap
    {n d : ℕ} (hn : 0 < n) {L : ℝ} (hL : 0 < L)
    (hL12 : 1 / L ≤ (1 : ℝ) / 12)
    {y : BranchPoint} (hy : InOuterParameterBox y)
    (hcap : xiNaturalMultiplierDegreeCap * d ≤ n) :
    xiNaturalMultiplierScaleConstant *
        Real.sqrt (residualParameterB y n (1 / L) * d) ≤ n := by
  rcases hy with ⟨_, _, _, ht1, _, hw1, _, _⟩
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hd0 : (0 : ℝ) ≤ d := Nat.cast_nonneg d
  have hcapR : (xiNaturalMultiplierDegreeCap : ℝ) * d ≤ n := by
    exact_mod_cast hcap
  have he0 : 0 ≤ (1 / L : ℝ) := (one_div_pos.mpr hL).le
  have hwe1 : y 2 * (1 / L) ≤ 1 / 2 := by
    have hmul := mul_le_mul hw1 hL12 he0 (by norm_num : (0 : ℝ) ≤ 6)
    nlinarith
  have hBupper : residualParameterB y n (1 / L) ≤ 11 / 4 * n := by
    unfold residualParameterB
    nlinarith [mul_nonneg hnR.le
      (by nlinarith : 0 ≤ 11 / 4 - (y 1 + y 2 * (1 / L)))]
  have hBpos : 0 < residualParameterB y n (1 / L) := by
    unfold residualParameterB
    have ht0 : 0 < y 1 := by nlinarith
    positivity
  have hsq : Real.sqrt (residualParameterB y n (1 / L) * d) ^ 2 =
      residualParameterB y n (1 / L) * d := by
    rw [Real.sq_sqrt]
    positivity
  have hcapMul := mul_le_mul_of_nonneg_left hcapR hnR.le
  have hBmul := mul_le_mul_of_nonneg_right hBupper hd0
  have hsqrt0 := Real.sqrt_nonneg (residualParameterB y n (1 / L) * d)
  have hradicand : (400000000000000 : ℝ) *
      (residualParameterB y n (1 / L) * d) ≤ (n : ℝ) ^ 2 := by
    norm_num [xiNaturalMultiplierDegreeCap] at hcapMul
    nlinarith [hBmul]
  have hsquare :
      (xiNaturalMultiplierScaleConstant *
        Real.sqrt (residualParameterB y n (1 / L) * d)) ^ 2 ≤
          (n : ℝ) ^ 2 := by
    rw [mul_pow, hsq]
    norm_num [xiNaturalMultiplierScaleConstant]
    simpa only [one_div] using hradicand
  nlinarith

theorem explicitCutoff_inverse_xiNaturalSaddleScale_le_two_div_log
    {n : ℕ} (hn : xiNaturalExplicitCutoffIndex ≤ n) :
    1 / xiNaturalSaddleScale n ≤ 2 / Real.log (n : ℝ) := by
  let C := xiNaturalSaddleIntervalConditions_of_explicitCutoff hn
  have hnR : (0 : ℝ) < n := by exact_mod_cast C.n_pos
  have hnHuge : (10 : ℝ) ^ 160 < (n : ℝ) :=
    ten_pow_oneSixty_le_exp_explicitLogCutoff.trans_lt
      (exp_explicitLogCutoff_lt_of_cutoffIndex_le hn)
  have hnEight : 8 ≤ n := by exact_mod_cast (show (8 : ℝ) ≤ n by nlinarith)
  have hlogn : 0 < Real.log (n : ℝ) := by
    apply Real.log_pos
    exact_mod_cast (show 1 < n by omega)
  have hcenter : (n : ℝ) ≤ xiNaturalMellinCenter n := by
    unfold xiNaturalMellinCenter
    have hnTwo : (2 : ℝ) ≤ n := by exact_mod_cast (show 2 ≤ n by omega)
    linarith
  have hlogCenter : Real.log (n : ℝ) ≤
      Real.log (xiNaturalMellinCenter n) :=
    Real.log_le_log hnR hcenter
  have hlower := quantitativeSaddleBranch_norm_lower_half_realLog
    C.center_mellin_mem_sector
  rw [← C.saddleScale_cast] at hlower
  simp only [norm_real, Real.norm_eq_abs, abs_of_pos C.center_pos,
    abs_of_pos C.saddleScale_pos] at hlower
  have hscale : Real.log (n : ℝ) / 2 ≤ xiNaturalSaddleScale n := by
    linarith
  have hLpos := C.saddleScale_pos
  rw [div_le_div_iff₀ hLpos hlogn]
  nlinarith

theorem xiNaturalMultiplier_radius_geometry_of_explicitCutoff
    {K : ℝ} (hK : xiNaturalMultiplierGeometryWedgeConstant ≤ K)
    {n d : ℕ} (hn : xiNaturalExplicitCutoffIndex ≤ n)
    (hW : TwoThirdsWedge K n d) (hd : 6 ≤ d) :
    let y := (exactXiPositiveParameterBranch_of_explicitCutoff hn).parameters
    let L := xiNaturalSaddleScale n
    let r := xiNaturalMultiplierRadius n d L y
    5 ≤ r ∧
      r ≤ manuscriptInteriorCauchyRadius (n : ℝ) ∧
      2 * r < (n : ℝ) + 1 / 2 ∧
      2 * r < residualParameterA y n (1 / L) ∧
      2 * r < residualParameterB y n (1 / L) ∧
      2 * r < residualParameterC y n ∧
      2 * r < residualParameterD y n (1 / L) := by
  let P := exactXiPositiveParameterBranch_of_explicitCutoff hn
  let C := xiNaturalSaddleIntervalConditions_of_explicitCutoff hn
  let y := P.parameters
  let L := xiNaturalSaddleScale n
  let B := residualParameterB y n (1 / L)
  let S := Real.sqrt (B * d)
  let r := xiNaturalMultiplierRadius n d L y
  have hcap := twoThirdsWedge_n_ge_multiplierDegreeCap_mul_degree hK C.n_pos hW
  have hsmall : xiNaturalMultiplierScaleConstant * S ≤ n :=
    multiplierScale_small_of_degree_cap C.n_pos C.saddleScale_pos
      (explicitCutoff_inverse_xiNaturalSaddleScale_le_twelve hn)
      P.in_outer_box hcap
  have hnd : d ≤ n := by
    unfold xiNaturalMultiplierDegreeCap at hcap
    omega
  have hpos := xiNaturalResidualParameters_pos C.n_pos C.saddleScale_pos
    (explicitCutoff_inverse_xiNaturalSaddleScale_le_twelve hn) P.in_outer_box
  rcases hpos with ⟨hA, hB, hC, hD⟩
  have hBge : (d : ℝ) ≤ B := by
    rcases P.in_outer_box with ⟨_, _, ht0, _, hw0, _, _, _⟩
    have he0 : 0 ≤ (1 / L : ℝ) := (one_div_pos.mpr C.saddleScale_pos).le
    have hbase : 1 ≤ y 1 + y 2 * (1 / L) := by
      have hw : 0 ≤ y 2 := by linarith
      nlinarith [mul_nonneg hw he0]
    unfold B residualParameterB
    have hnR : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    have hBn : (n : ℝ) ≤ (n : ℝ) * (y 1 + y 2 * (1 / L)) := by
      nlinarith [mul_nonneg hnR (sub_nonneg.mpr hbase)]
    exact (by exact_mod_cast hnd : (d : ℝ) ≤ n).trans hBn
  have hSnonneg : 0 ≤ S := Real.sqrt_nonneg _
  have hSge : (d : ℝ) ≤ S := by
    have hd0 : (0 : ℝ) ≤ d := Nat.cast_nonneg d
    have hsq : S ^ 2 = B * d := by
      dsimp only [S]
      rw [Real.sq_sqrt]
      positivity
    nlinarith [mul_nonneg (sub_nonneg.mpr hBge) hd0]
  have hrBound : r ≤ 8193 * S := by
    dsimp only [r, xiNaturalMultiplierRadius]
    nlinarith
  have hnR : (0 : ℝ) < n := by exact_mod_cast C.n_pos
  have hnHuge : (10 : ℝ) ^ 160 < (n : ℝ) :=
    ten_pow_oneSixty_le_exp_explicitLogCutoff.trans_lt
      (exp_explicitLogCutoff_lt_of_cutoffIndex_le hn)
  have hnEight : 8 ≤ n := by exact_mod_cast (show (8 : ℝ) ≤ n by nlinarith)
  have h2rN : 2 * r < (n : ℝ) := by
    norm_num [xiNaturalMultiplierScaleConstant] at hsmall
    nlinarith
  have hAlinear : 30 * (n : ℝ) ≤ residualParameterA y n (1 / L) := by
    rcases P.in_outer_box with ⟨ha0, _, _, _, _, _, _, _⟩
    have he := one_div_pos.mpr C.saddleScale_pos
    have hratio : 30 ≤ y 0 / (1 / L) := by
      rw [le_div_iff₀ he]
      have he12 := explicitCutoff_inverse_xiNaturalSaddleScale_le_twelve hn
      nlinarith
    unfold residualParameterA
    calc
      30 * (n : ℝ) ≤ (y 0 / (1 / L)) * n :=
        mul_le_mul_of_nonneg_right hratio (Nat.cast_nonneg n)
      _ = y 0 * n / (1 / L) := by ring
  have hBlinear : (n : ℝ) ≤ residualParameterB y n (1 / L) := by
    rcases P.in_outer_box with ⟨_, _, ht0, _, hw0, _, _, _⟩
    have he0 : 0 ≤ (1 / L : ℝ) := (one_div_pos.mpr C.saddleScale_pos).le
    have hw : 0 ≤ y 2 := by linarith
    have hbase : 1 ≤ y 1 + y 2 * (1 / L) := by
      nlinarith [mul_nonneg hw he0]
    unfold residualParameterB
    nlinarith [mul_nonneg (Nat.cast_nonneg n) (sub_nonneg.mpr hbase)]
  have hClinear : (7 / 4 : ℝ) * n ≤ residualParameterC y n := by
    rcases P.in_outer_box with ⟨_, _, ht0, _, _, _, _, _⟩
    unfold residualParameterC
    simpa [mul_comm] using
      mul_le_mul_of_nonneg_left ht0 (Nat.cast_nonneg n)
  have hDlinear : (n : ℝ) ≤ residualParameterD y n (1 / L) := by
    rcases P.in_outer_box with ⟨_, _, _, _, _, _, hd0, _⟩
    unfold residualParameterD
    have he0 : 0 ≤ (1 / L : ℝ) := (one_div_pos.mpr C.saddleScale_pos).le
    have hdelta : 0 ≤ y 3 := by linarith
    have hde : 0 ≤ y 3 * (1 / L) := mul_nonneg hdelta he0
    have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    nlinarith [mul_nonneg hn0 hde]
  dsimp only [y, L, r]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · dsimp only [xiNaturalMultiplierRadius]
    have hd5 : (5 : ℝ) ≤ d := by exact_mod_cast (show 5 ≤ d by omega)
    nlinarith
  · unfold manuscriptInteriorCauchyRadius
    norm_num [xiNaturalMultiplierScaleConstant] at hsmall
    nlinarith
  · linarith
  · exact h2rN.trans_le (by linarith [hAlinear])
  · exact h2rN.trans_le hBlinear
  · exact h2rN.trans_le (by linarith [hClinear])
  · exact h2rN.trans_le hDlinear

/-- Constant multiplying `d^3/(n^2 log n)` after the exact sixth-order
Hermite--Genocchi estimate and the coarse bound `B ≤ 11n/4`. -/
def xiNaturalMultiplierBudgetFactor : ℝ :=
  xiNaturalConcreteSixthResidualRateConstant * 8194 ^ 6 * (11 / 4) ^ 3 / 720

def xiNaturalMultiplierBudgetWedgeConstant : ℝ :=
  4 * xiNaturalMultiplierBudgetFactor

def xiNaturalConcreteWedgeConstant : ℝ :=
  xiNaturalMultiplierGeometryWedgeConstant +
    xiNaturalMultiplierBudgetWedgeConstant

theorem xiNaturalMultiplierBudgetFactor_nonneg :
    0 ≤ xiNaturalMultiplierBudgetFactor := by
  norm_num [xiNaturalMultiplierBudgetFactor,
    xiNaturalConcreteSixthResidualRateConstant,
    manuscriptSixthResidualRateConstant,
    xiNaturalMainCorrectionSixthRateConstant,
    manuscriptSixthResidualCauchyConstant,
    manuscriptSixthResidualBCConstant,
    manuscriptSixthResidualDConstant,
    manuscriptSixthResidualAConstant, Nat.factorial]

theorem xiNaturalConcreteWedge_ge_geometry :
    xiNaturalMultiplierGeometryWedgeConstant ≤
      xiNaturalConcreteWedgeConstant := by
  unfold xiNaturalConcreteWedgeConstant xiNaturalMultiplierBudgetWedgeConstant
  nlinarith [xiNaturalMultiplierBudgetFactor_nonneg]

theorem xiNaturalConcreteWedge_ge_budget :
    xiNaturalMultiplierBudgetWedgeConstant ≤
      xiNaturalConcreteWedgeConstant := by
  have hgeom : 0 ≤ xiNaturalMultiplierGeometryWedgeConstant := by
    norm_num [xiNaturalMultiplierGeometryWedgeConstant,
      xiNaturalMultiplierDegreeCap]
  unfold xiNaturalConcreteWedgeConstant
  linarith

theorem real_log_add_two_lt_two_log_of_eight_le
    {n : ℕ} (hn : 8 ≤ n) :
    Real.log ((n : ℝ) + 2) < 2 * Real.log (n : ℝ) := by
  have hnpos : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have harg : (n : ℝ) + 2 < (n : ℝ) ^ 2 := by
    have hnR : (8 : ℝ) ≤ n := by exact_mod_cast hn
    nlinarith
  calc
    Real.log ((n : ℝ) + 2) < Real.log ((n : ℝ) ^ 2) :=
      Real.log_lt_log (by positivity) harg
    _ = 2 * Real.log (n : ℝ) := by
      rw [Real.log_pow]
      norm_num

set_option maxHeartbeats 800000 in
theorem xiNaturalConcrete_multiplier_budget_of_explicitCutoff
    {K : ℝ} (hK : xiNaturalConcreteWedgeConstant ≤ K)
    {n d : ℕ} (hn : xiNaturalExplicitCutoffIndex ≤ n)
    (hW : TwoThirdsWedge K n d) (hd : 6 ≤ d) :
    let y := (exactXiPositiveParameterBranch_of_explicitCutoff hn).parameters
    let L := xiNaturalSaddleScale n
    let r := xiNaturalMultiplierRadius n d L y
    (xiNaturalConcreteSixthResidualRateConstant /
      ((n : ℝ) ^ 5 * Real.log (n : ℝ))) * (r + 5) ^ 6 / 720 < 1 / 2 := by
  let P := exactXiPositiveParameterBranch_of_explicitCutoff hn
  let C := xiNaturalSaddleIntervalConditions_of_explicitCutoff hn
  let y := P.parameters
  let L := xiNaturalSaddleScale n
  let B := residualParameterB y n (1 / L)
  let S := Real.sqrt (B * d)
  let r := xiNaturalMultiplierRadius n d L y
  have hgeomK : xiNaturalMultiplierGeometryWedgeConstant ≤ K :=
    xiNaturalConcreteWedge_ge_geometry.trans hK
  have hcap := twoThirdsWedge_n_ge_multiplierDegreeCap_mul_degree
    hgeomK C.n_pos hW
  have hsmall : xiNaturalMultiplierScaleConstant * S ≤ n :=
    multiplierScale_small_of_degree_cap C.n_pos C.saddleScale_pos
      (explicitCutoff_inverse_xiNaturalSaddleScale_le_twelve hn)
      P.in_outer_box hcap
  have hpos := xiNaturalResidualParameters_pos C.n_pos C.saddleScale_pos
    (explicitCutoff_inverse_xiNaturalSaddleScale_le_twelve hn) P.in_outer_box
  rcases hpos with ⟨_, hBpos, _, _⟩
  have hnR : (0 : ℝ) < n := by exact_mod_cast C.n_pos
  have hnHuge : (10 : ℝ) ^ 160 < (n : ℝ) :=
    ten_pow_oneSixty_le_exp_explicitLogCutoff.trans_lt
      (exp_explicitLogCutoff_lt_of_cutoffIndex_le hn)
  have hnEight : 8 ≤ n := by exact_mod_cast (show (8 : ℝ) ≤ n by nlinarith)
  have hlogn : 0 < Real.log (n : ℝ) := Real.log_pos (by
    exact_mod_cast (show 1 < n by omega))
  have hSnonneg : 0 ≤ S := Real.sqrt_nonneg _
  have hnd : d ≤ n := by
    unfold xiNaturalMultiplierDegreeCap at hcap
    omega
  have hBge : (d : ℝ) ≤ B := by
    rcases P.in_outer_box with ⟨_, _, ht0, _, hw0, _, _, _⟩
    have he0 : 0 ≤ (1 / L : ℝ) := (one_div_pos.mpr C.saddleScale_pos).le
    have hw : 0 ≤ y 2 := by linarith
    have hbase : 1 ≤ y 1 + y 2 * (1 / L) := by
      nlinarith [mul_nonneg hw he0]
    unfold B residualParameterB
    have hBn : (n : ℝ) ≤ (n : ℝ) * (y 1 + y 2 * (1 / L)) := by
      nlinarith [mul_nonneg (Nat.cast_nonneg n) (sub_nonneg.mpr hbase)]
    exact (by exact_mod_cast hnd : (d : ℝ) ≤ n).trans hBn
  have hSge : (d : ℝ) ≤ S := by
    have hd0 : (0 : ℝ) ≤ d := Nat.cast_nonneg d
    have hsq : S ^ 2 = B * d := by
      dsimp only [S]
      rw [Real.sq_sqrt]
      positivity
    nlinarith [mul_nonneg (sub_nonneg.mpr hBge) hd0]
  have hr8193 : r ≤ 8193 * S := by
    dsimp only [r, xiNaturalMultiplierRadius]
    nlinarith
  have hSfive : 5 ≤ S := by
    have hdR : (6 : ℝ) ≤ d := by exact_mod_cast hd
    linarith
  have hrFive : r + 5 ≤ 8194 * S := by linarith
  have hrFiveNonneg : 0 ≤ r + 5 := by
    dsimp only [r, xiNaturalMultiplierRadius]
    positivity
  have hpowRadius : (r + 5) ^ 6 ≤ (8194 * S) ^ 6 :=
    pow_le_pow_left₀ hrFiveNonneg hrFive 6
  have hSsq : S ^ 2 = B * d := by
    dsimp only [S]
    rw [Real.sq_sqrt]
    positivity
  have hSsix : S ^ 6 = (B * d) ^ 3 := by
    calc
      S ^ 6 = (S ^ 2) ^ 3 := by ring
      _ = (B * d) ^ 3 := by rw [hSsq]
  have hBupper : B ≤ 11 / 4 * (n : ℝ) := by
    rcases P.in_outer_box with ⟨_, _, _, ht1, _, hw1, _, _⟩
    have he0 : 0 ≤ (1 / L : ℝ) := (one_div_pos.mpr C.saddleScale_pos).le
    have hwe : y 2 * (1 / L) ≤ 1 / 2 := by
      have := mul_le_mul hw1
        (explicitCutoff_inverse_xiNaturalSaddleScale_le_twelve hn)
        he0 (by norm_num : (0 : ℝ) ≤ 6)
      nlinarith
    unfold B residualParameterB
    nlinarith [mul_nonneg hnR.le
      (by nlinarith : 0 ≤ 11 / 4 - (y 1 + y 2 * (1 / L)))]
  have hBpow : B ^ 3 ≤ (11 / 4 * (n : ℝ)) ^ 3 :=
    pow_le_pow_left₀ hBpos.le hBupper 3
  have hradiusFinal : (r + 5) ^ 6 ≤
      8194 ^ 6 * (11 / 4) ^ 3 * (n : ℝ) ^ 3 * (d : ℝ) ^ 3 := by
    calc
      (r + 5) ^ 6 ≤ (8194 * S) ^ 6 := hpowRadius
      _ = 8194 ^ 6 * (B ^ 3 * (d : ℝ) ^ 3) := by
        rw [mul_pow, hSsix, mul_pow]
      _ ≤ 8194 ^ 6 * ((11 / 4 * (n : ℝ)) ^ 3 * (d : ℝ) ^ 3) := by
        gcongr
      _ = 8194 ^ 6 * (11 / 4) ^ 3 * (n : ℝ) ^ 3 * (d : ℝ) ^ 3 := by ring
  have hconstant : 0 ≤ xiNaturalConcreteSixthResidualRateConstant := by
    norm_num [xiNaturalConcreteSixthResidualRateConstant,
      manuscriptSixthResidualRateConstant,
      xiNaturalMainCorrectionSixthRateConstant,
      manuscriptSixthResidualCauchyConstant,
      manuscriptSixthResidualBCConstant,
      manuscriptSixthResidualDConstant,
      manuscriptSixthResidualAConstant, Nat.factorial]
  have hdenom : 0 < (n : ℝ) ^ 5 * Real.log (n : ℝ) := by positivity
  have hfirst :
      (xiNaturalConcreteSixthResidualRateConstant /
          ((n : ℝ) ^ 5 * Real.log (n : ℝ))) * (r + 5) ^ 6 / 720 ≤
        xiNaturalMultiplierBudgetFactor * (d : ℝ) ^ 3 /
          ((n : ℝ) ^ 2 * Real.log (n : ℝ)) := by
    calc
      _ ≤ (xiNaturalConcreteSixthResidualRateConstant /
          ((n : ℝ) ^ 5 * Real.log (n : ℝ))) *
          (8194 ^ 6 * (11 / 4) ^ 3 * (n : ℝ) ^ 3 * (d : ℝ) ^ 3) / 720 := by
            gcongr
      _ = xiNaturalMultiplierBudgetFactor * (d : ℝ) ^ 3 /
          ((n : ℝ) ^ 2 * Real.log (n : ℝ)) := by
            unfold xiNaturalMultiplierBudgetFactor
            field_simp [hnR.ne', hlogn.ne']
  have hbudgetK : xiNaturalMultiplierBudgetWedgeConstant ≤ K :=
    xiNaturalConcreteWedge_ge_budget.trans hK
  have hFnonneg := xiNaturalMultiplierBudgetFactor_nonneg
  have hKpos : 0 < K := by
    unfold xiNaturalMultiplierBudgetWedgeConstant at hbudgetK
    have hFpos : 0 < xiNaturalMultiplierBudgetFactor := by
      norm_num [xiNaturalMultiplierBudgetFactor,
        xiNaturalConcreteSixthResidualRateConstant,
        manuscriptSixthResidualRateConstant,
        xiNaturalMainCorrectionSixthRateConstant,
        manuscriptSixthResidualCauchyConstant,
        manuscriptSixthResidualBCConstant,
        manuscriptSixthResidualDConstant,
        manuscriptSixthResidualAConstant, Nat.factorial]
    nlinarith
  have hW' : K * (d : ℝ) ^ 3 ≤
      (n : ℝ) ^ 2 * Real.log ((n : ℝ) + 2) := by
    unfold TwoThirdsWedge at hW
    simpa only [Nat.cast_add, Nat.cast_ofNat] using hW
  have hdegreeRate : (d : ℝ) ^ 3 /
      ((n : ℝ) ^ 2 * Real.log (n : ℝ)) ≤
        Real.log ((n : ℝ) + 2) / (K * Real.log (n : ℝ)) := by
    rw [div_le_div_iff₀ (by positivity) (mul_pos hKpos hlogn)]
    nlinarith [hW']
  have hlogRatio : Real.log ((n : ℝ) + 2) / Real.log (n : ℝ) < 2 := by
    rw [div_lt_iff₀ hlogn]
    exact real_log_add_two_lt_two_log_of_eight_le hnEight
  have hFoverK : xiNaturalMultiplierBudgetFactor / K ≤ 1 / 4 := by
    rw [div_le_iff₀ hKpos]
    unfold xiNaturalMultiplierBudgetWedgeConstant at hbudgetK
    linarith
  have hlogRatioNonneg : 0 ≤
      Real.log ((n : ℝ) + 2) / Real.log (n : ℝ) := by
    have hnPlus : (1 : ℝ) ≤ (n : ℝ) + 2 := by linarith
    exact div_nonneg (Real.log_nonneg hnPlus) hlogn.le
  calc
    _ ≤ xiNaturalMultiplierBudgetFactor * (d : ℝ) ^ 3 /
        ((n : ℝ) ^ 2 * Real.log (n : ℝ)) := hfirst
    _ ≤ xiNaturalMultiplierBudgetFactor *
        (Real.log ((n : ℝ) + 2) / (K * Real.log (n : ℝ))) := by
          rw [mul_div_assoc]
          exact mul_le_mul_of_nonneg_left hdegreeRate hFnonneg
    _ = (xiNaturalMultiplierBudgetFactor / K) *
        (Real.log ((n : ℝ) + 2) / Real.log (n : ℝ)) := by ring
    _ < (1 / 4 : ℝ) * 2 := by
      calc
        (xiNaturalMultiplierBudgetFactor / K) *
            (Real.log ((n : ℝ) + 2) / Real.log (n : ℝ)) ≤
          (1 / 4 : ℝ) *
            (Real.log ((n : ℝ) + 2) / Real.log (n : ℝ)) :=
              mul_le_mul_of_nonneg_right hFoverK hlogRatioNonneg
        _ < (1 / 4 : ℝ) * 2 :=
          mul_lt_mul_of_pos_left hlogRatio (by norm_num)
    _ = 1 / 2 := by norm_num

/-- Fully specialized strict unit bound for the concrete multiplier on the
disc containing the paper's thickened coefficient-index interval. -/
theorem xiNaturalConcreteMultiplier_sub_one_norm_lt_one_of_explicitCutoff
    {K : ℝ} (hK : xiNaturalConcreteWedgeConstant ≤ K)
    {n d : ℕ} (hn : xiNaturalExplicitCutoffIndex ≤ n)
    (hW : TwoThirdsWedge K n d) (hd : 6 ≤ d)
    {z : ℂ}
    (hz : z ∈ Metric.closedBall (0 : ℂ)
      (xiNaturalMultiplierRadius n d (xiNaturalSaddleScale n)
        (exactXiPositiveParameterBranch_of_explicitCutoff hn).parameters)) :
    ‖xiNaturalConcreteMultiplier n (xiNaturalSaddleScale n)
        (exactXiPositiveParameterBranch_of_explicitCutoff hn).parameters z - 1‖ < 1 := by
  let P := exactXiPositiveParameterBranch_of_explicitCutoff hn
  let C := xiNaturalSaddleIntervalConditions_of_explicitCutoff hn
  let y := P.parameters
  let L := xiNaturalSaddleScale n
  let r := xiNaturalMultiplierRadius n d L y
  have hgeometry := xiNaturalMultiplier_radius_geometry_of_explicitCutoff
    (xiNaturalConcreteWedge_ge_geometry.trans hK) hn hW hd
  dsimp only at hgeometry
  rcases hgeometry with ⟨hr5, hrInterior, hhalf, hA, hB, hC, hD⟩
  have hbudget := xiNaturalConcrete_multiplier_budget_of_explicitCutoff
    hK hn hW hd
  dsimp only at hbudget
  exact xiNaturalConcreteMultiplier_sub_one_norm_lt_one_of_radius
    P.in_outer_box (show 8 ≤ n by
      have hnHuge : (10 : ℝ) ^ 160 < (n : ℝ) :=
        ten_pow_oneSixty_le_exp_explicitLogCutoff.trans_lt
          (exp_explicitLogCutoff_lt_of_cutoffIndex_le hn)
      exact_mod_cast (show (8 : ℝ) ≤ n by nlinarith))
    C.coefficient_center_in_remote_sector C.saddleScale_pos
    (explicitCutoff_inverse_xiNaturalSaddleScale_le_twelve hn)
    (explicitCutoff_inverse_xiNaturalSaddleScale_le_two_div_log hn)
    P.equation hr5 hrInterior hhalf hA hB hC hD hbudget hz

/-- Concrete thickening of the coefficient-index interval `[0,d]` by the
twice-critical radius used in the multiplier argument. -/
def xiNaturalMultiplierTube
    (n d : ℕ) (L : ℝ) (y : BranchPoint) : Set ℂ :=
  {z | ∃ x : ℝ, x ∈ Set.Icc 0 (d : ℝ) ∧
    ‖z - (x : ℂ)‖ ≤ 8192 *
      Real.sqrt (residualParameterB y n (1 / L) * d)}

theorem xiNaturalMultiplierTube_subset_radius
    {n d : ℕ} {L : ℝ} {y : BranchPoint} :
    xiNaturalMultiplierTube n d L y ⊆
      Metric.closedBall (0 : ℂ) (xiNaturalMultiplierRadius n d L y) := by
  intro z hz
  rcases hz with ⟨x, hx, hzx⟩
  rcases hx with ⟨hx0, hxd⟩
  rw [Metric.mem_closedBall, dist_zero_right]
  have hxnorm : ‖(x : ℂ)‖ = x := by
    rw [norm_real, Real.norm_eq_abs, abs_of_nonneg hx0]
  calc
    ‖z‖ = ‖(z - (x : ℂ)) + (x : ℂ)‖ := by congr 1 <;> ring
    _ ≤ ‖z - (x : ℂ)‖ + ‖(x : ℂ)‖ := norm_add_le _ _
    _ ≤ 8192 * Real.sqrt (residualParameterB y n (1 / L) * d) + x := by
      rw [hxnorm]
      gcongr
    _ ≤ xiNaturalMultiplierRadius n d L y := by
      unfold xiNaturalMultiplierRadius
      linarith

theorem xiNaturalConcreteMultiplier_sub_one_norm_lt_one_on_tube
    {K : ℝ} (hK : xiNaturalConcreteWedgeConstant ≤ K)
    {n d : ℕ} (hn : xiNaturalExplicitCutoffIndex ≤ n)
    (hW : TwoThirdsWedge K n d) (hd : 6 ≤ d)
    {z : ℂ}
    (hz : z ∈ xiNaturalMultiplierTube n d (xiNaturalSaddleScale n)
      (exactXiPositiveParameterBranch_of_explicitCutoff hn).parameters) :
    ‖xiNaturalConcreteMultiplier n (xiNaturalSaddleScale n)
        (exactXiPositiveParameterBranch_of_explicitCutoff hn).parameters z - 1‖ < 1 :=
  xiNaturalConcreteMultiplier_sub_one_norm_lt_one_of_explicitCutoff
    hK hn hW hd (xiNaturalMultiplierTube_subset_radius hz)

end Zeta23.Research.JensenWedge
