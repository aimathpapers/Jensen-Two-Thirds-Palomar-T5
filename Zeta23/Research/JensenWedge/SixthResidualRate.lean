import Zeta23.Research.JensenWedge.MomentSaddleResidual
import Mathlib.Analysis.SpecialFunctions.Complex.LogBounds

/-!
# A single explicit rate for the sixth residual

This module reduces the term-by-term bound in `MomentSaddleResidual` to one
constant times `1 / (n^5 log n)`.  The reciprocal branch scale is required to
satisfy the manuscript-size inequality `e ≤ 2 / log n`.  Every floor and
Cauchy-radius loss is retained explicitly.
-/

noncomputable section

namespace Zeta23.Research.JensenWedge

open Complex Metric

/-- A generic logarithm estimate at the deliberately enormous Phase-26
cutoff. -/
theorem real_log_le_two_mul_div_ten_pow_forty_of_large
    {x : ℝ} (hx : 0 < x) (hlarge : (10 : ℝ) ^ 80 ≤ x) :
    Real.log x ≤ 2 * x / (10 : ℝ) ^ 40 := by
  let a : ℝ := (10 : ℝ) ^ 40
  have ha : 0 < a := by positivity
  have hxdiv : 0 < x / a := div_pos hx ha
  have hfactor : x = a * (x / a) := by field_simp
  have hloga := Real.log_le_sub_one_of_pos ha
  have hlogdiv := Real.log_le_sub_one_of_pos hxdiv
  have haa : a * a = (10 : ℝ) ^ 80 := by
    dsimp only [a]
    ring
  have ha_le : a ≤ x / a := by
    apply (le_div_iff₀ ha).2
    rw [haa]
    exact hlarge
  calc
    Real.log x = Real.log (a * (x / a)) := congrArg Real.log hfactor
    _ = Real.log a + Real.log (x / a) :=
      Real.log_mul ha.ne' hxdiv.ne'
    _ ≤ (a - 1) + (x / a - 1) := add_le_add hloga hlogdiv
    _ ≤ 2 * (x / a) := by linarith
    _ = 2 * x / (10 : ℝ) ^ 40 := by
      dsimp only [a]
      ring

/-- The explicit manuscript Cauchy envelope is already at most one half at
the conservative Lean cutoff. -/
theorem manuscriptCauchyEpsilon_le_half
    {n : ℕ} (hnLarge : Real.exp (leanSaddleCutoff + 2) < (n : ℝ)) :
    manuscriptCauchyEpsilon (n : ℝ) ≤ 1 / 2 := by
  let C : ℝ := manuscriptXiCoefficientErrorCoefficient
  have hnpos : (0 : ℝ) < n := (Real.exp_pos _).trans hnLarge
  have hpow := Real.pow_div_factorial_le_exp leanSaddleCutoff
    (show (0 : ℝ) ≤ leanSaddleCutoff by norm_num [leanSaddleCutoff]) 16
  have hcut : (10 : ℝ) ^ 80 ≤ Real.exp leanSaddleCutoff := by
    apply le_trans ?_ hpow
    norm_num [leanSaddleCutoff, Nat.factorial]
  have hcutShift : Real.exp leanSaddleCutoff < (n : ℝ) := by
    exact (Real.exp_lt_exp.mpr (by norm_num)).trans hnLarge
  have hnlarge : (10 : ℝ) ^ 80 ≤ (n : ℝ) := hcut.trans hcutShift.le
  have hthreeLarge : (10 : ℝ) ^ 80 ≤ 3 * (n : ℝ) := by
    exact hnlarge.trans (by nlinarith)
  have hthreePos : 0 < 3 * (n : ℝ) := mul_pos (by norm_num) hnpos
  have hlog := real_log_le_two_mul_div_ten_pow_forty_of_large
    hthreePos hthreeLarge
  have hC : 0 ≤ C := by
    norm_num [C, manuscriptXiCoefficientErrorCoefficient,
      complexXiCoefficientErrorCoefficient, fullThetaMomentErrorCoefficient,
      Nat.factorial]
  unfold manuscriptCauchyEpsilon
  change C * Real.log (3 * (n : ℝ)) / (n : ℝ) ≤ 1 / 2
  calc
    C * Real.log (3 * (n : ℝ)) / (n : ℝ) ≤
        C * (2 * (3 * (n : ℝ)) / (10 : ℝ) ^ 40) / (n : ℝ) := by
      exact div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_left hlog hC) hnpos.le
    _ = 6 * C / (10 : ℝ) ^ 40 := by
      field_simp [hnpos.ne']
      <;> ring
    _ ≤ 1 / 2 := by
      norm_num [C, manuscriptXiCoefficientErrorCoefficient,
        complexXiCoefficientErrorCoefficient, fullThetaMomentErrorCoefficient,
        Nat.factorial]

/-- The common integer anchor retained for the four nearby polygamma
arguments is at least `n/12`. -/
theorem manuscriptQuarterAnchor_ge_twelfth
    {n : ℕ} (hn : 8 ≤ n) :
    (n : ℝ) / 12 ≤ (((n / 4 - 1 : ℕ) : ℝ)) := by
  have hnat : n ≤ 12 * (n / 4 - 1) := by omega
  have hcast : (n : ℝ) ≤ 12 * (((n / 4 - 1 : ℕ) : ℝ)) := by
    exact_mod_cast hnat
  linarith

/-- Under the reciprocal-log scale bound, the distant floor anchor retains a
full logarithmic factor. -/
theorem manuscriptFarAnchor_ge_quarter_log
    {n : ℕ} (hn : 8 ≤ n)
    {e : ℝ} (he : 0 < e) (he12 : e ≤ 1 / 12)
    (heLog : e ≤ 2 / Real.log (n : ℝ))
    (hlogCut : 1 < Real.log (n : ℝ)) :
    (n : ℝ) * Real.log (n : ℝ) / 4 ≤
      (((⌊(n : ℝ) / e⌋₊ - 1 : ℕ) : ℝ)) := by
  have hnR : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have hnpos : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hlogpos : 0 < Real.log (n : ℝ) := zero_lt_one.trans hlogCut
  have hneNonneg : 0 ≤ (n : ℝ) / e := div_nonneg hnR he.le
  have hneLower : 12 * (n : ℝ) ≤ (n : ℝ) / e := by
    rw [le_div_iff₀ he]
    have hmul := mul_le_mul_of_nonneg_left he12 hnR
    nlinarith
  have hfloorTwo : 2 ≤ ⌊(n : ℝ) / e⌋₊ := by
    apply Nat.le_floor
    have hnEightR : (8 : ℝ) ≤ n := by exact_mod_cast hn
    nlinarith
  have hscaled :
      (n : ℝ) * Real.log (n : ℝ) / 2 ≤ (n : ℝ) / e := by
    rw [le_div_iff₀ he]
    have hfactor : 0 ≤ (n : ℝ) * Real.log (n : ℝ) / 2 := by positivity
    have hmul := mul_le_mul_of_nonneg_left heLog hfactor
    calc
      ((n : ℝ) * Real.log (n : ℝ) / 2) * e ≤
          ((n : ℝ) * Real.log (n : ℝ) / 2) *
            (2 / Real.log (n : ℝ)) := hmul
      _ = (n : ℝ) := by field_simp [hlogpos.ne']
  have hfloor :
      (n : ℝ) / e - 1 < ((⌊(n : ℝ) / e⌋₊ : ℕ) : ℝ) :=
    Nat.sub_one_lt_floor ((n : ℝ) / e)
  have hcastSub :
      (((⌊(n : ℝ) / e⌋₊ - 1 : ℕ) : ℝ)) =
        ((⌊(n : ℝ) / e⌋₊ : ℕ) : ℝ) - 1 := by
    rw [Nat.cast_sub (by omega : 1 ≤ ⌊(n : ℝ) / e⌋₊)]
    norm_num
  rw [hcastSub]
  have hnEightR : (8 : ℝ) ≤ n := by exact_mod_cast hn
  have hnlogEight : 8 ≤ (n : ℝ) * Real.log (n : ℝ) := by nlinarith
  nlinarith

/-- The fixed constants assigned to the Cauchy, nearby-pair, nearby-half,
and distant-tail pieces of the residual ledger. -/
def manuscriptSixthResidualCauchyConstant : ℝ := 540 * 2000 ^ 6

def manuscriptSixthResidualBCConstant : ℝ := 1440 * 12 ^ 6

def manuscriptSixthResidualDConstant : ℝ := 160 * 12 ^ 6

def manuscriptSixthResidualAConstant : ℝ := 24 * 4 ^ 5

/-- The one-constant sixth-residual envelope. -/
def manuscriptSixthResidualRateConstant : ℝ :=
  1280000 + manuscriptSixthResidualCauchyConstant +
    manuscriptSixthResidualBCConstant + manuscriptSixthResidualDConstant +
      manuscriptSixthResidualAConstant

/-- At the active cutoff, the sixth power denominator dominates the desired
fifth-power-log denominator. -/
theorem manuscript_fifth_log_le_sixth_power
    {n : ℕ} (hnLarge : Real.exp (leanSaddleCutoff + 2) < (n : ℝ)) :
    (n : ℝ) ^ 5 * Real.log (n : ℝ) ≤ (n : ℝ) ^ 6 := by
  have hnpos : (0 : ℝ) < n := (Real.exp_pos _).trans hnLarge
  have hlogleSub := Real.log_le_sub_one_of_pos hnpos
  have hlogle : Real.log (n : ℝ) ≤ (n : ℝ) := by linarith
  have hpowNonneg : 0 ≤ (n : ℝ) ^ 5 := pow_nonneg hnpos.le 5
  calc
    (n : ℝ) ^ 5 * Real.log (n : ℝ) ≤ (n : ℝ) ^ 5 * (n : ℝ) :=
      mul_le_mul_of_nonneg_left hlogle hpowNonneg
    _ = (n : ℝ) ^ 6 := by ring

/-- The order-six Cauchy-transport term has the target residual rate. -/
theorem manuscriptSixthResidual_cauchy_term_le
    {n : ℕ} (hnLarge : Real.exp (leanSaddleCutoff + 2) < (n : ℝ)) :
    Nat.factorial 6 *
          ((3 / 2 : ℝ) * manuscriptCauchyEpsilon (n : ℝ)) /
            manuscriptInteriorCauchyRadius (n : ℝ) ^ 6 ≤
      manuscriptSixthResidualCauchyConstant /
        ((n : ℝ) ^ 5 * Real.log (n : ℝ)) := by
  have hnpos : (0 : ℝ) < n := (Real.exp_pos _).trans hnLarge
  have hlogHuge : leanSaddleCutoff + 2 < Real.log (n : ℝ) :=
    (Real.lt_log_iff_exp_lt hnpos).2 hnLarge
  have hlogpos : 0 < Real.log (n : ℝ) := by
    have hcutpos : 0 < leanSaddleCutoff + 2 := by
      norm_num [leanSaddleCutoff]
    exact hcutpos.trans hlogHuge
  have htargetPos : 0 < (n : ℝ) ^ 5 * Real.log (n : ℝ) :=
    mul_pos (pow_pos hnpos 5) hlogpos
  have hdenom := manuscript_fifth_log_le_sixth_power hnLarge
  have heps := manuscriptCauchyEpsilon_le_half hnLarge
  calc
    Nat.factorial 6 *
          ((3 / 2 : ℝ) * manuscriptCauchyEpsilon (n : ℝ)) /
            manuscriptInteriorCauchyRadius (n : ℝ) ^ 6 ≤
        Nat.factorial 6 * ((3 / 2 : ℝ) * (1 / 2)) /
          manuscriptInteriorCauchyRadius (n : ℝ) ^ 6 := by
      gcongr
    _ = manuscriptSixthResidualCauchyConstant / (n : ℝ) ^ 6 := by
      norm_num [manuscriptSixthResidualCauchyConstant,
        manuscriptInteriorCauchyRadius, Nat.factorial]
      field_simp [hnpos.ne']
      <;> ring
    _ ≤ manuscriptSixthResidualCauchyConstant /
          ((n : ℝ) ^ 5 * Real.log (n : ℝ)) := by
      exact div_le_div_of_nonneg_left
        (by norm_num [manuscriptSixthResidualCauchyConstant]) htargetPos hdenom

/-- The `B-C` paired-polygamma term has the target residual rate. -/
theorem manuscriptSixthResidual_BC_term_le
    {n : ℕ} (hn : 8 ≤ n)
    (hnLarge : Real.exp (leanSaddleCutoff + 2) < (n : ℝ))
    {e : ℝ} (he : 0 < e)
    (heLog : e ≤ 2 / Real.log (n : ℝ)) :
    120 * (6 * n * e) / (((n / 4 - 1 : ℕ) : ℝ) ^ 6) ≤
      manuscriptSixthResidualBCConstant /
        ((n : ℝ) ^ 5 * Real.log (n : ℝ)) := by
  have hnpos : (0 : ℝ) < n := (Real.exp_pos _).trans hnLarge
  have hlogHuge : leanSaddleCutoff + 2 < Real.log (n : ℝ) :=
    (Real.lt_log_iff_exp_lt hnpos).2 hnLarge
  have hlogpos : 0 < Real.log (n : ℝ) := by
    have : 0 < leanSaddleCutoff + 2 := by norm_num [leanSaddleCutoff]
    exact this.trans hlogHuge
  have hanchor := manuscriptQuarterAnchor_ge_twelfth hn
  have hanchorPos : 0 < (((n / 4 - 1 : ℕ) : ℝ)) :=
    (div_pos hnpos (by norm_num : (0 : ℝ) < 12)).trans_le hanchor
  have hne : (n : ℝ) * e ≤ 2 * (n : ℝ) / Real.log (n : ℝ) := by
    have hmul := mul_le_mul_of_nonneg_left heLog hnpos.le
    calc
      (n : ℝ) * e ≤ (n : ℝ) * (2 / Real.log (n : ℝ)) := hmul
      _ = 2 * (n : ℝ) / Real.log (n : ℝ) := by ring
  have hnum :
      120 * (6 * (n : ℝ) * e) ≤
        1440 * (n : ℝ) / Real.log (n : ℝ) := by
    calc
      120 * (6 * (n : ℝ) * e) = 720 * ((n : ℝ) * e) := by ring
      _ ≤ 720 * (2 * (n : ℝ) / Real.log (n : ℝ)) :=
        mul_le_mul_of_nonneg_left hne (by norm_num)
      _ = 1440 * (n : ℝ) / Real.log (n : ℝ) := by ring
  have hpowAnchor :
      ((n : ℝ) / 12) ^ 6 ≤ (((n / 4 - 1 : ℕ) : ℝ)) ^ 6 :=
    pow_le_pow_left₀ (div_nonneg hnpos.le (by norm_num)) hanchor 6
  have hnumTarget : 0 ≤ 1440 * (n : ℝ) / Real.log (n : ℝ) := by positivity
  calc
    120 * (6 * n * e) / (((n / 4 - 1 : ℕ) : ℝ) ^ 6) ≤
        (1440 * (n : ℝ) / Real.log (n : ℝ)) /
          (((n / 4 - 1 : ℕ) : ℝ)) ^ 6 := by
      exact div_le_div_of_nonneg_right hnum (pow_nonneg hanchorPos.le 6)
    _ ≤ (1440 * (n : ℝ) / Real.log (n : ℝ)) /
          (((n : ℝ) / 12) ^ 6) := by
      exact div_le_div_of_nonneg_left hnumTarget
        (pow_pos (div_pos hnpos (by norm_num)) 6) hpowAnchor
    _ = manuscriptSixthResidualBCConstant /
          ((n : ℝ) ^ 5 * Real.log (n : ℝ)) := by
      unfold manuscriptSixthResidualBCConstant
      field_simp [hnpos.ne', hlogpos.ne']
      <;> ring

/-- The `D-(n+1/2)` paired-polygamma term has the target residual rate. -/
theorem manuscriptSixthResidual_D_term_le
    {n : ℕ} (hn : 8 ≤ n)
    (hnLarge : Real.exp (leanSaddleCutoff + 2) < (n : ℝ))
    {e : ℝ} (he : 0 < e)
    (heLog : e ≤ 2 / Real.log (n : ℝ)) :
    120 * ((5 / 12 : ℝ) * n * e + 1 / 2) /
          (((n / 4 - 1 : ℕ) : ℝ) ^ 6) ≤
      manuscriptSixthResidualDConstant /
        ((n : ℝ) ^ 5 * Real.log (n : ℝ)) := by
  have hnpos : (0 : ℝ) < n := (Real.exp_pos _).trans hnLarge
  have hlogHuge : leanSaddleCutoff + 2 < Real.log (n : ℝ) :=
    (Real.lt_log_iff_exp_lt hnpos).2 hnLarge
  have hlogpos : 0 < Real.log (n : ℝ) := by
    have : 0 < leanSaddleCutoff + 2 := by norm_num [leanSaddleCutoff]
    exact this.trans hlogHuge
  have hlogleSub := Real.log_le_sub_one_of_pos hnpos
  have hlogle : Real.log (n : ℝ) ≤ (n : ℝ) := by linarith
  have hne : (n : ℝ) * e ≤ 2 * (n : ℝ) / Real.log (n : ℝ) := by
    have hmul := mul_le_mul_of_nonneg_left heLog hnpos.le
    calc
      (n : ℝ) * e ≤ (n : ℝ) * (2 / Real.log (n : ℝ)) := hmul
      _ = 2 * (n : ℝ) / Real.log (n : ℝ) := by ring
  have hhalf : (1 / 2 : ℝ) ≤ (n : ℝ) / (2 * Real.log (n : ℝ)) := by
    rw [le_div_iff₀ (mul_pos (by norm_num) hlogpos)]
    nlinarith
  have hnum :
      120 * ((5 / 12 : ℝ) * n * e + 1 / 2) ≤
        160 * (n : ℝ) / Real.log (n : ℝ) := by
    calc
      120 * ((5 / 12 : ℝ) * n * e + 1 / 2) =
          50 * ((n : ℝ) * e) + 60 := by ring
      _ ≤ 50 * (2 * (n : ℝ) / Real.log (n : ℝ)) + 60 := by
        gcongr
      _ ≤ 50 * (2 * (n : ℝ) / Real.log (n : ℝ)) +
          120 * ((n : ℝ) / (2 * Real.log (n : ℝ))) := by
        have hh := mul_le_mul_of_nonneg_left hhalf
          (show (0 : ℝ) ≤ 120 by norm_num)
        norm_num at hh
        simpa only [add_comm] using
          add_le_add_left hh (50 * (2 * (n : ℝ) / Real.log (n : ℝ)))
      _ = 160 * (n : ℝ) / Real.log (n : ℝ) := by ring
  have hanchor := manuscriptQuarterAnchor_ge_twelfth hn
  have hanchorPos : 0 < (((n / 4 - 1 : ℕ) : ℝ)) :=
    (div_pos hnpos (by norm_num : (0 : ℝ) < 12)).trans_le hanchor
  have hpowAnchor :
      ((n : ℝ) / 12) ^ 6 ≤ (((n / 4 - 1 : ℕ) : ℝ)) ^ 6 :=
    pow_le_pow_left₀ (div_nonneg hnpos.le (by norm_num)) hanchor 6
  have hnumTarget : 0 ≤ 160 * (n : ℝ) / Real.log (n : ℝ) := by positivity
  calc
    120 * ((5 / 12 : ℝ) * n * e + 1 / 2) /
          (((n / 4 - 1 : ℕ) : ℝ) ^ 6) ≤
        (160 * (n : ℝ) / Real.log (n : ℝ)) /
          (((n / 4 - 1 : ℕ) : ℝ)) ^ 6 := by
      exact div_le_div_of_nonneg_right hnum (pow_nonneg hanchorPos.le 6)
    _ ≤ (160 * (n : ℝ) / Real.log (n : ℝ)) /
          (((n : ℝ) / 12) ^ 6) := by
      exact div_le_div_of_nonneg_left hnumTarget
        (pow_pos (div_pos hnpos (by norm_num)) 6) hpowAnchor
    _ = manuscriptSixthResidualDConstant /
          ((n : ℝ) ^ 5 * Real.log (n : ℝ)) := by
      unfold manuscriptSixthResidualDConstant
      field_simp [hnpos.ne', hlogpos.ne']
      <;> ring

/-- The distant unpaired polygamma tail has the target residual rate. -/
theorem manuscriptSixthResidual_A_term_le
    {n : ℕ} (hn : 8 ≤ n)
    (hnLarge : Real.exp (leanSaddleCutoff + 2) < (n : ℝ))
    {e : ℝ} (he : 0 < e) (he12 : e ≤ 1 / 12)
    (heLog : e ≤ 2 / Real.log (n : ℝ)) :
    24 / (((⌊(n : ℝ) / e⌋₊ - 1 : ℕ) : ℝ) ^ 5) ≤
      manuscriptSixthResidualAConstant /
        ((n : ℝ) ^ 5 * Real.log (n : ℝ)) := by
  have hnpos : (0 : ℝ) < n := (Real.exp_pos _).trans hnLarge
  have hlogHuge : leanSaddleCutoff + 2 < Real.log (n : ℝ) :=
    (Real.lt_log_iff_exp_lt hnpos).2 hnLarge
  have hlogOne : 1 < Real.log (n : ℝ) := by
    have : 1 < leanSaddleCutoff + 2 := by norm_num [leanSaddleCutoff]
    exact this.trans hlogHuge
  have hlogpos : 0 < Real.log (n : ℝ) := zero_lt_one.trans hlogOne
  have hfar := manuscriptFarAnchor_ge_quarter_log hn he he12 heLog hlogOne
  have hfarPos : 0 < (((⌊(n : ℝ) / e⌋₊ - 1 : ℕ) : ℝ)) :=
    (div_pos (mul_pos hnpos hlogpos) (by norm_num : (0 : ℝ) < 4)).trans_le hfar
  have hpowFar :
      ((n : ℝ) * Real.log (n : ℝ) / 4) ^ 5 ≤
        (((⌊(n : ℝ) / e⌋₊ - 1 : ℕ) : ℝ)) ^ 5 :=
    pow_le_pow_left₀
      (div_nonneg (mul_nonneg hnpos.le hlogpos.le) (by norm_num)) hfar 5
  have hlogPower :
      Real.log (n : ℝ) ≤ Real.log (n : ℝ) ^ 5 := by
    have hnonneg : 0 ≤ Real.log (n : ℝ) := hlogpos.le
    nlinarith [sq_nonneg (Real.log (n : ℝ) ^ 2 - 1)]
  have hdenomPower :
      (n : ℝ) ^ 5 * Real.log (n : ℝ) ≤
        (n : ℝ) ^ 5 * Real.log (n : ℝ) ^ 5 :=
    mul_le_mul_of_nonneg_left hlogPower (pow_nonneg hnpos.le 5)
  have htargetPos : 0 < (n : ℝ) ^ 5 * Real.log (n : ℝ) :=
    mul_pos (pow_pos hnpos 5) hlogpos
  calc
    24 / (((⌊(n : ℝ) / e⌋₊ - 1 : ℕ) : ℝ) ^ 5) ≤
        24 / (((n : ℝ) * Real.log (n : ℝ) / 4) ^ 5) := by
      exact div_le_div_of_nonneg_left (by norm_num)
        (pow_pos (div_pos (mul_pos hnpos hlogpos) (by norm_num)) 5) hpowFar
    _ = manuscriptSixthResidualAConstant /
          ((n : ℝ) ^ 5 * Real.log (n : ℝ) ^ 5) := by
      unfold manuscriptSixthResidualAConstant
      field_simp [hnpos.ne', hlogpos.ne']
      <;> ring
    _ ≤ manuscriptSixthResidualAConstant /
          ((n : ℝ) ^ 5 * Real.log (n : ℝ)) := by
      exact div_le_div_of_nonneg_left
        (by norm_num [manuscriptSixthResidualAConstant]) htargetPos hdenomPower

/-- Final single-rate theorem for the concrete outer-box sixth residual. -/
theorem manuscriptSixthResidual_outerBox_rate
    {y : BranchPoint} (hy : InOuterParameterBox y)
    {n : ℕ} (hn : 8 ≤ n)
    (hnLarge : Real.exp (leanSaddleCutoff + 2) < (n : ℝ))
    {e : ℝ} (he : 0 < e) (he12 : e ≤ 1 / 12)
    (heLog : e ≤ 2 / Real.log (n : ℝ))
    {z : ℂ}
    (hzNorm : ‖z‖ ≤ manuscriptInteriorCauchyRadius (n : ℝ))
    (hzRe : -(n : ℝ) / 2 ≤ z.re) :
    ‖manuscriptSixthResidualValue
        (manuscriptXiSixthLogDecomposition
          (manuscriptMomentSaddleMainSix ((n : ℂ) + z)) ((n : ℂ) + z)) n
        (residualParameterA y n e)
        (residualParameterB y n e)
        (residualParameterC y n)
        (residualParameterD y n e) z‖ ≤
      manuscriptSixthResidualRateConstant /
        ((n : ℝ) ^ 5 * Real.log (n : ℝ)) := by
  have hbase := manuscriptSixthResidual_outerBox_farA_norm_le
    hy hn hnLarge he he12 hzNorm hzRe
  have hCauchy := manuscriptSixthResidual_cauchy_term_le hnLarge
  have hBC := manuscriptSixthResidual_BC_term_le hn hnLarge he heLog
  have hD := manuscriptSixthResidual_D_term_le hn hnLarge he heLog
  have hA := manuscriptSixthResidual_A_term_le hn hnLarge he he12 heLog
  apply hbase.trans
  calc
    1280000 / ((n : ℝ) ^ 5 * Real.log (n : ℝ)) +
          Nat.factorial 6 *
            ((3 / 2 : ℝ) * manuscriptCauchyEpsilon (n : ℝ)) /
              manuscriptInteriorCauchyRadius (n : ℝ) ^ 6 +
        120 * (6 * n * e) / (((n / 4 - 1 : ℕ) : ℝ) ^ 6) +
        120 * ((5 / 12 : ℝ) * n * e + 1 / 2) /
          (((n / 4 - 1 : ℕ) : ℝ) ^ 6) +
        24 / (((⌊(n : ℝ) / e⌋₊ - 1 : ℕ) : ℝ) ^ 5) ≤
      1280000 / ((n : ℝ) ^ 5 * Real.log (n : ℝ)) +
        manuscriptSixthResidualCauchyConstant /
          ((n : ℝ) ^ 5 * Real.log (n : ℝ)) +
        manuscriptSixthResidualBCConstant /
          ((n : ℝ) ^ 5 * Real.log (n : ℝ)) +
        manuscriptSixthResidualDConstant /
          ((n : ℝ) ^ 5 * Real.log (n : ℝ)) +
        manuscriptSixthResidualAConstant /
          ((n : ℝ) ^ 5 * Real.log (n : ℝ)) := by gcongr
    _ = manuscriptSixthResidualRateConstant /
          ((n : ℝ) ^ 5 * Real.log (n : ℝ)) := by
      unfold manuscriptSixthResidualRateConstant
      ring

end Zeta23.Research.JensenWedge
