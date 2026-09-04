import Mathlib.Analysis.SpecialFunctions.Stirling

/-!
# Effective Stirling transport for the coefficient factorial quotient

The exact T1/T5 coefficient assembly evaluates the Gamma quotient only at a
positive integer `M`.  This module therefore uses Mathlib's real factorial
Stirling theorem directly, avoiding an unnecessary complex-Gamma extension.
It derives an explicit Robbins-rate error and proves that the quotient
`M!/(2M)!` is its traditional Holland elementary main times `1 + error`, with
`|error| <= 1/(4M)`.
-/

namespace Zeta23.Research.JensenWedge

open scoped Topology Real Nat Asymptotics
open Nat hiding log log_pow
open Finset Filter Real

noncomputable section

theorem log_stirlingSeq_sub_limit_le {n : ℕ} (hn : n ≠ 0) :
    Real.log (Stirling.stirlingSeq n) - Real.log (Real.sqrt Real.pi) ≤
      1 / (12 * (n : ℝ)) := by
  have hpos : 0 < Stirling.stirlingSeq n := by
    obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn
    exact Stirling.stirlingSeq'_pos k
  have hsqrt : 0 < Real.sqrt Real.pi := by positivity
  have hlimLog : Tendsto (fun N : ℕ => Real.log (Stirling.stirlingSeq (n + N))) atTop
      (𝓝 (Real.log (Real.sqrt Real.pi))) := by
    exact (Real.continuousAt_log hsqrt.ne').tendsto.comp
      (Stirling.tendsto_stirlingSeq_sqrt_pi.comp (by
        simpa [add_comm] using tendsto_add_atTop_nat n))
  have hlim : Tendsto
      (fun N : ℕ => Real.log (Stirling.stirlingSeq n) -
        Real.log (Stirling.stirlingSeq (n + N))) atTop
      (𝓝 (Real.log (Stirling.stirlingSeq n) - Real.log (Real.sqrt Real.pi))) :=
    tendsto_const_nhds.sub hlimLog
  apply le_of_tendsto' hlim
  intro N
  have htel : Real.log (Stirling.stirlingSeq n) -
      Real.log (Stirling.stirlingSeq (n + N)) =
      ∑ k ∈ Finset.range N,
        (Real.log (Stirling.stirlingSeq (n + k)) -
          Real.log (Stirling.stirlingSeq (n + k + 1))) := by
    simpa [Nat.add_assoc] using
      (Finset.sum_range_sub' (fun k : ℕ => Real.log (Stirling.stirlingSeq (n + k))) N).symm
  rw [htel]
  calc
    ∑ k ∈ Finset.range N,
        (Real.log (Stirling.stirlingSeq (n + k)) -
          Real.log (Stirling.stirlingSeq (n + k + 1)))
        ≤ ∑ k ∈ Finset.range N,
            (1 / (12 * ((n + k : ℕ) : ℝ) * ((n + k + 1 : ℕ) : ℝ))) := by
      apply Finset.sum_le_sum
      intro k hk
      simpa [Nat.cast_add, Nat.cast_one] using Stirling.log_stirlingSeq_sdiff_le (n + k)
    _ = 1 / (12 * (n : ℝ)) - 1 / (12 * ((n + N : ℕ) : ℝ)) := by
      rw [Finset.sum_congr rfl (fun (k : ℕ) _ => by
        have hnk : ((n + k : ℕ) : ℝ) ≠ 0 := by positivity
        have hnk1 : ((n + k + 1 : ℕ) : ℝ) ≠ 0 := by positivity
        rw [show 1 / (12 * ((n + k : ℕ) : ℝ) * ((n + k + 1 : ℕ) : ℝ)) =
            1 / (12 * ((n + k : ℕ) : ℝ)) -
            1 / (12 * ((n + k + 1 : ℕ) : ℝ)) by
          field_simp
          push_cast
          ring])]
      simpa [Nat.add_assoc] using
        (Finset.sum_range_sub' (fun k : ℕ => 1 / (12 * ((n + k : ℕ) : ℝ))) N)
    _ ≤ 1 / (12 * (n : ℝ)) := by
      have : 0 ≤ 1 / (12 * ((n + N : ℕ) : ℝ)) := by positivity
      linarith

/-- The multiplicative correction in the usual real Stirling formula. -/
def factorialStirlingCorrection (n : ℕ) : ℝ :=
  Stirling.stirlingSeq n / Real.sqrt Real.pi

theorem one_le_factorialStirlingCorrection {n : ℕ} (hn : n ≠ 0) :
    1 ≤ factorialStirlingCorrection n := by
  unfold factorialStirlingCorrection
  rw [le_div_iff₀ (by positivity)]
  simpa using Stirling.sqrt_pi_le_stirlingSeq hn

theorem factorialStirlingCorrection_le {n : ℕ} (hn : n ≠ 0) :
    factorialStirlingCorrection n ≤ 1 + 1 / (6 * (n : ℝ)) := by
  have hnR : (1 : ℝ) ≤ n := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hn
  have hpos : 0 < Stirling.stirlingSeq n := by
    obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn
    exact Stirling.stirlingSeq'_pos k
  have hsqrt : 0 < Real.sqrt Real.pi := by positivity
  let x := Real.log (Stirling.stirlingSeq n) - Real.log (Real.sqrt Real.pi)
  have hx0 : 0 ≤ x := by
    dsimp [x]
    exact sub_nonneg.mpr (Real.log_le_log hsqrt (Stirling.sqrt_pi_le_stirlingSeq hn))
  have hx : x ≤ 1 / (12 * (n : ℝ)) := log_stirlingSeq_sub_limit_le hn
  have hxSmall : x ≤ 1 / 12 := by
    calc
      x ≤ 1 / (12 * (n : ℝ)) := hx
      _ ≤ 1 / 12 := by
        rw [div_le_div_iff₀ (by positivity) (by norm_num)]
        nlinarith
  have hx2 : x < 2 := lt_of_le_of_lt hxSmall (by norm_num)
  have hexp : Real.exp x ≤ (2 + x) / (2 - x) :=
    Real.exp_le_two_add_div_two_sub hx0 hx2
  have hfrac : (2 + x) / (2 - x) ≤ 1 + 2 * x := by
    rw [div_le_iff₀ (by linarith)]
    nlinarith [sq_nonneg x]
  have hcorr : factorialStirlingCorrection n = Real.exp x := by
    unfold factorialStirlingCorrection
    rw [Real.exp_sub, Real.exp_log hpos, Real.exp_log hsqrt]
  rw [hcorr]
  calc
    Real.exp x ≤ (2 + x) / (2 - x) := hexp
    _ ≤ 1 + 2 * x := hfrac
    _ ≤ 1 + 2 * (1 / (12 * (n : ℝ))) := by gcongr
    _ = 1 + 1 / (6 * (n : ℝ)) := by ring

theorem abs_factorialStirlingCorrection_sub_one_le {n : ℕ} (hn : n ≠ 0) :
    |factorialStirlingCorrection n - 1| ≤ 1 / (6 * (n : ℝ)) := by
  rw [abs_of_nonneg (sub_nonneg.mpr (one_le_factorialStirlingCorrection hn))]
  linarith [factorialStirlingCorrection_le hn]

/-- The correction multiplying the elementary Stirling main term in `M!/(2M)!`. -/
def factorialRatioCorrection (M : ℕ) : ℝ :=
  factorialStirlingCorrection M / factorialStirlingCorrection (2 * M)

theorem abs_factorialRatioCorrection_sub_one_le {M : ℕ} (hM : M ≠ 0) :
    |factorialRatioCorrection M - 1| ≤ 1 / (4 * (M : ℝ)) := by
  have h2M : 2 * M ≠ 0 := mul_ne_zero (by norm_num) hM
  have hden : 1 ≤ factorialStirlingCorrection (2 * M) :=
    one_le_factorialStirlingCorrection h2M
  have hden0 : factorialStirlingCorrection (2 * M) ≠ 0 :=
    ne_of_gt (lt_of_lt_of_le zero_lt_one hden)
  have hnum := abs_factorialStirlingCorrection_sub_one_le hM
  have htwo := abs_factorialStirlingCorrection_sub_one_le h2M
  have hsub : |factorialStirlingCorrection M - factorialStirlingCorrection (2 * M)| ≤
      1 / (6 * (M : ℝ)) + 1 / (6 * ((2 * M : ℕ) : ℝ)) := by
    calc
      |factorialStirlingCorrection M - factorialStirlingCorrection (2 * M)| =
          |(factorialStirlingCorrection M - 1) -
            (factorialStirlingCorrection (2 * M) - 1)| := by ring_nf
      _ ≤ |factorialStirlingCorrection M - 1| +
          |factorialStirlingCorrection (2 * M) - 1| := abs_sub _ _
      _ ≤ 1 / (6 * (M : ℝ)) + 1 / (6 * ((2 * M : ℕ) : ℝ)) :=
        add_le_add hnum htwo
  unfold factorialRatioCorrection
  rw [show factorialStirlingCorrection M / factorialStirlingCorrection (2 * M) - 1 =
      (factorialStirlingCorrection M - factorialStirlingCorrection (2 * M)) /
        factorialStirlingCorrection (2 * M) by field_simp]
  rw [abs_div, abs_of_nonneg (le_trans zero_le_one hden)]
  calc
    |factorialStirlingCorrection M - factorialStirlingCorrection (2 * M)| /
          factorialStirlingCorrection (2 * M)
        ≤ |factorialStirlingCorrection M - factorialStirlingCorrection (2 * M)| :=
      div_le_self (abs_nonneg _) hden
    _ ≤ 1 / (6 * (M : ℝ)) + 1 / (6 * ((2 * M : ℕ) : ℝ)) := hsub
    _ = 1 / (4 * (M : ℝ)) := by
      push_cast
      ring

def factorialStirlingMain (n : ℕ) : ℝ :=
  Real.sqrt (2 * n) * (n / Real.exp 1) ^ n

def factorialRatioElementaryMain (M : ℕ) : ℝ :=
  factorialStirlingMain M / factorialStirlingMain (2 * M)

/-- The same elementary main in the traditional Holland/Stirling form. -/
def hollandFactorialRatioMain (M : ℕ) : ℝ :=
  Real.exp (M : ℝ) * ((M : ℝ) ^ M * Real.sqrt (M : ℝ)) /
    (((2 * M : ℕ) : ℝ) ^ (2 * M) * Real.sqrt ((2 * M : ℕ) : ℝ))

theorem factorialStirlingMain_pos {n : ℕ} (hn : n ≠ 0) :
    0 < factorialStirlingMain n := by
  unfold factorialStirlingMain
  positivity

theorem factorialRatioElementaryMain_eq_holland
    {M : ℕ} (hM : M ≠ 0) :
    factorialRatioElementaryMain M = hollandFactorialRatioMain M := by
  have hMR : (0 : ℝ) < M := by exact_mod_cast Nat.pos_of_ne_zero hM
  have h2MR : (0 : ℝ) < ((2 * M : ℕ) : ℝ) := by positivity
  have hsM : Real.sqrt (M : ℝ) ≠ 0 := ne_of_gt (Real.sqrt_pos.2 hMR)
  have hs2M : Real.sqrt ((2 * M : ℕ) : ℝ) ≠ 0 :=
    ne_of_gt (Real.sqrt_pos.2 h2MR)
  have hroot :
      Real.sqrt (2 * (((2 * M : ℕ) : ℝ))) = 2 * Real.sqrt (M : ℝ) := by
    rw [show (2 : ℝ) * (((2 * M : ℕ) : ℝ)) = (4 : ℝ) * (M : ℝ) by
      push_cast
      ring, Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 4)]
    rw [show (4 : ℝ) = (2 : ℝ) ^ 2 by norm_num, Real.sqrt_sq_eq_abs]
    norm_num
  have hexpM : Real.exp (M : ℝ) = Real.exp 1 ^ M := by
    simpa only [mul_one] using Real.exp_nat_mul 1 M
  unfold factorialRatioElementaryMain factorialStirlingMain hollandFactorialRatioMain
  rw [hroot, div_pow, div_pow, hexpM]
  push_cast
  field_simp
  rw [Real.sq_sqrt (by positivity), Real.sq_sqrt (by positivity)]
  ring

theorem factorial_ratio_eq_elementaryMain_mul_correction
    {M : ℕ} (hM : M ≠ 0) :
    (M.factorial : ℝ) / ((2 * M).factorial : ℝ) =
      factorialRatioElementaryMain M * factorialRatioCorrection M := by
  have h2M : 2 * M ≠ 0 := mul_ne_zero (by norm_num) hM
  have hmainM : factorialStirlingMain M ≠ 0 :=
    ne_of_gt (factorialStirlingMain_pos hM)
  have hmain2M : factorialStirlingMain (2 * M) ≠ 0 :=
    ne_of_gt (factorialStirlingMain_pos h2M)
  have hsqrt : Real.sqrt Real.pi ≠ 0 := ne_of_gt (by positivity)
  unfold factorialRatioElementaryMain factorialRatioCorrection
  unfold factorialStirlingCorrection Stirling.stirlingSeq factorialStirlingMain
  field_simp

theorem factorial_ratio_relative_error
    {M : ℕ} (hM : M ≠ 0) :
    ∃ error : ℝ,
      (M.factorial : ℝ) / ((2 * M).factorial : ℝ) =
        factorialRatioElementaryMain M * (1 + error) ∧
      |error| ≤ 1 / (4 * (M : ℝ)) := by
  refine ⟨factorialRatioCorrection M - 1, ?_,
    abs_factorialRatioCorrection_sub_one_le hM⟩
  rw [show 1 + (factorialRatioCorrection M - 1) = factorialRatioCorrection M by ring]
  exact factorial_ratio_eq_elementaryMain_mul_correction hM

end

end Zeta23.Research.JensenWedge
