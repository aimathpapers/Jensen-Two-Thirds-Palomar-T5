import Zeta23.Research.JensenWedge.SixthResidualAssembly
import Zeta23.Research.JensenWedge.QuantitativeBranch

/-!
# Concrete parameter geometry for the sixth residual

The residual theorem is written in terms of the hypergeometric parameters
`A,B,C,D`.  This module reconstructs them from the paper's branch coordinates
`(alpha,t,w,delta)`, the integer center `n`, and `e = 1 / L_n`.  Exact outer
box arithmetic then supplies every right-half-plane and displacement premise
used by `SixthResidualAssembly`.
-/

noncomputable section

namespace Zeta23.Research.JensenWedge

/-- `A = alpha n / e` in the paper's scaled branch coordinates. -/
def residualParameterA (y : BranchPoint) (n : ℕ) (e : ℝ) : ℝ :=
  y 0 * n / e

/-- `B = n(t+w e)`. -/
def residualParameterB (y : BranchPoint) (n : ℕ) (e : ℝ) : ℝ :=
  n * (y 1 + y 2 * e)

/-- `C = nt`. -/
def residualParameterC (y : BranchPoint) (n : ℕ) : ℝ :=
  n * y 1

/-- `D = n(1+delta e)`. -/
def residualParameterD (y : BranchPoint) (n : ℕ) (e : ℝ) : ℝ :=
  n * (1 + y 3 * e)

/-- The residual parameterization is exactly the earlier Jacobi
parameterization after setting its reciprocal scale to `1/n`. -/
theorem residualParameters_eq_jacobiParameters
    {y : BranchPoint} {n : ℕ} {e : ℝ}
    (hn : 0 < n) (he : 0 < e) :
    residualParameterA y n e = jacobiA y (1 / n) e ∧
      residualParameterB y n e = jacobiB y (1 / n) e ∧
      residualParameterC y n = jacobiC y (1 / n) ∧
      residualParameterD y n e = jacobiD y (1 / n) e := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  constructor
  · simp only [residualParameterA, jacobiA]
    field_simp [ne_of_gt hnR, ne_of_gt he]
  constructor
  · simp only [residualParameterB, jacobiB]
    field_simp [ne_of_gt hnR]
  constructor
  · simp only [residualParameterC, jacobiC]
    field_simp [ne_of_gt hnR]
  · simp only [residualParameterD, jacobiD]
    field_simp [ne_of_gt hnR]

/-- All finite geometry needed to invoke the sixth-residual bound at a
complex offset `z`.  The integer anchor is the conservative floor `n/4`. -/
structure ResidualParameterCertificate
    (y : BranchPoint) (n : ℕ) (e : ℝ) (z : ℂ) : Prop where
  anchor_two : 2 ≤ n / 4
  B_right : ((n / 4 : ℕ) : ℝ) ≤
    (((residualParameterB y n e : ℝ) : ℂ) + z).re
  C_right : ((n / 4 : ℕ) : ℝ) ≤
    (((residualParameterC y n : ℝ) : ℂ) + z).re
  D_right : ((n / 4 : ℕ) : ℝ) ≤
    (((residualParameterD y n e : ℝ) : ℂ) + z).re
  half_right : ((n / 4 : ℕ) : ℝ) ≤
    ((n : ℂ) + 1 / 2 + z).re
  A_right : ((n / 4 : ℕ) : ℝ) ≤
    (((residualParameterA y n e : ℝ) : ℂ) + z).re
  BC_distance :
    ‖((residualParameterB y n e : ℝ) : ℂ) -
        ((residualParameterC y n : ℝ) : ℂ)‖ ≤
      6 * n * e
  Dhalf_distance :
    ‖((residualParameterD y n e : ℝ) : ℂ) -
        ((n : ℂ) + 1 / 2)‖ ≤
      (5 / 12 : ℝ) * n * e + 1 / 2

/-- The paper's exact outer parameter box constructs the full residual
geometry certificate. -/
theorem residualParameterCertificate_of_outerBox
    {y : BranchPoint} (hy : InOuterParameterBox y)
    {n : ℕ} (hn : 8 ≤ n)
    {e : ℝ} (he : 0 < e) (he12 : e ≤ 1 / 12)
    {z : ℂ} (hz : -(n : ℝ) / 2 ≤ z.re) :
    ResidualParameterCertificate y n e z := by
  rcases hy with ⟨ha0, ha1, ht0, ht1, hw0, hw1, hd0, hd1⟩
  have hnR : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have hnRpos : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hmcast : (((n / 4 : ℕ) : ℝ)) ≤ (n : ℝ) / 4 := by
    simpa using (Nat.cast_div_le (m := n) (n := 4) :
      (((n / 4 : ℕ) : ℝ)) ≤ (n : ℝ) / (4 : ℝ))
  have hwe : 0 ≤ y 2 * e :=
    (mul_pos (lt_of_lt_of_le (by norm_num) hw0) he).le
  have hde : 0 ≤ y 3 * e :=
    (mul_pos (lt_of_lt_of_le (by norm_num) hd0) he).le
  have hBbase : 7 / 4 ≤ y 1 + y 2 * e := by linarith
  have hCbase : 7 / 4 ≤ y 1 := ht0
  have hDbase : 1 ≤ 1 + y 3 * e := by linarith
  have hBlinear : (7 / 4 : ℝ) * n ≤ residualParameterB y n e := by
    unfold residualParameterB
    simpa [mul_comm] using mul_le_mul_of_nonneg_left hBbase hnR
  have hClinear : (7 / 4 : ℝ) * n ≤ residualParameterC y n := by
    unfold residualParameterC
    simpa [mul_comm] using mul_le_mul_of_nonneg_left hCbase hnR
  have hDlinear : (n : ℝ) ≤ residualParameterD y n e := by
    unfold residualParameterD
    simpa [mul_comm] using mul_le_mul_of_nonneg_left hDbase hnR
  have hratio : 30 ≤ y 0 / e := by
    rw [le_div_iff₀ he]
    nlinarith
  have hAlinear : (30 : ℝ) * n ≤ residualParameterA y n e := by
    unfold residualParameterA
    calc
      (30 : ℝ) * n ≤ (y 0 / e) * n :=
        mul_le_mul_of_nonneg_right hratio hnR
      _ = y 0 * n / e := by ring
  have hBCeq : residualParameterB y n e - residualParameterC y n =
      (n : ℝ) * y 2 * e := by
    unfold residualParameterB residualParameterC
    ring
  have hBCnonneg : 0 ≤ (n : ℝ) * y 2 * e := by positivity
  have hBCbound :
      |residualParameterB y n e - residualParameterC y n| ≤ 6 * n * e := by
    rw [hBCeq, abs_of_nonneg hBCnonneg]
    have := mul_le_mul_of_nonneg_right hw1
      (mul_nonneg hnR he.le)
    nlinarith
  have hDdiff : residualParameterD y n e - ((n : ℝ) + 1 / 2) =
      (n : ℝ) * y 3 * e - 1 / 2 := by
    unfold residualParameterD
    ring
  have hDterm : 0 ≤ (n : ℝ) * y 3 * e := by positivity
  have hDupper : (n : ℝ) * y 3 * e ≤ (5 / 12 : ℝ) * n * e := by
    have := mul_le_mul_of_nonneg_right hd1
      (mul_nonneg hnR he.le)
    nlinarith
  refine {
    anchor_two := by omega
    B_right := ?_
    C_right := ?_
    D_right := ?_
    half_right := ?_
    A_right := ?_
    BC_distance := ?_
    Dhalf_distance := ?_ }
  · norm_num only [Complex.add_re, Complex.ofReal_re]
    exact hmcast.trans (by linarith)
  · norm_num only [Complex.add_re, Complex.ofReal_re]
    exact hmcast.trans (by linarith)
  · norm_num only [Complex.add_re, Complex.ofReal_re]
    exact hmcast.trans (by linarith)
  · norm_num [Complex.div_re, Complex.normSq_apply]
    exact hmcast.trans (by linarith)
  · norm_num only [Complex.add_re, Complex.ofReal_re]
    exact hmcast.trans (by linarith)
  · simpa only [← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
      using hBCbound
  · have hcast :
        ((residualParameterD y n e : ℝ) : ℂ) -
            ((n : ℂ) + 1 / 2) =
          ((residualParameterD y n e - ((n : ℝ) + 1 / 2) : ℝ) : ℂ) := by
      push_cast
      ring
    rw [hcast, Complex.norm_real, Real.norm_eq_abs]
    rw [hDdiff]
    calc
      |(n : ℝ) * y 3 * e - 1 / 2| ≤
          (n : ℝ) * y 3 * e + 1 / 2 := by
        rw [sub_eq_add_neg]
        exact (abs_add_le _ _).trans_eq (by
          rw [abs_of_nonneg hDterm, abs_neg,
            abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2)])
      _ ≤ (5 / 12 : ℝ) * n * e + 1 / 2 := by linarith

/-- The distant `A` argument admits the much larger integer anchor
`floor(n/e)`.  Keeping this separate from the common `n/4` anchor preserves
the logarithmic gain in the final residual estimate. -/
theorem residualParameterA_floor_anchor_of_outerBox
    {y : BranchPoint} (hy : InOuterParameterBox y)
    {n : ℕ} (hn : 8 ≤ n)
    {e : ℝ} (he : 0 < e) (he12 : e ≤ 1 / 12)
    {z : ℂ} (hzRe : -(n : ℝ) / 2 ≤ z.re) :
    2 ≤ ⌊(n : ℝ) / e⌋₊ ∧
      ((⌊(n : ℝ) / e⌋₊ : ℕ) : ℝ) ≤
        (((residualParameterA y n e : ℝ) : ℂ) + z).re := by
  rcases hy with ⟨ha0, _ha1, _ht0, _ht1, _hw0, _hw1, _hd0, _hd1⟩
  have hnR : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have hnRpos : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hnEightR : (8 : ℝ) ≤ n := by exact_mod_cast hn
  have hneNonneg : 0 ≤ (n : ℝ) / e := div_nonneg hnR he.le
  have hneLower : 12 * (n : ℝ) ≤ (n : ℝ) / e := by
    rw [le_div_iff₀ he]
    have hmul := mul_le_mul_of_nonneg_left he12 hnR
    nlinarith
  have hfloorTwo : 2 ≤ ⌊(n : ℝ) / e⌋₊ := by
    apply Nat.le_floor
    nlinarith
  have hfloorLe : ((⌊(n : ℝ) / e⌋₊ : ℕ) : ℝ) ≤ (n : ℝ) / e :=
    Nat.floor_le hneNonneg
  have hAlinear :
      (5 / 2 : ℝ) * ((n : ℝ) / e) ≤ residualParameterA y n e := by
    unfold residualParameterA
    have hscale : 0 ≤ (n : ℝ) / e := hneNonneg
    have hmul := mul_le_mul_of_nonneg_right ha0 hscale
    calc
      (5 / 2 : ℝ) * ((n : ℝ) / e) ≤ y 0 * ((n : ℝ) / e) := hmul
      _ = y 0 * (n : ℝ) / e := by ring
  constructor
  · exact hfloorTwo
  · norm_num only [Complex.add_re, Complex.ofReal_re]
    linarith

/-- The concrete outer-box parameters instantiate the end-to-end residual
bound, leaving only the moving-saddle `mainSix` value explicit. -/
theorem manuscriptSixthResidual_outerBox_norm_le
    {y : BranchPoint} (hy : InOuterParameterBox y)
    {n : ℕ} (hn : 8 ≤ n)
    (hnLarge : Real.exp (leanSaddleCutoff + 2) < (n : ℝ))
    {e : ℝ} (he : 0 < e) (he12 : e ≤ 1 / 12)
    {z mainSix : ℂ} {Hmain : ℝ}
    (hzNorm : ‖z‖ ≤ manuscriptInteriorCauchyRadius (n : ℝ))
    (hzRe : -(n : ℝ) / 2 ≤ z.re)
    (hmain : ‖mainSix‖ ≤ Hmain) :
    ‖manuscriptSixthResidualValue
        (manuscriptXiSixthLogDecomposition mainSix ((n : ℂ) + z)) n
        (residualParameterA y n e)
        (residualParameterB y n e)
        (residualParameterC y n)
        (residualParameterD y n e) z‖ ≤
      (Hmain + Nat.factorial 6 *
        ((3 / 2 : ℝ) * manuscriptCauchyEpsilon (n : ℝ)) /
          manuscriptInteriorCauchyRadius (n : ℝ) ^ 6) +
        120 * (6 * n * e) / (((n / 4 - 1 : ℕ) : ℝ) ^ 6) +
        120 * ((5 / 12 : ℝ) * n * e + 1 / 2) /
          (((n / 4 - 1 : ℕ) : ℝ) ^ 6) +
        24 / (((n / 4 - 1 : ℕ) : ℝ) ^ 5) := by
  let C := residualParameterCertificate_of_outerBox hy hn he he12 hzRe
  have hzCenter : (n : ℂ) + z ∈
      Metric.closedBall ((n : ℝ) : ℂ)
        (manuscriptInteriorCauchyRadius (n : ℝ)) := by
    rw [Metric.mem_closedBall, dist_eq_norm]
    convert hzNorm using 1 <;> push_cast <;> ring
  have hbase := manuscriptSixthResidualValue_of_xiDecomposition_norm_le
    hnLarge hzCenter hmain C.anchor_two C.B_right C.C_right C.D_right
      C.half_right C.A_right
  apply hbase.trans
  gcongr
  · exact C.BC_distance
  · exact C.Dhalf_distance

end Zeta23.Research.JensenWedge
