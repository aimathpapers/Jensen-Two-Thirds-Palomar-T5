import Zeta23.GammaFacts.StirlingRight
import Zeta23.Research.JensenWedge.FactorialRatioStirling
import Zeta23.Research.JensenWedge.SaddleMainRatio
import Mathlib.Analysis.ODE.Gronwall

/-!
# Complex Gamma-ratio transport for the coefficient theorem

This module supplies the exact differential identity behind the complex
Stirling factor in Theorem 7.1.  The quotient is normalized by the traditional
elementary main term.  Its logarithmic derivative is exactly a difference of
the all-point right-half-plane digamma remainders proved in
`GammaFacts/StirlingRight.lean`, hence is bounded by `3 / (Re z)^2`.

The next substage integrates this differential identity from a positive
integer anchor to the narrow coefficient sector.
-/

namespace Zeta23.Research.JensenWedge

open Complex Filter Topology Set Zeta23.StirlingRight

noncomputable section

/-- The holomorphic continuation of `M! / (2M)!` to the right half-plane. -/
def complexFactorialRatio (z : ℂ) : ℂ :=
  Complex.Gamma (z + 1) / Complex.Gamma (2 * z + 1)

/-- Logarithm of Holland's elementary main term, using the principal logarithm
on the right half-plane. -/
def complexFactorialRatioLogMain (z : ℂ) : ℂ :=
  z + (z + 1 / 2) * Complex.log z -
    (2 * z + 1 / 2) * Complex.log (2 * z)

/-- Holland's elementary main term in a manifestly holomorphic form. -/
def complexFactorialRatioMain (z : ℂ) : ℂ :=
  Complex.exp (complexFactorialRatioLogMain z)

/-- The exact multiplicative correction to the complex elementary main. -/
def complexFactorialRatioCorrection (z : ℂ) : ℂ :=
  complexFactorialRatio z / complexFactorialRatioMain z

/-- Stirling's all-point digamma remainder. -/
def digammaStirlingResidual (z : ℂ) : ℂ :=
  Complex.digamma z - Complex.log z + (1 / 2 : ℂ) / z

/-- Logarithmic derivative error of the normalized Gamma quotient. -/
def gammaRatioLogDerivError (z : ℂ) : ℂ :=
  digammaStirlingResidual z - 2 * digammaStirlingResidual (2 * z)

theorem complexFactorialRatioMain_ne_zero (z : ℂ) :
    complexFactorialRatioMain z ≠ 0 :=
  Complex.exp_ne_zero _

private theorem gamma_ne_neg_nat_re {z : ℂ} (hz : 0 < z.re) :
    ∀ m : ℕ, z ≠ -(m : ℂ) := by
  intro m h
  rw [h] at hz
  simp only [Complex.neg_re, Complex.natCast_re] at hz
  nlinarith [Nat.cast_nonneg (α := ℝ) m]

/-- Gamma's derivative is Gamma times digamma on the right half-plane. -/
theorem hasDerivAt_Gamma_re {z : ℂ} (hz : 0 < z.re) :
    HasDerivAt Complex.Gamma (Complex.Gamma z * Complex.digamma z) z := by
  have hdiff := (Complex.differentiableAt_Gamma z (gamma_ne_neg_nat_re hz)).hasDerivAt
  have hne := Complex.Gamma_ne_zero (gamma_ne_neg_nat_re hz)
  apply hdiff.congr_deriv
  rw [Complex.digamma_def, logDeriv_apply]
  field_simp

theorem hasDerivAt_complexFactorialRatioLogMain {z : ℂ} (hz : 0 < z.re) :
    HasDerivAt complexFactorialRatioLogMain
      (Complex.log z - 2 * Complex.log (2 * z)) z := by
  have hz0 : z ≠ 0 := fun h ↦ by rw [h] at hz; simp at hz
  have h2z0 : 2 * z ≠ 0 := mul_ne_zero (by norm_num) hz0
  have hzLog : HasDerivAt (fun w : ℂ ↦ Complex.log w) z⁻¹ z := Complex.hasDerivAt_log
    (Complex.mem_slitPlane_iff.mpr (Or.inl hz))
  have h2zRe : 0 < (2 * z).re := by simp; linarith
  have h2zLog : HasDerivAt (fun w : ℂ ↦ Complex.log (2 * w)) z⁻¹ z := by
    have h := (Complex.hasDerivAt_log
      (Complex.mem_slitPlane_iff.mpr (Or.inl h2zRe))).comp z
        ((hasDerivAt_id z).const_mul 2)
    convert h using 1 <;> try rfl
    field_simp [hz0, h2z0]
  have hraw := ((hasDerivAt_id z).add
    (((hasDerivAt_id z).add_const (1 / 2 : ℂ)).mul hzLog)).sub
      ((((hasDerivAt_id z).const_mul 2).add_const (1 / 2 : ℂ)).mul h2zLog)
  apply hraw.congr_of_eventuallyEq (Filter.Eventually.of_forall fun w ↦ by
    rfl) |>.congr_deriv
  simp only [id_eq]
  field_simp [hz0, h2z0]
  ring

theorem hasDerivAt_complexFactorialRatioMain {z : ℂ} (hz : 0 < z.re) :
    HasDerivAt complexFactorialRatioMain
      (complexFactorialRatioMain z *
        (Complex.log z - 2 * Complex.log (2 * z))) z := by
  change HasDerivAt (fun w ↦ Complex.exp (complexFactorialRatioLogMain w))
    (Complex.exp (complexFactorialRatioLogMain z) *
      (Complex.log z - 2 * Complex.log (2 * z))) z
  exact (hasDerivAt_complexFactorialRatioLogMain hz).cexp

theorem hasDerivAt_complexFactorialRatio {z : ℂ} (hz : 0 < z.re) :
    HasDerivAt complexFactorialRatio
      (complexFactorialRatio z *
        (Complex.digamma z - 2 * Complex.digamma (2 * z))) z := by
  have hz1 : 0 < (z + 1).re := by simp; linarith
  have h2z1 : 0 < (2 * z + 1).re := by simp; linarith
  have hnum := (hasDerivAt_Gamma_re hz1).comp z ((hasDerivAt_id z).add_const 1)
  have hden := (hasDerivAt_Gamma_re h2z1).comp z
    (((hasDerivAt_id z).const_mul 2).add_const 1)
  have hden_ne := Complex.Gamma_ne_zero (gamma_ne_neg_nat_re h2z1)
  have hquot := hnum.div hden hden_ne
  have hzRec := Complex.digamma_apply_add_one z (gamma_ne_neg_nat_re hz)
  have h2zRe : 0 < (2 * z).re := by simp; linarith
  have h2zRec := Complex.digamma_apply_add_one (2 * z)
    (gamma_ne_neg_nat_re h2zRe)
  apply hquot.congr_of_eventuallyEq (Filter.Eventually.of_forall fun w ↦ by
    rfl) |>.congr_deriv
  simp only [complexFactorialRatio, Function.comp_apply, id_eq]
  rw [hzRec, h2zRec]
  have hz0 : z ≠ 0 := fun h ↦ by rw [h] at hz; simp at hz
  have h2z0 : 2 * z ≠ 0 := mul_ne_zero (by norm_num) hz0
  field_simp [hden_ne, hz0, h2z0]
  ring

/-- Exact differential equation for the normalized complex Gamma quotient. -/
theorem hasDerivAt_complexFactorialRatioCorrection {z : ℂ} (hz : 0 < z.re) :
    HasDerivAt complexFactorialRatioCorrection
      (complexFactorialRatioCorrection z * gammaRatioLogDerivError z) z := by
  have hratio := hasDerivAt_complexFactorialRatio hz
  have hmain := hasDerivAt_complexFactorialRatioMain hz
  have hmain_ne := complexFactorialRatioMain_ne_zero z
  have hquot := hratio.div hmain hmain_ne
  apply hquot.congr_deriv
  simp only [complexFactorialRatioCorrection, gammaRatioLogDerivError,
    digammaStirlingResidual]
  have hz0 : z ≠ 0 := fun h ↦ by rw [h] at hz; simp at hz
  have h2z0 : 2 * z ≠ 0 := mul_ne_zero (by norm_num) hz0
  field_simp [hmain_ne, hz0, h2z0]
  ring

/-- The exact logarithmic derivative error is uniformly `O((Re z)^-2)`. -/
theorem norm_gammaRatioLogDerivError_le {z : ℂ} (hz : 1 ≤ z.re) :
    ‖gammaRatioLogDerivError z‖ ≤ 3 / z.re ^ 2 := by
  have hz2 : 1 ≤ (2 * z).re := by simp; linarith
  have h1 : ‖digammaStirlingResidual z‖ ≤ 2 / z.re ^ 2 := by
    simpa only [digammaStirlingResidual] using digamma_stirling_re_all hz
  have h2 : ‖digammaStirlingResidual (2 * z)‖ ≤ 2 / (2 * z).re ^ 2 := by
    simpa only [digammaStirlingResidual] using digamma_stirling_re_all hz2
  have htri : ‖digammaStirlingResidual z -
      2 * digammaStirlingResidual (2 * z)‖ ≤
      ‖digammaStirlingResidual z‖ +
        ‖2 * digammaStirlingResidual (2 * z)‖ := norm_sub_le _ _
  rw [norm_mul, norm_ofNat] at htri
  calc
    ‖gammaRatioLogDerivError z‖ ≤
        ‖digammaStirlingResidual z‖ +
          2 * ‖digammaStirlingResidual (2 * z)‖ := by
      simpa only [gammaRatioLogDerivError] using htri
    _ ≤ 2 / z.re ^ 2 + 2 * (2 / (2 * z).re ^ 2) := by gcongr
    _ = 3 / z.re ^ 2 := by
      have h2re : (2 * z).re = 2 * z.re := by norm_num
      rw [h2re]
      have hz0 : z.re ≠ 0 := ne_of_gt (lt_of_lt_of_le zero_lt_one hz)
      field_simp
      ring

/-- At positive integers the complex Gamma quotient is exactly the factorial
quotient used by the coefficient identity. -/
theorem complexFactorialRatio_natCast (M : ℕ) :
    complexFactorialRatio (M : ℂ) =
      (((M.factorial : ℝ) / ((2 * M).factorial : ℝ)) : ℂ) := by
  unfold complexFactorialRatio
  have hGM : Complex.Gamma (((M + 1 : ℕ) : ℂ)) = M.factorial := by
    simpa only [Nat.cast_add, Nat.cast_one] using Complex.Gamma_nat_eq_factorial M
  have hG2M : Complex.Gamma (((2 * M + 1 : ℕ) : ℂ)) =
      (2 * M).factorial := by
    simpa only [Nat.cast_add, Nat.cast_one] using
      Complex.Gamma_nat_eq_factorial (2 * M)
  rw [show (M : ℂ) + 1 = ((M + 1 : ℕ) : ℂ) by push_cast; ring,
    show 2 * (M : ℂ) + 1 = ((2 * M + 1 : ℕ) : ℂ) by push_cast; ring,
    hGM, hG2M]
  congr 1

/-- Real logarithmic form of Holland's elementary factorial-ratio main. -/
theorem factorialRatioElementaryMain_eq_exp_log {M : ℕ} (hM : M ≠ 0) :
    factorialRatioElementaryMain M = Real.exp
      ((M : ℝ) + ((M : ℝ) + 1 / 2) * Real.log (M : ℝ) -
        (((2 * M : ℕ) : ℝ) + 1 / 2) * Real.log ((2 * M : ℕ) : ℝ)) := by
  have hMR : (0 : ℝ) < M := by exact_mod_cast Nat.pos_of_ne_zero hM
  have h2MR : (0 : ℝ) < (2 * M : ℕ) := by positivity
  have hpowM : Real.exp ((M : ℝ) * Real.log (M : ℝ)) =
      (M : ℝ) ^ M := by
    calc
      Real.exp ((M : ℝ) * Real.log (M : ℝ)) =
          Real.exp (Real.log (M : ℝ)) ^ M := by
        simpa using Real.exp_nat_mul (Real.log (M : ℝ)) M
      _ = (M : ℝ) ^ M := by rw [Real.exp_log hMR]
  have hpow2M : Real.exp (((2 * M : ℕ) : ℝ) *
      Real.log ((2 * M : ℕ) : ℝ)) =
      ((2 * M : ℕ) : ℝ) ^ (2 * M) := by
    calc
      Real.exp (((2 * M : ℕ) : ℝ) * Real.log ((2 * M : ℕ) : ℝ)) =
          Real.exp (Real.log ((2 * M : ℕ) : ℝ)) ^ (2 * M) := by
        simpa using Real.exp_nat_mul (Real.log ((2 * M : ℕ) : ℝ)) (2 * M)
      _ = ((2 * M : ℕ) : ℝ) ^ (2 * M) := by rw [Real.exp_log h2MR]
  have hsqrtM : Real.exp ((1 / 2 : ℝ) * Real.log (M : ℝ)) =
      Real.sqrt (M : ℝ) := by
    rw [← Real.exp_log (Real.sqrt_pos.2 hMR)]
    rw [Real.log_sqrt hMR.le]
    ring
  have hsqrt2M : Real.exp ((1 / 2 : ℝ) *
      Real.log ((2 * M : ℕ) : ℝ)) = Real.sqrt ((2 * M : ℕ) : ℝ) := by
    rw [← Real.exp_log (Real.sqrt_pos.2 h2MR)]
    rw [Real.log_sqrt h2MR.le]
    ring
  have hblockM : Real.exp (((M : ℝ) + 1 / 2) * Real.log (M : ℝ)) =
      (M : ℝ) ^ M * Real.sqrt (M : ℝ) := by
    rw [add_mul, Real.exp_add, hpowM, hsqrtM]
  have hblock2M : Real.exp ((((2 * M : ℕ) : ℝ) + 1 / 2) *
      Real.log ((2 * M : ℕ) : ℝ)) =
      ((2 * M : ℕ) : ℝ) ^ (2 * M) *
        Real.sqrt ((2 * M : ℕ) : ℝ) := by
    rw [add_mul, Real.exp_add, hpow2M, hsqrt2M]
  rw [factorialRatioElementaryMain_eq_holland hM]
  unfold hollandFactorialRatioMain
  rw [Real.exp_sub, Real.exp_add, hblockM, hblock2M]

/-- The holomorphic elementary main specializes exactly to the real Holland
main at every positive integer. -/
theorem complexFactorialRatioMain_natCast {M : ℕ} (hM : M ≠ 0) :
    complexFactorialRatioMain (M : ℂ) =
      (factorialRatioElementaryMain M : ℂ) := by
  rw [complexFactorialRatioMain, complexFactorialRatioLogMain]
  have h2cast : 2 * (M : ℂ) = ((2 * M : ℕ) : ℂ) := by push_cast; ring
  rw [h2cast, ← Complex.natCast_log, ← Complex.natCast_log]
  have hexponent :
      (M : ℂ) + ((M : ℂ) + 1 / 2) * (Real.log (M : ℝ) : ℂ) -
          (((2 * M : ℕ) : ℂ) + 1 / 2) *
            (Real.log ((2 * M : ℕ) : ℝ) : ℂ) =
        (((M : ℝ) + ((M : ℝ) + 1 / 2) * Real.log (M : ℝ) -
          (((2 * M : ℕ) : ℝ) + 1 / 2) *
            Real.log ((2 * M : ℕ) : ℝ) : ℝ) : ℂ) := by
    push_cast
    ring
  rw [hexponent, ← Complex.ofReal_exp]
  exact congrArg (fun x : ℝ ↦ (x : ℂ))
    (factorialRatioElementaryMain_eq_exp_log hM).symm

/-- The complex correction has precisely the Robbins correction as its
positive-integer anchor. -/
theorem complexFactorialRatioCorrection_natCast {M : ℕ} (hM : M ≠ 0) :
    complexFactorialRatioCorrection (M : ℂ) =
      (factorialRatioCorrection M : ℂ) := by
  rw [complexFactorialRatioCorrection, complexFactorialRatio_natCast M,
    complexFactorialRatioMain_natCast hM]
  have hmain : factorialRatioElementaryMain M ≠ 0 := by
    exact ne_of_gt (div_pos (factorialStirlingMain_pos hM)
      (factorialStirlingMain_pos (mul_ne_zero (by norm_num) hM)))
  have hreal : (M.factorial : ℝ) / ((2 * M).factorial : ℝ) /
      factorialRatioElementaryMain M = factorialRatioCorrection M := by
    apply (div_eq_iff hmain).2
    simpa [mul_comm] using factorial_ratio_eq_elementaryMain_mul_correction hM
  simpa only [Complex.ofReal_div] using
    congrArg (fun x : ℝ ↦ (x : ℂ)) hreal

/-- Straight segment from a positive-integer anchor to a complex coefficient
parameter. -/
def gammaRatioAnchorPoint (M : ℕ) (z : ℂ) (t : ℝ) : ℂ :=
  (M : ℂ) + (t : ℂ) * (z - (M : ℂ))

def gammaRatioAnchorPath (M : ℕ) (z : ℂ) (t : ℝ) : ℂ :=
  complexFactorialRatioCorrection (gammaRatioAnchorPoint M z t)

def gammaRatioAnchorPathD1 (M : ℕ) (z : ℂ) (t : ℝ) : ℂ :=
  (z - (M : ℂ)) * gammaRatioAnchorPath M z t *
    gammaRatioLogDerivError (gammaRatioAnchorPoint M z t)

theorem gammaRatioAnchorPoint_re_ge
    {M : ℕ} {z : ℂ} {t : ℝ}
    (hz : (M : ℝ) ≤ z.re) (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    (M : ℝ) ≤ (gammaRatioAnchorPoint M z t).re := by
  simp only [gammaRatioAnchorPoint, Complex.add_re, Complex.mul_re,
    Complex.ofReal_re, Complex.ofReal_im, Complex.sub_re, Complex.natCast_re,
    zero_mul, sub_zero]
  exact le_add_of_nonneg_right (mul_nonneg ht.1 (sub_nonneg.mpr hz))

theorem hasDerivAt_gammaRatioAnchorPath
    {M : ℕ} {z : ℂ} {t : ℝ}
    (hM : M ≠ 0) (hz : (M : ℝ) ≤ z.re)
    (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    HasDerivAt (gammaRatioAnchorPath M z) (gammaRatioAnchorPathD1 M z t) t := by
  have hM1 : (1 : ℝ) ≤ M := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hM
  have hpRe : 0 < (gammaRatioAnchorPoint M z t).re :=
    lt_of_lt_of_le zero_lt_one (hM1.trans (gammaRatioAnchorPoint_re_ge hz ht))
  have hinner : HasDerivAt
      (fun w : ℂ ↦ (M : ℂ) + w * (z - (M : ℂ)))
      (z - (M : ℂ)) (t : ℂ) := by
    simpa using ((hasDerivAt_id (t : ℂ)).mul_const (z - (M : ℂ))).const_add (M : ℂ)
  have hcomp := (hasDerivAt_complexFactorialRatioCorrection hpRe).comp (t : ℂ) hinner
  have hreal := hcomp.comp_ofReal
  apply hreal.congr_deriv
  simp only [gammaRatioAnchorPathD1, gammaRatioAnchorPath,
    gammaRatioAnchorPoint]
  ring

def gammaRatioAnchorRate (M : ℕ) (z : ℂ) : ℝ :=
  3 * ‖z - (M : ℂ)‖ / (M : ℝ) ^ 2

theorem gammaRatioAnchorRate_nonneg (M : ℕ) (z : ℂ) :
    0 ≤ gammaRatioAnchorRate M z := by
  unfold gammaRatioAnchorRate
  positivity

theorem norm_gammaRatioAnchorPathD1_le
    {M : ℕ} {z : ℂ} {t : ℝ}
    (hM : M ≠ 0) (hz : (M : ℝ) ≤ z.re)
    (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    ‖gammaRatioAnchorPathD1 M z t‖ ≤
      gammaRatioAnchorRate M z * ‖gammaRatioAnchorPath M z t‖ := by
  have hM1 : (1 : ℝ) ≤ M := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hM
  have hpRe : (M : ℝ) ≤ (gammaRatioAnchorPoint M z t).re :=
    gammaRatioAnchorPoint_re_ge hz ht
  have hp1 : 1 ≤ (gammaRatioAnchorPoint M z t).re := hM1.trans hpRe
  have herr := norm_gammaRatioLogDerivError_le hp1
  have hMpos : 0 < (M : ℝ) := lt_of_lt_of_le zero_lt_one hM1
  have hpPos : 0 < (gammaRatioAnchorPoint M z t).re :=
    lt_of_lt_of_le zero_lt_one hp1
  have hfrac : 3 / (gammaRatioAnchorPoint M z t).re ^ 2 ≤
      3 / (M : ℝ) ^ 2 := by
    apply div_le_div_of_nonneg_left (by norm_num) (by positivity)
    nlinarith [sq_nonneg ((gammaRatioAnchorPoint M z t).re - (M : ℝ))]
  calc
    ‖gammaRatioAnchorPathD1 M z t‖ =
        ‖z - (M : ℂ)‖ * ‖gammaRatioAnchorPath M z t‖ *
          ‖gammaRatioLogDerivError (gammaRatioAnchorPoint M z t)‖ := by
      simp only [gammaRatioAnchorPathD1, norm_mul]
    _ ≤ ‖z - (M : ℂ)‖ * ‖gammaRatioAnchorPath M z t‖ *
        (3 / (M : ℝ) ^ 2) := by gcongr; exact herr.trans hfrac
    _ = gammaRatioAnchorRate M z * ‖gammaRatioAnchorPath M z t‖ := by
      unfold gammaRatioAnchorRate
      ring

/-- Grönwall transport of the normalized Gamma quotient along the anchor
segment. -/
theorem norm_gammaRatioAnchorPath_le
    {M : ℕ} {z : ℂ} (hM : M ≠ 0) (hz : (M : ℝ) ≤ z.re)
    {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    ‖gammaRatioAnchorPath M z t‖ ≤
      ‖gammaRatioAnchorPath M z 0‖ *
        Real.exp (gammaRatioAnchorRate M z * t) := by
  let f : ℝ → ℂ := gammaRatioAnchorPath M z
  let f' : ℝ → ℂ := gammaRatioAnchorPathD1 M z
  let K : ℝ := gammaRatioAnchorRate M z
  have hderiv : ∀ u ∈ Set.Icc (0 : ℝ) 1, HasDerivAt f (f' u) u := by
    intro u hu
    exact hasDerivAt_gammaRatioAnchorPath hM hz hu
  have hcont : ContinuousOn f (Set.Icc (0 : ℝ) 1) := by
    intro u hu
    exact (hderiv u hu).continuousAt.continuousWithinAt
  have hwithin : ∀ u ∈ Set.Ico (0 : ℝ) 1,
      HasDerivWithinAt f (f' u) (Set.Ici u) u := by
    intro u hu
    exact (hderiv u ⟨hu.1, hu.2.le⟩).hasDerivWithinAt
  have hbound : ∀ u ∈ Set.Ico (0 : ℝ) 1,
      ‖f' u‖ ≤ K * ‖f u‖ + 0 := by
    intro u hu
    simpa only [add_zero, f, f', K] using
      norm_gammaRatioAnchorPathD1_le hM hz ⟨hu.1, hu.2.le⟩
  have hgr := norm_le_gronwallBound_of_norm_deriv_right_le hcont hwithin
    (le_rfl : ‖f 0‖ ≤ ‖f 0‖) hbound t ht
  rw [gronwallBound_ε0, sub_zero] at hgr
  exact hgr

theorem gammaRatioAnchorPath_zero_sub_one_le
    {M : ℕ} {z : ℂ} (hM : M ≠ 0) :
    ‖gammaRatioAnchorPath M z 0 - 1‖ ≤ 1 / (4 * (M : ℝ)) := by
  have h := abs_factorialRatioCorrection_sub_one_le hM
  have hp : gammaRatioAnchorPoint M z 0 = (M : ℂ) := by
    simp [gammaRatioAnchorPoint]
  rw [gammaRatioAnchorPath, hp, complexFactorialRatioCorrection_natCast hM]
  rw [← Complex.ofReal_one, ← Complex.ofReal_sub, Complex.norm_real]
  exact h

theorem gammaRatioAnchorPath_zero_norm_le
    {M : ℕ} {z : ℂ} (hM : M ≠ 0) :
    ‖gammaRatioAnchorPath M z 0‖ ≤ 5 / 4 := by
  have hM1 : (1 : ℝ) ≤ M := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hM
  calc
    ‖gammaRatioAnchorPath M z 0‖ =
        ‖(gammaRatioAnchorPath M z 0 - 1) + 1‖ := by ring_nf
    _ ≤ ‖gammaRatioAnchorPath M z 0 - 1‖ + ‖(1 : ℂ)‖ := norm_add_le _ _
    _ ≤ 1 / (4 * (M : ℝ)) + 1 := by
      exact add_le_add (gammaRatioAnchorPath_zero_sub_one_le hM) (by norm_num)
    _ ≤ 5 / 4 := by
      have hdiv : 1 / (4 * (M : ℝ)) ≤ 1 / 4 := by
        apply one_div_le_one_div_of_le (by norm_num)
        nlinarith
      nlinarith

theorem gammaRatioAnchorRate_le
    {M : ℕ} {z : ℂ} (hM : M ≠ 0)
    (hdist : ‖z - (M : ℂ)‖ ≤ (M : ℝ) / 100) :
    gammaRatioAnchorRate M z ≤ 3 / (100 * (M : ℝ)) := by
  have hMpos : (0 : ℝ) < M := by exact_mod_cast Nat.pos_of_ne_zero hM
  unfold gammaRatioAnchorRate
  calc
    3 * ‖z - (M : ℂ)‖ / (M : ℝ) ^ 2 ≤
        3 * ((M : ℝ) / 100) / (M : ℝ) ^ 2 := by gcongr
    _ = 3 / (100 * (M : ℝ)) := by field_simp

theorem exp_gammaRatioAnchorRate_le_two
    {M : ℕ} {z : ℂ} (hM : M ≠ 0)
    (hdist : ‖z - (M : ℂ)‖ ≤ (M : ℝ) / 100) :
    Real.exp (gammaRatioAnchorRate M z) ≤ 2 := by
  have hM1 : (1 : ℝ) ≤ M := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hM
  have hK0 := gammaRatioAnchorRate_nonneg M z
  have hK : gammaRatioAnchorRate M z ≤ 3 / 100 := by
    calc
      gammaRatioAnchorRate M z ≤ 3 / (100 * (M : ℝ)) :=
        gammaRatioAnchorRate_le hM hdist
      _ ≤ 3 / 100 := by
        rw [div_le_div_iff₀ (by positivity) (by norm_num)]
        nlinarith
  have hK2 : gammaRatioAnchorRate M z < 2 := lt_of_le_of_lt hK (by norm_num)
  calc
    Real.exp (gammaRatioAnchorRate M z) ≤
        (2 + gammaRatioAnchorRate M z) /
          (2 - gammaRatioAnchorRate M z) :=
      Real.exp_le_two_add_div_two_sub hK0 hK2
    _ ≤ 2 := by
      rw [div_le_iff₀ (sub_pos.mpr hK2)]
      nlinarith

theorem norm_gammaRatioAnchorPath_le_five_halves
    {M : ℕ} {z : ℂ} (hM : M ≠ 0) (hz : (M : ℝ) ≤ z.re)
    (hdist : ‖z - (M : ℂ)‖ ≤ (M : ℝ) / 100)
    {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    ‖gammaRatioAnchorPath M z t‖ ≤ 5 / 2 := by
  have hpath := norm_gammaRatioAnchorPath_le hM hz ht
  have hK0 := gammaRatioAnchorRate_nonneg M z
  have hKt : gammaRatioAnchorRate M z * t ≤ gammaRatioAnchorRate M z := by
    nlinarith [mul_nonneg hK0 (sub_nonneg.mpr ht.2)]
  have hexp : Real.exp (gammaRatioAnchorRate M z * t) ≤ 2 :=
    (Real.exp_le_exp.mpr hKt).trans (exp_gammaRatioAnchorRate_le_two hM hdist)
  calc
    ‖gammaRatioAnchorPath M z t‖ ≤
        ‖gammaRatioAnchorPath M z 0‖ *
          Real.exp (gammaRatioAnchorRate M z * t) := hpath
    _ ≤ (5 / 4) * 2 := by
      gcongr
      exact gammaRatioAnchorPath_zero_norm_le hM
    _ = 5 / 2 := by norm_num

theorem norm_gammaRatioAnchorPathD1_le_three_fortieth
    {M : ℕ} {z : ℂ} (hM : M ≠ 0) (hz : (M : ℝ) ≤ z.re)
    (hdist : ‖z - (M : ℂ)‖ ≤ (M : ℝ) / 100)
    {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    ‖gammaRatioAnchorPathD1 M z t‖ ≤ 3 / (40 * (M : ℝ)) := by
  have hMpos : (0 : ℝ) < M := by exact_mod_cast Nat.pos_of_ne_zero hM
  calc
    ‖gammaRatioAnchorPathD1 M z t‖ ≤
        gammaRatioAnchorRate M z * ‖gammaRatioAnchorPath M z t‖ :=
      norm_gammaRatioAnchorPathD1_le hM hz ht
    _ ≤ (3 / (100 * (M : ℝ))) * (5 / 2) := by
      gcongr
      · exact gammaRatioAnchorRate_le hM hdist
      · exact norm_gammaRatioAnchorPath_le_five_halves hM hz hdist ht
    _ = 3 / (40 * (M : ℝ)) := by field_simp; ring

theorem gammaRatioAnchorPath_one_sub_zero_le
    {M : ℕ} {z : ℂ} (hM : M ≠ 0) (hz : (M : ℝ) ≤ z.re)
    (hdist : ‖z - (M : ℂ)‖ ≤ (M : ℝ) / 100) :
    ‖gammaRatioAnchorPath M z 1 - gammaRatioAnchorPath M z 0‖ ≤
      3 / (40 * (M : ℝ)) := by
  have hderiv : ∀ t ∈ Set.Icc (0 : ℝ) 1,
      HasDerivAt (gammaRatioAnchorPath M z) (gammaRatioAnchorPathD1 M z t) t := by
    intro t ht
    exact hasDerivAt_gammaRatioAnchorPath hM hz ht
  have hbound : ∀ t ∈ Set.Icc (0 : ℝ) 1,
      ‖gammaRatioAnchorPathD1 M z t‖ ≤ 3 / (40 * (M : ℝ)) := by
    intro t ht
    exact norm_gammaRatioAnchorPathD1_le_three_fortieth hM hz hdist ht
  have h := norm_sub_le_mul_of_hasDerivAt_le (a := 0) (b := 1)
    (C := 3 / (40 * (M : ℝ))) (by norm_num) hderiv hbound
  simpa using h

/-- Effective complex-sector transport from a nearby positive integer. -/
theorem norm_complexFactorialRatioCorrection_sub_one_le_of_anchor
    {M : ℕ} {z : ℂ} (hM : M ≠ 0) (hz : (M : ℝ) ≤ z.re)
    (hdist : ‖z - (M : ℂ)‖ ≤ (M : ℝ) / 100) :
    ‖complexFactorialRatioCorrection z - 1‖ ≤ 1 / (2 * (M : ℝ)) := by
  have hMpos : (0 : ℝ) < M := by exact_mod_cast Nat.pos_of_ne_zero hM
  have hp0 : gammaRatioAnchorPoint M z 0 = (M : ℂ) := by
    simp [gammaRatioAnchorPoint]
  have hp1 : gammaRatioAnchorPoint M z 1 = z := by
    simp [gammaRatioAnchorPoint]
  have hmove := gammaRatioAnchorPath_one_sub_zero_le hM hz hdist
  have hanchor := gammaRatioAnchorPath_zero_sub_one_le (z := z) hM
  rw [gammaRatioAnchorPath, hp1, gammaRatioAnchorPath, hp0] at hmove
  calc
    ‖complexFactorialRatioCorrection z - 1‖ =
        ‖(complexFactorialRatioCorrection z -
          complexFactorialRatioCorrection (M : ℂ)) +
          (complexFactorialRatioCorrection (M : ℂ) - 1)‖ := by ring_nf
    _ ≤ ‖complexFactorialRatioCorrection z -
          complexFactorialRatioCorrection (M : ℂ)‖ +
        ‖complexFactorialRatioCorrection (M : ℂ) - 1‖ := norm_add_le _ _
    _ ≤ 3 / (40 * (M : ℝ)) + 1 / (4 * (M : ℝ)) :=
      add_le_add hmove (by simpa [gammaRatioAnchorPath, hp0] using hanchor)
    _ ≤ 1 / (2 * (M : ℝ)) := by
      field_simp
      nlinarith

/-- Complex Gamma quotient equals the traditional elementary main times an
explicit `1 + error`, under the nearby-integer anchor conditions. -/
theorem complexFactorialRatio_relative_error_of_anchor
    {M : ℕ} {z : ℂ} (hM : M ≠ 0) (hz : (M : ℝ) ≤ z.re)
    (hdist : ‖z - (M : ℂ)‖ ≤ (M : ℝ) / 100) :
    ∃ error : ℂ,
      complexFactorialRatio z = complexFactorialRatioMain z * (1 + error) ∧
      ‖error‖ ≤ 1 / (2 * (M : ℝ)) := by
  refine ⟨complexFactorialRatioCorrection z - 1, ?_,
    norm_complexFactorialRatioCorrection_sub_one_le_of_anchor hM hz hdist⟩
  have hmain := complexFactorialRatioMain_ne_zero z
  rw [show 1 + (complexFactorialRatioCorrection z - 1) =
    complexFactorialRatioCorrection z by ring]
  unfold complexFactorialRatioCorrection
  field_simp

/-- The floor of the real part supplies a valid integer anchor throughout the
fixed coefficient sector. -/
theorem leanCoefficientSector_floor_anchor
    {z : ℂ} (hz : z ∈ leanCoefficientSector) :
    ∃ M : ℕ, M ≠ 0 ∧ (M : ℝ) ≤ z.re ∧
      ‖z - (M : ℂ)‖ ≤ (M : ℝ) / 100 ∧
      ‖z‖ ≤ 2 * (M : ℝ) := by
  have hsaddle : z ∈ leanSaddleSector :=
    leanTwoShiftAdmissible_base (leanCoefficientSector_admissible hz)
  have hcomponents := leanSaddleSector_parameter_component_bounds hsaddle
  have hhuge := leanSaddleSector_parameterNorm_ge_fiveHundredBillion hsaddle
  have hnormpos : 0 < ‖z‖ := by linarith
  have hzim : |z.im| < ‖z‖ / 200 := by
    rw [← Complex.norm_mul_sin_arg, abs_mul, abs_of_pos hnormpos]
    calc
      ‖z‖ * |Real.sin z.arg| ≤ ‖z‖ * |z.arg| :=
        mul_le_mul_of_nonneg_left Real.abs_sin_le_abs hnormpos.le
      _ < ‖z‖ * (1 / 200) := mul_lt_mul_of_pos_left hz.2 hnormpos
      _ = ‖z‖ / 200 := by ring
  have hzre0 : 0 ≤ z.re := by
    have hnorm0 := norm_nonneg z
    nlinarith
  let M : ℕ := ⌊z.re⌋₊
  have hMle : (M : ℝ) ≤ z.re := Nat.floor_le hzre0
  have hzlt : z.re < (M : ℝ) + 1 := by
    simpa only [M] using Nat.lt_floor_add_one z.re
  have hMposR : (0 : ℝ) < M := by
    nlinarith
  have hMne : M ≠ 0 := by exact_mod_cast hMposR.ne'
  have hreDiff0 : 0 ≤ z.re - (M : ℝ) := sub_nonneg.mpr hMle
  have hreDiff1 : z.re - (M : ℝ) ≤ 1 := by linarith
  have hdist0 : ‖z - (M : ℂ)‖ ≤
      |z.re - (M : ℝ)| + |z.im| := by
    have h := Complex.norm_le_abs_re_add_abs_im (z - (M : ℂ))
    simpa using h
  have hdist1 : ‖z - (M : ℂ)‖ ≤ 1 + ‖z‖ / 200 := by
    calc
      ‖z - (M : ℂ)‖ ≤ |z.re - (M : ℝ)| + |z.im| := hdist0
      _ ≤ 1 + ‖z‖ / 200 := by
        rw [abs_of_nonneg hreDiff0]
        exact add_le_add hreDiff1 hzim.le
  have hdist : ‖z - (M : ℂ)‖ ≤ (M : ℝ) / 100 := by
    refine hdist1.trans ?_
    nlinarith
  have hnormM : ‖z‖ ≤ 2 * (M : ℝ) := by
    nlinarith
  exact ⟨M, hMne, hMle, hdist, hnormM⟩

/-- Fixed-sector complex Stirling theorem for the Gamma quotient appearing in
Theorem 7.1.  The error is explicit and holomorphic-source based. -/
theorem complexFactorialRatio_relative_error_fixedSector
    {z : ℂ} (hz : z ∈ leanCoefficientSector) :
    ∃ error : ℂ,
      complexFactorialRatio z = complexFactorialRatioMain z * (1 + error) ∧
      ‖error‖ ≤ 1 / ‖z‖ := by
  obtain ⟨M, hM, hMle, hdist, hnormM⟩ := leanCoefficientSector_floor_anchor hz
  obtain ⟨error, heq, herr⟩ :=
    complexFactorialRatio_relative_error_of_anchor hM hMle hdist
  have hMpos : (0 : ℝ) < M := by exact_mod_cast Nat.pos_of_ne_zero hM
  have hznorm : 0 < ‖z‖ := by
    exact lt_of_lt_of_le (by positivity : (0 : ℝ) < M) (hMle.trans (Complex.re_le_norm z))
  refine ⟨error, heq, herr.trans ?_⟩
  apply one_div_le_one_div_of_le hznorm
  exact hnormM

end

end Zeta23.Research.JensenWedge
