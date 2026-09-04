import Zeta23.Research.JensenWedge.XiNaturalSixCoefficientMatch
import Zeta23.Research.JensenWedge.FiniteFreeAdapters

/-!
# Exact finite-free specialization of the xi comparison polynomial

The paper's terminating `_3F_2` comparison is the ascending multiplicative
finite-free convolution of two scaled Jacobi factors.  This module defines
those factors by their finite coefficient products and proves the identity
coefficient by coefficient.  No Jacobi-root, MSS, or MMP theorem is asserted
here; those general literature results remain explicit typed inputs.
-/

namespace Zeta23.Research.JensenWedge

open Finset Polynomial

noncomputable section

/-- Positive-product part of the scaled terminating Jacobi factor
`_2F_1(-d,U;V;(scale/U) X)`. -/
def jacobiFactorMagnitude (U V scale : ℝ) : ℕ → ℝ
  | 0 => 1
  | k + 1 => jacobiFactorMagnitude U V scale k *
      ((U + k) * scale) / (U * (V + k))

/-- Coefficient of the degree-`d`, constant-term-one Jacobi factor. -/
def jacobiFactorCoefficient
    (d : ℕ) (U V scale : ℝ) (k : ℕ) : ℝ :=
  (-1 : ℝ) ^ k * (Nat.choose d k : ℝ) *
    jacobiFactorMagnitude U V scale k

/-- Finite scaled Jacobi factor in the ascending convention. -/
def jacobiFactorPolynomial
    (d : ℕ) (U V scale : ℝ) : ℝ[X] :=
  ∑ k ∈ range (d + 1),
    Polynomial.monomial k (jacobiFactorCoefficient d U V scale k)

theorem jacobiFactorMagnitude_zero (U V scale : ℝ) :
    jacobiFactorMagnitude U V scale 0 = 1 := by
  rfl

theorem jacobiFactorMagnitude_succ (U V scale : ℝ) (k : ℕ) :
    jacobiFactorMagnitude U V scale (k + 1) =
      jacobiFactorMagnitude U V scale k *
        ((U + k) * scale) / (U * (V + k)) := by
  rfl

theorem coeff_jacobiFactorPolynomial
    (d k : ℕ) (U V scale : ℝ) :
    (jacobiFactorPolynomial d U V scale).coeff k =
      if k ≤ d then jacobiFactorCoefficient d U V scale k else 0 := by
  simp [jacobiFactorPolynomial, Polynomial.coeff_monomial]

theorem jacobiFactorPolynomial_coeff_zero
    (d : ℕ) (U V scale : ℝ) :
    (jacobiFactorPolynomial d U V scale).coeff 0 = 1 := by
  simp [coeff_jacobiFactorPolynomial, jacobiFactorCoefficient,
    jacobiFactorMagnitude]

theorem jacobiFactorMagnitude_scale
    (U V scale : ℝ) (k : ℕ) :
    jacobiFactorMagnitude U V scale k =
      scale ^ k * jacobiFactorMagnitude U V 1 k := by
  induction k with
  | zero => simp [jacobiFactorMagnitude]
  | succ k ih =>
      rw [jacobiFactorMagnitude_succ, jacobiFactorMagnitude_succ, ih,
        pow_succ]
      ring

/-- Scaling the argument of the unscaled Jacobi factor is exactly the
coefficient-scale parameter used above. -/
theorem eval_jacobiFactorPolynomial_scale
    (d : ℕ) (U V scale x : ℝ) :
    Polynomial.eval x (jacobiFactorPolynomial d U V scale) =
      Polynomial.eval (scale * x) (jacobiFactorPolynomial d U V 1) := by
  unfold jacobiFactorPolynomial
  simp only [Polynomial.eval_finsetSum, Polynomial.eval_monomial]
  apply Finset.sum_congr rfl
  intro k hk
  unfold jacobiFactorCoefficient
  rw [jacobiFactorMagnitude_scale]
  ring

/-- The coefficient definition satisfies the expected terminating `_2F_1`
recursion. -/
theorem jacobiFactorCoefficient_succ
    {d k : ℕ} (hk : k < d) {U V scale : ℝ}
    (hU : U ≠ 0) (hVk : V + k ≠ 0) :
    jacobiFactorCoefficient d U V scale (k + 1) =
      jacobiFactorCoefficient d U V scale k *
        (((k : ℝ) - d) * (U + k) * scale) /
          (U * (V + k) * (k + 1)) := by
  have hstep := alternatingChoose_step hk
  unfold jacobiFactorCoefficient
  rw [jacobiFactorMagnitude_succ]
  field_simp [hU, hVk]
  field_simp [hU, hVk] at hstep
  linear_combination
    -(jacobiFactorMagnitude U V scale k * (U + k) * scale) * hstep

/-- Coefficients of the ascending convolution of the two paper-specific
Jacobi factors, before identification with `_3F_2`. -/
theorem coeff_finiteFree_jacobiFactors
    {d k : ℕ} (hk : k ≤ d)
    (A B C D : ℝ) :
    (finiteFreeAscending d
        (jacobiFactorPolynomial d A B 1)
        (jacobiFactorPolynomial d C D D)).coeff k =
      (-1 : ℝ) ^ k * (Nat.choose d k : ℝ) *
        jacobiFactorMagnitude A B 1 k *
        jacobiFactorMagnitude C D D k := by
  have hchooseNat : Nat.choose d k ≠ 0 := Nat.choose_ne_zero hk
  have hchoose : (Nat.choose d k : ℝ) ≠ 0 := by exact_mod_cast hchooseNat
  rw [coeff_finiteFreeAscending, if_pos hk,
    coeff_jacobiFactorPolynomial, if_pos hk,
    coeff_jacobiFactorPolynomial, if_pos hk]
  unfold jacobiFactorCoefficient
  have hsign : (-1 : ℝ) ^ k * (-1 : ℝ) ^ k = 1 := by
    rw [← pow_add]
    nth_rewrite 1 [show k + k = 2 * k by omega]
    rw [pow_mul]
    norm_num
  have hsignsq : ((-1 : ℝ) ^ k) ^ 2 = 1 := by
    rw [pow_two, hsign]
  field_simp [hchoose]
  rw [hsignsq]
  ring

/-- The terminating `_3F_2` coefficient is the common binomial factor times
the two positive Jacobi products. -/
theorem terminating3F2Coefficient_eq_jacobiMagnitudes
    {d k : ℕ} (hk : k ≤ d)
    {A B C D : ℝ} (hA : 0 < A) (hB : 0 < B)
    (hC : 0 < C) (hD : 0 < D) :
    terminating3F2Coefficient d A B C D (D / (A * C)) k =
      (-1 : ℝ) ^ k * (Nat.choose d k : ℝ) *
        jacobiFactorMagnitude A B 1 k *
        jacobiFactorMagnitude C D D k := by
  induction k with
  | zero =>
      simp [terminating3F2Coefficient_zero, jacobiFactorMagnitude]
  | succ k ih =>
      have hkd : k < d := by omega
      have hAk : 0 < A + (k : ℝ) := by positivity
      have hBk : 0 < B + (k : ℝ) := by positivity
      have hCk : 0 < C + (k : ℝ) := by positivity
      have hDk : 0 < D + (k : ℝ) := by positivity
      have hstep := alternatingChoose_step hkd
      rw [terminating3F2Coefficient_succ, ih (by omega),
        jacobiFactorMagnitude_succ, jacobiFactorMagnitude_succ]
      field_simp [hA.ne', hB.ne', hC.ne', hD.ne', hAk.ne', hBk.ne',
        hCk.ne', hDk.ne']
      field_simp at hstep
      rw [pow_succ] at hstep
      linear_combination
        (jacobiFactorMagnitude A B 1 k *
          jacobiFactorMagnitude C D D k) * hstep

/-- Exact paper identity
`p_F = q_(A,B) box_d q_(C,D)(D·)` in the ascending normalization. -/
theorem terminating3F2Polynomial_eq_finiteFree_jacobiFactors
    {d : ℕ} {A B C D : ℝ}
    (hA : 0 < A) (hB : 0 < B) (hC : 0 < C) (hD : 0 < D) :
    terminating3F2Polynomial d A B C D (D / (A * C)) =
      finiteFreeAscending d
        (jacobiFactorPolynomial d A B 1)
        (jacobiFactorPolynomial d C D D) := by
  ext k
  by_cases hk : k ≤ d
  · rw [coeff_terminating3F2Polynomial, if_pos hk,
      coeff_finiteFree_jacobiFactors hk]
    exact terminating3F2Coefficient_eq_jacobiMagnitudes hk hA hB hC hD
  · rw [coeff_terminating3F2Polynomial, if_neg hk,
      coeff_finiteFreeAscending, if_neg hk]

/-- The concrete xi comparison polynomial inherits the exact finite-free
factorization at every certified branch point. -/
theorem xiNaturalComparisonPolynomial_eq_finiteFree
    {n : ℕ} (hn : 0 < n) {L : ℝ} (hL : 0 < L)
    (hL12 : 1 / L ≤ (1 : ℝ) / 12)
    {y : BranchPoint} (hy : InOuterParameterBox y) (d : ℕ) :
    xiNaturalComparisonPolynomial n d L y =
      finiteFreeAscending d
        (jacobiFactorPolynomial d (residualParameterA y n (1 / L))
          (residualParameterB y n (1 / L)) 1)
        (jacobiFactorPolynomial d (residualParameterC y n)
          (residualParameterD y n (1 / L))
          (residualParameterD y n (1 / L))) := by
  rcases xiNaturalResidualParameters_pos hn hL hL12 hy with
    ⟨hA, hB, hC, hD⟩
  unfold xiNaturalComparisonPolynomial
  exact terminating3F2Polynomial_eq_finiteFree_jacobiFactors hA hB hC hD

/-- Explicit-cutoff specialization of the exact finite-free identity. -/
theorem xiNaturalComparisonPolynomial_eq_finiteFree_of_explicitCutoff
    {n : ℕ} (hn : xiNaturalExplicitCutoffIndex ≤ n) (d : ℕ) :
    xiNaturalComparisonPolynomial n d (xiNaturalSaddleScale n)
        (exactXiPositiveParameterBranch_of_explicitCutoff hn).parameters =
      finiteFreeAscending d
        (jacobiFactorPolynomial d
          (residualParameterA
            (exactXiPositiveParameterBranch_of_explicitCutoff hn).parameters n
            (1 / xiNaturalSaddleScale n))
          (residualParameterB
            (exactXiPositiveParameterBranch_of_explicitCutoff hn).parameters n
            (1 / xiNaturalSaddleScale n)) 1)
        (jacobiFactorPolynomial d
          (residualParameterC
            (exactXiPositiveParameterBranch_of_explicitCutoff hn).parameters n)
          (residualParameterD
            (exactXiPositiveParameterBranch_of_explicitCutoff hn).parameters n
            (1 / xiNaturalSaddleScale n))
          (residualParameterD
            (exactXiPositiveParameterBranch_of_explicitCutoff hn).parameters n
            (1 / xiNaturalSaddleScale n))) := by
  let B := exactXiPositiveParameterBranch_of_explicitCutoff hn
  let C := xiNaturalSaddleIntervalConditions_of_explicitCutoff hn
  exact xiNaturalComparisonPolynomial_eq_finiteFree C.n_pos C.saddleScale_pos
    (explicitCutoff_inverse_xiNaturalSaddleScale_le_twelve hn) B.in_outer_box d

/-! ## Narrow classical-input specialization -/

/-- Typed form of the consumed MSS interval theorem, now tied to the exact
finite-free operation and to the roots of both input factors.  Supplying this
record remains an external classical-mathematics obligation. -/
structure MSSFiniteFreeIntervalInput
    (p q : ℝ[X]) (d : ℕ) : Prop where
  first_factor : HasDistinctPositiveRoots p.eval d
  first_degree : p.natDegree ≤ d
  second_factor : HasDistinctPositiveRoots q.eval d
  second_degree : q.natDegree ≤ d
  product_interval :
    ∀ {uLower uUpper vLower vUpper : ℝ},
      0 < uLower →
      0 < vLower →
      (∀ x, p.eval x = 0 → uLower ≤ x ∧ x ≤ uUpper) →
      (∀ x, q.eval x = 0 → vLower ≤ x ∧ x ≤ vUpper) →
      ∀ z, (finiteFreeAscending d p q).eval z = 0 →
        uLower * vLower ≤ z ∧ z ≤ uUpper * vUpper

/-- Exact external boundary for the paper-specific comparison.  General
Jacobi root/matrix correspondence, MSS, and MMP are the only fields; all
normalization and specialization work is performed in Lean.  Crucially, the
MMP field is stated for the two concrete Jacobi factors.  It does not assume
that the paper's `_3F_2` comparison already has the desired roots. -/
structure XiNaturalClassicalRootInputs
    (n d : ℕ) (L : ℝ) (y : BranchPoint) where
  first_jacobi : RatioFreeJacobiInput
    (jacobiFactorPolynomial d
      (residualParameterA y n (1 / L))
      (residualParameterB y n (1 / L)) 1)
    d (residualParameterA y n (1 / L))
      (residualParameterB y n (1 / L))
  second_jacobi : RatioFreeJacobiInput
    (jacobiFactorPolynomial d
      (residualParameterC y n)
      (residualParameterD y n (1 / L)) 1)
    d (residualParameterC y n)
      (residualParameterD y n (1 / L))
  mss : MSSFiniteFreeIntervalInput
    (jacobiFactorPolynomial d
      (residualParameterA y n (1 / L))
      (residualParameterB y n (1 / L)) 1)
    (jacobiFactorPolynomial d
      (residualParameterC y n)
      (residualParameterD y n (1 / L))
      (residualParameterD y n (1 / L))) d
  mmp : MMPFiniteFreeLogMeshInput
    (jacobiFactorPolynomial d
      (residualParameterA y n (1 / L))
      (residualParameterB y n (1 / L)) 1)
    (jacobiFactorPolynomial d
      (residualParameterC y n)
      (residualParameterD y n (1 / L))
      (residualParameterD y n (1 / L))) d

theorem sqrt_mul_div_self_eq_sqrt_div
    {D : ℝ} (hD : 0 < D) (d : ℕ) :
    Real.sqrt (D * d) / D = Real.sqrt ((d : ℝ) / D) := by
  have hDd : 0 ≤ D * (d : ℝ) := mul_nonneg hD.le (Nat.cast_nonneg d)
  have hdD : 0 ≤ (d : ℝ) / D := div_nonneg (Nat.cast_nonneg d) hD.le
  have hleft : 0 ≤ Real.sqrt (D * d) / D := div_nonneg (Real.sqrt_nonneg _) hD.le
  have hright : 0 ≤ Real.sqrt ((d : ℝ) / D) := Real.sqrt_nonneg _
  have hsquare : (Real.sqrt (D * d) / D) ^ 2 =
      Real.sqrt ((d : ℝ) / D) ^ 2 := by
    rw [div_pow, Real.sq_sqrt hDd, Real.sq_sqrt hdD]
    field_simp [hD.ne']
  nlinarith

theorem XiNaturalClassicalRootInputs.first_factor_interval
    {n d : ℕ} {L : ℝ} {y : BranchPoint}
    (I : XiNaturalClassicalRootInputs n d L y)
    {x : ℝ}
    (hx : (jacobiFactorPolynomial d
      (residualParameterA y n (1 / L))
      (residualParameterB y n (1 / L)) 1).eval x = 0) :
    residualParameterB y n (1 / L) -
        8 * Real.sqrt (residualParameterB y n (1 / L) * d) ≤ x ∧
      x ≤ residualParameterB y n (1 / L) +
        8 * Real.sqrt (residualParameterB y n (1 / L) * d) :=
  I.first_jacobi.root_interval hx

theorem XiNaturalClassicalRootInputs.second_scaled_factor_interval
    {n d : ℕ} {L : ℝ} {y : BranchPoint}
    (I : XiNaturalClassicalRootInputs n d L y)
    (hD : 0 < residualParameterD y n (1 / L))
    {x : ℝ}
    (hx : (jacobiFactorPolynomial d
      (residualParameterC y n)
      (residualParameterD y n (1 / L))
      (residualParameterD y n (1 / L))).eval x = 0) :
    1 - 8 * Real.sqrt ((d : ℝ) / residualParameterD y n (1 / L)) ≤ x ∧
      x ≤ 1 + 8 * Real.sqrt ((d : ℝ) /
        residualParameterD y n (1 / L)) := by
  have hxUnscaled :
      (jacobiFactorPolynomial d
        (residualParameterC y n)
        (residualParameterD y n (1 / L)) 1).eval
          (residualParameterD y n (1 / L) * x) = 0 := by
    rw [← eval_jacobiFactorPolynomial_scale]
    exact hx
  have hraw := I.second_jacobi.root_interval hxUnscaled
  have hsqrt := sqrt_mul_div_self_eq_sqrt_div hD d
  constructor
  · calc
      1 - 8 * Real.sqrt ((d : ℝ) / residualParameterD y n (1 / L)) =
          (residualParameterD y n (1 / L) -
            8 * Real.sqrt (residualParameterD y n (1 / L) * d)) /
              residualParameterD y n (1 / L) := by
                rw [← hsqrt]
                field_simp [hD.ne']
      _ ≤ (residualParameterD y n (1 / L) * x) /
            residualParameterD y n (1 / L) :=
          div_le_div_of_nonneg_right hraw.1 hD.le
      _ = x := by field_simp [hD.ne']
  · calc
      x = (residualParameterD y n (1 / L) * x) /
          residualParameterD y n (1 / L) := by field_simp [hD.ne']
      _ ≤ (residualParameterD y n (1 / L) +
            8 * Real.sqrt (residualParameterD y n (1 / L) * d)) /
              residualParameterD y n (1 / L) :=
          div_le_div_of_nonneg_right hraw.2 hD.le
      _ = 1 + 8 * Real.sqrt ((d : ℝ) /
          residualParameterD y n (1 / L)) := by
            rw [← hsqrt]
            field_simp [hD.ne']

/-- MMP supplies simple positive roots of the concrete Jacobi convolution;
Lean's coefficientwise `_3F_2` identity transports them to the published
comparison polynomial. -/
theorem XiNaturalClassicalRootInputs.comparison_hasDistinctPositiveRoots
    {n d : ℕ} {L : ℝ} {y : BranchPoint}
    (I : XiNaturalClassicalRootInputs n d L y)
    (hn : 0 < n) (hL : 0 < L)
    (hL12 : 1 / L ≤ (1 : ℝ) / 12)
    (hy : InOuterParameterBox y) :
    HasDistinctPositiveRoots (xiNaturalComparisonFunction n d L y) d :=
  by
    change HasDistinctPositiveRoots
      (xiNaturalComparisonPolynomial n d L y).eval d
    rw [xiNaturalComparisonPolynomial_eq_finiteFree hn hL hL12 hy d]
    exact I.mmp.hasDistinctPositiveRoots

/-- Exact coarse geometry consumed by the product-localization calculation.
The later wedge/cutoff layer is responsible for constructing these three
inequalities. -/
structure XiNaturalFiniteFreeGeometry
    (n d : ℕ) (L : ℝ) (y : BranchPoint) : Prop where
  B_ge_256d : 256 * (d : ℝ) ≤ residualParameterB y n (1 / L)
  D_ge_256d : 256 * (d : ℝ) ≤ residualParameterD y n (1 / L)
  B_le_six_D : residualParameterB y n (1 / L) ≤
    6 * residualParameterD y n (1 / L)

theorem XiNaturalClassicalRootInputs.comparison_root_product_interval
    {n d : ℕ} {L : ℝ} {y : BranchPoint}
    (I : XiNaturalClassicalRootInputs n d L y)
    (hn : 0 < n) (hL : 0 < L)
    (hL12 : 1 / L ≤ (1 : ℝ) / 12)
    (hy : InOuterParameterBox y)
    (G : XiNaturalFiniteFreeGeometry n d L y) (i : Fin d) :
    let B := residualParameterB y n (1 / L)
    let D := residualParameterD y n (1 / L)
    (B - 8 * Real.sqrt (B * d)) *
          (1 - 8 * Real.sqrt ((d : ℝ) / D)) ≤ I.mmp.roots i ∧
      I.mmp.roots i ≤
        (B + 8 * Real.sqrt (B * d)) *
          (1 + 8 * Real.sqrt ((d : ℝ) / D)) := by
  rcases xiNaturalResidualParameters_pos hn hL hL12 hy with
    ⟨_, hB, _, hD⟩
  have hBLower :
      0 < residualParameterB y n (1 / L) -
        8 * Real.sqrt (residualParameterB y n (1 / L) * d) := by
    have hBd : 0 ≤ residualParameterB y n (1 / L) * (d : ℝ) :=
      mul_nonneg hB.le (Nat.cast_nonneg d)
    have hmul := mul_le_mul_of_nonneg_left G.B_ge_256d hB.le
    have hsqrt_sq := Real.sq_sqrt hBd
    have hsqrt_nonneg := Real.sqrt_nonneg
      (residualParameterB y n (1 / L) * (d : ℝ))
    nlinarith
  have hDLower :
      0 < 1 - 8 * Real.sqrt
        ((d : ℝ) / residualParameterD y n (1 / L)) := by
    have hratio :
        (d : ℝ) / residualParameterD y n (1 / L) ≤ (1 : ℝ) / 256 := by
      apply (div_le_iff₀ hD).2
      nlinarith [G.D_ge_256d]
    have hratio_nonneg :
        0 ≤ (d : ℝ) / residualParameterD y n (1 / L) :=
      div_nonneg (Nat.cast_nonneg d) hD.le
    have hsqrt_sq := Real.sq_sqrt hratio_nonneg
    have hsqrt_nonneg := Real.sqrt_nonneg
      ((d : ℝ) / residualParameterD y n (1 / L))
    nlinarith
  apply I.mss.product_interval
  · exact hBLower
  · exact hDLower
  · intro x hx
    exact I.first_factor_interval hx
  · intro x hx
    exact I.second_scaled_factor_interval hD hx
  · exact I.mmp.roots_are_zeros i

theorem sqrt_mul_sqrt_div_eq_mul_sqrt_div
    {B D : ℝ} (hB : 0 < B) (hD : 0 < D) (d : ℕ) :
    Real.sqrt (B * d) * Real.sqrt (B / D) =
      B * Real.sqrt ((d : ℝ) / D) := by
  have hBd : 0 ≤ B * (d : ℝ) := mul_nonneg hB.le (Nat.cast_nonneg d)
  have hBD : 0 ≤ B / D := div_nonneg hB.le hD.le
  have hdD : 0 ≤ (d : ℝ) / D := div_nonneg (Nat.cast_nonneg d) hD.le
  have hleft : 0 ≤ Real.sqrt (B * d) * Real.sqrt (B / D) := by positivity
  have hright : 0 ≤ B * Real.sqrt ((d : ℝ) / D) := by positivity
  have hsquare :
      (Real.sqrt (B * d) * Real.sqrt (B / D)) ^ 2 =
        (B * Real.sqrt ((d : ℝ) / D)) ^ 2 := by
    rw [mul_pow, mul_pow, Real.sq_sqrt hBd, Real.sq_sqrt hBD,
      Real.sq_sqrt hdD]
    field_simp [hD.ne']
  nlinarith

/-- The paper's corrected root localization constant, derived after the
provisional `256d` bounds rather than assumed in a final certificate. -/
theorem XiNaturalClassicalRootInputs.comparison_root_localization
    {n d : ℕ} {L : ℝ} {y : BranchPoint}
    (I : XiNaturalClassicalRootInputs n d L y)
    (hn : 0 < n) (hL : 0 < L)
    (hL12 : 1 / L ≤ (1 : ℝ) / 12)
    (hy : InOuterParameterBox y)
    (G : XiNaturalFiniteFreeGeometry n d L y) (i : Fin d) :
    let B := residualParameterB y n (1 / L)
    |I.mmp.roots i - B| ≤ localizationConstant * Real.sqrt (B * d) := by
  let B := residualParameterB y n (1 / L)
  let D := residualParameterD y n (1 / L)
  let r := Real.sqrt (B * (d : ℝ))
  let s := Real.sqrt ((d : ℝ) / D)
  let q := Real.sqrt (B / D)
  rcases xiNaturalResidualParameters_pos hn hL hL12 hy with
    ⟨_, hB, _, hD⟩
  have hr : 0 ≤ r := Real.sqrt_nonneg _
  have hs : 0 ≤ s := Real.sqrt_nonneg _
  have hBnonneg : 0 ≤ B := hB.le
  have hDnonneg : 0 ≤ D := hD.le
  have hBs : B * s = r * q := by
    dsimp only [B, D, r, s, q]
    exact (sqrt_mul_sqrt_div_eq_mul_sqrt_div hB hD d).symm
  have hratio : B / D ≤ 6 := by
    rw [div_le_iff₀ hD]
    exact G.B_le_six_D
  have hq : q ≤ Real.sqrt 6 := by
    exact Real.sqrt_le_sqrt hratio
  have hdD : (d : ℝ) / D ≤ 1 / 256 := by
    rw [div_le_iff₀ hD]
    nlinarith [G.D_ge_256d]
  have hsSq : s ^ 2 = (d : ℝ) / D := by
    exact Real.sq_sqrt (div_nonneg (Nat.cast_nonneg d) hD.le)
  have hs16 : s ≤ 1 / 16 := by
    nlinarith
  have hplus := productDeviation_le_localizationConstant
    hBnonneg hr hs
    (u := 8 * r) (v := 8 * s) (q := q)
    (by simp [abs_of_nonneg hr]) (by simp [abs_of_nonneg hs])
    hBs hq hs16
  have hminus := productDeviation_le_localizationConstant
    hBnonneg hr hs
    (u := -(8 * r)) (v := -(8 * s)) (q := q)
    (by simp [abs_of_nonneg hr]) (by simp [abs_of_nonneg hs])
    hBs hq hs16
  have hproduct := I.comparison_root_product_interval hn hL hL12 hy G i
  dsimp only at hproduct
  change
    (B - 8 * r) * (1 - 8 * s) ≤ I.mmp.roots i ∧
      I.mmp.roots i ≤ (B + 8 * r) * (1 + 8 * s) at hproduct
  have hlower : B - localizationConstant * r ≤
      (B - 8 * r) * (1 - 8 * s) := by
    rw [abs_le] at hminus
    nlinarith
  have hupper : (B + 8 * r) * (1 + 8 * s) ≤
      B + localizationConstant * r := by
    rw [abs_le] at hplus
    nlinarith
  rw [abs_le]
  constructor <;> nlinarith

theorem xiNaturalFiniteFreeGeometry_of_n_ge_256d
    {n d : ℕ} (hn : 0 < n) {L : ℝ} (hL : 0 < L)
    (hL12 : 1 / L ≤ (1 : ℝ) / 12)
    {y : BranchPoint} (hy : InOuterParameterBox y)
    (hnd : 256 * d ≤ n) :
    XiNaturalFiniteFreeGeometry n d L y := by
  rcases hy with ⟨_, _, ht0, ht1, hw0, hw1, hd0, _⟩
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hndR : 256 * (d : ℝ) ≤ n := by exact_mod_cast hnd
  have he : 0 < (1 / L : ℝ) := one_div_pos.mpr hL
  have hwy0 : 0 ≤ y 2 := le_trans (by norm_num) hw0
  have hwe0 : 0 ≤ y 2 * (1 / L) := by
    exact mul_nonneg hwy0 he.le
  have hwe1 : y 2 * (1 / L) ≤ 1 / 2 := by
    have hmul := mul_le_mul hw1 hL12 he.le (by norm_num : (0 : ℝ) ≤ 6)
    norm_num at hmul ⊢
    exact hmul
  have hde0 : 0 ≤ y 3 * (1 / L) := by
    exact mul_nonneg (le_trans (by norm_num) hd0) he.le
  refine {
    B_ge_256d := ?_
    D_ge_256d := ?_
    B_le_six_D := ?_
  }
  · unfold residualParameterB
    have : (n : ℝ) ≤ (n : ℝ) * (y 1 + y 2 * (1 / L)) := by
      nlinarith [mul_nonneg hnR.le (sub_nonneg.mpr (by linarith :
        1 ≤ y 1 + y 2 * (1 / L)))]
    linarith
  · unfold residualParameterD
    have : (n : ℝ) ≤ (n : ℝ) * (1 + y 3 * (1 / L)) := by
      nlinarith [mul_nonneg hnR.le hde0]
    linarith
  · unfold residualParameterB residualParameterD
    have hBbase : y 1 + y 2 * (1 / L) ≤ 11 / 4 := by linarith
    have hDbase : 1 ≤ 1 + y 3 * (1 / L) := by linarith
    nlinarith [mul_le_mul_of_nonneg_left hBbase hnR.le,
      mul_le_mul_of_nonneg_left hDbase hnR.le]

/-- A fixed exact lower bound on the eventual headline wedge constant that
forces the provisional `n ≥ 256d` geometry. -/
def xiNaturalFiniteFreeWedgeConstant : ℝ := 2 * 256 ^ 3

theorem twoThirdsWedge_n_ge_256_mul_degree
    {K : ℝ} (hK : xiNaturalFiniteFreeWedgeConstant ≤ K)
    {n d : ℕ} (hn : 0 < n) (hW : TwoThirdsWedge K n d) :
    256 * d ≤ n := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hnOne : (1 : ℝ) ≤ n := by
    exact_mod_cast (Nat.one_le_iff_ne_zero.mpr hn.ne')
  have hlog : Real.log ((n : ℝ) + 2) ≤ 2 * n := by
    have hbase := Real.log_le_sub_one_of_pos
      (show (0 : ℝ) < (n : ℝ) + 2 by positivity)
    nlinarith
  have hd3 : 0 ≤ (d : ℝ) ^ 3 := by positivity
  have hKlower : xiNaturalFiniteFreeWedgeConstant * (d : ℝ) ^ 3 ≤
      K * (d : ℝ) ^ 3 := mul_le_mul_of_nonneg_right hK hd3
  have hcube : ((256 : ℝ) * d) ^ 3 ≤ (n : ℝ) ^ 3 := by
    unfold TwoThirdsWedge at hW
    dsimp [xiNaturalFiniteFreeWedgeConstant] at hKlower
    nlinarith [mul_le_mul_of_nonneg_left hlog (sq_nonneg (n : ℝ))]
  have hlinear : (256 : ℝ) * d ≤ n := by
    exact le_of_pow_le_pow_left₀ (by norm_num : (3 : ℕ) ≠ 0) hnR.le hcube
  exact_mod_cast hlinear

/-- Explicit-cutoff branch specialization of the complete coarse geometry.
-/
theorem xiNaturalFiniteFreeGeometry_of_explicitCutoff
    {K : ℝ} (hK : xiNaturalFiniteFreeWedgeConstant ≤ K)
    {n d : ℕ} (hn : xiNaturalExplicitCutoffIndex ≤ n)
    (hW : TwoThirdsWedge K n d) :
    XiNaturalFiniteFreeGeometry n d (xiNaturalSaddleScale n)
      (exactXiPositiveParameterBranch_of_explicitCutoff hn).parameters := by
  let B := exactXiPositiveParameterBranch_of_explicitCutoff hn
  let C := xiNaturalSaddleIntervalConditions_of_explicitCutoff hn
  exact xiNaturalFiniteFreeGeometry_of_n_ge_256d C.n_pos C.saddleScale_pos
    (explicitCutoff_inverse_xiNaturalSaddleScale_le_twelve hn) B.in_outer_box
    (twoThirdsWedge_n_ge_256_mul_degree hK C.n_pos hW)

/-- Concrete root localization for the actual xi comparison polynomial.
Only the three named classical root inputs remain external; the branch,
cutoff, finite-free identity, parameter inequalities, and localization
constant are all instantiated inside Lean. -/
theorem XiNaturalClassicalRootInputs.comparison_root_localization_of_explicitCutoff
    {K : ℝ} (hK : xiNaturalFiniteFreeWedgeConstant ≤ K)
    {n d : ℕ} (hn : xiNaturalExplicitCutoffIndex ≤ n)
    (hW : TwoThirdsWedge K n d)
    (I : XiNaturalClassicalRootInputs n d (xiNaturalSaddleScale n)
      (exactXiPositiveParameterBranch_of_explicitCutoff hn).parameters)
    (i : Fin d) :
    let B := residualParameterB
      (exactXiPositiveParameterBranch_of_explicitCutoff hn).parameters n
      (1 / xiNaturalSaddleScale n)
    |I.mmp.roots i - B| ≤ localizationConstant * Real.sqrt (B * d) := by
  let B := exactXiPositiveParameterBranch_of_explicitCutoff hn
  let C := xiNaturalSaddleIntervalConditions_of_explicitCutoff hn
  exact I.comparison_root_localization C.n_pos C.saddleScale_pos
    (explicitCutoff_inverse_xiNaturalSaddleScale_le_twelve hn) B.in_outer_box
    (xiNaturalFiniteFreeGeometry_of_explicitCutoff hK hn hW) i

end

end Zeta23.Research.JensenWedge
