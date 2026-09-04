import Zeta23.Research.JensenWedge.XiNaturalLogCertificateDecomposition
import Zeta23.Research.JensenWedge.MovingSaddleLowerOrders

/-!
# Lower forward differences of the explicit natural main

This module is the exact local-FTC adapter for the main part of the
branch-fixed auxiliary logarithm.  It records the four pointwise normalized
derivative estimates on the one real interval actually used by the six
samples, then proves the corresponding order-two through order-five forward
difference estimates with no factorial loss.

The first structure below is the final pointwise conclusion consumed by the
localized FTC theorem.  A second, more primitive structure separates its
proof into the chain-scaled moving-saddle term and the remaining explicit
main correction.  Lean combines those two error budgets without hiding a
sign, power of two, or triangle-inequality loss.  The interval instantiation
of the two primitive budgets is deliberately left to the next stage.
-/

namespace Zeta23.Research.JensenWedge

open Complex Set

noncomputable section

theorem complexXiNaturalAuxiliaryLogMain_analyticOnNhd :
    AnalyticOnNhd ℂ complexXiNaturalAuxiliaryLogMain
      leanXiCoefficientSector :=
  differentiableOn_complexXiNaturalAuxiliaryLogMain.analyticOnNhd
    isOpen_leanXiCoefficientSector

theorem hasDerivAt_iteratedDeriv_complexXiNaturalAuxiliaryLogMain
    (s : ℕ) {z : ℂ} (hz : z ∈ leanXiCoefficientSector) :
    HasDerivAt (iteratedDeriv s complexXiNaturalAuxiliaryLogMain)
      (iteratedDeriv (s + 1) complexXiNaturalAuxiliaryLogMain z) z := by
  have h :=
    (complexXiNaturalAuxiliaryLogMain_analyticOnNhd.iterated_deriv s) z hz
  rw [iteratedDeriv_succ, iteratedDeriv_eq_iterate]
  exact h.differentiableAt.hasDerivAt

theorem complexForwardDiff_const_mul
    (q : ℕ) (a : ℂ) (f : ℂ → ℂ) (z : ℂ) :
    complexForwardDiff q (fun w => a * f w) z =
      a * complexForwardDiff q f z := by
  induction q generalizing z with
  | zero => rfl
  | succ q ih =>
      simp only [complexForwardDiff, ih]
      ring

/-! ## Exact chain-scaled saddle coordinates -/

/-- Order-two saddle contribution after the affine change `N=2M-2`.
The factor is exactly `2^2`. -/
def xiNaturalMainSaddleTwo (M : ℂ) : ℂ :=
  4 * manuscriptSaddleMainTwo (coefficientMellinParameter M)

/-- Order-three saddle contribution after the affine change `N=2M-2`.
The factor is exactly `2^3`. -/
def xiNaturalMainSaddleThree (M : ℂ) : ℂ :=
  8 * manuscriptSaddleMainThree (coefficientMellinParameter M)

/-- Order-four saddle contribution after the affine change `N=2M-2`.
The factor is exactly `2^4`. -/
def xiNaturalMainSaddleFour (M : ℂ) : ℂ :=
  16 * manuscriptSaddleMainFour (coefficientMellinParameter M)

/-- Order-five saddle contribution after the affine change `N=2M-2`.
The factor is exactly `2^5`. -/
def xiNaturalMainSaddleFive (M : ℂ) : ℂ :=
  32 * manuscriptSaddleMainFive (coefficientMellinParameter M)

/-- What remains in the actual order-two derivative of the explicit natural
main after the chain-scaled moving-saddle term is removed. -/
def xiNaturalMainCorrectionTwo (M : ℂ) : ℂ :=
  iteratedDeriv 2 complexXiNaturalAuxiliaryLogMain M -
    xiNaturalMainSaddleTwo M

/-- Order-three version of `xiNaturalMainCorrectionTwo`. -/
def xiNaturalMainCorrectionThree (M : ℂ) : ℂ :=
  iteratedDeriv 3 complexXiNaturalAuxiliaryLogMain M -
    xiNaturalMainSaddleThree M

/-- Order-four version of `xiNaturalMainCorrectionTwo`. -/
def xiNaturalMainCorrectionFour (M : ℂ) : ℂ :=
  iteratedDeriv 4 complexXiNaturalAuxiliaryLogMain M -
    xiNaturalMainSaddleFour M

/-- Order-five version of `xiNaturalMainCorrectionTwo`. -/
def xiNaturalMainCorrectionFive (M : ℂ) : ℂ :=
  iteratedDeriv 5 complexXiNaturalAuxiliaryLogMain M -
    xiNaturalMainSaddleFive M

theorem xiNaturalMain_orderTwo_decomposition (M : ℂ) :
    iteratedDeriv 2 complexXiNaturalAuxiliaryLogMain M =
      xiNaturalMainSaddleTwo M + xiNaturalMainCorrectionTwo M := by
  unfold xiNaturalMainCorrectionTwo
  ring

theorem xiNaturalMain_orderThree_decomposition (M : ℂ) :
    iteratedDeriv 3 complexXiNaturalAuxiliaryLogMain M =
      xiNaturalMainSaddleThree M + xiNaturalMainCorrectionThree M := by
  unfold xiNaturalMainCorrectionThree
  ring

theorem xiNaturalMain_orderFour_decomposition (M : ℂ) :
    iteratedDeriv 4 complexXiNaturalAuxiliaryLogMain M =
      xiNaturalMainSaddleFour M + xiNaturalMainCorrectionFour M := by
  unfold xiNaturalMainCorrectionFour
  ring

theorem xiNaturalMain_orderFive_decomposition (M : ℂ) :
    iteratedDeriv 5 complexXiNaturalAuxiliaryLogMain M =
      xiNaturalMainSaddleFive M + xiNaturalMainCorrectionFive M := by
  unfold xiNaturalMainCorrectionFive
  ring

/-- Pointwise lower-derivative estimates for the explicit natural main on
the complete six-sample interval.  These are the four analytic producers
that the remaining part of Step 3 must construct. -/
structure XiNaturalMainLowerDerivativeBounds
    (n : ℕ) (L epsilon : ℝ) : Prop where
  epsilon_nonneg : 0 ≤ epsilon
  interval_mem_sector : ∀ y : ℝ,
    y ∈ Set.Icc (n : ℝ) ((n : ℝ) + 5) →
      (y : ℂ) ∈ leanXiCoefficientSector
  orderTwo : ∀ y : ℝ,
    y ∈ Set.Icc (n : ℝ) ((n : ℝ) + 5) →
      ‖(-((n : ℝ) * L) : ℂ) *
          iteratedDeriv 2 complexXiNaturalAuxiliaryLogMain (y : ℂ) - (-2)‖ ≤
        epsilon
  orderThree : ∀ y : ℝ,
    y ∈ Set.Icc (n : ℝ) ((n : ℝ) + 5) →
      ‖(((n : ℝ) ^ 2 * L / 2 : ℝ) : ℂ) *
          iteratedDeriv 3 complexXiNaturalAuxiliaryLogMain (y : ℂ) - (-1)‖ ≤
        epsilon
  orderFour : ∀ y : ℝ,
    y ∈ Set.Icc (n : ℝ) ((n : ℝ) + 5) →
      ‖(-((n : ℝ) ^ 3 * L / 2 : ℝ) : ℂ) *
          iteratedDeriv 4 complexXiNaturalAuxiliaryLogMain (y : ℂ) - (-2)‖ ≤
        epsilon
  orderFive : ∀ y : ℝ,
    y ∈ Set.Icc (n : ℝ) ((n : ℝ) + 5) →
      ‖(((n : ℝ) ^ 4 * L / 6 : ℝ) : ℂ) *
          iteratedDeriv 5 complexXiNaturalAuxiliaryLogMain (y : ℂ) - (-2)‖ ≤
        epsilon

/-- Primitive pointwise certificate.  Its `saddle*` fields concern only the
exact rational tower `H2,...,H5`; its `correction*` fields concern everything
else in the displayed natural main.  This separation prevents a successful
bound on one source from masking a sign or scale error in the other. -/
structure XiNaturalMainLowerPointwiseCertificate
    (n : ℕ) (L saddleError correctionError : ℝ) : Prop where
  saddleError_nonneg : 0 ≤ saddleError
  correctionError_nonneg : 0 ≤ correctionError
  interval_mem_sector : ∀ y : ℝ,
    y ∈ Set.Icc (n : ℝ) ((n : ℝ) + 5) →
      (y : ℂ) ∈ leanXiCoefficientSector
  saddleTwo : ∀ y : ℝ,
    y ∈ Set.Icc (n : ℝ) ((n : ℝ) + 5) →
      ‖(-((n : ℝ) * L) : ℂ) * xiNaturalMainSaddleTwo (y : ℂ) - (-2)‖ ≤
        saddleError
  saddleThree : ∀ y : ℝ,
    y ∈ Set.Icc (n : ℝ) ((n : ℝ) + 5) →
      ‖(((n : ℝ) ^ 2 * L / 2 : ℝ) : ℂ) *
          xiNaturalMainSaddleThree (y : ℂ) - (-1)‖ ≤
        saddleError
  saddleFour : ∀ y : ℝ,
    y ∈ Set.Icc (n : ℝ) ((n : ℝ) + 5) →
      ‖(-((n : ℝ) ^ 3 * L / 2 : ℝ) : ℂ) *
          xiNaturalMainSaddleFour (y : ℂ) - (-2)‖ ≤
        saddleError
  saddleFive : ∀ y : ℝ,
    y ∈ Set.Icc (n : ℝ) ((n : ℝ) + 5) →
      ‖(((n : ℝ) ^ 4 * L / 6 : ℝ) : ℂ) *
          xiNaturalMainSaddleFive (y : ℂ) - (-2)‖ ≤
        saddleError
  correctionTwo : ∀ y : ℝ,
    y ∈ Set.Icc (n : ℝ) ((n : ℝ) + 5) →
      ‖(-((n : ℝ) * L) : ℂ) * xiNaturalMainCorrectionTwo (y : ℂ)‖ ≤
        correctionError
  correctionThree : ∀ y : ℝ,
    y ∈ Set.Icc (n : ℝ) ((n : ℝ) + 5) →
      ‖(((n : ℝ) ^ 2 * L / 2 : ℝ) : ℂ) *
          xiNaturalMainCorrectionThree (y : ℂ)‖ ≤
        correctionError
  correctionFour : ∀ y : ℝ,
    y ∈ Set.Icc (n : ℝ) ((n : ℝ) + 5) →
      ‖(-((n : ℝ) ^ 3 * L / 2 : ℝ) : ℂ) *
          xiNaturalMainCorrectionFour (y : ℂ)‖ ≤
        correctionError
  correctionFive : ∀ y : ℝ,
    y ∈ Set.Icc (n : ℝ) ((n : ℝ) + 5) →
      ‖(((n : ℝ) ^ 4 * L / 6 : ℝ) : ℂ) *
          xiNaturalMainCorrectionFive (y : ℂ)‖ ≤
        correctionError

private theorem norm_scaled_sum_sub_le
    (a u v c : ℂ) {eu ev : ℝ}
    (hu : ‖a * u - c‖ ≤ eu) (hv : ‖a * v‖ ≤ ev) :
    ‖a * (u + v) - c‖ ≤ eu + ev := by
  calc
    ‖a * (u + v) - c‖ = ‖(a * u - c) + a * v‖ := by ring
    _ ≤ ‖a * u - c‖ + ‖a * v‖ := norm_add_le _ _
    _ ≤ eu + ev := add_le_add hu hv

/-- The primitive saddle/correction split constructs the final pointwise
derivative bounds with exactly the sum of the two declared budgets. -/
theorem XiNaturalMainLowerPointwiseCertificate.derivativeBounds
    {n : ℕ} {L saddleError correctionError : ℝ}
    (C : XiNaturalMainLowerPointwiseCertificate
      n L saddleError correctionError) :
    XiNaturalMainLowerDerivativeBounds n L
      (saddleError + correctionError) := by
  refine {
    epsilon_nonneg := add_nonneg C.saddleError_nonneg C.correctionError_nonneg
    interval_mem_sector := C.interval_mem_sector
    orderTwo := ?_
    orderThree := ?_
    orderFour := ?_
    orderFive := ?_
  }
  · intro y hy
    rw [xiNaturalMain_orderTwo_decomposition]
    exact norm_scaled_sum_sub_le _ _ _ _ (C.saddleTwo y hy)
      (C.correctionTwo y hy)
  · intro y hy
    rw [xiNaturalMain_orderThree_decomposition]
    exact norm_scaled_sum_sub_le _ _ _ _ (C.saddleThree y hy)
      (C.correctionThree y hy)
  · intro y hy
    rw [xiNaturalMain_orderFour_decomposition]
    exact norm_scaled_sum_sub_le _ _ _ _ (C.saddleFour y hy)
      (C.correctionFour y hy)
  · intro y hy
    rw [xiNaturalMain_orderFive_decomposition]
    exact norm_scaled_sum_sub_le _ _ _ _ (C.saddleFive y hy)
      (C.correctionFive y hy)

private theorem XiNaturalMainLowerDerivativeBounds.scaled_forwardDiff
    {n : ℕ} {L epsilon : ℝ}
    (B : XiNaturalMainLowerDerivativeBounds n L epsilon)
    (q : ℕ) (hq : q ≤ 5) (a c : ℂ)
    (hbound : ∀ y : ℝ,
      y ∈ Set.Icc (n : ℝ) ((n : ℝ) + 5) →
        ‖a * iteratedDeriv q complexXiNaturalAuxiliaryLogMain (y : ℂ) - c‖ ≤
          epsilon) :
    ‖a * complexForwardDiff q complexXiNaturalAuxiliaryLogMain (n : ℂ) - c‖ ≤
      epsilon := by
  let derivs : ℕ → ℂ → ℂ := fun s z =>
    a * iteratedDeriv s complexXiNaturalAuxiliaryLogMain z
  have hinterval : Set.Icc (n : ℝ) ((n : ℝ) + (q : ℝ)) ⊆
      Set.Icc (n : ℝ) ((n : ℝ) + 5) := by
    intro y hy
    constructor
    · exact hy.1
    · have hqR : (q : ℝ) ≤ 5 := by exact_mod_cast hq
      linarith [hy.2]
  have hderiv : ∀ s y,
      y ∈ Set.Icc (n : ℝ) ((n : ℝ) + (q : ℝ)) →
      HasDerivAt (derivs s) (derivs (s + 1) (y : ℂ)) (y : ℂ) := by
    intro s y hy
    simpa only [derivs] using
      (hasDerivAt_iteratedDeriv_complexXiNaturalAuxiliaryLogMain s
        (B.interval_mem_sector y (hinterval hy))).const_mul a
  have hbound' : ∀ y,
      y ∈ Set.Icc (n : ℝ) ((n : ℝ) + (q : ℝ)) →
      ‖derivs (0 + q) (y : ℂ) - c‖ ≤ epsilon := by
    intro y hy
    simpa only [derivs, zero_add] using hbound y (hinterval hy)
  have hmain := norm_complexForwardDiff_sub_constant_le_on_real_interval
    derivs q 0 (n : ℝ) c hderiv hbound'
  rw [show (n : ℂ) = ((n : ℝ) : ℂ) by norm_num]
  rw [← complexForwardDiff_const_mul]
  simpa only [derivs, iteratedDeriv_zero] using hmain

/-- The pointwise main estimates imply exactly the four normalized forward-
difference estimates, retaining all manuscript signs and rational scales. -/
theorem XiNaturalMainLowerDerivativeBounds.forwardDiff_bounds
    {n : ℕ} {L epsilon : ℝ}
    (B : XiNaturalMainLowerDerivativeBounds n L epsilon) :
    ‖(-((n : ℝ) * L) : ℂ) *
        complexForwardDiff 2 complexXiNaturalAuxiliaryLogMain (n : ℂ) + 2‖ ≤
      epsilon ∧
    ‖(((n : ℝ) ^ 2 * L / 2 : ℝ) : ℂ) *
        complexForwardDiff 3 complexXiNaturalAuxiliaryLogMain (n : ℂ) + 1‖ ≤
      epsilon ∧
    ‖(-((n : ℝ) ^ 3 * L / 2 : ℝ) : ℂ) *
        complexForwardDiff 4 complexXiNaturalAuxiliaryLogMain (n : ℂ) + 2‖ ≤
      epsilon ∧
    ‖(((n : ℝ) ^ 4 * L / 6 : ℝ) : ℂ) *
        complexForwardDiff 5 complexXiNaturalAuxiliaryLogMain (n : ℂ) + 2‖ ≤
      epsilon := by
  constructor
  · have h := B.scaled_forwardDiff 2 (by norm_num)
      (-((n : ℝ) * L) : ℂ) (-2) B.orderTwo
    convert h using 1 <;> ring
  constructor
  · have h := B.scaled_forwardDiff 3 (by norm_num)
      ((((n : ℝ) ^ 2 * L / 2 : ℝ) : ℂ)) (-1) B.orderThree
    convert h using 1 <;> ring
  constructor
  · have h := B.scaled_forwardDiff 4 (by norm_num)
      (-((n : ℝ) ^ 3 * L / 2 : ℝ) : ℂ) (-2) B.orderFour
    convert h using 1 <;> ring
  · have h := B.scaled_forwardDiff 5 (by norm_num)
      ((((n : ℝ) ^ 4 * L / 6 : ℝ) : ℂ)) (-2) B.orderFive
    convert h using 1 <;> ring

end

end Zeta23.Research.JensenWedge
