import Zeta23.Research.JensenWedge.ManuscriptCoefficientTheorem

/-!
# Proportional-disc Cauchy transport for the manuscript coefficient error

This module instantiates the generic Cauchy adapter on the paper's positive
real centers and radius `x / 1000`.  The disc is proved to lie inside the
paired coefficient sector, including the shifted parameter `N = 2M - 2`.
-/

namespace Zeta23.Research.JensenWedge

open Complex Filter Set

noncomputable section

def manuscriptCauchyRadius (x : ℝ) : ℝ := x / 1000

def manuscriptCauchyEpsilon (x : ℝ) : ℝ :=
  manuscriptXiCoefficientErrorCoefficient * Real.log (3 * x) / x

theorem manuscriptCauchy_large_properties
    {x : ℝ} (hx : Real.exp (leanSaddleCutoff + 2) < x) :
    1000 < x ∧
      2 * Real.exp (leanSaddleCutoff + 1) < x ∧
      Real.exp (leanSaddleCutoff + 1) < x ∧ 0 < x := by
  have hcut : 0 < leanSaddleCutoff + 2 := by
    norm_num [leanSaddleCutoff]
  have hlinear := Real.add_one_lt_exp (ne_of_gt hcut)
  have hthousand : (1000 : ℝ) < Real.exp (leanSaddleCutoff + 2) := by
    norm_num [leanSaddleCutoff] at hlinear ⊢
    nlinarith [hlinear]
  have hdouble :
      2 * Real.exp (leanSaddleCutoff + 1) <
        Real.exp (leanSaddleCutoff + 2) := by
    have hpos := Real.exp_pos (leanSaddleCutoff + 1)
    calc
      2 * Real.exp (leanSaddleCutoff + 1) =
          Real.exp (leanSaddleCutoff + 1) * 2 := by ring
      _ < Real.exp (leanSaddleCutoff + 1) * Real.exp 1 :=
        mul_lt_mul_of_pos_left Real.exp_one_gt_two hpos
      _ = Real.exp ((leanSaddleCutoff + 1) + 1) := by
        exact (Real.exp_add (leanSaddleCutoff + 1) 1).symm
      _ = Real.exp (leanSaddleCutoff + 2) := by ring_nf
  have hsingle :
      Real.exp (leanSaddleCutoff + 1) <
        Real.exp (leanSaddleCutoff + 2) := by
    exact Real.exp_lt_exp.mpr (by norm_num)
  exact ⟨hthousand.trans hx, hdouble.trans hx, hsingle.trans hx,
    (Real.exp_pos _).trans (hsingle.trans hx)⟩

theorem manuscriptCauchy_closedBall_subset_sector
    {x : ℝ} (hx : Real.exp (leanSaddleCutoff + 2) < x) :
    Metric.closedBall (x : ℂ) (manuscriptCauchyRadius x) ⊆
      leanXiCoefficientSector := by
  intro z hz
  rcases manuscriptCauchy_large_properties hx with
    ⟨hxThousand, hxDouble, hxCut, hxpos⟩
  have hdist : ‖z - (x : ℂ)‖ ≤ x / 1000 := by
    simpa only [manuscriptCauchyRadius, Metric.mem_closedBall,
      dist_eq_norm] using hz
  have hzReDiff : |z.re - x| ≤ x / 1000 := by
    have h := (Complex.abs_re_le_norm (z - (x : ℂ))).trans hdist
    simpa using h
  have hzIm : |z.im| ≤ x / 1000 := by
    have h := (Complex.abs_im_le_norm (z - (x : ℂ))).trans hdist
    simpa using h
  have hzRe : 0 < z.re := by
    rcases abs_le.mp hzReDiff with ⟨hlower, _⟩
    nlinarith
  have hzNormLower : 999 / 1000 * x ≤ ‖z‖ := by
    have htri : x ≤ ‖z‖ + ‖z - (x : ℂ)‖ := by
      calc
        x = ‖(x : ℂ)‖ := by simp [abs_of_pos hxpos]
        _ = ‖z - (z - (x : ℂ))‖ := by congr 1 <;> ring
        _ ≤ ‖z‖ + ‖z - (x : ℂ)‖ := norm_sub_le _ _
    nlinarith
  have hzNormUpper : ‖z‖ ≤ 1001 / 1000 * x := by
    have htri : ‖z‖ ≤ ‖(x : ℂ)‖ + ‖z - (x : ℂ)‖ := by
      calc
        ‖z‖ = ‖(x : ℂ) + (z - (x : ℂ))‖ := by congr 1 <;> ring
        _ ≤ ‖(x : ℂ)‖ + ‖z - (x : ℂ)‖ := norm_add_le _ _
    rw [norm_real, Real.norm_eq_abs, abs_of_pos hxpos] at htri
    nlinarith
  have hzNe : z ≠ 0 := by
    apply norm_pos_iff.mp
    have : 0 < 999 / 1000 * x := mul_pos (by norm_num) hxpos
    linarith
  have hzArg : |z.arg| < saddleOuterAngle := by
    have hargRange : |z.arg| ≤ Real.pi / 2 :=
      Complex.abs_arg_le_pi_div_two_iff.mpr hzRe.le
    have hsin : |Real.sin z.arg| ≤ 1 / 999 := by
      rw [Complex.sin_arg, abs_div, abs_of_nonneg (norm_nonneg z)]
      apply (div_le_iff₀ (norm_pos_iff.mpr hzNe)).mpr
      nlinarith
    have hjordan : 2 / Real.pi * |z.arg| ≤ |Real.sin z.arg| :=
      Real.mul_abs_le_abs_sin hargRange
    calc
      |z.arg| = (Real.pi / 2) * (2 / Real.pi * |z.arg|) := by
        field_simp [Real.pi_ne_zero]
      _ ≤ (Real.pi / 2) * |Real.sin z.arg| := by gcongr
      _ ≤ (Real.pi / 2) * (1 / 999) := by gcongr
      _ < 1 / 400 := by
        rw [div_mul_div_comm]
        nlinarith [Real.pi_lt_four]
      _ < saddleOuterAngle := by norm_num [saddleOuterAngle]
  let N : ℂ := coefficientMellinParameter z
  let a : ℝ := 2 * x - 2
  have hNdiff : ‖N - (a : ℂ)‖ ≤ x / 500 := by
    have heq : N - (a : ℂ) = 2 * (z - (x : ℂ)) := by
      simp only [N, a, coefficientMellinParameter]
      push_cast
      ring
    rw [heq, norm_mul]
    norm_num
    nlinarith
  have hNReDiff : |N.re - a| ≤ x / 500 := by
    have h := (Complex.abs_re_le_norm (N - (a : ℂ))).trans hNdiff
    simpa using h
  have hNIm : |N.im| ≤ x / 500 := by
    have h := (Complex.abs_im_le_norm (N - (a : ℂ))).trans hNdiff
    simpa using h
  have hNRe : 0 < N.re := by
    rcases abs_le.mp hNReDiff with ⟨hlower, _⟩
    dsimp only [a] at hlower
    nlinarith
  have hNNormLower : 998 / 500 * x ≤ ‖N‖ := by
    have htri : a ≤ ‖N‖ + ‖N - (a : ℂ)‖ := by
      have haPos : 0 < a := by dsimp only [a]; nlinarith
      calc
        a = ‖(a : ℂ)‖ := by simp [abs_of_pos haPos]
        _ = ‖N - (N - (a : ℂ))‖ := by congr 1 <;> ring
        _ ≤ ‖N‖ + ‖N - (a : ℂ)‖ := norm_sub_le _ _
    dsimp only [a] at htri
    nlinarith
  have hNNormUpper : ‖N‖ ≤ 3 * x := by
    have htri : ‖N‖ ≤ ‖(a : ℂ)‖ + ‖N - (a : ℂ)‖ := by
      calc
        ‖N‖ = ‖(a : ℂ) + (N - (a : ℂ))‖ := by congr 1 <;> ring
        _ ≤ ‖(a : ℂ)‖ + ‖N - (a : ℂ)‖ := norm_add_le _ _
    have haPos : 0 < a := by dsimp only [a]; nlinarith
    simp only [norm_real, Real.norm_eq_abs, abs_of_pos haPos] at htri
    dsimp only [a] at htri
    nlinarith
  have hNNe : N ≠ 0 := by
    apply norm_pos_iff.mp
    have : 0 < 998 / 500 * x := mul_pos (by norm_num) hxpos
    linarith
  have hNArg : |N.arg| < saddleOuterAngle := by
    have hargRange : |N.arg| ≤ Real.pi / 2 :=
      Complex.abs_arg_le_pi_div_two_iff.mpr hNRe.le
    have hsin : |Real.sin N.arg| ≤ 1 / 998 := by
      rw [Complex.sin_arg, abs_div, abs_of_nonneg (norm_nonneg N)]
      apply (div_le_iff₀ (norm_pos_iff.mpr hNNe)).mpr
      nlinarith
    have hjordan : 2 / Real.pi * |N.arg| ≤ |Real.sin N.arg| :=
      Real.mul_abs_le_abs_sin hargRange
    calc
      |N.arg| = (Real.pi / 2) * (2 / Real.pi * |N.arg|) := by
        field_simp [Real.pi_ne_zero]
      _ ≤ (Real.pi / 2) * |Real.sin N.arg| := by gcongr
      _ ≤ (Real.pi / 2) * (1 / 998) := by gcongr
      _ < 1 / 400 := by
        rw [div_mul_div_comm]
        nlinarith [Real.pi_lt_four]
      _ < saddleOuterAngle := by norm_num [saddleOuterAngle]
  have hzRadial : Real.exp (leanSaddleCutoff + 1) < ‖z‖ := by
    nlinarith
  have hNRadial : Real.exp (leanSaddleCutoff + 1) < ‖N‖ := by
    nlinarith
  exact ⟨⟨hzRadial, hzArg⟩, ⟨hNRadial, hNArg⟩⟩

theorem manuscriptCauchy_shifted_norm_bounds
    {x : ℝ} (hx : Real.exp (leanSaddleCutoff + 2) < x)
    {z : ℂ} (hz : z ∈ Metric.closedBall (x : ℂ) (manuscriptCauchyRadius x)) :
    x ≤ ‖coefficientMellinParameter z‖ ∧
      ‖coefficientMellinParameter z‖ ≤ 3 * x := by
  rcases manuscriptCauchy_large_properties hx with ⟨hxThousand, _, _, hxpos⟩
  have hdist : ‖z - (x : ℂ)‖ ≤ x / 1000 := by
    simpa only [manuscriptCauchyRadius, Metric.mem_closedBall,
      dist_eq_norm] using hz
  let N : ℂ := coefficientMellinParameter z
  let a : ℝ := 2 * x - 2
  have hNdiff : ‖N - (a : ℂ)‖ ≤ x / 500 := by
    have heq : N - (a : ℂ) = 2 * (z - (x : ℂ)) := by
      simp only [N, a, coefficientMellinParameter]
      push_cast
      ring
    rw [heq, norm_mul]
    norm_num
    nlinarith
  have haPos : 0 < a := by dsimp only [a]; nlinarith
  have hlower : a ≤ ‖N‖ + ‖N - (a : ℂ)‖ := by
    calc
      a = ‖(a : ℂ)‖ := by simp [abs_of_pos haPos]
      _ = ‖N - (N - (a : ℂ))‖ := by congr 1 <;> ring
      _ ≤ ‖N‖ + ‖N - (a : ℂ)‖ := norm_sub_le _ _
  have hupper : ‖N‖ ≤ ‖(a : ℂ)‖ + ‖N - (a : ℂ)‖ := by
    calc
      ‖N‖ = ‖(a : ℂ) + (N - (a : ℂ))‖ := by congr 1 <;> ring
      _ ≤ ‖(a : ℂ)‖ + ‖N - (a : ℂ)‖ := norm_add_le _ _
  rw [norm_real, Real.norm_eq_abs, abs_of_pos haPos] at hupper
  dsimp only [a] at hlower hupper
  change x ≤ ‖N‖ ∧ ‖N‖ ≤ 3 * x
  constructor <;> nlinarith

theorem manuscriptXiCoefficientRelativeError_eq_holomorphicRelativeError
    {M : ℂ} (hM : M ∈ leanXiCoefficientSector) :
    manuscriptXiCoefficientRelativeError M =
      holomorphicRelativeError complexXiCoefficientMoment
        manuscriptXiCoefficientMain M := by
  unfold holomorphicRelativeError
  rw [complexXiCoefficientMoment_manuscript_factorization hM]
  field_simp [manuscriptXiCoefficientMain_ne_zero hM]
  ring

theorem manuscriptCauchy_error_norm_le
    {x : ℝ} (hx : Real.exp (leanSaddleCutoff + 2) < x)
    {z : ℂ} (hz : z ∈ Metric.closedBall (x : ℂ) (manuscriptCauchyRadius x)) :
    ‖manuscriptXiCoefficientRelativeError z‖ ≤
      manuscriptCauchyEpsilon x := by
  have hzSector := manuscriptCauchy_closedBall_subset_sector hx hz
  have hbase := manuscriptXiCoefficientRelativeError_norm_le hzSector
  rcases manuscriptCauchy_shifted_norm_bounds hx hz with ⟨hNlower, hNupper⟩
  let N : ℂ := coefficientMellinParameter z
  let C : ℝ := manuscriptXiCoefficientErrorCoefficient
  have hxpos : 0 < x := (manuscriptCauchy_large_properties hx).2.2.2
  have hNpos : 0 < ‖N‖ := hxpos.trans_le hNlower
  have hthreePos : 0 < 3 * x := mul_pos (by norm_num) hxpos
  have hlogUpper : Real.log ‖N‖ ≤ Real.log (3 * x) :=
    Real.log_le_log hNpos hNupper
  have hlogNonneg : 0 ≤ Real.log ‖N‖ := by
    apply Real.log_nonneg
    have hxThousand := (manuscriptCauchy_large_properties hx).1
    linarith
  have hlogThreeNonneg : 0 ≤ Real.log (3 * x) := by
    apply Real.log_nonneg
    have hxThousand := (manuscriptCauchy_large_properties hx).1
    nlinarith
  have hC : 0 ≤ C := by
    norm_num [C, manuscriptXiCoefficientErrorCoefficient,
      complexXiCoefficientErrorCoefficient, fullThetaMomentErrorCoefficient]
  change ‖manuscriptXiCoefficientRelativeError z‖ ≤
    C * Real.log (3 * x) / x
  calc
    ‖manuscriptXiCoefficientRelativeError z‖ ≤
        C * Real.log ‖N‖ / ‖N‖ := by
      simpa only [C, N] using hbase
    _ ≤ C * Real.log (3 * x) / ‖N‖ := by
      apply div_le_div_of_nonneg_right _ (norm_nonneg N)
      exact mul_le_mul_of_nonneg_left hlogUpper hC
    _ ≤ C * Real.log (3 * x) / x := by
      exact div_le_div_of_nonneg_left
        (mul_nonneg hC hlogThreeNonneg) hxpos hNlower

/-- The paper's proportional-disc Cauchy estimate, now instantiated for the
actual manuscript coefficient error at every order through six. -/
theorem manuscriptXiCoefficientRelativeError_derivatives_through_six
    {x : ℝ} (hx : Real.exp (leanSaddleCutoff + 2) < x) :
    ∀ j ≤ 6,
      ‖iteratedDeriv j manuscriptXiCoefficientRelativeError (x : ℂ)‖ ≤
        j.factorial * manuscriptCauchyEpsilon x /
          manuscriptCauchyRadius x ^ j := by
  have hxpos : 0 < x := (manuscriptCauchy_large_properties hx).2.2.2
  have hradius : 0 < manuscriptCauchyRadius x := by
    unfold manuscriptCauchyRadius
    positivity
  let D : Set ℂ := Metric.closedBall (x : ℂ) (manuscriptCauchyRadius x)
  have hD : D ⊆ leanXiCoefficientSector :=
    manuscriptCauchy_closedBall_subset_sector hx
  have htransport := relativeError_derivatives_through_six
    (actual := complexXiCoefficientMoment)
    (main := manuscriptXiCoefficientMain)
    (domain := D) (center := (x : ℂ))
    (radius := manuscriptCauchyRadius x)
    (epsilon := manuscriptCauchyEpsilon x)
    hradius (by exact Subset.rfl)
    (differentiableOn_complexXiCoefficientMoment.mono hD)
    (differentiableOn_manuscriptXiCoefficientMain.mono hD)
    (fun z hz => manuscriptXiCoefficientMain_ne_zero (hD hz))
    (fun z hz => by
      rw [← manuscriptXiCoefficientRelativeError_eq_holomorphicRelativeError
        (hD hz)]
      exact manuscriptCauchy_error_norm_le hx hz)
  have hxmem : (x : ℂ) ∈ leanXiCoefficientSector := by
    apply hD
    exact Metric.mem_closedBall_self hradius.le
  have heq : manuscriptXiCoefficientRelativeError =ᶠ[nhds (x : ℂ)]
      holomorphicRelativeError complexXiCoefficientMoment
        manuscriptXiCoefficientMain := by
    filter_upwards [isOpen_leanXiCoefficientSector.mem_nhds hxmem] with z hz
    exact manuscriptXiCoefficientRelativeError_eq_holomorphicRelativeError hz
  intro j hj
  rw [heq.iteratedDeriv_eq j]
  exact htransport j hj

end

end Zeta23.Research.JensenWedge
