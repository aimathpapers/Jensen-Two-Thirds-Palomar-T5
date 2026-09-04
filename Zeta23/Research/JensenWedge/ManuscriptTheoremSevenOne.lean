import Zeta23.Research.JensenWedge.ManuscriptCauchyTransport

/-!
# Literal sector form of manuscript Theorem 7.1

The analytic implementation uses three fixed sectors.  Saddle and contour
estimates hold on the proof sector `1/100`; the coefficient main and error are
holomorphic on the manuscript outer sector `1/200`; and the quantitative
coefficient estimate is asserted on the closed inner sector `1/400`.

The extra proof-sector margin is what makes the affine parameter
`N = 2M - 2` uniform all the way to the boundary of the manuscript sectors.
-/

namespace Zeta23.Research.JensenWedge

open Complex Filter Set

noncomputable section

/-- The explicit radial threshold used to witness the existential radius in
manuscript Theorem 7.1. -/
def manuscriptTheoremRadius : ℝ := Real.exp (leanSaddleCutoff + 2)

def manuscriptOuterSectorAt (R : ℝ) : Set ℂ :=
  {M | R < ‖M‖ ∧ |M.arg| < saddleOuterAngle}

def manuscriptInnerSectorAt (R : ℝ) : Set ℂ :=
  {M | R < ‖M‖ ∧ |M.arg| ≤ saddleInnerAngle}

def manuscriptOuterSector : Set ℂ :=
  manuscriptOuterSectorAt manuscriptTheoremRadius

def manuscriptInnerSector : Set ℂ :=
  manuscriptInnerSectorAt manuscriptTheoremRadius

/-- The relative error used in the literal manuscript statement.  Defining it
as the quotient makes its outer-sector holomorphy independent of the
quantitative inner-sector estimates. -/
def manuscriptPaperRelativeError (M : ℂ) : ℂ :=
  complexXiCoefficientMoment M / manuscriptXiCoefficientMain M - 1

/-- Explicit coefficient in the paper's `log |M| / |M|` normalization. -/
def manuscriptPaperErrorCoefficient : ℝ :=
  2 * manuscriptXiCoefficientErrorCoefficient

private theorem manuscriptTheoremRadius_gt_thousand :
    1000 < manuscriptTheoremRadius := by
  have hcut : 0 < leanSaddleCutoff + 2 := by
    norm_num [leanSaddleCutoff]
  have hlinear := Real.add_one_lt_exp (ne_of_gt hcut)
  unfold manuscriptTheoremRadius
  norm_num [leanSaddleCutoff] at hlinear ⊢
  linarith

private theorem manuscript_shiftFactor_arg_lt_inner
    {M : ℂ} (hMnorm : manuscriptTheoremRadius < ‖M‖) :
    |(1 - 1 / M).arg| < saddleInnerAngle := by
  let w : ℂ := -(1 / M)
  let z : ℂ := 1 + w
  have hMlarge : 1000 < ‖M‖ := manuscriptTheoremRadius_gt_thousand.trans hMnorm
  have hMpos : 0 < ‖M‖ := by linarith
  have hMne : M ≠ 0 := norm_pos_iff.mp hMpos
  have hwNorm : ‖w‖ < 1 / 1000 := by
    simp only [w, norm_neg, norm_div, norm_one]
    rw [div_lt_iff₀ hMpos]
    nlinarith
  have hzRe : 0 < z.re := by
    have hwRe := Complex.abs_re_le_norm w
    simp only [z, add_re, one_re]
    nlinarith [neg_le_of_abs_le hwRe]
  have hzNormLower : 999 / 1000 < ‖z‖ := by
    have htri : (1 : ℝ) ≤ ‖z‖ + ‖w‖ := by
      calc
        (1 : ℝ) = ‖(1 : ℂ)‖ := by norm_num
        _ = ‖z - w‖ := by simp only [z]; ring_nf
        _ ≤ ‖z‖ + ‖w‖ := norm_sub_le _ _
    linarith
  have hzNe : z ≠ 0 := norm_pos_iff.mp (by linarith)
  have hzIm : |z.im| < 1 / 1000 := by
    have := Complex.abs_im_le_norm w
    simp only [z, add_im, one_im, zero_add] at ⊢
    exact this.trans_lt hwNorm
  have hsin : |Real.sin z.arg| < 1 / 999 := by
    rw [Complex.sin_arg, abs_div, abs_of_nonneg (norm_nonneg z)]
    rw [div_lt_iff₀ (norm_pos_iff.mpr hzNe)]
    nlinarith
  have hargRange : |z.arg| ≤ Real.pi / 2 :=
    Complex.abs_arg_le_pi_div_two_iff.mpr hzRe.le
  have hjordan : 2 / Real.pi * |z.arg| ≤ |Real.sin z.arg| :=
    Real.mul_abs_le_abs_sin hargRange
  have hzArg : |z.arg| < saddleInnerAngle := by
    calc
      |z.arg| = (Real.pi / 2) * (2 / Real.pi * |z.arg|) := by
        field_simp [Real.pi_ne_zero]
      _ ≤ (Real.pi / 2) * |Real.sin z.arg| := by gcongr
      _ < (Real.pi / 2) * (1 / 999) := by gcongr
      _ < 1 / 400 := by
        rw [div_mul_div_comm]
        nlinarith [Real.pi_lt_four]
      _ = saddleInnerAngle := by norm_num [saddleInnerAngle]
  simpa only [z, w, sub_eq_add_neg] using hzArg

private theorem coefficientMellinParameter_norm_lower
    {M : ℂ} (hMnorm : manuscriptTheoremRadius < ‖M‖) :
    ‖M‖ < ‖coefficientMellinParameter M‖ := by
  have hlarge : 2 < ‖M‖ := manuscriptTheoremRadius_gt_thousand.trans hMnorm |>.trans' (by norm_num)
  have htri : ‖(2 : ℂ) * M‖ ≤ ‖coefficientMellinParameter M‖ + ‖(2 : ℂ)‖ := by
    calc
      ‖(2 : ℂ) * M‖ =
          ‖coefficientMellinParameter M + (2 : ℂ)‖ := by
            congr 1
            unfold coefficientMellinParameter
            ring
      _ ≤ ‖coefficientMellinParameter M‖ + ‖(2 : ℂ)‖ := norm_add_le _ _
  simp only [norm_mul, norm_ofNat] at htri
  nlinarith

private theorem coefficientMellinParameter_norm_upper
    {M : ℂ} (hMnorm : manuscriptTheoremRadius < ‖M‖) :
    ‖coefficientMellinParameter M‖ ≤ 3 * ‖M‖ := by
  have hlarge : 2 < ‖M‖ := manuscriptTheoremRadius_gt_thousand.trans hMnorm |>.trans' (by norm_num)
  unfold coefficientMellinParameter
  calc
    ‖2 * M - 2‖ ≤ ‖2 * M‖ + ‖(2 : ℂ)‖ := norm_sub_le _ _
    _ = 2 * ‖M‖ + 2 := by norm_num
    _ ≤ 3 * ‖M‖ := by linarith

private theorem coefficientMellinParameter_arg_eq
    {M : ℂ} (hMnorm : manuscriptTheoremRadius < ‖M‖)
    (hMArg : |M.arg| < saddleOuterAngle) :
    (coefficientMellinParameter M).arg = M.arg + (1 - 1 / M).arg := by
  let z : ℂ := 1 - 1 / M
  have hMlarge : 1000 < ‖M‖ := manuscriptTheoremRadius_gt_thousand.trans hMnorm
  have hMpos : 0 < ‖M‖ := by linarith
  have hMne : M ≠ 0 := norm_pos_iff.mp hMpos
  have hzArg : |z.arg| < saddleInnerAngle := by
    simpa only [z] using manuscript_shiftFactor_arg_lt_inner hMnorm
  have hsumAbs : |M.arg + z.arg| < saddleProofAngle := by
    calc
      |M.arg + z.arg| ≤ |M.arg| + |z.arg| := abs_add_le _ _
      _ < saddleOuterAngle + saddleInnerAngle := add_lt_add hMArg hzArg
      _ < saddleProofAngle := by
        norm_num [saddleInnerAngle, saddleOuterAngle, saddleProofAngle]
  have hsumRange : M.arg + z.arg ∈ Set.Ioc (-Real.pi) Real.pi := by
    have hsmall : |M.arg + z.arg| < Real.pi :=
      hsumAbs.trans (saddleProofAngle_lt_pi_div_two.trans
        (half_lt_self Real.pi_pos))
    rw [abs_lt] at hsmall
    exact ⟨hsmall.1, hsmall.2.le⟩
  have hzNe : z ≠ 0 := by
    have hinvNorm : ‖1 / M‖ < 1 := by
      simp only [norm_div, norm_one]
      rw [div_lt_one hMpos]
      linarith
    have hinvRe := Complex.abs_re_le_norm (1 / M)
    have hzRe : 0 < z.re := by
      simp only [z, sub_re, one_re]
      nlinarith [le_trans (le_abs_self ((1 / M).re)) hinvRe]
    intro hz
    rw [hz] at hzRe
    norm_num at hzRe
  have hfactor : coefficientMellinParameter M = (2 : ℝ) * (M * z) := by
    simp only [z, coefficientMellinParameter]
    field_simp [hMne]
    simp [sub_eq_add_neg, mul_comm]
  rw [hfactor, Complex.arg_real_mul _ (by norm_num : (0 : ℝ) < 2)]
  exact Complex.arg_mul hMne hzNe hsumRange

theorem manuscriptOuterSector_parameter_geometry
    {M : ℂ} (hM : M ∈ manuscriptOuterSector) :
    M ∈ leanSaddleSector ∧
      coefficientMellinParameter M ∈ leanSaddleSector := by
  change manuscriptTheoremRadius < ‖M‖ ∧ |M.arg| < saddleOuterAngle at hM
  have hMradial : Real.exp leanSaddleCutoff < ‖M‖ := by
    exact (Real.exp_lt_exp.mpr (by norm_num)).trans hM.1
  have hNradial : Real.exp leanSaddleCutoff <
      ‖coefficientMellinParameter M‖ :=
    hMradial.trans (coefficientMellinParameter_norm_lower hM.1)
  have hNargEq := coefficientMellinParameter_arg_eq hM.1 hM.2
  have hshift := manuscript_shiftFactor_arg_lt_inner hM.1
  have hNarg : |(coefficientMellinParameter M).arg| < saddleProofAngle := by
    rw [hNargEq]
    calc
      |M.arg + (1 - 1 / M).arg| ≤
          |M.arg| + |(1 - 1 / M).arg| := abs_add_le _ _
      _ < saddleOuterAngle + saddleInnerAngle := add_lt_add hM.2 hshift
      _ < saddleProofAngle := by
        norm_num [saddleInnerAngle, saddleOuterAngle, saddleProofAngle]
  exact ⟨⟨hMradial, hM.2.trans saddleOuterAngle_lt_proofAngle⟩,
    ⟨hNradial, hNarg⟩⟩

theorem manuscriptInnerSector_subset_leanXiCoefficientSector :
    manuscriptInnerSector ⊆ leanXiCoefficientSector := by
  intro M hM
  change manuscriptTheoremRadius < ‖M‖ ∧ |M.arg| ≤ saddleInnerAngle at hM
  have hMradial : Real.exp (leanSaddleCutoff + 1) < ‖M‖ :=
    (Real.exp_lt_exp.mpr (by norm_num)).trans hM.1
  have hNradial : Real.exp (leanSaddleCutoff + 1) <
      ‖coefficientMellinParameter M‖ :=
    hMradial.trans (coefficientMellinParameter_norm_lower hM.1)
  have hMouter : |M.arg| < saddleOuterAngle :=
    hM.2.trans_lt saddle_angles_pos.2.1
  have hNargEq := coefficientMellinParameter_arg_eq hM.1 hMouter
  have hshift := manuscript_shiftFactor_arg_lt_inner hM.1
  have hNarg : |(coefficientMellinParameter M).arg| < saddleOuterAngle := by
    rw [hNargEq]
    calc
      |M.arg + (1 - 1 / M).arg| ≤
          |M.arg| + |(1 - 1 / M).arg| := abs_add_le _ _
      _ < saddleInnerAngle + saddleInnerAngle :=
        add_lt_add_of_le_of_lt hM.2 hshift
      _ = saddleOuterAngle := by
        norm_num [saddleInnerAngle, saddleOuterAngle]
  exact ⟨⟨hMradial, hMouter⟩, ⟨hNradial, hNarg⟩⟩

theorem isOpen_manuscriptOuterSector : IsOpen manuscriptOuterSector := by
  rw [isOpen_iff_mem_nhds]
  intro M hM
  have hgeometry := manuscriptOuterSector_parameter_geometry hM
  have hMre : 0 < M.re := leanSaddleSector_re_pos hgeometry.1
  have hslit : M ∈ slitPlane := Or.inl hMre
  change manuscriptTheoremRadius < ‖M‖ ∧ |M.arg| < saddleOuterAngle at hM
  have hradial : {z : ℂ | manuscriptTheoremRadius < ‖z‖} ∈ nhds M :=
    continuous_norm.continuousAt (Ioi_mem_nhds hM.1)
  have hangle : {z : ℂ | |z.arg| < saddleOuterAngle} ∈ nhds M :=
    (Complex.continuousAt_arg hslit).abs (Iio_mem_nhds hM.2)
  exact inter_mem hradial hangle

theorem manuscriptSaddleMain_ne_zero_of_sector
    {s : ℂ} (hs : s ∈ leanSaddleSector) :
    manuscriptSaddleMain s ≠ 0 := by
  have hmain := saddleMomentMain_ne_zero hs
  have heq := saddleMomentMain_eq_manuscriptSaddleMain_mul_correction hs
  intro hzero
  apply hmain
  rw [heq, hzero, zero_mul]

theorem differentiableAt_manuscriptSaddleMain_of_sector
    {s : ℂ} (hs : s ∈ leanSaddleSector) :
    DifferentiableAt ℂ manuscriptSaddleMain s := by
  have hcorrection : coefficientGaussianCorrection s ≠ 0 := by
    unfold coefficientGaussianCorrection
    exact Complex.exp_ne_zero _
  have hright : DifferentiableAt ℂ
      (fun z => saddleMomentMain z / coefficientGaussianCorrection z) s :=
    (hasDerivAt_saddleMomentMain hs).differentiableAt.div
      (differentiableAt_coefficientGaussianCorrection hs) hcorrection
  have heq : manuscriptSaddleMain =ᶠ[nhds s]
      fun z => saddleMomentMain z / coefficientGaussianCorrection z := by
    filter_upwards [isOpen_leanSaddleSector.mem_nhds hs] with z hz
    rw [saddleMomentMain_eq_manuscriptSaddleMain_mul_correction hz]
    field_simp [coefficientGaussianCorrection, Complex.exp_ne_zero]
  exact hright.congr_of_eventuallyEq heq

theorem differentiableAt_manuscriptCoefficientElementaryMain_of_re_pos
    {M : ℂ} (hMre : 0 < M.re)
    (hNre : 0 < (coefficientMellinParameter M).re) :
    DifferentiableAt ℂ manuscriptCoefficientElementaryMain M := by
  have hlogM : DifferentiableAt ℂ log M :=
    Complex.differentiableAt_log
      (Complex.mem_slitPlane_iff.mpr (Or.inl hMre))
  have hNdiff : DifferentiableAt ℂ coefficientMellinParameter M :=
    differentiableAt_coefficientMellinParameter M
  have hlogN : DifferentiableAt ℂ
      (fun z => log (coefficientMellinParameter z)) M :=
    (Complex.differentiableAt_log
      (Complex.mem_slitPlane_iff.mpr (Or.inl hNre))).comp M hNdiff
  have hinner : DifferentiableAt ℂ
      (fun z => z - 2 + (z + 1 / 2) * log z -
        coefficientMellinParameter z * log 2 -
        (coefficientMellinParameter z + 1 / 2) *
          log (coefficientMellinParameter z)) M := by
    fun_prop
  unfold manuscriptCoefficientElementaryMain
  exact hinner.cexp

theorem manuscriptXiCoefficientMain_ne_zero_of_outer
    {M : ℂ} (hM : M ∈ manuscriptOuterSector) :
    manuscriptXiCoefficientMain M ≠ 0 := by
  have hgeometry := manuscriptOuterSector_parameter_geometry hM
  unfold manuscriptXiCoefficientMain manuscriptCoefficientElementaryMain
  exact mul_ne_zero (Complex.exp_ne_zero _)
    (manuscriptSaddleMain_ne_zero_of_sector hgeometry.2)

theorem differentiableAt_manuscriptXiCoefficientMain_of_outer
    {M : ℂ} (hM : M ∈ manuscriptOuterSector) :
    DifferentiableAt ℂ manuscriptXiCoefficientMain M := by
  have hgeometry := manuscriptOuterSector_parameter_geometry hM
  have hMre : 0 < M.re := leanSaddleSector_re_pos hgeometry.1
  have hNre : 0 < (coefficientMellinParameter M).re :=
    leanSaddleSector_re_pos hgeometry.2
  have hNdiff : DifferentiableAt ℂ coefficientMellinParameter M :=
    differentiableAt_coefficientMellinParameter M
  unfold manuscriptXiCoefficientMain
  exact (differentiableAt_manuscriptCoefficientElementaryMain_of_re_pos hMre hNre).mul
    ((differentiableAt_manuscriptSaddleMain_of_sector hgeometry.2).comp M hNdiff)

theorem differentiableAt_complexXiCoefficientMoment_of_outer
    {M : ℂ} (hM : M ∈ manuscriptOuterSector) :
    DifferentiableAt ℂ complexXiCoefficientMoment M := by
  let N : ℂ := coefficientMellinParameter M
  have hgeometry := manuscriptOuterSector_parameter_geometry hM
  have hMre : 0 < M.re := leanSaddleSector_re_pos hgeometry.1
  have hNre : 0 < N.re := leanSaddleSector_re_pos hgeometry.2
  have hNdiff : DifferentiableAt ℂ coefficientMellinParameter M :=
    differentiableAt_coefficientMellinParameter M
  have hfullN : DifferentiableAt ℂ
      (fun z => fullThetaMoment (coefficientMellinParameter z)) M :=
    (differentiableAt_fullThetaMoment (by linarith)).comp M hNdiff
  have hfullN2 : DifferentiableAt ℂ
      (fun z => fullThetaMoment (coefficientMellinParameter z + 2)) M := by
    have hcomp := (differentiableAt_fullThetaMoment (s := N + 2) (by
      norm_num
      linarith)).comp M (hNdiff.add_const 2)
    simpa only [Function.comp_def, N] using hcomp
  have hcoefficient : DifferentiableAt ℂ
      (fun z => coefficientMomentMultiplier (coefficientMellinParameter z)) M := by
    unfold coefficientMomentMultiplier coefficientMellinParameter
    fun_prop
  have hdyadic : DifferentiableAt ℂ coefficientDyadicScale M := by
    unfold coefficientDyadicScale
    fun_prop
  have hratio := (hasDerivAt_complexFactorialRatio hMre).differentiableAt
  change DifferentiableAt ℂ
    (fun z => complexFactorialRatio z * coefficientDyadicScale z *
      (coefficientMomentMultiplier (coefficientMellinParameter z) *
          fullThetaMoment (coefficientMellinParameter z) -
        fullThetaMoment (coefficientMellinParameter z + 2))) M
  exact (hratio.mul hdyadic).mul ((hcoefficient.mul hfullN).sub hfullN2)

theorem differentiableAt_manuscriptPaperRelativeError_of_outer
    {M : ℂ} (hM : M ∈ manuscriptOuterSector) :
    DifferentiableAt ℂ manuscriptPaperRelativeError M := by
  unfold manuscriptPaperRelativeError
  exact ((differentiableAt_complexXiCoefficientMoment_of_outer hM).div
    (differentiableAt_manuscriptXiCoefficientMain_of_outer hM)
    (manuscriptXiCoefficientMain_ne_zero_of_outer hM)).sub_const 1

theorem differentiableOn_complexXiCoefficientMoment_manuscriptOuter :
    DifferentiableOn ℂ complexXiCoefficientMoment manuscriptOuterSector := by
  intro M hM
  exact (differentiableAt_complexXiCoefficientMoment_of_outer hM).differentiableWithinAt

theorem differentiableOn_manuscriptXiCoefficientMain_manuscriptOuter :
    DifferentiableOn ℂ manuscriptXiCoefficientMain manuscriptOuterSector := by
  intro M hM
  exact (differentiableAt_manuscriptXiCoefficientMain_of_outer hM).differentiableWithinAt

theorem differentiableOn_manuscriptPaperRelativeError_manuscriptOuter :
    DifferentiableOn ℂ manuscriptPaperRelativeError manuscriptOuterSector := by
  intro M hM
  exact (differentiableAt_manuscriptPaperRelativeError_of_outer hM).differentiableWithinAt

theorem manuscriptPaperRelativeError_eq
    {M : ℂ} (hM : M ∈ leanXiCoefficientSector) :
    manuscriptPaperRelativeError M = manuscriptXiCoefficientRelativeError M := by
  unfold manuscriptPaperRelativeError
  rw [complexXiCoefficientMoment_manuscript_factorization hM]
  field_simp [manuscriptXiCoefficientMain_ne_zero hM]
  ring

theorem complexXiCoefficientMoment_paper_factorization
    {M : ℂ} (hM : M ∈ manuscriptOuterSector) :
    complexXiCoefficientMoment M = manuscriptXiCoefficientMain M *
      (1 + manuscriptPaperRelativeError M) := by
  unfold manuscriptPaperRelativeError
  field_simp [manuscriptXiCoefficientMain_ne_zero_of_outer hM]
  ring

theorem manuscriptPaperRelativeError_norm_le
    {M : ℂ} (hM : M ∈ manuscriptInnerSector) :
    ‖manuscriptPaperRelativeError M‖ ≤
      manuscriptPaperErrorCoefficient * Real.log ‖M‖ / ‖M‖ := by
  have hpaired := manuscriptInnerSector_subset_leanXiCoefficientSector hM
  have hbase := manuscriptXiCoefficientRelativeError_norm_le hpaired
  change manuscriptTheoremRadius < ‖M‖ ∧ |M.arg| ≤ saddleInnerAngle at hM
  let N : ℂ := coefficientMellinParameter M
  let C : ℝ := manuscriptXiCoefficientErrorCoefficient
  have hNlower : ‖M‖ < ‖N‖ := coefficientMellinParameter_norm_lower hM.1
  have hNupper : ‖N‖ ≤ 3 * ‖M‖ := coefficientMellinParameter_norm_upper hM.1
  have hMlarge : 3 ≤ ‖M‖ := by
    linarith [manuscriptTheoremRadius_gt_thousand.trans hM.1]
  have hMpos : 0 < ‖M‖ := by linarith
  have hNpos : 0 < ‖N‖ := hMpos.trans hNlower
  have hlogMnonneg : 0 ≤ Real.log ‖M‖ := Real.log_nonneg (by linarith)
  have hlogNnonneg : 0 ≤ Real.log ‖N‖ := Real.log_nonneg (by linarith)
  have hlogThree : Real.log 3 ≤ Real.log ‖M‖ :=
    Real.log_le_log (by norm_num) hMlarge
  have hlogN : Real.log ‖N‖ ≤ 2 * Real.log ‖M‖ := by
    calc
      Real.log ‖N‖ ≤ Real.log (3 * ‖M‖) := Real.log_le_log hNpos hNupper
      _ = Real.log 3 + Real.log ‖M‖ := by rw [Real.log_mul (by norm_num) hMpos.ne']
      _ ≤ 2 * Real.log ‖M‖ := by linarith
  have hC : 0 ≤ C := by
    norm_num [C, manuscriptXiCoefficientErrorCoefficient,
      complexXiCoefficientErrorCoefficient, fullThetaMomentErrorCoefficient]
  rw [manuscriptPaperRelativeError_eq hpaired]
  change ‖manuscriptXiCoefficientRelativeError M‖ ≤
    (2 * C) * Real.log ‖M‖ / ‖M‖
  calc
    ‖manuscriptXiCoefficientRelativeError M‖ ≤
        C * Real.log ‖N‖ / ‖N‖ := by simpa only [C, N] using hbase
    _ ≤ C * (2 * Real.log ‖M‖) / ‖N‖ := by
      apply div_le_div_of_nonneg_right _ (norm_nonneg N)
      exact mul_le_mul_of_nonneg_left hlogN hC
    _ ≤ C * (2 * Real.log ‖M‖) / ‖M‖ := by
      exact div_le_div_of_nonneg_left
        (mul_nonneg hC (mul_nonneg (by norm_num) hlogMnonneg)) hMpos hNlower.le
    _ = (2 * C) * Real.log ‖M‖ / ‖M‖ := by ring

/-- Effective, literal-sector form of manuscript Theorem 7.1. -/
theorem manuscriptTheoremSevenOne_effective :
    IsOpen manuscriptOuterSector ∧
      DifferentiableOn ℂ complexXiCoefficientMoment manuscriptOuterSector ∧
      DifferentiableOn ℂ manuscriptXiCoefficientMain manuscriptOuterSector ∧
      DifferentiableOn ℂ manuscriptPaperRelativeError manuscriptOuterSector ∧
      (∀ M ∈ manuscriptOuterSector, manuscriptXiCoefficientMain M ≠ 0) ∧
      ∀ M ∈ manuscriptInnerSector,
        complexXiCoefficientMoment M = manuscriptXiCoefficientMain M *
          (1 + manuscriptPaperRelativeError M) ∧
        ‖manuscriptPaperRelativeError M‖ ≤
          manuscriptPaperErrorCoefficient * Real.log ‖M‖ / ‖M‖ := by
  exact ⟨isOpen_manuscriptOuterSector,
    differentiableOn_complexXiCoefficientMoment_manuscriptOuter,
    differentiableOn_manuscriptXiCoefficientMain_manuscriptOuter,
    differentiableOn_manuscriptPaperRelativeError_manuscriptOuter,
    fun M hM => manuscriptXiCoefficientMain_ne_zero_of_outer hM,
    fun M hM => by
      have hMouter : M ∈ manuscriptOuterSector := by
        change manuscriptTheoremRadius < ‖M‖ ∧ |M.arg| < saddleOuterAngle
        exact ⟨hM.1, hM.2.trans_lt saddle_angles_pos.2.1⟩
      exact ⟨complexXiCoefficientMoment_paper_factorization hMouter,
        manuscriptPaperRelativeError_norm_le hM⟩⟩

theorem manuscriptTheoremSevenOne :
    ∃ R C : ℝ, 0 < R ∧ 0 < C ∧
      IsOpen (manuscriptOuterSectorAt R) ∧
      DifferentiableOn ℂ complexXiCoefficientMoment (manuscriptOuterSectorAt R) ∧
      DifferentiableOn ℂ manuscriptXiCoefficientMain (manuscriptOuterSectorAt R) ∧
      DifferentiableOn ℂ manuscriptPaperRelativeError (manuscriptOuterSectorAt R) ∧
      (∀ M ∈ manuscriptOuterSectorAt R, manuscriptXiCoefficientMain M ≠ 0) ∧
      ∀ M ∈ manuscriptInnerSectorAt R,
        complexXiCoefficientMoment M = manuscriptXiCoefficientMain M *
          (1 + manuscriptPaperRelativeError M) ∧
        ‖manuscriptPaperRelativeError M‖ ≤
          C * Real.log ‖M‖ / ‖M‖ := by
  refine ⟨manuscriptTheoremRadius, manuscriptPaperErrorCoefficient,
    Real.exp_pos _, ?_, ?_⟩
  · norm_num [manuscriptPaperErrorCoefficient,
      manuscriptXiCoefficientErrorCoefficient,
      complexXiCoefficientErrorCoefficient, fullThetaMomentErrorCoefficient]
  · simpa only [manuscriptOuterSector, manuscriptInnerSector] using
      manuscriptTheoremSevenOne_effective

/-- The proportional-disc Cauchy consequence of the literal manuscript
error, through every derivative used by the sixth-order argument. -/
theorem manuscriptPaperRelativeError_derivatives_through_six
    {x : ℝ} (hx : Real.exp (leanSaddleCutoff + 2) < x) :
    ∀ j ≤ 6,
      ‖iteratedDeriv j manuscriptPaperRelativeError (x : ℂ)‖ ≤
        j.factorial * manuscriptCauchyEpsilon x /
          manuscriptCauchyRadius x ^ j := by
  have hxpos : 0 < x :=
    (manuscriptCauchy_large_properties hx).2.2.2
  have hradius : 0 < manuscriptCauchyRadius x := by
    unfold manuscriptCauchyRadius
    positivity
  have hxmem : (x : ℂ) ∈ leanXiCoefficientSector := by
    apply manuscriptCauchy_closedBall_subset_sector hx
    exact Metric.mem_closedBall_self hradius.le
  have heq : manuscriptPaperRelativeError =ᶠ[nhds (x : ℂ)]
      manuscriptXiCoefficientRelativeError := by
    filter_upwards [isOpen_leanXiCoefficientSector.mem_nhds hxmem] with z hz
    exact manuscriptPaperRelativeError_eq hz
  intro j hj
  rw [heq.iteratedDeriv_eq j]
  exact manuscriptXiCoefficientRelativeError_derivatives_through_six hx j hj

end

end Zeta23.Research.JensenWedge
