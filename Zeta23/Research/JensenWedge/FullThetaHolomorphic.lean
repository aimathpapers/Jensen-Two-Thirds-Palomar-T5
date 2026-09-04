import Zeta23.Research.JensenWedge.CoefficientAssembly

/-!
# Holomorphy of the full theta moment and coefficient error

The pointwise T5 theorem is not enough for the six-derivative Cauchy step:
the exact coefficient continuation and its relative error must be holomorphic
on an open sector.  This module identifies the full theta moment with an
ordinary Mellin transform, proves the endpoint bounds required by Mathlib's
Mellin differentiation theorem, and transports holomorphy through the exact
coefficient factorization.
-/

namespace Zeta23.Research.JensenWedge

open Complex Filter Function MeasureTheory Set Topology Asymptotics

noncomputable section

def fullThetaMellinKernelReal (u : ℝ) : ℝ :=
  Real.exp (u / 4) * riemannThetaTail (Real.exp u)

def fullThetaMellinKernel (u : ℝ) : ℂ :=
  (fullThetaMellinKernelReal u : ℂ)

theorem continuous_fullThetaMellinKernelReal :
    Continuous fullThetaMellinKernelReal := by
  have htheta : Continuous (fun u : ℝ => riemannThetaTail (Real.exp u)) := by
    rw [continuous_iff_continuousAt]
    intro u
    exact (riemannThetaTail_differentiableAt (Real.exp_pos u)).continuousAt.comp
      Real.continuous_exp.continuousAt
  exact (Real.continuous_exp.comp (continuous_id.div_const 4)).mul htheta

theorem continuous_fullThetaMellinKernel :
    Continuous fullThetaMellinKernel :=
  Complex.continuous_ofReal.comp continuous_fullThetaMellinKernelReal

theorem locallyIntegrableOn_fullThetaMellinKernel :
    LocallyIntegrableOn fullThetaMellinKernel (Ioi 0) :=
  continuous_fullThetaMellinKernel.continuousOn.locallyIntegrableOn
    measurableSet_Ioi

/-- The theta Mellin kernel beats `exp(-u)` at infinity. -/
theorem fullThetaMellinKernelReal_isBigO_exp_neg :
    fullThetaMellinKernelReal =O[atTop] (fun u : ℝ => Real.exp (-u)) := by
  have hpow : (fun t => HurwitzKernelBounds.F_nat 0 1 t) =O[atTop]
      (fun t : ℝ => t ^ (-(5 / 4 : ℝ))) :=
    (hurwitzFNat_one_isBigO_exp 0).trans
      (isLittleO_exp_neg_mul_rpow_atTop
        (by positivity : 0 < Real.pi / 2) (-(5 / 4 : ℝ))).isBigO
  have hexp : Tendsto (fun u : ℝ => Real.exp u) atTop atTop :=
    Real.tendsto_exp_atTop
  have hcomp := hpow.comp_tendsto hexp
  have hmul :=
    (isBigO_refl (fun u : ℝ => Real.exp (u / 4)) atTop).mul hcomp
  refine hmul.congr' ?_ ?_
  · filter_upwards [] with u
    simp only [Function.comp_apply, fullThetaMellinKernelReal,
      riemannThetaTail_eq_FNat_zero (Real.exp_pos u)]
  · filter_upwards [] with u
    dsimp only [Function.comp_apply]
    rw [Real.rpow_def_of_pos (Real.exp_pos _), Real.log_exp, ← Real.exp_add]
    congr 1
    ring

theorem fullThetaMellinKernel_isBigO_atTop (r : ℝ) :
    fullThetaMellinKernel =O[atTop] (fun u : ℝ => u ^ r) := by
  have hexp : (fun u : ℝ => Real.exp (-u)) =O[atTop]
      (fun u : ℝ => u ^ r) := by
    simpa only [neg_one_mul] using
      (isLittleO_exp_neg_mul_rpow_atTop one_pos r).isBigO
  have hreal := fullThetaMellinKernelReal_isBigO_exp_neg.trans
    hexp
  change (fun u => (fullThetaMellinKernelReal u : ℂ)) =O[atTop]
    (fun u : ℝ => u ^ r)
  exact Complex.isBigO_ofReal_left.mpr hreal

theorem fullThetaMellinKernel_isBigO_zero :
    fullThetaMellinKernel =O[𝓝[>] 0] (fun u : ℝ => u ^ (0 : ℝ)) := by
  simpa only [Real.rpow_zero] using
    (isBigO_const_of_tendsto
      (y := fullThetaMellinKernel 0)
      (l := 𝓝[>] (0 : ℝ))
      continuous_fullThetaMellinKernel.continuousAt.continuousWithinAt
      (one_ne_zero : (1 : ℝ) ≠ 0))

theorem fullThetaMoment_eq_mellin (s : ℂ) :
    fullThetaMoment s = mellin fullThetaMellinKernel (s + 1) := by
  unfold fullThetaMoment mellin
  apply setIntegral_congr_fun measurableSet_Ioi
  intro u hu
  change fullThetaContourIntegrand s (u : ℂ) = _
  rw [fullThetaContourIntegrand_eq_thetaTail s u]
  unfold fullThetaMellinKernel fullThetaMellinKernelReal
  change exp (s * log (u : ℂ) + (u : ℂ) / 4) *
      (riemannThetaTail (Real.exp u) : ℂ) =
    (u : ℂ) ^ (s + 1 - 1) •
      ((Real.exp (u / 4) * riemannThetaTail (Real.exp u) : ℝ) : ℂ)
  have hu0 : (u : ℂ) ≠ 0 := ofReal_ne_zero.mpr hu.ne'
  rw [Complex.cpow_def_of_ne_zero hu0]
  rw [show s + 1 - 1 = s by ring]
  rw [smul_eq_mul]
  push_cast
  rw [show s * log (u : ℂ) + (u : ℂ) / 4 =
      log (u : ℂ) * s + (u : ℂ) / 4 by ring]
  rw [Complex.exp_add]
  ring

theorem differentiableAt_fullThetaMoment
    {s : ℂ} (hs : -1 < s.re) : DifferentiableAt ℂ fullThetaMoment s := by
  have hzero : fullThetaMellinKernel =O[𝓝[>] 0]
      (fun u : ℝ => u ^ (-(0 : ℝ))) := by
    simpa only [neg_zero] using fullThetaMellinKernel_isBigO_zero
  have hderiv := mellin_hasDerivAt_of_isBigO_rpow
    (a := (s + 1).re + 1) (b := 0)
    locallyIntegrableOn_fullThetaMellinKernel
    (fullThetaMellinKernel_isBigO_atTop (-((s + 1).re + 1)))
    (by linarith)
    hzero
    (by simp; linarith)
  rw [show fullThetaMoment = fun z =>
      mellin fullThetaMellinKernel (z + 1) by
    funext z
    exact fullThetaMoment_eq_mellin z]
  exact (hderiv.2.comp s ((hasDerivAt_id s).add_const 1)).differentiableAt

/-! ## Holomorphic transport through the coefficient assembly -/

theorem isOpen_leanCoefficientSector : IsOpen leanCoefficientSector := by
  rw [isOpen_iff_mem_nhds]
  intro s hs
  rcases hs with ⟨hradial, hangle⟩
  have hnormpos : 0 < ‖s‖ :=
    (Real.exp_pos (leanSaddleCutoff + 1)).trans hradial
  have hsne : s ≠ 0 := norm_pos_iff.mp hnormpos
  have hargSmall : |s.arg| < Real.pi / 2 :=
    hangle.trans saddle_angles_pos.2.2
  have hsre : 0 < s.re :=
    (Complex.abs_arg_lt_pi_div_two_iff.mp hargSmall).resolve_right hsne
  have hslit : s ∈ slitPlane := Or.inl hsre
  have hradialN :
      {z : ℂ | Real.exp (leanSaddleCutoff + 1) < ‖z‖} ∈ 𝓝 s :=
    continuous_norm.continuousAt (Ioi_mem_nhds hradial)
  have hangleN : {z : ℂ | |z.arg| < saddleOuterAngle} ∈ 𝓝 s :=
    (Complex.continuousAt_arg hslit).abs (Iio_mem_nhds hangle)
  exact inter_mem hradialN hangleN

theorem isOpen_leanXiCoefficientSector : IsOpen leanXiCoefficientSector := by
  change IsOpen
    (leanCoefficientSector ∩
      coefficientMellinParameter ⁻¹' leanCoefficientSector)
  exact isOpen_leanCoefficientSector.inter
    (isOpen_leanCoefficientSector.preimage (by
      unfold coefficientMellinParameter
      fun_prop))

theorem leanSaddleSector_re_pos
    {s : ℂ} (hs : s ∈ leanSaddleSector) : 0 < s.re := by
  have hargSmall : |s.arg| < Real.pi / 2 :=
    hs.2.trans saddleProofAngle_lt_pi_div_two
  exact (Complex.abs_arg_lt_pi_div_two_iff.mp hargSmall).resolve_right
    (leanSaddleSector_quantitative hs).parameter_ne_zero

theorem differentiableAt_coefficientMellinParameter (M : ℂ) :
    DifferentiableAt ℂ coefficientMellinParameter M := by
  unfold coefficientMellinParameter
  fun_prop

theorem differentiableAt_complexXiCoefficientMoment
    {M : ℂ} (hM : M ∈ leanXiCoefficientSector) :
    DifferentiableAt ℂ complexXiCoefficientMoment M := by
  let N : ℂ := coefficientMellinParameter M
  have hMouter : M ∈ leanSaddleSector :=
    leanTwoShiftAdmissible_base (leanCoefficientSector_admissible hM.1)
  have hNouter : N ∈ leanSaddleSector :=
    leanTwoShiftAdmissible_base (leanCoefficientSector_admissible hM.2)
  have hMre : 0 < M.re := leanSaddleSector_re_pos hMouter
  have hNre : 0 < N.re := leanSaddleSector_re_pos hNouter
  have hNdiff : DifferentiableAt ℂ coefficientMellinParameter M :=
    differentiableAt_coefficientMellinParameter M
  have hfullN : DifferentiableAt ℂ
      (fun z => fullThetaMoment (coefficientMellinParameter z)) M :=
    (differentiableAt_fullThetaMoment (by linarith)).comp M hNdiff
  have hN2re : -1 < (N + 2).re := by
    norm_num
    linarith
  have hfullN2 : DifferentiableAt ℂ
      (fun z => fullThetaMoment (coefficientMellinParameter z + 2)) M :=
    by
      have hcomp := (differentiableAt_fullThetaMoment hN2re).comp M
        (hNdiff.add_const 2)
      simpa only [Function.comp_def] using hcomp
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

theorem differentiableAt_complexXiCoefficientMain
    {M : ℂ} (hM : M ∈ leanXiCoefficientSector) :
    DifferentiableAt ℂ complexXiCoefficientMain M := by
  let N : ℂ := coefficientMellinParameter M
  have hMouter : M ∈ leanSaddleSector :=
    leanTwoShiftAdmissible_base (leanCoefficientSector_admissible hM.1)
  have hNouter : N ∈ leanSaddleSector :=
    leanTwoShiftAdmissible_base (leanCoefficientSector_admissible hM.2)
  have hMre : 0 < M.re := leanSaddleSector_re_pos hMouter
  have hNdiff : DifferentiableAt ℂ coefficientMellinParameter M :=
    differentiableAt_coefficientMellinParameter M
  have hsaddle : DifferentiableAt ℂ
      (fun z => saddleMomentMain (coefficientMellinParameter z)) M :=
    by
      simpa only [Function.comp_def] using
        (hasDerivAt_saddleMomentMain hNouter).differentiableAt.comp M hNdiff
  have hbranch : DifferentiableAt ℂ
      (fun z => quantitativeSaddleBranch (coefficientMellinParameter z)) M :=
    by
      simpa only [Function.comp_def] using
        (hasDerivAt_quantitativeSaddleBranch hNouter).differentiableAt.comp M hNdiff
  have hcoefficient : DifferentiableAt ℂ
      (fun z => coefficientMomentMultiplier (coefficientMellinParameter z)) M := by
    unfold coefficientMomentMultiplier coefficientMellinParameter
    fun_prop
  have hdyadic : DifferentiableAt ℂ coefficientDyadicScale M := by
    unfold coefficientDyadicScale
    fun_prop
  have hratio := (hasDerivAt_complexFactorialRatioMain hMre).differentiableAt
  change DifferentiableAt ℂ
    (fun z => complexFactorialRatioMain z * coefficientDyadicScale z *
      saddleMomentMain (coefficientMellinParameter z) *
        (coefficientMomentMultiplier (coefficientMellinParameter z) -
          quantitativeSaddleBranch (coefficientMellinParameter z) ^ 2)) M
  exact ((hratio.mul hdyadic).mul hsaddle).mul
    (hcoefficient.sub (hbranch.pow 2))

theorem complexXiCoefficientRelativeError_eq_holomorphicRelativeError
    {M : ℂ} (hM : M ∈ leanXiCoefficientSector) :
    complexXiCoefficientRelativeError M =
      holomorphicRelativeError complexXiCoefficientMoment
        complexXiCoefficientMain M := by
  unfold holomorphicRelativeError
  rw [complexXiCoefficientMoment_factorization hM]
  field_simp [complexXiCoefficientMain_ne_zero hM]
  ring

theorem differentiableOn_complexXiCoefficientMoment :
    DifferentiableOn ℂ complexXiCoefficientMoment leanXiCoefficientSector := by
  intro M hM
  exact (differentiableAt_complexXiCoefficientMoment hM).differentiableWithinAt

theorem differentiableOn_complexXiCoefficientMain :
    DifferentiableOn ℂ complexXiCoefficientMain leanXiCoefficientSector := by
  intro M hM
  exact (differentiableAt_complexXiCoefficientMain hM).differentiableWithinAt

/-- The explicit error used in the T5 coefficient theorem is genuinely
holomorphic on its open sector; it is not merely a pointwise witness. -/
theorem differentiableOn_complexXiCoefficientRelativeError :
    DifferentiableOn ℂ complexXiCoefficientRelativeError
      leanXiCoefficientSector := by
  intro M hM
  have hgenericAt : DifferentiableAt ℂ
      (holomorphicRelativeError complexXiCoefficientMoment
        complexXiCoefficientMain) M := by
    unfold holomorphicRelativeError
    exact ((differentiableAt_complexXiCoefficientMoment hM).div
      (differentiableAt_complexXiCoefficientMain hM)
      (complexXiCoefficientMain_ne_zero hM)).sub_const 1
  exact hgenericAt.differentiableWithinAt.congr
    (fun z hz => complexXiCoefficientRelativeError_eq_holomorphicRelativeError hz)
    (complexXiCoefficientRelativeError_eq_holomorphicRelativeError hM)

/-- Holomorphic strengthening of the exported T5 statement. -/
theorem complexXiCoefficient_sector_holomorphic_asymptotic :
    IsOpen leanXiCoefficientSector ∧
      DifferentiableOn ℂ complexXiCoefficientMoment leanXiCoefficientSector ∧
      DifferentiableOn ℂ complexXiCoefficientMain leanXiCoefficientSector ∧
      DifferentiableOn ℂ complexXiCoefficientRelativeError
        leanXiCoefficientSector ∧
      ∀ M ∈ leanXiCoefficientSector,
        complexXiCoefficientMain M ≠ 0 ∧
          complexXiCoefficientMoment M = complexXiCoefficientMain M *
            (1 + complexXiCoefficientRelativeError M) ∧
          ‖complexXiCoefficientRelativeError M‖ ≤
            complexXiCoefficientErrorCoefficient *
              Real.log ‖coefficientMellinParameter M‖ /
                ‖coefficientMellinParameter M‖ := by
  exact ⟨isOpen_leanXiCoefficientSector,
    differentiableOn_complexXiCoefficientMoment,
    differentiableOn_complexXiCoefficientMain,
    differentiableOn_complexXiCoefficientRelativeError,
    fun M hM => complexXiCoefficient_sector_asymptotic hM⟩

end

end Zeta23.Research.JensenWedge
