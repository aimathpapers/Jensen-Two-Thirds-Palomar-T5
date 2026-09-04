import Zeta23.Research.JensenWedge.TwoShiftCoefficient

namespace Zeta23.Research.JensenWedge

open Complex Filter Function MeasureTheory Set Topology

noncomputable section

/-!
# Exact differential identities for the saddle main term

This module rewrites the concrete Gaussian saddle main as the exponential of
an explicit logarithmic main and differentiates every factor.  In particular,
the determinant factor and the exact Jacobian correction are retained.  These
identities are the algebraic/holomorphic input for the subsequent uniform
two-shift ratio estimate; no asymptotic estimate is asserted here.
-/

def saddleCurvatureAlong (s : ℂ) : ℂ :=
  let L := quantitativeSaddleBranch s
  s * (L⁻¹ + (L ^ 2)⁻¹) - 3 / 4

def saddleCurvatureAlongD1 (s : ℂ) : ℂ :=
  let L := quantitativeSaddleBranch s
  let dL := L / sectorialSaddleCurvature s L
  (L⁻¹ + (L ^ 2)⁻¹) +
    s * (-dL / L ^ 2 - 2 * dL / L ^ 3)

theorem saddleCurvatureAlong_eq
    {s : ℂ} (hs : s ∈ leanSaddleSector) :
    saddleCurvatureAlong s =
      leadingCurvature s (quantitativeSaddleBranch s) := by
  have hLne := (quantitativeSaddleBranch_scaled_bounds
    (leanSaddleSector_quantitative hs)).1
  rw [leadingCurvature_eq_paper hLne]
  simp only [saddleCurvatureAlong, one_div]

theorem hasDerivAt_saddleCurvatureAlong
    {s : ℂ} (hs : s ∈ leanSaddleSector) :
    HasDerivAt saddleCurvatureAlong (saddleCurvatureAlongD1 s) s := by
  let L : ℂ := quantitativeSaddleBranch s
  let dL : ℂ := L / sectorialSaddleCurvature s L
  have hL : HasDerivAt quantitativeSaddleBranch dL s :=
    hasDerivAt_quantitativeSaddleBranch hs
  have hLne : L ≠ 0 :=
    (quantitativeSaddleBranch_scaled_bounds
      (leanSaddleSector_quantitative hs)).1
  have hLne' : quantitativeSaddleBranch s ≠ 0 := by
    simpa only [L] using hLne
  have hInv : HasDerivAt (quantitativeSaddleBranch⁻¹)
      (-dL / L ^ 2) s := by
    simpa only [L] using hL.inv hLne
  have hSqInv : HasDerivAt
      ((quantitativeSaddleBranch ^ 2)⁻¹)
      (-2 * dL / L ^ 3) s := by
    have hSq := hL.pow 2
    apply (hSq.inv (pow_ne_zero 2 hLne)).congr_deriv
    simp only [Pi.pow_apply, L]
    field_simp [hLne']
    ring
  have hsum := hInv.add hSqInv
  have hprod := (hasDerivAt_id s).mul hsum
  have hfinal := hprod.sub_const (3 / 4 : ℂ)
  change HasDerivAt
    (fun z : ℂ => z * ((quantitativeSaddleBranch z)⁻¹ +
      (quantitativeSaddleBranch z ^ 2)⁻¹) - 3 / 4)
    (saddleCurvatureAlongD1 s) s
  apply hfinal.congr_deriv
  simp only [saddleCurvatureAlongD1, Pi.add_apply, Pi.inv_apply,
    Pi.pow_apply, id_eq, L, dL]
  field_simp [hLne']
  ring

def saddleLeadingLog (s : ℂ) : ℂ :=
  leadingLogIntegrand s (quantitativeSaddleBranch s)

def saddleLeadingLogD1 (s : ℂ) : ℂ :=
  let L := quantitativeSaddleBranch s
  let dL := L / sectorialSaddleCurvature s L
  log L + dL

theorem hasDerivAt_saddleLeadingLog
    {s : ℂ} (hs : s ∈ leanSaddleSector) :
    HasDerivAt saddleLeadingLog (saddleLeadingLogD1 s) s := by
  let L : ℂ := quantitativeSaddleBranch s
  let dL : ℂ := L / sectorialSaddleCurvature s L
  have hL : HasDerivAt quantitativeSaddleBranch dL s :=
    hasDerivAt_quantitativeSaddleBranch hs
  have hLne : L ≠ 0 :=
    (quantitativeSaddleBranch_scaled_bounds
      (leanSaddleSector_quantitative hs)).1
  have hLre : 0 < L.re := by
    linarith [quantitativeSaddleBranch_re_gt hs]
  have hlog : HasDerivAt (fun z : ℂ => log (quantitativeSaddleBranch z))
      (L⁻¹ * dL) s := by
    exact (Complex.hasDerivAt_log
      (Complex.mem_slitPlane_iff.mpr (Or.inl hLre))).comp s hL
  have hfirst := (hasDerivAt_id s).mul hlog
  have hlinear := hL.div_const (4 : ℂ)
  have hexp := (hL.cexp).const_mul (Real.pi : ℂ)
  have hraw0 := (hfirst.add hlinear).sub hexp
  have hfun :
      (fun z : ℂ => z * log (quantitativeSaddleBranch z) +
        quantitativeSaddleBranch z / 4 -
          (Real.pi : ℂ) * exp (quantitativeSaddleBranch z)) =ᶠ[nhds s]
      (((id * fun z => log (quantitativeSaddleBranch z)) +
          fun z => quantitativeSaddleBranch z / 4) -
          fun z => (Real.pi : ℂ) * exp (quantitativeSaddleBranch z)) := by
    filter_upwards with z
    rfl
  have hraw := hraw0.congr_of_eventuallyEq hfun
  have hroot : sectorialSaddleEquation s L = 0 :=
    (quantitativeSaddleBranch_spec
      (leanSaddleSector_quantitative hs)).2.1
  have hstationary : leadingLogD1 s L = 1 :=
    leadingLogD1_at_saddle hLne hroot
  change HasDerivAt
    (fun z : ℂ => z * log (quantitativeSaddleBranch z) +
      quantitativeSaddleBranch z / 4 -
        (Real.pi : ℂ) * exp (quantitativeSaddleBranch z))
    (saddleLeadingLogD1 s) s
  apply hraw.congr_deriv
  simp only [saddleLeadingLogD1, L, dL, one_mul, id_eq]
  unfold leadingLogD1 at hstationary
  simp only [L] at hstationary
  rw [one_div] at hstationary
  rw [div_eq_mul_inv] at hstationary
  calc
    log (quantitativeSaddleBranch s) +
          s * ((quantitativeSaddleBranch s)⁻¹ *
            (quantitativeSaddleBranch s /
              sectorialSaddleCurvature s (quantitativeSaddleBranch s))) +
        quantitativeSaddleBranch s /
            sectorialSaddleCurvature s (quantitativeSaddleBranch s) / 4 -
          (Real.pi : ℂ) *
            (exp (quantitativeSaddleBranch s) *
              (quantitativeSaddleBranch s /
                sectorialSaddleCurvature s (quantitativeSaddleBranch s))) =
        log (quantitativeSaddleBranch s) +
          (quantitativeSaddleBranch s /
            sectorialSaddleCurvature s (quantitativeSaddleBranch s)) *
            (s * (quantitativeSaddleBranch s)⁻¹ + 4⁻¹ -
              (Real.pi : ℂ) * exp (quantitativeSaddleBranch s)) := by ring
    _ = log (quantitativeSaddleBranch s) +
          quantitativeSaddleBranch s /
            sectorialSaddleCurvature s (quantitativeSaddleBranch s) := by
      rw [hstationary]
      ring

def saddleMomentLogMain (s : ℂ) : ℂ :=
  saddleLeadingLog s +
    (1 / 2 : ℂ) * log ((2 * Real.pi : ℂ) / saddleCurvatureAlong s) +
      1 / (2 * saddleCurvatureAlong s)

theorem saddleMomentMain_eq_exp_logMain
    {s : ℂ} (hs : s ∈ leanSaddleSector) :
    saddleMomentMain s = exp (saddleMomentLogMain s) := by
  let L : ℂ := quantitativeSaddleBranch s
  let K : ℂ := leadingCurvature s L
  have hKre : 0 < K.re :=
    quantitativeSaddleBranch_curvature_re_pos hs
  have hKne : K ≠ 0 := by
    intro hzero
    rw [hzero] at hKre
    simp at hKre
  have hbase : (2 * Real.pi : ℂ) / K ≠ 0 := by
    apply div_ne_zero
    · exact mul_ne_zero (by norm_num) (ofReal_ne_zero.mpr Real.pi_ne_zero)
    · exact hKne
  rw [saddleMomentMain, integral_leadingGaussian hKre,
    leadingIntegrand_eq_exp_logIntegrand,
    Complex.cpow_def_of_ne_zero hbase]
  unfold saddleMomentLogMain saddleLeadingLog
  rw [saddleCurvatureAlong_eq hs]
  simp only [L, K]
  rw [← exp_add, ← exp_add]
  congr 1
  ring

def saddleMomentLogMainD1 (s : ℂ) : ℂ :=
  let K := saddleCurvatureAlong s
  let dK := saddleCurvatureAlongD1 s
  saddleLeadingLogD1 s - dK / (2 * K) - dK / (2 * K ^ 2)

theorem hasDerivAt_saddleMomentLogMain
    {s : ℂ} (hs : s ∈ leanSaddleSector) :
    HasDerivAt saddleMomentLogMain (saddleMomentLogMainD1 s) s := by
  let K : ℂ := saddleCurvatureAlong s
  let dK : ℂ := saddleCurvatureAlongD1 s
  have hK : HasDerivAt saddleCurvatureAlong dK s :=
    hasDerivAt_saddleCurvatureAlong hs
  have hKre : 0 < K.re := by
    change 0 < (saddleCurvatureAlong s).re
    rw [saddleCurvatureAlong_eq hs]
    exact quantitativeSaddleBranch_curvature_re_pos hs
  have hKne : K ≠ 0 := by
    intro hzero
    rw [hzero] at hKre
    simp at hKre
  let C : ℂ := 2 * Real.pi
  have hCne : C ≠ 0 := by
    exact mul_ne_zero (by norm_num) (ofReal_ne_zero.mpr Real.pi_ne_zero)
  have hbaseDeriv : HasDerivAt
      (fun z : ℂ => C / saddleCurvatureAlong z)
      (-C * dK / K ^ 2) s := by
    have hraw := (hasDerivAt_const s C).div hK hKne
    apply hraw.congr_deriv
    simp only [K]
    field_simp [hKne]
    ring
  have hbaseRe : 0 < (C / K).re := by
    rw [Complex.div_re]
    simp only [C, mul_re, ofReal_re, ofReal_im, mul_zero, sub_zero]
    norm_num
    apply div_pos
    · exact mul_pos (mul_pos (by norm_num : (0 : ℝ) < 2) Real.pi_pos) hKre
    · exact normSq_pos.mpr hKne
  have hbaseLog : HasDerivAt
      (fun z : ℂ => log (C / saddleCurvatureAlong z))
      ((C / K)⁻¹ * (-C * dK / K ^ 2)) s := by
    exact (Complex.hasDerivAt_log
      (Complex.mem_slitPlane_iff.mpr (Or.inl hbaseRe))).comp s hbaseDeriv
  have hbaseHalf := hbaseLog.const_mul (1 / 2 : ℂ)
  have hcorrection := (hK.inv hKne).const_mul (1 / 2 : ℂ)
  have hsum :=
    ((hasDerivAt_saddleLeadingLog hs).add hbaseHalf).add hcorrection
  have hfun :
      (fun z : ℂ => saddleLeadingLog z +
        (1 / 2 : ℂ) * log ((2 * Real.pi : ℂ) / saddleCurvatureAlong z) +
          1 / (2 * saddleCurvatureAlong z)) =ᶠ[nhds s]
      ((saddleLeadingLog +
          fun z => (1 / 2 : ℂ) * log (C / saddleCurvatureAlong z)) +
          fun z => (1 / 2 : ℂ) * (saddleCurvatureAlong z)⁻¹) := by
    filter_upwards with z
    simp only [C, Pi.add_apply]
    simp only [div_eq_mul_inv, mul_inv_rev]
    ring
  have hsum' := hsum.congr_of_eventuallyEq hfun
  change HasDerivAt
    (fun z : ℂ => saddleLeadingLog z +
      (1 / 2 : ℂ) * log ((2 * Real.pi : ℂ) / saddleCurvatureAlong z) +
        1 / (2 * saddleCurvatureAlong z))
    (saddleMomentLogMainD1 s) s
  apply hsum'.congr_deriv
  simp only [saddleMomentLogMainD1, K, dK, C]
  field_simp [hKne, Real.pi_ne_zero]
  ring

theorem hasDerivAt_saddleMomentMain
    {s : ℂ} (hs : s ∈ leanSaddleSector) :
    HasDerivAt saddleMomentMain
      (saddleMomentMain s * saddleMomentLogMainD1 s) s := by
  have hExp := (hasDerivAt_saddleMomentLogMain hs).cexp
  have hEq :
      saddleMomentMain =ᶠ[nhds s] fun z => exp (saddleMomentLogMain z) := by
    filter_upwards [isOpen_leanSaddleSector.mem_nhds hs] with z hz
    exact saddleMomentMain_eq_exp_logMain hz
  have hDeriv := hExp.congr_of_eventuallyEq hEq
  apply hDeriv.congr_deriv
  rw [saddleMomentMain_eq_exp_logMain hs]

theorem saddleMomentMain_logarithmicDerivative
    {s : ℂ} (hs : s ∈ leanSaddleSector) :
    (saddleMomentMain s * saddleMomentLogMainD1 s) /
        saddleMomentMain s = saddleMomentLogMainD1 s := by
  field_simp [saddleMomentMain_ne_zero hs]

end

end Zeta23.Research.JensenWedge
