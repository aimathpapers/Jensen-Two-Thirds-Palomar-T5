import Zeta23.Research.JensenWedge.XiNaturalMainCorrectionBounds

/-!
# Kernel identification of the moving-saddle derivative tower

This module differentiates the displayed moving-saddle logarithm directly.
It proves the reduced numerator recurrence through order six, identifies the
frozen `H2,...,H6` tables, and constructs the two symbolic-identification
records formerly supplied as CAS inputs.  Computer algebra remains useful as
independent corroboration, but it is not a premise of these theorems.
-/

namespace Zeta23.Research.JensenWedge

open Complex

noncomputable section

def saddleTermDerivR (term : BivariateTerm) (r sigma : ℂ) : ℂ :=
  (term.coeff : ℂ) * ((term.rPow : ℂ) * r ^ (term.rPow - 1)) *
    sigma ^ term.sigmaPow

def saddleTermDerivSigma (term : BivariateTerm) (r sigma : ℂ) : ℂ :=
  (term.coeff : ℂ) * r ^ term.rPow *
    ((term.sigmaPow : ℂ) * sigma ^ (term.sigmaPow - 1))

def saddleTermsDerivR (terms : List BivariateTerm) (r sigma : ℂ) : ℂ :=
  (terms.map fun term => saddleTermDerivR term r sigma).sum

def saddleTermsDerivSigma (terms : List BivariateTerm) (r sigma : ℂ) : ℂ :=
  (terms.map fun term => saddleTermDerivSigma term r sigma).sum

theorem hasDerivAt_evalBivariateTerms_r (terms : List BivariateTerm) (r sigma : ℂ) :
    HasDerivAt (fun z => evalBivariateTerms terms z sigma)
      (saddleTermsDerivR terms r sigma) r := by
  induction terms with
  | nil => simpa [evalBivariateTerms, saddleTermsDerivR] using hasDerivAt_const r (0 : ℂ)
  | cons term terms ih =>
      simp only [evalBivariateTerms, List.map_cons, List.sum_cons, saddleTermsDerivR]
      apply HasDerivAt.add ?_ ih
      unfold BivariateTerm.eval saddleTermDerivR
      simpa only [Pi.pow_apply, id_eq, one_mul, mul_one] using
        ((((hasDerivAt_id' r).pow term.rPow).const_mul
          (term.coeff : ℂ)).mul_const (sigma ^ term.sigmaPow))

theorem hasDerivAt_evalBivariateTerms_sigma (terms : List BivariateTerm) (r sigma : ℂ) :
    HasDerivAt (fun z => evalBivariateTerms terms r z)
      (saddleTermsDerivSigma terms r sigma) sigma := by
  induction terms with
  | nil => simpa [evalBivariateTerms, saddleTermsDerivSigma] using hasDerivAt_const sigma (0 : ℂ)
  | cons term terms ih =>
      simp only [evalBivariateTerms, List.map_cons, List.sum_cons, saddleTermsDerivSigma]
      apply HasDerivAt.add ?_ ih
      unfold BivariateTerm.eval saddleTermDerivSigma
      simpa only [Pi.pow_apply, id_eq, one_mul, mul_one] using
        (((hasDerivAt_id' sigma).pow term.sigmaPow).const_mul
          ((term.coeff : ℂ) * r ^ term.rPow))

theorem hasDerivAt_evalBivariateTerms_comp
    (terms : List BivariateTerm) {r sigma : ℂ → ℂ} {z dr ds : ℂ}
    (hr : HasDerivAt r dr z) (hs : HasDerivAt sigma ds z) :
    HasDerivAt (fun w => evalBivariateTerms terms (r w) (sigma w))
      (saddleTermsDerivR terms (r z) (sigma z) * dr +
        saddleTermsDerivSigma terms (r z) (sigma z) * ds) z := by
  induction terms with
  | nil =>
      simpa [evalBivariateTerms, saddleTermsDerivR, saddleTermsDerivSigma] using
        hasDerivAt_const z (0 : ℂ)
  | cons term terms ih =>
      change HasDerivAt
        (fun w => term.eval (r w) (sigma w) +
          evalBivariateTerms terms (r w) (sigma w))
        ((saddleTermDerivR term (r z) (sigma z) +
            saddleTermsDerivR terms (r z) (sigma z)) * dr +
          (saddleTermDerivSigma term (r z) (sigma z) +
            saddleTermsDerivSigma terms (r z) (sigma z)) * ds) z
      have hterm := ((((hr.pow term.rPow).const_mul (term.coeff : ℂ)).mul
        (hs.pow term.sigmaPow)))
      apply (hterm.add ih).congr_deriv
      unfold saddleTermDerivR saddleTermDerivSigma
      simp only [Pi.pow_apply]
      ring

def movingSaddleNumeratorStep (k : ℕ) (P Pr Ps r sigma : ℂ) : ℂ :=
  let B : ℂ := 4 + 4 * r - 3 * sigma;
  -4 * (r ^ 2 * (Pr * B - 8 * k * P) + k * r * P * B) +
    (3 * sigma - 4) * ((k - 1) * P * B + sigma * (Ps * B + 6 * k * P))

set_option maxHeartbeats 4000000 in
theorem h2Numerator_step (r sigma : ℂ) :
    movingSaddleNumeratorStep 2 (h2Numerator r sigma)
      (saddleTermsDerivR h2Terms r sigma) (saddleTermsDerivSigma h2Terms r sigma) r sigma =
        h3Numerator r sigma := by
  unfold movingSaddleNumeratorStep h2Numerator h3Numerator saddleTermsDerivR saddleTermsDerivSigma
    evalBivariateTerms saddleTermDerivR saddleTermDerivSigma BivariateTerm.eval
  norm_num [h2Terms, h3Terms]
  ring

set_option maxHeartbeats 4000000 in
theorem h3Numerator_step (r sigma : ℂ) :
    movingSaddleNumeratorStep 3 (h3Numerator r sigma)
      (saddleTermsDerivR h3Terms r sigma) (saddleTermsDerivSigma h3Terms r sigma) r sigma =
        h4Numerator r sigma := by
  unfold movingSaddleNumeratorStep h3Numerator h4Numerator saddleTermsDerivR saddleTermsDerivSigma
    evalBivariateTerms saddleTermDerivR saddleTermDerivSigma BivariateTerm.eval
  norm_num [h3Terms, h4Terms]
  ring

set_option maxHeartbeats 4000000 in
theorem h4Numerator_step (r sigma : ℂ) :
    movingSaddleNumeratorStep 4 (h4Numerator r sigma)
      (saddleTermsDerivR h4Terms r sigma) (saddleTermsDerivSigma h4Terms r sigma) r sigma =
        h5Numerator r sigma := by
  unfold movingSaddleNumeratorStep h4Numerator h5Numerator saddleTermsDerivR saddleTermsDerivSigma
    evalBivariateTerms saddleTermDerivR saddleTermDerivSigma BivariateTerm.eval
  norm_num [h4Terms, h5Terms]
  ring

set_option maxHeartbeats 8000000 in
theorem h5Numerator_step (r sigma : ℂ) :
    movingSaddleNumeratorStep 5 (h5Numerator r sigma)
      (saddleTermsDerivR h5Terms r sigma) (saddleTermsDerivSigma h5Terms r sigma) r sigma =
        h6Numerator r sigma := by
  unfold movingSaddleNumeratorStep h5Numerator h6Numerator saddleTermsDerivR saddleTermsDerivSigma
    evalBivariateTerms saddleTermDerivR saddleTermDerivSigma BivariateTerm.eval
  norm_num [h5Terms, h6Terms]
  ring

def manuscriptSaddleB (N : ℂ) : ℂ :=
  (4 : ℂ) + (4 : ℂ) * manuscriptSaddleR N -
    (3 : ℂ) * manuscriptSaddleSigma N

theorem manuscriptSaddleQ_scaled
    {N : ℂ} (hN : N ∈ leanSaddleSector) :
    manuscriptSaddleQ N =
      N * quantitativeSaddleBranch N * manuscriptSaddleB N / 4 := by
  have hNne := (leanSaddleSector_quantitative hN).parameter_ne_zero
  have hLne := (quantitativeSaddleBranch_scaled_bounds
    (leanSaddleSector_quantitative hN)).1
  unfold manuscriptSaddleQ manuscriptSaddleB manuscriptSaddleR manuscriptSaddleSigma
  field_simp [hNne, hLne]
  ring

theorem manuscriptSaddleB_ne_zero
    {N : ℂ} (hN : N ∈ leanSaddleSector) : manuscriptSaddleB N ≠ 0 := by
  have hNne := (leanSaddleSector_quantitative hN).parameter_ne_zero
  have hLne := (quantitativeSaddleBranch_scaled_bounds
    (leanSaddleSector_quantitative hN)).1
  have hQne := manuscriptSaddleQ_ne_zero hN
  rw [manuscriptSaddleQ_scaled hN] at hQne
  exact fun h => hQne (by rw [h]; ring)

theorem hasDerivAt_manuscriptSaddleR
    {N : ℂ} (hN : N ∈ leanSaddleSector) :
    HasDerivAt manuscriptSaddleR
      (-4 * manuscriptSaddleR N ^ 2 / (N * manuscriptSaddleB N)) N := by
  let L := quantitativeSaddleBranch N
  have hNne := (leanSaddleSector_quantitative hN).parameter_ne_zero
  have hLne : L ≠ 0 := (quantitativeSaddleBranch_scaled_bounds
    (leanSaddleSector_quantitative hN)).1
  have hQne := manuscriptSaddleQ_ne_zero hN
  have hL : HasDerivAt quantitativeSaddleBranch
      (L / manuscriptSaddleQ N) N := by
    simpa only [L, manuscriptSaddleQ, sectorialSaddleCurvature] using
      hasDerivAt_quantitativeSaddleBranch hN
  unfold manuscriptSaddleR
  simp only [one_div]
  exact (hL.inv hLne).congr_deriv (by
      rw [manuscriptSaddleQ_scaled hN]
      unfold manuscriptSaddleB manuscriptSaddleR manuscriptSaddleSigma
      dsimp [L] at hLne ⊢
      field_simp [hNne, hLne, manuscriptSaddleB_ne_zero hN]
    )

theorem hasDerivAt_manuscriptSaddleSigma
    {N : ℂ} (hN : N ∈ leanSaddleSector) :
    HasDerivAt manuscriptSaddleSigma
      (manuscriptSaddleSigma N * (3 * manuscriptSaddleSigma N - 4) /
        (N * manuscriptSaddleB N)) N := by
  let L := quantitativeSaddleBranch N
  have hNne := (leanSaddleSector_quantitative hN).parameter_ne_zero
  have hLne : L ≠ 0 := (quantitativeSaddleBranch_scaled_bounds
    (leanSaddleSector_quantitative hN)).1
  have hL : HasDerivAt quantitativeSaddleBranch
      (L / manuscriptSaddleQ N) N := by
    simpa only [L, manuscriptSaddleQ, sectorialSaddleCurvature] using
      hasDerivAt_quantitativeSaddleBranch hN
  unfold manuscriptSaddleSigma
  apply (hL.div (hasDerivAt_id' N) hNne).congr_deriv
  rw [manuscriptSaddleQ_scaled hN]
  have hBne := manuscriptSaddleB_ne_zero hN
  dsimp [L] at hLne ⊢
  field_simp [hNne, hLne, hBne]
  unfold manuscriptSaddleB manuscriptSaddleR manuscriptSaddleSigma
  field_simp [hNne, hLne]
  ring

def saddleReducedMain (terms : List BivariateTerm) (k : ℕ) (N : ℂ) : ℂ :=
  evalBivariateTerms terms (manuscriptSaddleR N) (manuscriptSaddleSigma N) /
    (manuscriptSaddleB N ^ (2 * k) *
      (N ^ (k - 1) * quantitativeSaddleBranch N))

def saddleReducedMainDerivative (terms : List BivariateTerm) (k : ℕ) (N : ℂ) : ℂ :=
  let r := manuscriptSaddleR N
  let sigma := manuscriptSaddleSigma N
  let B := manuscriptSaddleB N
  let L := quantitativeSaddleBranch N
  let dr := -4 * r ^ 2 / (N * B)
  let ds := sigma * (3 * sigma - 4) / (N * B)
  let dL := L / manuscriptSaddleQ N
  let P := evalBivariateTerms terms r sigma
  let dP := saddleTermsDerivR terms r sigma * dr + saddleTermsDerivSigma terms r sigma * ds
  let dB := 4 * dr - 3 * ds
  let D := B ^ (2 * k) * (N ^ (k - 1) * L)
  let dD := ((2 * k : ℕ) : ℂ) * B ^ (2 * k - 1) * dB *
      (N ^ (k - 1) * L) +
    B ^ (2 * k) *
      (((k - 1 : ℕ) : ℂ) * N ^ (k - 1 - 1) * L + N ^ (k - 1) * dL)
  (dP * D - P * dD) / D ^ 2

theorem hasDerivAt_saddleReducedMain
    (terms : List BivariateTerm) (k : ℕ) {N : ℂ}
    (hN : N ∈ leanSaddleSector) :
    HasDerivAt (saddleReducedMain terms k) (saddleReducedMainDerivative terms k N) N := by
  let r := manuscriptSaddleR N
  let sigma := manuscriptSaddleSigma N
  let B := manuscriptSaddleB N
  let L := quantitativeSaddleBranch N
  let dr := -4 * r ^ 2 / (N * B)
  let ds := sigma * (3 * sigma - 4) / (N * B)
  let dL := L / manuscriptSaddleQ N
  have hNne := (leanSaddleSector_quantitative hN).parameter_ne_zero
  have hLne : L ≠ 0 := (quantitativeSaddleBranch_scaled_bounds
    (leanSaddleSector_quantitative hN)).1
  have hBne : B ≠ 0 := manuscriptSaddleB_ne_zero hN
  have hr : HasDerivAt manuscriptSaddleR dr N := by
    simpa only [r, B, dr] using hasDerivAt_manuscriptSaddleR hN
  have hs : HasDerivAt manuscriptSaddleSigma ds N := by
    simpa only [sigma, B, ds] using hasDerivAt_manuscriptSaddleSigma hN
  have hL : HasDerivAt quantitativeSaddleBranch dL N := by
    simpa only [L, dL, manuscriptSaddleQ, sectorialSaddleCurvature] using
      hasDerivAt_quantitativeSaddleBranch hN
  have hP := hasDerivAt_evalBivariateTerms_comp terms hr hs
  have hB : HasDerivAt manuscriptSaddleB (4 * dr - 3 * ds) N := by
    change HasDerivAt
      (fun z : ℂ => (4 : ℂ) + (4 : ℂ) * manuscriptSaddleR z -
        (3 : ℂ) * manuscriptSaddleSigma z) (4 * dr - 3 * ds) N
    have hraw := (((hasDerivAt_const N (4 : ℂ)).add
      (hr.const_mul (4 : ℂ))).sub (hs.const_mul (3 : ℂ)))
    apply hraw.congr_deriv
    ring
  have hBpow := hB.pow (2 * k)
  have hNpow := (hasDerivAt_id' N).pow (k - 1)
  have hscale := hNpow.mul hL
  have hden := hBpow.mul hscale
  have hdenne : manuscriptSaddleB N ^ (2 * k) *
      (N ^ (k - 1) * quantitativeSaddleBranch N) ≠ 0 :=
    mul_ne_zero (pow_ne_zero _ hBne)
      (mul_ne_zero (pow_ne_zero _ hNne) hLne)
  have hquot := hP.div hden (by
    simpa only [Pi.mul_apply, Pi.pow_apply, id_eq] using hdenne)
  unfold saddleReducedMain
  apply hquot.congr_deriv
  unfold saddleReducedMainDerivative
  dsimp only [r, sigma, B, L, dr, ds, dL]
  simp only [Pi.mul_apply, Pi.pow_apply]
  ring

set_option maxHeartbeats 4000000 in
theorem saddleReducedMain_step_two
    {N : ℂ} (hN : N ∈ leanSaddleSector) :
    HasDerivAt (saddleReducedMain h2Terms 2) (saddleReducedMain h3Terms 3 N) N := by
  apply (hasDerivAt_saddleReducedMain h2Terms 2 hN).congr_deriv
  have hNne := (leanSaddleSector_quantitative hN).parameter_ne_zero
  have hLne := (quantitativeSaddleBranch_scaled_bounds
    (leanSaddleSector_quantitative hN)).1
  have hBne := manuscriptSaddleB_ne_zero hN
  have hQ := manuscriptSaddleQ_scaled hN
  have hstep := h2Numerator_step (manuscriptSaddleR N) (manuscriptSaddleSigma N)
  unfold saddleReducedMainDerivative saddleReducedMain
  dsimp
  rw [hQ]
  field_simp [hNne, hLne, hBne]
  unfold h2Numerator h3Numerator at hstep
  rw [← hstep]
  unfold movingSaddleNumeratorStep manuscriptSaddleB manuscriptSaddleR manuscriptSaddleSigma
  field_simp [hNne, hLne]
  ring

set_option maxHeartbeats 4000000 in
theorem saddleReducedMain_step_three
    {N : ℂ} (hN : N ∈ leanSaddleSector) :
    HasDerivAt (saddleReducedMain h3Terms 3) (saddleReducedMain h4Terms 4 N) N := by
  apply (hasDerivAt_saddleReducedMain h3Terms 3 hN).congr_deriv
  have hNne := (leanSaddleSector_quantitative hN).parameter_ne_zero
  have hLne := (quantitativeSaddleBranch_scaled_bounds
    (leanSaddleSector_quantitative hN)).1
  have hBne := manuscriptSaddleB_ne_zero hN
  have hQ := manuscriptSaddleQ_scaled hN
  have hstep := h3Numerator_step (manuscriptSaddleR N) (manuscriptSaddleSigma N)
  unfold saddleReducedMainDerivative saddleReducedMain
  dsimp
  rw [hQ]
  field_simp [hNne, hLne, hBne]
  unfold h3Numerator h4Numerator at hstep
  rw [← hstep]
  unfold movingSaddleNumeratorStep manuscriptSaddleB manuscriptSaddleR manuscriptSaddleSigma
  field_simp [hNne, hLne]
  ring

set_option maxHeartbeats 4000000 in
theorem saddleReducedMain_step_four
    {N : ℂ} (hN : N ∈ leanSaddleSector) :
    HasDerivAt (saddleReducedMain h4Terms 4) (saddleReducedMain h5Terms 5 N) N := by
  apply (hasDerivAt_saddleReducedMain h4Terms 4 hN).congr_deriv
  have hNne := (leanSaddleSector_quantitative hN).parameter_ne_zero
  have hLne := (quantitativeSaddleBranch_scaled_bounds
    (leanSaddleSector_quantitative hN)).1
  have hBne := manuscriptSaddleB_ne_zero hN
  have hQ := manuscriptSaddleQ_scaled hN
  have hstep := h4Numerator_step (manuscriptSaddleR N) (manuscriptSaddleSigma N)
  unfold saddleReducedMainDerivative saddleReducedMain
  dsimp
  rw [hQ]
  field_simp [hNne, hLne, hBne]
  unfold h4Numerator h5Numerator at hstep
  rw [← hstep]
  unfold movingSaddleNumeratorStep manuscriptSaddleB manuscriptSaddleR manuscriptSaddleSigma
  field_simp [hNne, hLne]
  ring

set_option maxHeartbeats 8000000 in
theorem saddleReducedMain_step_five
    {N : ℂ} (hN : N ∈ leanSaddleSector) :
    HasDerivAt (saddleReducedMain h5Terms 5) (saddleReducedMain h6Terms 6 N) N := by
  apply (hasDerivAt_saddleReducedMain h5Terms 5 hN).congr_deriv
  have hNne := (leanSaddleSector_quantitative hN).parameter_ne_zero
  have hLne := (quantitativeSaddleBranch_scaled_bounds
    (leanSaddleSector_quantitative hN)).1
  have hBne := manuscriptSaddleB_ne_zero hN
  have hQ := manuscriptSaddleQ_scaled hN
  have hstep := h5Numerator_step (manuscriptSaddleR N) (manuscriptSaddleSigma N)
  unfold saddleReducedMainDerivative saddleReducedMain
  dsimp
  rw [hQ]
  field_simp [hNne, hLne, hBne]
  unfold h5Numerator h6Numerator at hstep
  rw [← hstep]
  unfold movingSaddleNumeratorStep manuscriptSaddleB manuscriptSaddleR manuscriptSaddleSigma
  field_simp [hNne, hLne]
  ring

def manuscriptG0AuxNumerator (N : ℂ) : ℂ :=
  let L := quantitativeSaddleBranch N
  3 * L ^ 3 - 4 * L ^ 2 * N - 3 * L ^ 2 - 4 * L * N - 4 * N

def manuscriptG0FirstDerivative (N : ℂ) : ℂ :=
  log (quantitativeSaddleBranch N) -
    manuscriptG0AuxNumerator N / (8 * manuscriptSaddleQ N ^ 2)

def manuscriptSaddleQFirstDerivative (N : ℂ) : ℂ :=
  let L := quantitativeSaddleBranch N
  let dL := L / manuscriptSaddleQ N
  dL * N + (1 + L) - (3 / 2) * L * dL

theorem hasDerivAt_manuscriptSaddleQ
    {N : ℂ} (hN : N ∈ leanSaddleSector) :
    HasDerivAt manuscriptSaddleQ (manuscriptSaddleQFirstDerivative N) N := by
  let L := quantitativeSaddleBranch N
  let dL := L / manuscriptSaddleQ N
  have hL : HasDerivAt quantitativeSaddleBranch dL N := by
    simpa only [L, dL, manuscriptSaddleQ, sectorialSaddleCurvature] using
      hasDerivAt_quantitativeSaddleBranch hN
  unfold manuscriptSaddleQ
  have hraw := (((hL.const_add 1).mul (hasDerivAt_id' N)).sub
    ((hL.pow 2).const_mul (3 / 4 : ℂ)))
  apply hraw.congr_deriv
  dsimp [manuscriptSaddleQFirstDerivative]
  dsimp only [L, dL]
  ring

theorem hasDerivAt_manuscriptSaddleG0
    {N : ℂ} (hN : N ∈ leanSaddleSector) :
    HasDerivAt manuscriptSaddleG0 (manuscriptG0FirstDerivative N) N := by
  let L := quantitativeSaddleBranch N
  let Q := manuscriptSaddleQ N
  let dL := L / Q
  let dQ := manuscriptSaddleQFirstDerivative N
  have hLne : L ≠ 0 := (quantitativeSaddleBranch_scaled_bounds
    (leanSaddleSector_quantitative hN)).1
  have hQne : Q ≠ 0 := manuscriptSaddleQ_ne_zero hN
  have hL : HasDerivAt quantitativeSaddleBranch dL N := by
    simpa only [L, Q, dL, manuscriptSaddleQ, sectorialSaddleCurvature] using
      hasDerivAt_quantitativeSaddleBranch hN
  have hQ : HasDerivAt manuscriptSaddleQ dQ N := by
    simpa only [dQ] using hasDerivAt_manuscriptSaddleQ hN
  have hlogL : HasDerivAt (fun z => log (quantitativeSaddleBranch z))
      (L⁻¹ * dL) N :=
    (Complex.hasDerivAt_log (Complex.mem_slitPlane_iff.mpr
      (Or.inl (by linarith [quantitativeSaddleBranch_re_gt hN])))).comp N hL
  have hlogQ : HasDerivAt (fun z => log (manuscriptSaddleQ z))
      (Q⁻¹ * dQ) N :=
    (Complex.hasDerivAt_log (Complex.mem_slitPlane_iff.mpr
      (Or.inl (manuscriptSaddleQ_re_pos hN)))).comp N hQ
  have hraw := ((((((hasDerivAt_id' N).add_const 1).mul hlogL).add
    (hL.div_const 4)).sub ((hasDerivAt_id' N).div hL hLne)).sub
      (hlogQ.div_const 2))
  unfold manuscriptSaddleG0
  apply hraw.congr_deriv
  unfold manuscriptG0FirstDerivative manuscriptG0AuxNumerator
  dsimp [dQ, manuscriptSaddleQFirstDerivative]
  dsimp only [L, Q, dL]
  dsimp [L, Q] at hLne hQne ⊢
  field_simp [hLne, hQne]
  unfold manuscriptSaddleQ
  ring

theorem hasDerivAt_manuscriptG0AuxNumerator
    {N : ℂ} (hN : N ∈ leanSaddleSector) :
    HasDerivAt manuscriptG0AuxNumerator
      (let L := quantitativeSaddleBranch N
       let dL := L / manuscriptSaddleQ N
       9 * L ^ 2 * dL -
         4 * (2 * L * dL * N + L ^ 2) -
         6 * L * dL - 4 * (dL * N + L) - 4) N := by
  let L := quantitativeSaddleBranch N
  let dL := L / manuscriptSaddleQ N
  have hL : HasDerivAt quantitativeSaddleBranch dL N := by
    simpa only [L, dL, manuscriptSaddleQ, sectorialSaddleCurvature] using
      hasDerivAt_quantitativeSaddleBranch hN
  unfold manuscriptG0AuxNumerator
  change HasDerivAt
    (fun z => 3 * quantitativeSaddleBranch z ^ 3 -
      4 * quantitativeSaddleBranch z ^ 2 * z -
      3 * quantitativeSaddleBranch z ^ 2 -
      4 * quantitativeSaddleBranch z * z - 4 * z) _ N
  have hraw := ((((((hL.pow 3).const_mul 3).sub
    ((hL.pow 2).mul (hasDerivAt_id' N) |>.const_mul 4)).sub
      ((hL.pow 2).const_mul 3)).sub
        (hL.mul (hasDerivAt_id' N) |>.const_mul 4)).sub
          ((hasDerivAt_id' N).const_mul 4))
  have hraw' : HasDerivAt
      (fun z => 3 * quantitativeSaddleBranch z ^ 3 -
        4 * quantitativeSaddleBranch z ^ 2 * z -
        3 * quantitativeSaddleBranch z ^ 2 -
        4 * quantitativeSaddleBranch z * z - 4 * z) _ N :=
    hraw.congr_of_eventuallyEq (by
      filter_upwards with z
      simp only [Pi.pow_apply, Pi.mul_apply, Pi.sub_apply]
      ring)
  apply hraw'.congr_deriv
  dsimp [L, dL]
  ring

set_option maxHeartbeats 8000000 in
theorem hasDerivAt_manuscriptG0FirstDerivative
    {N : ℂ} (hN : N ∈ leanSaddleSector) :
    HasDerivAt manuscriptG0FirstDerivative (saddleReducedMain h2Terms 2 N) N := by
  let L := quantitativeSaddleBranch N
  let Q := manuscriptSaddleQ N
  let dL := L / Q
  let dQ := manuscriptSaddleQFirstDerivative N
  let A := manuscriptG0AuxNumerator N
  let dA :=
    9 * L ^ 2 * dL - 4 * (2 * L * dL * N + L ^ 2) -
      6 * L * dL - 4 * (dL * N + L) - 4
  have hNne := (leanSaddleSector_quantitative hN).parameter_ne_zero
  have hLne : L ≠ 0 := (quantitativeSaddleBranch_scaled_bounds
    (leanSaddleSector_quantitative hN)).1
  have hQne : Q ≠ 0 := manuscriptSaddleQ_ne_zero hN
  have hBne := manuscriptSaddleB_ne_zero hN
  have hL : HasDerivAt quantitativeSaddleBranch dL N := by
    simpa only [L, Q, dL, manuscriptSaddleQ, sectorialSaddleCurvature] using
      hasDerivAt_quantitativeSaddleBranch hN
  have hQ : HasDerivAt manuscriptSaddleQ dQ N := by
    simpa only [dQ] using hasDerivAt_manuscriptSaddleQ hN
  have hA : HasDerivAt manuscriptG0AuxNumerator dA N := by
    simpa only [L, Q, dL, A, dA] using hasDerivAt_manuscriptG0AuxNumerator hN
  have hlogL : HasDerivAt (fun z => log (quantitativeSaddleBranch z))
      (L⁻¹ * dL) N :=
    (Complex.hasDerivAt_log (Complex.mem_slitPlane_iff.mpr
      (Or.inl (by linarith [quantitativeSaddleBranch_re_gt hN])))).comp N hL
  have hden : HasDerivAt (fun z => 8 * manuscriptSaddleQ z ^ 2)
      (8 * (2 * Q * dQ)) N := by
    have hraw := (hQ.pow 2).const_mul 8
    have hraw' : HasDerivAt (fun z => 8 * manuscriptSaddleQ z ^ 2) _ N :=
      hraw.congr_of_eventuallyEq (by
        filter_upwards with z
        simp only [Pi.pow_apply])
    apply hraw'.congr_deriv
    ring
  have hfrac := hA.div hden (mul_ne_zero (by norm_num) (pow_ne_zero 2 hQne))
  unfold manuscriptG0FirstDerivative
  apply (hlogL.sub hfrac).congr_deriv
  unfold saddleReducedMain
  dsimp [A, dA, dQ, dL, manuscriptG0AuxNumerator, manuscriptSaddleQFirstDerivative]
  rw [manuscriptSaddleQ_scaled hN]
  dsimp [L, Q] at hLne hQne ⊢
  field_simp [hNne, hLne, hBne, hQne]
  unfold manuscriptSaddleB manuscriptSaddleR manuscriptSaddleSigma
  unfold evalBivariateTerms BivariateTerm.eval
  simp only [h2Terms, List.map_cons, List.sum_cons, List.map_nil, List.sum_nil]
  field_simp [hNne, hLne]
  norm_num
  unfold manuscriptSaddleQ
  ring

theorem iteratedDeriv_two_manuscriptSaddleG0
    {N : ℂ} (hN : N ∈ leanSaddleSector) :
    iteratedDeriv 2 manuscriptSaddleG0 N = saddleReducedMain h2Terms 2 N := by
  rw [show 2 = 1 + 1 by norm_num, iteratedDeriv_succ, iteratedDeriv_one]
  have heq : deriv manuscriptSaddleG0 =ᶠ[nhds N] manuscriptG0FirstDerivative := by
    filter_upwards [isOpen_leanSaddleSector.mem_nhds hN] with z hz
    exact (hasDerivAt_manuscriptSaddleG0 hz).deriv
  rw [heq.deriv_eq, (hasDerivAt_manuscriptG0FirstDerivative hN).deriv]

theorem iteratedDeriv_three_manuscriptSaddleG0
    {N : ℂ} (hN : N ∈ leanSaddleSector) :
    iteratedDeriv 3 manuscriptSaddleG0 N = saddleReducedMain h3Terms 3 N := by
  rw [show 3 = 2 + 1 by norm_num, iteratedDeriv_succ]
  have heq : iteratedDeriv 2 manuscriptSaddleG0 =ᶠ[nhds N]
      saddleReducedMain h2Terms 2 := by
    filter_upwards [isOpen_leanSaddleSector.mem_nhds hN] with z hz
    exact iteratedDeriv_two_manuscriptSaddleG0 hz
  rw [heq.deriv_eq, (saddleReducedMain_step_two hN).deriv]

theorem iteratedDeriv_four_manuscriptSaddleG0
    {N : ℂ} (hN : N ∈ leanSaddleSector) :
    iteratedDeriv 4 manuscriptSaddleG0 N = saddleReducedMain h4Terms 4 N := by
  rw [show 4 = 3 + 1 by norm_num, iteratedDeriv_succ]
  have heq : iteratedDeriv 3 manuscriptSaddleG0 =ᶠ[nhds N]
      saddleReducedMain h3Terms 3 := by
    filter_upwards [isOpen_leanSaddleSector.mem_nhds hN] with z hz
    exact iteratedDeriv_three_manuscriptSaddleG0 hz
  rw [heq.deriv_eq, (saddleReducedMain_step_three hN).deriv]

theorem iteratedDeriv_five_manuscriptSaddleG0
    {N : ℂ} (hN : N ∈ leanSaddleSector) :
    iteratedDeriv 5 manuscriptSaddleG0 N = saddleReducedMain h5Terms 5 N := by
  rw [show 5 = 4 + 1 by norm_num, iteratedDeriv_succ]
  have heq : iteratedDeriv 4 manuscriptSaddleG0 =ᶠ[nhds N]
      saddleReducedMain h4Terms 4 := by
    filter_upwards [isOpen_leanSaddleSector.mem_nhds hN] with z hz
    exact iteratedDeriv_four_manuscriptSaddleG0 hz
  rw [heq.deriv_eq, (saddleReducedMain_step_four hN).deriv]

theorem iteratedDeriv_six_manuscriptSaddleG0
    {N : ℂ} (hN : N ∈ leanSaddleSector) :
    iteratedDeriv 6 manuscriptSaddleG0 N = saddleReducedMain h6Terms 6 N := by
  rw [show 6 = 5 + 1 by norm_num, iteratedDeriv_succ]
  have heq : iteratedDeriv 5 manuscriptSaddleG0 =ᶠ[nhds N]
      saddleReducedMain h5Terms 5 := by
    filter_upwards [isOpen_leanSaddleSector.mem_nhds hN] with z hz
    exact iteratedDeriv_five_manuscriptSaddleG0 hz
  rw [heq.deriv_eq, (saddleReducedMain_step_five hN).deriv]

theorem saddleReducedMain_h2_eq
    (N : ℂ) : saddleReducedMain h2Terms 2 N = manuscriptSaddleMainTwo N := by
  unfold saddleReducedMain manuscriptSaddleMainTwo saddleH2 h2Numerator
    h2ReducedDenominator manuscriptSaddleB
  norm_num only [Nat.reduceMul, Nat.reduceSub]
  simp only [div_eq_mul_inv, mul_inv_rev]
  ring

theorem saddleReducedMain_h3_eq
    (N : ℂ) : saddleReducedMain h3Terms 3 N = manuscriptSaddleMainThree N := by
  unfold saddleReducedMain manuscriptSaddleMainThree saddleH3 h3Numerator
    h3ReducedDenominator manuscriptSaddleB
  norm_num only [Nat.reduceMul, Nat.reduceSub]
  simp only [div_eq_mul_inv, mul_inv_rev]
  ring

theorem saddleReducedMain_h4_eq
    (N : ℂ) : saddleReducedMain h4Terms 4 N = manuscriptSaddleMainFour N := by
  unfold saddleReducedMain manuscriptSaddleMainFour saddleH4 h4Numerator
    h4ReducedDenominator manuscriptSaddleB
  norm_num only [Nat.reduceMul, Nat.reduceSub]
  simp only [div_eq_mul_inv, mul_inv_rev]
  ring

theorem saddleReducedMain_h5_eq
    (N : ℂ) : saddleReducedMain h5Terms 5 N = manuscriptSaddleMainFive N := by
  unfold saddleReducedMain manuscriptSaddleMainFive saddleH5 h5Numerator
    h5ReducedDenominator manuscriptSaddleB
  norm_num only [Nat.reduceMul, Nat.reduceSub]
  simp only [div_eq_mul_inv, mul_inv_rev]
  ring

theorem saddleReducedMain_h6_eq
    (N : ℂ) : saddleReducedMain h6Terms 6 N = manuscriptSaddleMainSix N := by
  unfold saddleReducedMain manuscriptSaddleMainSix saddleH6 h6Numerator
    h6ReducedDenominator manuscriptSaddleB
  norm_num only [Nat.reduceMul, Nat.reduceSub]
  simp only [div_eq_mul_inv, mul_inv_rev]
  ring

/-- Kernel producer for all four lower symbolic identities formerly supplied
through the CAS interface. -/
theorem manuscriptG0LowerIdentification_of_mem_sector
    {N : ℂ} (hN : N ∈ leanSaddleSector) :
    ManuscriptG0LowerIdentification N where
  orderTwo := (iteratedDeriv_two_manuscriptSaddleG0 hN).trans
    (saddleReducedMain_h2_eq N)
  orderThree := (iteratedDeriv_three_manuscriptSaddleG0 hN).trans
    (saddleReducedMain_h3_eq N)
  orderFour := (iteratedDeriv_four_manuscriptSaddleG0 hN).trans
    (saddleReducedMain_h4_eq N)
  orderFive := (iteratedDeriv_five_manuscriptSaddleG0 hN).trans
    (saddleReducedMain_h5_eq N)

/-- Kernel producer for the sixth symbolic identity formerly supplied through
the CAS interface. -/
theorem manuscriptG0SixthIdentification_of_mem_sector
    {N : ℂ} (hN : N ∈ leanSaddleSector) :
    ManuscriptG0SixthIdentification N where
  exact_value := (iteratedDeriv_six_manuscriptSaddleG0 hN).trans
    (saddleReducedMain_h6_eq N)

end

end Zeta23.Research.JensenWedge
