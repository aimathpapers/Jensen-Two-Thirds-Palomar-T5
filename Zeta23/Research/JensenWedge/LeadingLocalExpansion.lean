import Zeta23.Research.JensenWedge.LeadingGaussianMoments
import Mathlib.Analysis.Calculus.TaylorIntegral

/-!
# Cubic Taylor expansion on the legal horizontal saddle segment

This module isolates the local analytic step in T3.  It first proves a
vector-valued cubic Taylor formula with an explicit integral remainder, then
instantiates it for the published logarithmic integrand on the horizontal
segment through the concrete saddle.  The segment is kept inside the right
half-plane, so the principal logarithm never meets its cut.
-/

namespace Zeta23.Research.JensenWedge

open Complex Filter MeasureTheory Set Topology
open scoped Interval

noncomputable section

attribute [local instance 1100] NormedSpace.complexToReal

/-- Cubic Taylor's formula with an integral fourth-derivative remainder,
assuming regularity only on the segment that is actually integrated. -/
theorem cubicTaylorIntegralOnSegment
    (f : ℝ → ℂ) (x y : ℝ)
    (hf : ∀ t ∈ Icc (0 : ℝ) 1, ContDiffAt ℝ 4 f (x + t * y)) :
    f (x + y) =
      f x + y • iteratedDeriv 1 f x + (y ^ 2 / 2) • iteratedDeriv 2 f x +
        (y ^ 3 / 6) • iteratedDeriv 3 f x +
        (1 / 6 : ℝ) • ∫ t in 0..1, ((1 - t) ^ 3 * y ^ 4) •
          iteratedDeriv 4 f (x + t * y) := by
  have h := map_add_eq_sum_add_integral_iteratedFDeriv
    (f := f) (x := x) (y := y) (n := 3)
    (fun t ht => hf t ht)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add,
    Nat.factorial_zero, Nat.factorial_succ, Nat.cast_one, inv_one,
    iteratedFDeriv_apply_eq_iteratedDeriv_mul_prod, Finset.prod_const,
    Finset.card_univ, Fintype.card_fin, smul_smul, smul_eq_mul] at h
  convert h using 1 <;> norm_num <;> ring

/-- Global-regularity wrapper around `cubicTaylorIntegralOnSegment`. -/
theorem cubicTaylorIntegral
    (f : ℝ → ℂ) (hf : ContDiff ℝ 4 f) (x y : ℝ) :
    f (x + y) =
      f x + y • iteratedDeriv 1 f x + (y ^ 2 / 2) • iteratedDeriv 2 f x +
        (y ^ 3 / 6) • iteratedDeriv 3 f x +
        (1 / 6 : ℝ) • ∫ t in 0..1, ((1 - t) ^ 3 * y ^ 4) •
          iteratedDeriv 4 f (x + t * y) :=
  cubicTaylorIntegralOnSegment f x y fun _ _ => hf.contDiffAt

/-- The explicit fourth-derivative remainder used by `cubicTaylorIntegral`. -/
def cubicTaylorRemainder (f : ℝ → ℂ) (x y : ℝ) : ℂ :=
  (1 / 6 : ℝ) • ∫ t in 0..1, ((1 - t) ^ 3 * y ^ 4) •
    iteratedDeriv 4 f (x + t * y)

/-- A fail-closed norm bound for the cubic Taylor remainder.  The constant is
deliberately coarse: retaining the weight only improves the factor `1/6` to
`1/24`, and the analytic application does not need that sharpening. -/
theorem norm_cubicTaylorRemainder_le
    (f : ℝ → ℂ) (x y C : ℝ)
    (hbound : ∀ t ∈ Icc (0 : ℝ) 1,
      ‖iteratedDeriv 4 f (x + t * y)‖ ≤ C) :
    ‖cubicTaylorRemainder f x y‖ ≤ C * |y| ^ 4 / 6 := by
  have hint : ‖∫ t in (0 : ℝ)..1, ((1 - t) ^ 3 * y ^ 4) •
      iteratedDeriv 4 f (x + t * y)‖ ≤ |y| ^ 4 * C := by
    calc
      ‖∫ t in (0 : ℝ)..1, ((1 - t) ^ 3 * y ^ 4) •
          iteratedDeriv 4 f (x + t * y)‖ ≤ (|y| ^ 4 * C) * |1 - 0| := by
        apply intervalIntegral.norm_integral_le_of_norm_le_const
        intro t ht
        have ht' : t ∈ Icc (0 : ℝ) 1 := by
          rw [uIoc_of_le zero_le_one] at ht
          exact ⟨ht.1.le, ht.2⟩
        rw [norm_smul, Real.norm_eq_abs, abs_mul, abs_pow,
          abs_of_nonneg (sub_nonneg.mpr ht'.2), abs_pow]
        have hcube : (1 - t) ^ 3 ≤ 1 := by
          simpa using pow_le_pow_left₀ (sub_nonneg.mpr ht'.2)
            (by linarith [ht'.1] : 1 - t ≤ 1) 3
        calc
          (1 - t) ^ 3 * |y| ^ 4 * ‖iteratedDeriv 4 f (x + t * y)‖ ≤
              1 * |y| ^ 4 * C := by
            gcongr
            exact hbound t ht'
          _ = |y| ^ 4 * C := by ring
      _ = |y| ^ 4 * C := by norm_num
  rw [cubicTaylorRemainder, norm_smul, Real.norm_eq_abs,
    abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 6)]
  calc
    (1 / 6 : ℝ) * ‖∫ t in (0 : ℝ)..1, ((1 - t) ^ 3 * y ^ 4) •
        iteratedDeriv 4 f (x + t * y)‖ ≤ (1 / 6 : ℝ) * (|y| ^ 4 * C) := by
      gcongr
    _ = C * |y| ^ 4 / 6 := by ring

def leadingHorizontalLog (s L : ℂ) (r : ℝ) : ℂ :=
  leadingLogIntegrand s (L + r)

def leadingHorizontalD1 (s L : ℂ) (r : ℝ) : ℂ :=
  leadingLogD1 s (L + r)

def leadingHorizontalD2 (s L : ℂ) (r : ℝ) : ℂ :=
  leadingLogD2 s (L + r)

def leadingHorizontalD3 (s L : ℂ) (r : ℝ) : ℂ :=
  leadingLogD3 s (L + r)

def leadingHorizontalD4 (s L : ℂ) (r : ℝ) : ℂ :=
  leadingLogD4 s (L + r)

theorem hasDerivAt_leadingHorizontalLog
    {s L : ℂ} {r : ℝ} (hr : 0 < (L + r).re) :
    HasDerivAt (leadingHorizontalLog s L) (leadingHorizontalD1 s L r) r := by
  have houter := hasDerivAt_leadingLogIntegrand (s := s)
    (u := L + (r : ℂ)) (Or.inl hr)
  change HasDerivAt (fun y : ℝ => leadingLogIntegrand s (L + (y : ℂ)))
    (leadingLogD1 s (L + (r : ℂ))) r
  simpa using (HasDerivAt.comp_const_add L (r : ℂ) houter).comp_ofReal

theorem hasDerivAt_leadingHorizontalD1
    {s L : ℂ} {r : ℝ} (hr : 0 < (L + r).re) :
    HasDerivAt (leadingHorizontalD1 s L) (leadingHorizontalD2 s L r) r := by
  have hne : L + (r : ℂ) ≠ 0 := by
    intro hzero
    rw [hzero] at hr
    norm_num at hr
  have houter := hasDerivAt_leadingLogD1 (s := s) (u := L + (r : ℂ)) hne
  change HasDerivAt (fun y : ℝ => leadingLogD1 s (L + (y : ℂ)))
    (leadingLogD2 s (L + (r : ℂ))) r
  simpa using (HasDerivAt.comp_const_add L (r : ℂ) houter).comp_ofReal

theorem hasDerivAt_leadingHorizontalD2
    {s L : ℂ} {r : ℝ} (hr : 0 < (L + r).re) :
    HasDerivAt (leadingHorizontalD2 s L) (leadingHorizontalD3 s L r) r := by
  have hne : L + (r : ℂ) ≠ 0 := by
    intro hzero
    rw [hzero] at hr
    norm_num at hr
  have houter := hasDerivAt_leadingLogD2 (s := s) (u := L + (r : ℂ)) hne
  change HasDerivAt (fun y : ℝ => leadingLogD2 s (L + (y : ℂ)))
    (leadingLogD3 s (L + (r : ℂ))) r
  simpa using (HasDerivAt.comp_const_add L (r : ℂ) houter).comp_ofReal

theorem hasDerivAt_leadingHorizontalD3
    {s L : ℂ} {r : ℝ} (hr : 0 < (L + r).re) :
    HasDerivAt (leadingHorizontalD3 s L) (leadingHorizontalD4 s L r) r := by
  have hne : L + (r : ℂ) ≠ 0 := by
    intro hzero
    rw [hzero] at hr
    norm_num at hr
  have houter := hasDerivAt_leadingLogD3 (s := s) (u := L + (r : ℂ)) hne
  change HasDerivAt (fun y : ℝ => leadingLogD3 s (L + (y : ℂ)))
    (leadingLogD4 s (L + (r : ℂ))) r
  simpa using (HasDerivAt.comp_const_add L (r : ℂ) houter).comp_ofReal

/-- The published logarithmic integrand is `C^4` along every branch-safe
horizontal point. -/
theorem leadingHorizontalLog_contDiffAt_four
    {s L : ℂ} {r : ℝ} (hr : 0 < (L + r).re) :
    ContDiffAt ℝ 4 (leadingHorizontalLog s L) r := by
  have hlog : ContDiffAt ℂ 4 (fun u : ℂ => log u) (L + (r : ℂ)) :=
    Complex.contDiffAt_log (Or.inl hr)
  have houter : ContDiffAt ℂ 4 (leadingLogIntegrand s) (L + (r : ℂ)) := by
    unfold leadingLogIntegrand
    exact ((contDiffAt_const.mul hlog).add (contDiffAt_id.div_const 4)).sub
      (contDiffAt_const.mul Complex.contDiff_exp.contDiffAt)
  have hofReal : ContDiffAt ℝ 4 (fun x : ℝ => (x : ℂ)) r :=
    Complex.ofRealCLM.contDiff.contDiffAt
  have hinner : ContDiffAt ℝ 4 (fun x : ℝ => L + (x : ℂ)) r :=
    contDiffAt_const.add hofReal
  exact (houter.restrict_scalars ℝ).comp r hinner

/-- At the center of a branch-safe horizontal segment, the first four real
iterated derivatives are exactly the named complex differential tower. -/
theorem leadingHorizontalLog_iteratedDeriv_tower
    {s L : ℂ} (hL : 0 < L.re) :
    iteratedDeriv 1 (leadingHorizontalLog s L) 0 = leadingLogD1 s L ∧
      iteratedDeriv 2 (leadingHorizontalLog s L) 0 = leadingLogD2 s L ∧
      iteratedDeriv 3 (leadingHorizontalLog s L) 0 = leadingLogD3 s L ∧
      iteratedDeriv 4 (leadingHorizontalLog s L) 0 = leadingLogD4 s L := by
  have hpos : ∀ᶠ r : ℝ in 𝓝 0, 0 < (L + r).re := by
    filter_upwards [Ioi_mem_nhds (show -L.re < (0 : ℝ) by linarith)] with r hr
    change -L.re < r at hr
    simp only [add_re, ofReal_re]
    linarith
  have h01 : deriv (leadingHorizontalLog s L) =ᶠ[𝓝 0]
      leadingHorizontalD1 s L := hpos.mono fun _ hr =>
    (hasDerivAt_leadingHorizontalLog hr).deriv
  have h12 : deriv (leadingHorizontalD1 s L) =ᶠ[𝓝 0]
      leadingHorizontalD2 s L := hpos.mono fun _ hr =>
    (hasDerivAt_leadingHorizontalD1 hr).deriv
  have h23 : deriv (leadingHorizontalD2 s L) =ᶠ[𝓝 0]
      leadingHorizontalD3 s L := hpos.mono fun _ hr =>
    (hasDerivAt_leadingHorizontalD2 hr).deriv
  have h34 : deriv (leadingHorizontalD3 s L) =ᶠ[𝓝 0]
      leadingHorizontalD4 s L := hpos.mono fun _ hr =>
    (hasDerivAt_leadingHorizontalD3 hr).deriv
  have h1 : iteratedDeriv 1 (leadingHorizontalLog s L) 0 =
      leadingHorizontalD1 s L 0 := by
    rw [show 1 = 0 + 1 by norm_num, iteratedDeriv_succ', iteratedDeriv_zero]
    exact h01.eq_of_nhds
  have h2 : iteratedDeriv 2 (leadingHorizontalLog s L) 0 =
      leadingHorizontalD2 s L 0 := by
    rw [show 2 = 1 + 1 by norm_num, iteratedDeriv_succ']
    calc
      iteratedDeriv 1 (deriv (leadingHorizontalLog s L)) 0 =
          iteratedDeriv 1 (leadingHorizontalD1 s L) 0 :=
        h01.iteratedDeriv_eq 1
      _ = deriv (leadingHorizontalD1 s L) 0 := by
        rw [show 1 = 0 + 1 by norm_num, iteratedDeriv_succ', iteratedDeriv_zero]
      _ = leadingHorizontalD2 s L 0 := h12.eq_of_nhds
  have h3 : iteratedDeriv 3 (leadingHorizontalLog s L) 0 =
      leadingHorizontalD3 s L 0 := by
    rw [show 3 = 2 + 1 by norm_num, iteratedDeriv_succ']
    calc
      iteratedDeriv 2 (deriv (leadingHorizontalLog s L)) 0 =
          iteratedDeriv 2 (leadingHorizontalD1 s L) 0 :=
        h01.iteratedDeriv_eq 2
      _ = iteratedDeriv 1 (deriv (leadingHorizontalD1 s L)) 0 := by
        rw [show 2 = 1 + 1 by norm_num, iteratedDeriv_succ']
      _ = iteratedDeriv 1 (leadingHorizontalD2 s L) 0 :=
        h12.iteratedDeriv_eq 1
      _ = deriv (leadingHorizontalD2 s L) 0 := by
        rw [show 1 = 0 + 1 by norm_num, iteratedDeriv_succ', iteratedDeriv_zero]
      _ = leadingHorizontalD3 s L 0 := h23.eq_of_nhds
  have h4 : iteratedDeriv 4 (leadingHorizontalLog s L) 0 =
      leadingHorizontalD4 s L 0 := by
    rw [show 4 = 3 + 1 by norm_num, iteratedDeriv_succ']
    calc
      iteratedDeriv 3 (deriv (leadingHorizontalLog s L)) 0 =
          iteratedDeriv 3 (leadingHorizontalD1 s L) 0 :=
        h01.iteratedDeriv_eq 3
      _ = iteratedDeriv 2 (deriv (leadingHorizontalD1 s L)) 0 := by
        rw [show 3 = 2 + 1 by norm_num, iteratedDeriv_succ']
      _ = iteratedDeriv 2 (leadingHorizontalD2 s L) 0 :=
        h12.iteratedDeriv_eq 2
      _ = iteratedDeriv 1 (deriv (leadingHorizontalD2 s L)) 0 := by
        rw [show 2 = 1 + 1 by norm_num, iteratedDeriv_succ']
      _ = iteratedDeriv 1 (leadingHorizontalD3 s L) 0 :=
        h23.iteratedDeriv_eq 1
      _ = deriv (leadingHorizontalD3 s L) 0 := by
        rw [show 1 = 0 + 1 by norm_num, iteratedDeriv_succ', iteratedDeriv_zero]
      _ = leadingHorizontalD4 s L 0 := h34.eq_of_nhds
  simpa [leadingHorizontalD1, leadingHorizontalD2, leadingHorizontalD3,
    leadingHorizontalD4] using And.intro h1 (And.intro h2 (And.intro h3 h4))

theorem leadingHorizontalLog_iteratedDeriv_four
    {s L : ℂ} {r : ℝ} (hr : 0 < (L + r).re) :
    iteratedDeriv 4 (leadingHorizontalLog s L) r = leadingLogD4 s (L + r) := by
  have htower := (leadingHorizontalLog_iteratedDeriv_tower
    (s := s) (L := L + (r : ℂ)) hr).2.2.2
  have hfun : (fun x : ℝ => leadingHorizontalLog s L (r + x)) =
      leadingHorizontalLog s (L + (r : ℂ)) := by
    funext x
    simp only [leadingHorizontalLog]
    congr 1
    push_cast
    ring
  calc
    iteratedDeriv 4 (leadingHorizontalLog s L) r =
        iteratedDeriv 4 (leadingHorizontalLog s L) (r + 0) := by simp
    _ = iteratedDeriv 4 (fun x : ℝ => leadingHorizontalLog s L (r + x)) 0 := by
      rw [iteratedDeriv_comp_const_add]
    _ = iteratedDeriv 4 (leadingHorizontalLog s (L + (r : ℂ))) 0 := by rw [hfun]
    _ = leadingLogD4 s (L + r) := htower

def leadingCubicCoefficient (s L : ℂ) : ℂ :=
  leadingLogD3 s L / 6

def leadingLocalRemainder (s L : ℂ) (r : ℝ) : ℂ :=
  cubicTaylorRemainder (leadingHorizontalLog s L) 0 r

/-- Exact paper expansion on the legal local horizontal segment. -/
theorem leadingLocalExpansion_exact
    {s L : ℂ} (hL : 1 < L.re)
    (hroot : sectorialSaddleEquation s L = 0)
    {r : ℝ} (hr : |r| ≤ 1 / 10) :
    leadingLogIntegrand s (L + r) - leadingLogIntegrand s L =
      (r : ℂ) - leadingCurvature s L * (r : ℂ) ^ 2 / 2 +
        leadingCubicCoefficient s L * (r : ℂ) ^ 3 +
        leadingLocalRemainder s L r := by
  have hsegment : ∀ t ∈ Icc (0 : ℝ) 1, 0 < (L + t * r).re := by
    intro t ht
    have htAbs : |t| ≤ 1 := by rw [abs_of_nonneg ht.1]; exact ht.2
    have htr : |t * r| ≤ 1 / 10 := by
      rw [abs_mul]
      calc
        |t| * |r| ≤ 1 * (1 / 10) := mul_le_mul htAbs hr (abs_nonneg _) zero_le_one
        _ = 1 / 10 := by ring
    simp only [add_re, mul_re, ofReal_re, ofReal_im, zero_mul, sub_zero]
    linarith [neg_le_of_abs_le htr]
  have hcont : ∀ t ∈ Icc (0 : ℝ) 1,
      ContDiffAt ℝ 4 (leadingHorizontalLog s L) (0 + t * r) := by
    intro t ht
    simpa using leadingHorizontalLog_contDiffAt_four (hsegment t ht)
  have htaylor := cubicTaylorIntegralOnSegment
    (leadingHorizontalLog s L) 0 r hcont
  have htower := leadingHorizontalLog_iteratedDeriv_tower (s := s) (L := L)
    (lt_trans zero_lt_one hL)
  have hD1 := leadingLogD1_at_saddle (s := s) (L := L)
    (by intro hzero; rw [hzero] at hL; norm_num at hL) hroot
  have hD2 := leadingLogD2_at_saddle (s := s) (L := L)
    (by intro hzero; rw [hzero] at hL; norm_num at hL) hroot
  rw [htower.1, htower.2.1, htower.2.2.1, hD1, hD2] at htaylor
  simp only [leadingHorizontalLog, zero_add, ofReal_zero, add_zero] at htaylor
  have htaylor' :
      leadingLogIntegrand s (L + r) =
        leadingLogIntegrand s L + r • (1 : ℂ) +
          (r ^ 2 / 2) • (-leadingCurvature s L) +
          (r ^ 3 / 6) • leadingLogD3 s L +
          leadingLocalRemainder s L r := by
    simpa only [leadingLocalRemainder, cubicTaylorRemainder, zero_add] using htaylor
  rw [htaylor']
  simp only [leadingCubicCoefficient, Complex.real_smul]
  push_cast
  ring

/-- The local fourth-derivative bound is consumed through the exact integral
remainder, with no appeal to an unnamed Taylor constant. -/
theorem norm_leadingLocalRemainder_le
    {s L : ℂ} {r C : ℝ}
    (hsegment : ∀ t ∈ Icc (0 : ℝ) 1, 0 < (L + t * r).re)
    (hbound : ∀ t ∈ Icc (0 : ℝ) 1, ‖leadingLogD4 s (L + t * r)‖ ≤ C) :
    ‖leadingLocalRemainder s L r‖ ≤ C * |r| ^ 4 / 6 := by
  apply norm_cubicTaylorRemainder_le
  intro t ht
  simp only [zero_add]
  rw [leadingHorizontalLog_iteratedDeriv_four (s := s) (L := L) (r := t * r)
    (by simpa only [ofReal_mul] using hsegment t ht)]
  simpa only [ofReal_mul] using hbound t ht

/-- The saddle ratio is bounded below absolutely and above by the concrete
curvature.  This is the bridge from derivative formulas written with `s/L`
to the Gaussian scale `K`. -/
theorem quantitativeSaddleBranch_ratio_norm_bounds
    {s : ℂ} (hs : s ∈ leanSaddleSector) :
    1 ≤ ‖s / quantitativeSaddleBranch s‖ ∧
      ‖s / quantitativeSaddleBranch s‖ ≤
        2 * ‖leadingCurvature s (quantitativeSaddleBranch s)‖ := by
  let L : ℂ := quantitativeSaddleBranch s
  let B : ℂ := s / L
  let a : ℂ := 1 + 1 / L - (3 / 4) * (L / s)
  have hinput := leanSaddleSector_quantitative hs
  have hbounds := quantitativeSaddleBranch_scaled_bounds hinput
  have hLne : L ≠ 0 := hbounds.1
  have hsne : s ≠ 0 := hinput.parameter_ne_zero
  have haDiff : a - 1 = 1 / L - (3 / 4) * (L / s) := by
    simp only [a]
    ring
  have haNorm : ‖a - 1‖ ≤ 1 / 4 := by
    rw [haDiff]
    calc
      ‖(1 : ℂ) / L - (3 / 4) * (L / s)‖ ≤
          ‖(1 : ℂ) / L‖ + ‖(3 / 4 : ℂ) * (L / s)‖ := norm_sub_le _ _
      _ = ‖(1 : ℂ) / L‖ + (3 / 4 : ℝ) * ‖L / s‖ := by
        rw [norm_mul]
        norm_num
      _ ≤ 7 / 50 + (3 / 4 : ℝ) * (7 / 50) := by
        gcongr
        · exact hbounds.2.1
        · exact hbounds.2.2
      _ ≤ 1 / 4 := by norm_num
  have haLower : 3 / 4 ≤ ‖a‖ := by
    have hone : ‖(1 : ℂ)‖ ≤ ‖a‖ + ‖a - 1‖ := by
      calc
        ‖(1 : ℂ)‖ = ‖a - (a - 1)‖ := by ring_nf
        _ ≤ ‖a‖ + ‖a - 1‖ := norm_sub_le _ _
    norm_num at hone
    linarith
  have hBprod : B * (L / s) = 1 := by
    simp only [B]
    field_simp [hsne, hLne]
  have hBone : 1 ≤ ‖B‖ := by
    have hprodNorm : (1 : ℝ) = ‖B‖ * ‖L / s‖ := by
      calc
        (1 : ℝ) = ‖(1 : ℂ)‖ := by norm_num
        _ = ‖B * (L / s)‖ := by rw [hBprod]
        _ = ‖B‖ * ‖L / s‖ := norm_mul _ _
    have hupper : ‖B‖ * ‖L / s‖ ≤ ‖B‖ * (7 / 50) := by
      gcongr
      exact hbounds.2.2
    nlinarith [norm_nonneg B]
  have hfactor := leadingCurvature_factor hsne hLne
  change 1 ≤ ‖B‖ ∧ ‖B‖ ≤ 2 * ‖leadingCurvature s L‖
  constructor
  · exact hBone
  · rw [hfactor, norm_mul]
    change ‖B‖ ≤ 2 * (‖B‖ * ‖a‖)
    nlinarith [norm_nonneg B]

/-- Concrete fourth-derivative control on the full local window. -/
theorem quantitativeSaddleBranch_leadingLogD4_norm_le
    {s : ℂ} (hs : s ∈ leanSaddleSector) {r : ℝ} (hr : |r| ≤ 1 / 10) :
    ‖leadingLogD4 s (quantitativeSaddleBranch s + r)‖ ≤
      32 * ‖leadingCurvature s (quantitativeSaddleBranch s)‖ := by
  let L : ℂ := quantitativeSaddleBranch s
  let B : ℂ := s / L
  let u : ℂ := L + r
  have hinput := leanSaddleSector_quantitative hs
  have hbounds := quantitativeSaddleBranch_scaled_bounds hinput
  have hLne : L ≠ 0 := hbounds.1
  have hsne : s ≠ 0 := hinput.parameter_ne_zero
  have hroot : sectorialSaddleEquation s L = 0 :=
    (quantitativeSaddleBranch_spec hinput).2.1
  have hmap : s = L * ((Real.pi : ℂ) * exp L + 3 / 4) := by
    unfold sectorialSaddleEquation saddleParameterMap at hroot
    exact (eq_of_sub_eq_zero hroot).symm
  have hB : B = (Real.pi : ℂ) * exp L + 3 / 4 := by
    simp only [B]
    rw [hmap]
    field_simp [hLne]
  have hratio := quantitativeSaddleBranch_ratio_norm_bounds hs
  change ‖leadingLogD4 s u‖ ≤
    32 * ‖leadingCurvature s L‖
  have hLre : 1000 < L.re := quantitativeSaddleBranch_re_gt hs
  have huRe : 999 < u.re := by
    simp only [u, add_re, ofReal_re]
    linarith [neg_le_of_abs_le hr]
  have huNorm : 1 ≤ ‖u‖ := by
    have hre := Complex.abs_re_le_norm u
    have : u.re ≤ ‖u‖ := le_trans (le_abs_self _) hre
    linarith
  have hLnorm : ‖L‖ ≤ 2 * ‖u‖ := by
    calc
      ‖L‖ = ‖u - (r : ℂ)‖ := by
        congr 1
        simp only [u]
        push_cast
        ring
      _ ≤ ‖u‖ + ‖(r : ℂ)‖ := norm_sub_le _ _
      _ = ‖u‖ + |r| := by rw [norm_real, Real.norm_eq_abs]
      _ ≤ 2 * ‖u‖ := by linarith
  have huPow : ‖u‖ ≤ ‖u‖ ^ 4 := by
    have h2 : ‖u‖ ≤ ‖u‖ ^ 2 := by
      nlinarith [mul_nonneg (sub_nonneg.mpr huNorm) (norm_nonneg u)]
    have h2one : 1 ≤ ‖u‖ ^ 2 := by nlinarith [sq_nonneg (‖u‖ - 1)]
    have h4 : ‖u‖ ^ 2 ≤ ‖u‖ ^ 4 := by
      nlinarith [mul_nonneg (sub_nonneg.mpr h2one) (sq_nonneg ‖u‖)]
    exact h2.trans h4
  have huNe : ‖u‖ ^ 4 ≠ 0 := pow_ne_zero _ (ne_of_gt (lt_of_lt_of_le zero_lt_one huNorm))
  have hsBL : s = B * L := by
    simp only [B]
    field_simp [hLne]
  have hfirst : ‖(-6 : ℂ) * s / u ^ 4‖ ≤ 12 * ‖B‖ := by
    rw [norm_div, norm_mul, norm_pow, norm_neg, norm_ofNat, hsBL, norm_mul]
    have hnum : 6 * (‖B‖ * ‖L‖) ≤ 6 * (‖B‖ * (2 * ‖u‖ ^ 4)) := by
      gcongr
      exact hLnorm.trans (mul_le_mul_of_nonneg_left huPow (by norm_num))
    calc
      6 * (‖B‖ * ‖L‖) / ‖u‖ ^ 4 ≤
          6 * (‖B‖ * (2 * ‖u‖ ^ 4)) / ‖u‖ ^ 4 := by gcongr
      _ = 12 * ‖B‖ := by field_simp [huNe]; ring
  have hexpTwo : Real.exp r ≤ 2 := by
    have hrle : r ≤ 1 / 10 := le_trans (le_abs_self r) hr
    have hmono : Real.exp r ≤ Real.exp (1 / 10) := Real.exp_le_exp.mpr hrle
    have hbound := Real.exp_bound_div_one_sub_of_interval
      (x := (1 / 10 : ℝ)) (by norm_num) (by norm_num)
    norm_num at hbound
    linarith
  have hpiL : (Real.pi : ℂ) * exp L = B - 3 / 4 := by
    rw [hB]
    ring
  have hsecond : ‖(Real.pi : ℂ) * exp u‖ ≤ 4 * ‖B‖ := by
    have hexpAdd : exp u = exp L * exp (r : ℂ) := by
      simp only [u]
      rw [exp_add]
    rw [hexpAdd, ← mul_assoc, hpiL, norm_mul, norm_exp]
    simp only [ofReal_re]
    calc
      ‖B - 3 / 4‖ * Real.exp r ≤ (‖B‖ + 3 / 4) * Real.exp r := by
        gcongr
        exact (norm_sub_le B (3 / 4)).trans_eq (by norm_num)
      _ ≤ (‖B‖ + 3 / 4) * 2 := by gcongr
      _ ≤ 4 * ‖B‖ := by nlinarith [hratio.1]
  calc
    ‖leadingLogD4 s u‖ = ‖(-6 : ℂ) * s / u ^ 4 - (Real.pi : ℂ) * exp u‖ := by
      rfl
    _ ≤ ‖(-6 : ℂ) * s / u ^ 4‖ + ‖(Real.pi : ℂ) * exp u‖ := norm_sub_le _ _
    _ ≤ 12 * ‖B‖ + 4 * ‖B‖ := add_le_add hfirst hsecond
    _ ≤ 32 * ‖leadingCurvature s L‖ := by nlinarith [hratio.2]

theorem quantitativeSaddleBranch_localExpansion_exact
    {s : ℂ} (hs : s ∈ leanSaddleSector) {r : ℝ} (hr : |r| ≤ 1 / 10) :
    leadingLogIntegrand s (quantitativeSaddleBranch s + r) -
        leadingLogIntegrand s (quantitativeSaddleBranch s) =
      (r : ℂ) - leadingCurvature s (quantitativeSaddleBranch s) * (r : ℂ) ^ 2 / 2 +
        leadingCubicCoefficient s (quantitativeSaddleBranch s) * (r : ℂ) ^ 3 +
        leadingLocalRemainder s (quantitativeSaddleBranch s) r := by
  exact leadingLocalExpansion_exact (s := s) (L := quantitativeSaddleBranch s)
    (by linarith [quantitativeSaddleBranch_re_gt hs])
    (quantitativeSaddleBranch_spec (leanSaddleSector_quantitative hs)).2.1 hr

/-- Fully concrete local Taylor remainder on the selected sectorial branch. -/
theorem quantitativeSaddleBranch_localRemainder_norm_le
    {s : ℂ} (hs : s ∈ leanSaddleSector) {r : ℝ} (hr : |r| ≤ 1 / 10) :
    ‖leadingLocalRemainder s (quantitativeSaddleBranch s) r‖ ≤
      6 * ‖leadingCurvature s (quantitativeSaddleBranch s)‖ * |r| ^ 4 := by
  have hsegment : ∀ t ∈ Icc (0 : ℝ) 1,
      0 < (quantitativeSaddleBranch s + t * r).re := by
    intro t ht
    have htAbs : |t| ≤ 1 := by rw [abs_of_nonneg ht.1]; exact ht.2
    have htr : |t * r| ≤ 1 / 10 := by
      rw [abs_mul]
      calc
        |t| * |r| ≤ 1 * (1 / 10) := mul_le_mul htAbs hr (abs_nonneg _) zero_le_one
        _ = 1 / 10 := by ring
    have hLre := quantitativeSaddleBranch_re_gt hs
    simp only [add_re, mul_re, ofReal_re, ofReal_im, zero_mul, sub_zero]
    linarith [neg_le_of_abs_le htr]
  have hD4 : ∀ t ∈ Icc (0 : ℝ) 1,
      ‖leadingLogD4 s (quantitativeSaddleBranch s + t * r)‖ ≤
        32 * ‖leadingCurvature s (quantitativeSaddleBranch s)‖ := by
    intro t ht
    have htAbs : |t| ≤ 1 := by rw [abs_of_nonneg ht.1]; exact ht.2
    have htr : |t * r| ≤ 1 / 10 := by
      rw [abs_mul]
      calc
        |t| * |r| ≤ 1 * |r| := mul_le_mul_of_nonneg_right htAbs (abs_nonneg r)
        _ = |r| := one_mul _
        _ ≤ 1 / 10 := hr
    simpa only [ofReal_mul] using
      (quantitativeSaddleBranch_leadingLogD4_norm_le hs htr)
  have hraw :
      ‖leadingLocalRemainder s (quantitativeSaddleBranch s) r‖ ≤
        (32 * ‖leadingCurvature s (quantitativeSaddleBranch s)‖) * |r| ^ 4 / 6 :=
    norm_leadingLocalRemainder_le hsegment hD4
  calc
    ‖leadingLocalRemainder s (quantitativeSaddleBranch s) r‖ ≤
        (32 * ‖leadingCurvature s (quantitativeSaddleBranch s)‖) * |r| ^ 4 / 6 := hraw
    _ ≤ 6 * ‖leadingCurvature s (quantitativeSaddleBranch s)‖ * |r| ^ 4 := by
      have hnonneg :
          0 ≤ ‖leadingCurvature s (quantitativeSaddleBranch s)‖ * |r| ^ 4 :=
        mul_nonneg (norm_nonneg _) (pow_nonneg (abs_nonneg _) _)
      nlinarith

end

end Zeta23.Research.JensenWedge
