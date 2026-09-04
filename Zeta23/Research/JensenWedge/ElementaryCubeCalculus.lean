import Zeta23.Research.JensenWedge.ElementaryCubeBounds

/-!
# Exact elementary cube calculus

This module formalizes the repeated-FTC kernel calculus used by the `C¹`
parameter map.  It deliberately works with exact reciprocal powers and
explicit unit-cube integrals; no truncated symbolic series is used.
-/

namespace Zeta23.Research.JensenWedge

open MeasureTheory Set

/-- The reciprocal-power kernel appearing after repeated finite differences. -/
noncomputable def elementaryCubeKernel {q : ℕ} (p : ℕ) (s z : ℝ) (u : Fin q → ℝ) : ℝ :=
  (cubeDenominator s z u)⁻¹ ^ p

/-- The exact `q`-cube integral with reciprocal exponent `p`. -/
noncomputable def elementaryCubeIntegral (q p : ℕ) (s z : ℝ) : ℝ :=
  ∫ u in unitCube q, elementaryCubeKernel p s z u

/-- The paper's kernel `Phi_q`. -/
noncomputable def elementaryPhi (q : ℕ) (s z : ℝ) : ℝ :=
  elementaryCubeIntegral q q s z

/-- Rising multiplier `(q)_r`. -/
def risingMultiplier (q r : ℕ) : ℕ :=
  ∏ i ∈ Finset.range r, (q + i)

theorem risingMultiplier_zero (q : ℕ) : risingMultiplier q 0 = 1 := by
  simp [risingMultiplier]

theorem risingMultiplier_one (q : ℕ) : risingMultiplier q 1 = q := by
  simp [risingMultiplier]

theorem risingMultiplier_two (q : ℕ) : risingMultiplier q 2 = q * (q + 1) := by
  norm_num [risingMultiplier, Finset.prod_range_succ]

noncomputable def elementaryPhiD1 (q : ℕ) (s z : ℝ) : ℝ :=
  -(q : ℝ) * elementaryCubeIntegral q (q + 1) s z

noncomputable def elementaryPhiD2 (q : ℕ) (s z : ℝ) : ℝ :=
  (q : ℝ) * (q + 1) * elementaryCubeIntegral q (q + 2) s z

theorem isCompact_unitCube (q : ℕ) : IsCompact (unitCube q) := by
  exact isCompact_Icc

theorem measurableSet_unitCube (q : ℕ) : MeasurableSet (unitCube q) := by
  exact measurableSet_Icc

noncomputable def unitIntervalMeasure : Measure ℝ :=
  volume.restrict (Set.Icc (0 : ℝ) 1)

theorem volume_restrict_unitCube_eq_pi (q : ℕ) :
    volume.restrict (unitCube q) = Measure.pi (fun _ : Fin q => unitIntervalMeasure) := by
  rw [unitCube, ← Set.pi_univ_Icc, volume_pi, Measure.restrict_pi_pi]
  rfl

/-- Fubini decomposition of the genuine `(q+1)`-cube, with the zeroth
coordinate integrated first. -/
theorem integral_unitCube_succ
    {q : ℕ} (F : (Fin (q + 1) → ℝ) → ℝ)
    (hF : IntegrableOn F (unitCube (q + 1)) volume) :
    (∫ x in unitCube (q + 1), F x) =
      ∫ t in Set.Icc (0 : ℝ) 1,
        ∫ u in unitCube q, F (Fin.cons t u) := by
  let μ : Measure ℝ := unitIntervalMeasure
  haveI : SigmaFinite μ := by
    dsimp [μ, unitIntervalMeasure]
    infer_instance
  let e : (Fin (q + 1) → ℝ) ≃ᵐ ℝ × (Fin q → ℝ) :=
    MeasurableEquiv.piFinSuccAbove (fun _ : Fin (q + 1) => ℝ) 0
  let g : ℝ × (Fin q → ℝ) → ℝ := fun y => F (e.symm y)
  have hFpi : Integrable F (Measure.pi (fun _ : Fin (q + 1) => μ)) := by
    rw [← volume_restrict_unitCube_eq_pi (q + 1)]
    exact hF
  have hmp : MeasurePreserving e
      (Measure.pi (fun _ : Fin (q + 1) => μ))
      (μ.prod (Measure.pi (fun _ : Fin q => μ))) := by
    exact measurePreserving_piFinSuccAbove (fun _ : Fin (q + 1) => μ) 0
  have hg : Integrable g (μ.prod (Measure.pi (fun _ : Fin q => μ))) := by
    apply (hmp.integrable_comp_emb e.measurableEmbedding).mp
    change Integrable (fun x => g (e x)) (Measure.pi (fun _ : Fin (q + 1) => μ))
    have hge : (fun x => g (e x)) = F := by
      funext x
      simp only [g, e.symm_apply_apply]
    rw [hge]
    exact hFpi
  change (∫ x, F x ∂(volume.restrict (unitCube (q + 1)))) =
    ∫ t, ∫ u, F (Fin.cons t u) ∂(volume.restrict (unitCube q)) ∂μ
  rw [volume_restrict_unitCube_eq_pi (q + 1), volume_restrict_unitCube_eq_pi q]
  calc
    (∫ x, F x ∂Measure.pi (fun _ : Fin (q + 1) => μ)) =
        ∫ y, g y ∂(μ.prod (Measure.pi (fun _ : Fin q => μ))) := by
          have htransport := hmp.integral_comp' g
          have hge : (fun x => g (e x)) = F := by
            funext x
            simp only [g, e.symm_apply_apply]
          rw [hge] at htransport
          exact htransport
    _ = ∫ t, ∫ u, g (t, u) ∂(Measure.pi (fun _ : Fin q => μ)) ∂μ :=
      integral_prod g hg
    _ = ∫ t, ∫ u, F (Fin.cons t u) ∂(Measure.pi (fun _ : Fin q => μ)) ∂μ := by
      congr 1
      funext t
      congr 1
      funext u
      have hecons : e.symm (t, u) = Fin.cons t u := by
        funext i
        refine Fin.cases ?_ ?_ i
        · simp [e]
        · intro j
          simp [e]
      change F (e.symm (t, u)) = F (Fin.cons t u)
      rw [hecons]

/-- Fubini decomposition of the genuine `(q+1)`-cube, with the tail cube
integrated first.  Keeping both orientations explicit avoids silently
identifying iterated integrals without an integrability proof. -/
theorem integral_unitCube_succ_tail
    {q : ℕ} (F : (Fin (q + 1) → ℝ) → ℝ)
    (hF : IntegrableOn F (unitCube (q + 1)) volume) :
    (∫ x in unitCube (q + 1), F x) =
      ∫ u in unitCube q,
        ∫ t in Set.Icc (0 : ℝ) 1, F (Fin.cons t u) := by
  let μ : Measure ℝ := unitIntervalMeasure
  haveI : SigmaFinite μ := by
    dsimp [μ, unitIntervalMeasure]
    infer_instance
  let e : (Fin (q + 1) → ℝ) ≃ᵐ ℝ × (Fin q → ℝ) :=
    MeasurableEquiv.piFinSuccAbove (fun _ : Fin (q + 1) => ℝ) 0
  let g : ℝ × (Fin q → ℝ) → ℝ := fun y => F (e.symm y)
  have hFpi : Integrable F (Measure.pi (fun _ : Fin (q + 1) => μ)) := by
    rw [← volume_restrict_unitCube_eq_pi (q + 1)]
    exact hF
  have hmp : MeasurePreserving e
      (Measure.pi (fun _ : Fin (q + 1) => μ))
      (μ.prod (Measure.pi (fun _ : Fin q => μ))) := by
    exact measurePreserving_piFinSuccAbove (fun _ : Fin (q + 1) => μ) 0
  have hg : Integrable g (μ.prod (Measure.pi (fun _ : Fin q => μ))) := by
    apply (hmp.integrable_comp_emb e.measurableEmbedding).mp
    change Integrable (fun x => g (e x)) (Measure.pi (fun _ : Fin (q + 1) => μ))
    have hge : (fun x => g (e x)) = F := by
      funext x
      simp only [g, e.symm_apply_apply]
    rw [hge]
    exact hFpi
  change (∫ x, F x ∂(volume.restrict (unitCube (q + 1)))) =
    ∫ u, ∫ t, F (Fin.cons t u) ∂μ ∂(volume.restrict (unitCube q))
  rw [volume_restrict_unitCube_eq_pi (q + 1), volume_restrict_unitCube_eq_pi q]
  calc
    (∫ x, F x ∂Measure.pi (fun _ : Fin (q + 1) => μ)) =
        ∫ y, g y ∂(μ.prod (Measure.pi (fun _ : Fin q => μ))) := by
          have htransport := hmp.integral_comp' g
          have hge : (fun x => g (e x)) = F := by
            funext x
            simp only [g, e.symm_apply_apply]
          rw [hge] at htransport
          exact htransport
    _ = ∫ u, ∫ t, g (t, u) ∂μ ∂(Measure.pi (fun _ : Fin q => μ)) :=
      integral_prod_symm g hg
    _ = ∫ u, ∫ t, F (Fin.cons t u) ∂μ ∂(Measure.pi (fun _ : Fin q => μ)) := by
      congr 1
      funext u
      congr 1
      funext t
      have hecons : e.symm (t, u) = Fin.cons t u := by
        funext i
        refine Fin.cases ?_ ?_ i
        · simp [e]
        · intro j
          simp [e]
      change F (e.symm (t, u)) = F (Fin.cons t u)
      rw [hecons]

theorem continuousOn_elementaryCubeKernel
    {q p : ℕ} {s z : ℝ} (hs : 0 < s) (hz : 0 ≤ z) :
    ContinuousOn (elementaryCubeKernel p s z) (unitCube q) := by
  have hd : Continuous (fun u : Fin q → ℝ => cubeDenominator s z u) := by
    unfold cubeDenominator
    fun_prop
  have hd0 : ∀ u ∈ unitCube q, cubeDenominator s z u ≠ 0 := by
    intro u hu
    exact ne_of_gt (hs.trans_le (cubeDenominator_lower_bound le_rfl hz hu))
  change ContinuousOn (fun u : Fin q → ℝ => (cubeDenominator s z u)⁻¹ ^ p)
    (unitCube q)
  exact (hd.continuousOn.inv₀ hd0).pow p

/-- One differentiation in the first scale variable raises the reciprocal
power and supplies the exact signed multiplier. -/
theorem hasDerivAt_elementaryCubeKernel
    {q p : ℕ} {s z : ℝ} {u : Fin q → ℝ}
    (hden : cubeDenominator s z u ≠ 0) :
    HasDerivAt (fun x => elementaryCubeKernel p x z u)
      (-(p : ℝ) * elementaryCubeKernel (p + 1) s z u) s := by
  have hlin : HasDerivAt (fun x : ℝ => cubeDenominator x z u) 1 s := by
    simpa [cubeDenominator] using
      (hasDerivAt_id s).add_const (z * ∑ i, u i)
  cases p with
  | zero => simpa [elementaryCubeKernel] using hasDerivAt_const s (1 : ℝ)
  | succ p =>
      have hinv := hlin.inv hden
      have hpow := hinv.pow (p + 1)
      change HasDerivAt (fun x => (cubeDenominator x z u)⁻¹ ^ (p + 1))
        (-(p + 1 : ℕ) * (cubeDenominator s z u)⁻¹ ^ (p + 2)) s
      apply hpow.congr_deriv
      simp only [Nat.add_sub_cancel]
      rw [show (cubeDenominator s z u)⁻¹ ^ (p + 2) =
          (cubeDenominator s z u)⁻¹ ^ p * (cubeDenominator s z u)⁻¹ ^ 2 by
        rw [← pow_add]]
      simp only [div_eq_mul_inv, inv_pow, Pi.inv_apply]
      ring

/-- Advancing the scale by one is exactly one more finite difference, and
one more cube coordinate.  This is the repeated-FTC recursion behind the
elementary factors. -/
theorem elementaryCubeIntegral_shift_sub
    {q p : ℕ} {s : ℝ} (hs : 0 < s) :
    elementaryCubeIntegral q p (s + 1) 1 -
        elementaryCubeIntegral q p s 1 =
      -(p : ℝ) * elementaryCubeIntegral (q + 1) (p + 1) s 1 := by
  have hcont (x : ℝ) (hx : 0 < x) :
      ContinuousOn (elementaryCubeKernel p x 1) (unitCube q) :=
    continuousOn_elementaryCubeKernel hx (by norm_num)
  have hint (x : ℝ) (hx : 0 < x) :
      IntegrableOn (elementaryCubeKernel p x 1) (unitCube q) volume :=
    (hcont x hx).integrableOn_compact (isCompact_unitCube q)
  have hsucc : 0 < s + 1 := by linarith
  have houter : IntegrableOn
      (elementaryCubeKernel (p + 1) s 1) (unitCube (q + 1)) volume :=
    (continuousOn_elementaryCubeKernel hs (by norm_num)).integrableOn_compact
      (isCompact_unitCube (q + 1))
  rw [elementaryCubeIntegral, elementaryCubeIntegral, ← integral_sub
    (hint (s + 1) hsucc) (hint s hs)]
  rw [elementaryCubeIntegral, integral_unitCube_succ_tail _ houter,
    ← integral_const_mul]
  apply setIntegral_congr_fun (measurableSet_unitCube q)
  intro u hu
  have hsum_nonneg : 0 ≤ ∑ i, u i := by
    exact Finset.sum_nonneg fun i _ => hu.1 i
  have hpoint :
      (∫ t in Set.Icc (0 : ℝ) 1,
          -(p : ℝ) * elementaryCubeKernel (p + 1) (s + t) 1 u) =
        elementaryCubeKernel p (s + 1) 1 u -
          elementaryCubeKernel p s 1 u := by
    have hderiv : ∀ t ∈ Set.Icc (0 : ℝ) 1,
        HasDerivAt (fun x => elementaryCubeKernel p (s + x) 1 u)
          (-(p : ℝ) * elementaryCubeKernel (p + 1) (s + t) 1 u) t := by
      intro t ht
      have hden : cubeDenominator (s + t) 1 u ≠ 0 := by
        apply ne_of_gt
        simp only [cubeDenominator, one_mul]
        linarith [ht.1]
      exact (hasDerivAt_elementaryCubeKernel (p := p) hden).comp_const_add s t
    have hdencont : Continuous
        (fun t : ℝ => cubeDenominator (s + t) 1 u) := by
      unfold cubeDenominator
      fun_prop
    have hden0 : ∀ t ∈ Set.Icc (0 : ℝ) 1,
        cubeDenominator (s + t) 1 u ≠ 0 := by
      intro t ht
      apply ne_of_gt
      simp only [cubeDenominator, one_mul]
      linarith [ht.1]
    have hprimeCont : ContinuousOn
        (fun t : ℝ => -(p : ℝ) * elementaryCubeKernel (p + 1) (s + t) 1 u)
        (Set.Icc (0 : ℝ) 1) := by
      exact continuousOn_const.mul
        ((hdencont.continuousOn.inv₀ hden0).pow (p + 1))
    have hi := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le
      (f := fun x => elementaryCubeKernel p (s + x) 1 u)
      (f' := fun t => -(p : ℝ) * elementaryCubeKernel (p + 1) (s + t) 1 u)
      (a := 0) (b := 1) (by norm_num)
      (HasDerivAt.continuousOn hderiv)
      (fun t ht => hderiv t ⟨ht.1.le, ht.2.le⟩)
      (by simpa only [neg_mul] using
        hprimeCont.intervalIntegrable_of_Icc (by norm_num))
    rw [intervalIntegral.integral_of_le (by norm_num),
      ← integral_Icc_eq_integral_Ioc] at hi
    simpa using hi
  change elementaryCubeKernel p (s + 1) 1 u -
      elementaryCubeKernel p s 1 u =
    -(p : ℝ) * ∫ t in Set.Icc (0 : ℝ) 1,
      elementaryCubeKernel (p + 1) s 1 (Fin.cons t u)
  rw [← hpoint, ← integral_const_mul]
  congr 1
  funext t
  simp only [elementaryCubeKernel, cubeDenominator, Fin.sum_univ_succ,
    Fin.cons_zero, Fin.cons_succ]
  ring_nf

/-- The elementary logarithmic factor before applying finite differences. -/
noncomputable def elementaryLogFactor (s : ℝ) : ℝ :=
  Real.log s - Real.log (s + 1)

/-- Iterated forward difference with the paper's convention
`Δf(s) = f(s+1)-f(s)`. -/
def iteratedForwardDifference : ℕ → (ℝ → ℝ) → ℝ → ℝ
  | 0, f => f
  | n + 1, f => fun s =>
      iteratedForwardDifference n f (s + 1) - iteratedForwardDifference n f s

/-- The zeroth elementary factor is the negative one-dimensional reciprocal
kernel integral. -/
theorem elementaryLogFactor_eq_neg_cube
    {s : ℝ} (hs : 0 < s) :
    elementaryLogFactor s = -elementaryCubeIntegral 1 1 s 1 := by
  have houter : IntegrableOn (elementaryCubeKernel 1 s 1) (unitCube 1) volume :=
    (continuousOn_elementaryCubeKernel hs (by norm_num)).integrableOn_compact
      (isCompact_unitCube 1)
  have hdecomp := integral_unitCube_succ (q := 0)
    (elementaryCubeKernel 1 s 1) houter
  have hcube : elementaryCubeIntegral 1 1 s 1 =
      ∫ t in Set.Icc (0 : ℝ) 1, (s + t)⁻¹ := by
    rw [elementaryCubeIntegral, hdecomp]
    congr 1
    funext t
    simp [elementaryCubeKernel, cubeDenominator]
    rw [show volume.real (unitCube 0) = 1 from unitCube_volume_real 0]
    simp
  have hderiv : ∀ t ∈ Set.Icc (0 : ℝ) 1,
      HasDerivAt (fun x : ℝ => Real.log (s + x)) (s + t)⁻¹ t := by
    intro t ht
    exact (Real.hasDerivAt_log (by linarith [ht.1] : s + t ≠ 0)).comp_const_add s t
  have hprimeCont : ContinuousOn (fun t : ℝ => (s + t)⁻¹)
      (Set.Icc (0 : ℝ) 1) := by
    have hcont : Continuous (fun t : ℝ => s + t) := by fun_prop
    exact hcont.continuousOn.inv₀ (fun t ht => by linarith [ht.1])
  have hi := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le
    (f := fun x : ℝ => Real.log (s + x))
    (f' := fun t : ℝ => (s + t)⁻¹)
    (a := 0) (b := 1) (by norm_num)
    (HasDerivAt.continuousOn hderiv)
    (fun t ht => hderiv t ⟨ht.1.le, ht.2.le⟩)
    (hprimeCont.intervalIntegrable_of_Icc (by norm_num))
  rw [intervalIntegral.integral_of_le (by norm_num),
    ← integral_Icc_eq_integral_Ioc] at hi
  rw [hcube]
  simpa [elementaryLogFactor] using (congrArg Neg.neg hi).symm

theorem elementaryLogFactor_cube_q1
    {s : ℝ} (hs : 0 < s) :
    iteratedForwardDifference 0 elementaryLogFactor s =
      -elementaryCubeIntegral 1 1 s 1 := by
  simpa [iteratedForwardDifference] using elementaryLogFactor_eq_neg_cube hs

theorem elementaryLogFactor_cube_q2
    {s : ℝ} (hs : 0 < s) :
    iteratedForwardDifference 1 elementaryLogFactor s =
      elementaryCubeIntegral 2 2 s 1 := by
  change elementaryLogFactor (s + 1) - elementaryLogFactor s = _
  rw [elementaryLogFactor_eq_neg_cube (by linarith),
    elementaryLogFactor_eq_neg_cube hs]
  have hshift := elementaryCubeIntegral_shift_sub (q := 1) (p := 1) hs
  norm_num at hshift
  linarith

theorem elementaryLogFactor_cube_q3
    {s : ℝ} (hs : 0 < s) :
    iteratedForwardDifference 2 elementaryLogFactor s =
      -2 * elementaryCubeIntegral 3 3 s 1 := by
  change iteratedForwardDifference 1 elementaryLogFactor (s + 1) -
    iteratedForwardDifference 1 elementaryLogFactor s = _
  rw [elementaryLogFactor_cube_q2 (by linarith),
    elementaryLogFactor_cube_q2 hs,
    elementaryCubeIntegral_shift_sub (q := 2) (p := 2) hs]
  ring

theorem elementaryLogFactor_cube_q4
    {s : ℝ} (hs : 0 < s) :
    iteratedForwardDifference 3 elementaryLogFactor s =
      6 * elementaryCubeIntegral 4 4 s 1 := by
  change iteratedForwardDifference 2 elementaryLogFactor (s + 1) -
    iteratedForwardDifference 2 elementaryLogFactor s = _
  rw [elementaryLogFactor_cube_q3 (by linarith),
    elementaryLogFactor_cube_q3 hs]
  have hshift := elementaryCubeIntegral_shift_sub (q := 3) (p := 3) hs
  norm_num at hshift
  linarith

/-- Exact rescaling from a large argument `s/x` to the compact cube kernel.
No asymptotic expansion is involved. -/
theorem elementaryCubeIntegral_div_scale
    {q p : ℕ} {s x : ℝ} (hx : 0 < x) :
    elementaryCubeIntegral q p (s / x) 1 =
      x ^ p * elementaryCubeIntegral q p s x := by
  rw [elementaryCubeIntegral, elementaryCubeIntegral, ← integral_const_mul]
  apply setIntegral_congr_fun (measurableSet_unitCube q)
  intro u _hu
  simp only [elementaryCubeKernel, cubeDenominator, one_mul]
  have hden : s / x + ∑ i, u i = x⁻¹ * (s + x * ∑ i, u i) := by
    field_simp
  rw [hden, mul_inv_rev, mul_pow, inv_inv]
  ring

theorem elementaryLogFactor_scaled_q1
    {s x : ℝ} (hs : 0 < s) (hx : 0 < x) :
    iteratedForwardDifference 0 elementaryLogFactor (s / x) =
      -x * elementaryPhi 1 s x := by
  rw [elementaryLogFactor_cube_q1 (div_pos hs hx),
    elementaryCubeIntegral_div_scale (q := 1) (p := 1) hx]
  simp [elementaryPhi]

theorem elementaryLogFactor_scaled_q2
    {s x : ℝ} (hs : 0 < s) (hx : 0 < x) :
    iteratedForwardDifference 1 elementaryLogFactor (s / x) =
      x ^ 2 * elementaryPhi 2 s x := by
  rw [elementaryLogFactor_cube_q2 (div_pos hs hx),
    elementaryCubeIntegral_div_scale (q := 2) (p := 2) hx]
  rfl

theorem elementaryLogFactor_scaled_q3
    {s x : ℝ} (hs : 0 < s) (hx : 0 < x) :
    iteratedForwardDifference 2 elementaryLogFactor (s / x) =
      -2 * x ^ 3 * elementaryPhi 3 s x := by
  rw [elementaryLogFactor_cube_q3 (div_pos hs hx),
    elementaryCubeIntegral_div_scale (q := 3) (p := 3) hx]
  simp only [elementaryPhi]
  ring

theorem elementaryLogFactor_scaled_q4
    {s x : ℝ} (hs : 0 < s) (hx : 0 < x) :
    iteratedForwardDifference 3 elementaryLogFactor (s / x) =
      6 * x ^ 4 * elementaryPhi 4 s x := by
  rw [elementaryLogFactor_cube_q4 (div_pos hs hx),
    elementaryCubeIntegral_div_scale (q := 4) (p := 4) hx]
  simp only [elementaryPhi]
  ring

/-- Differentiation under the genuine finite-dimensional cube integral. -/
theorem hasDerivAt_elementaryCubeIntegral
    {q p : ℕ} {s z : ℝ} (hs : 0 < s) (hz : 0 ≤ z) :
    HasDerivAt (fun x => elementaryCubeIntegral q p x z)
      (-(p : ℝ) * elementaryCubeIntegral q (p + 1) s z) s := by
  let r : ℝ := s / 2
  have hr : 0 < r := by dsimp [r]; positivity
  have hsHalf : 0 < s / 2 := by positivity
  let F : ℝ → (Fin q → ℝ) → ℝ := fun x u => elementaryCubeKernel p x z u
  let F' : ℝ → (Fin q → ℝ) → ℝ := fun x u =>
    -(p : ℝ) * elementaryCubeKernel (p + 1) x z u
  let C : ℝ := (p : ℝ) * (s / 2)⁻¹ ^ (p + 1)
  have hxpos : ∀ x ∈ Metric.ball s r, 0 < x := by
    intro x hx
    rw [Metric.mem_ball, Real.dist_eq] at hx
    dsimp [r] at hx
    have := (abs_lt.mp hx).1
    linarith
  have hFcont : ∀ x ∈ Metric.ball s r,
      ContinuousOn (F x) (unitCube q) := by
    intro x hx
    exact continuousOn_elementaryCubeKernel (hxpos x hx) hz
  have hF'cont : ∀ x ∈ Metric.ball s r,
      ContinuousOn (F' x) (unitCube q) := by
    intro x hx
    exact continuousOn_const.mul
      (continuousOn_elementaryCubeKernel (p := p + 1) (hxpos x hx) hz)
  have hparam := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (𝕜 := ℝ) (E := ℝ) (μ := volume.restrict (unitCube q))
    (F := F) (F' := F') (x₀ := s) (s := Metric.ball s r)
    (bound := fun _ => C)
    (Metric.ball_mem_nhds s hr)
    (by
      filter_upwards [Metric.ball_mem_nhds s hr] with x hx
      exact (hFcont x hx).aestronglyMeasurable (measurableSet_unitCube q))
    ((hFcont s (Metric.mem_ball_self hr)).integrableOn_compact
      (isCompact_unitCube q))
    ((hF'cont s (Metric.mem_ball_self hr)).aestronglyMeasurable
      (measurableSet_unitCube q))
    (by
      filter_upwards [ae_restrict_mem (measurableSet_unitCube q)] with u hu x hx
      have hxhalf : s / 2 ≤ x := by
        rw [Metric.mem_ball, Real.dist_eq] at hx
        dsimp [r] at hx
        have := (abs_lt.mp hx).1
        linarith
      change |-(p : ℝ) * elementaryCubeKernel (p + 1) x z u| ≤ C
      simpa [F', C, elementaryCubeKernel, abs_mul] using
        cube_derivative_kernel_bound (A := (p : ℝ)) (p := p + 1)
          (Nat.cast_nonneg p) hsHalf hxhalf hz hu)
    ((integrableOn_const (measure_Icc_lt_top.ne)).integrable)
    (by
      filter_upwards [ae_restrict_mem (measurableSet_unitCube q)] with u hu x hx
      have hdenPos : 0 < cubeDenominator x z u :=
        (hxpos x hx).trans_le (cubeDenominator_lower_bound le_rfl hz hu)
      exact hasDerivAt_elementaryCubeKernel (ne_of_gt hdenPos))
  have h := hparam.2
  change HasDerivAt (fun x => ∫ u in unitCube q, elementaryCubeKernel p x z u)
    (-(p : ℝ) * (∫ u in unitCube q, elementaryCubeKernel (p + 1) s z u)) s
  simpa only [F, F', elementaryCubeIntegral, integral_const_mul] using h

theorem hasDerivAt_elementaryPhi
    {q : ℕ} {s z : ℝ} (hs : 0 < s) (hz : 0 ≤ z) :
    HasDerivAt (fun x => elementaryPhi q x z)
      (elementaryPhiD1 q s z) s := by
  simpa only [elementaryPhi, elementaryPhiD1] using
    hasDerivAt_elementaryCubeIntegral (q := q) (p := q) hs hz

theorem hasDerivAt_elementaryPhi_firstDerivative
    {q : ℕ} {s z : ℝ} (hs : 0 < s) (hz : 0 ≤ z) :
    HasDerivAt
      (fun x => elementaryPhiD1 q x z)
      (elementaryPhiD2 q s z) s := by
  have h := (hasDerivAt_elementaryCubeIntegral (q := q) (p := q + 1) hs hz).const_mul
    (-(q : ℝ))
  change HasDerivAt
    (fun x => -(q : ℝ) * elementaryCubeIntegral q (q + 1) x z)
    ((q : ℝ) * (q + 1) * elementaryCubeIntegral q (q + 2) s z) s
  apply h.congr_deriv
  push_cast
  ring

/-- Exact first-argument segment formula for `Phi_q`. -/
theorem elementaryPhi_add_sub_eq_segment
    {q : ℕ} {s h z : ℝ} (hs : 0 < s) (hh : 0 ≤ h) (hz : 0 ≤ z) :
    elementaryPhi q (s + h) z - elementaryPhi q s z =
      h * ∫ u in Set.Icc (0 : ℝ) 1, elementaryPhiD1 q (s + u * h) z := by
  have hpos : ∀ u ∈ Set.Icc (0 : ℝ) 1, 0 < s + u * h := by
    intro u hu
    linarith [mul_nonneg hu.1 hh]
  have hderiv : ∀ u ∈ Set.Icc (0 : ℝ) 1,
      HasDerivAt (fun v : ℝ => elementaryPhi q (s + v * h) z)
        (h * elementaryPhiD1 q (s + u * h) z) u := by
    intro u hu
    have hinner : HasDerivAt (fun v : ℝ => s + v * h) h u := by
      simpa [mul_comm] using ((hasDerivAt_id u).mul_const h).const_add s
    simpa [Function.comp_def, mul_comm] using
      (hasDerivAt_elementaryPhi (q := q) (hpos u hu) hz).comp u hinner
  have hprimeCont : ContinuousOn
      (fun u : ℝ => h * elementaryPhiD1 q (s + u * h) z)
      (Set.Icc (0 : ℝ) 1) := by
    intro u hu
    have hinner : HasDerivAt (fun v : ℝ => s + v * h) h u := by
      simpa [mul_comm] using ((hasDerivAt_id u).mul_const h).const_add s
    have hcomp := (hasDerivAt_elementaryPhi_firstDerivative
      (q := q) (hpos u hu) hz).comp u hinner
    have hc : ContinuousAt (fun v : ℝ => elementaryPhiD1 q (s + v * h) z) u := by
      simpa [Function.comp_def] using hcomp.continuousAt
    exact (continuousAt_const.mul hc).continuousWithinAt
  have hi := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le
    (f := fun v : ℝ => elementaryPhi q (s + v * h) z)
    (f' := fun u : ℝ => h * elementaryPhiD1 q (s + u * h) z)
    (a := 0) (b := 1) (by norm_num)
    (HasDerivAt.continuousOn hderiv)
    (fun u hu => hderiv u ⟨hu.1.le, hu.2.le⟩)
    (hprimeCont.intervalIntegrable_of_Icc (by norm_num))
  rw [intervalIntegral.integral_of_le (by norm_num),
    ← integral_Icc_eq_integral_Ioc, integral_const_mul] at hi
  simpa using hi.symm

/-- Exact segment formula for the first derivative, used for the `t`
derivative of the paired `B-C` term. -/
theorem elementaryPhiD1_add_sub_eq_segment
    {q : ℕ} {s h z : ℝ} (hs : 0 < s) (hh : 0 ≤ h) (hz : 0 ≤ z) :
    elementaryPhiD1 q (s + h) z - elementaryPhiD1 q s z =
      h * ∫ u in Set.Icc (0 : ℝ) 1, elementaryPhiD2 q (s + u * h) z := by
  have hpos : ∀ u ∈ Set.Icc (0 : ℝ) 1, 0 < s + u * h := by
    intro u hu
    linarith [mul_nonneg hu.1 hh]
  have hderiv : ∀ u ∈ Set.Icc (0 : ℝ) 1,
      HasDerivAt (fun v : ℝ => elementaryPhiD1 q (s + v * h) z)
        (h * elementaryPhiD2 q (s + u * h) z) u := by
    intro u hu
    have hinner : HasDerivAt (fun v : ℝ => s + v * h) h u := by
      simpa [mul_comm] using ((hasDerivAt_id u).mul_const h).const_add s
    simpa [Function.comp_def, mul_comm] using
      (hasDerivAt_elementaryPhi_firstDerivative (q := q) (hpos u hu) hz).comp u hinner
  have hD2cont : ContinuousOn
      (fun u : ℝ => h * elementaryPhiD2 q (s + u * h) z)
      (Set.Icc (0 : ℝ) 1) := by
    intro u hu
    have hinner : HasDerivAt (fun v : ℝ => s + v * h) h u := by
      simpa [mul_comm] using ((hasDerivAt_id u).mul_const h).const_add s
    have hbase := (hasDerivAt_elementaryCubeIntegral
      (q := q) (p := q + 2) (hpos u hu) hz).comp u hinner
    have hc : ContinuousAt
        (fun v : ℝ => elementaryCubeIntegral q (q + 2) (s + v * h) z) u := by
      simpa [Function.comp_def] using hbase.continuousAt
    have hc' : ContinuousAt
        (fun v : ℝ => h * elementaryPhiD2 q (s + v * h) z) u := by
      have hhcont : ContinuousAt (fun _v : ℝ => h) u := continuousAt_const
      have hqcont : ContinuousAt (fun _v : ℝ => (q : ℝ)) u := continuousAt_const
      have hq1cont : ContinuousAt (fun _v : ℝ => (q : ℝ) + 1) u := continuousAt_const
      have hcraw := hhcont.mul ((hqcont.mul hq1cont).mul hc)
      convert hcraw using 1
      funext v
      simp only [elementaryPhiD2, Pi.mul_apply]
    exact hc'.continuousWithinAt
  have hi := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le
    (f := fun v : ℝ => elementaryPhiD1 q (s + v * h) z)
    (f' := fun u : ℝ => h * elementaryPhiD2 q (s + u * h) z)
    (a := 0) (b := 1) (by norm_num)
    (HasDerivAt.continuousOn hderiv)
    (fun u hu => hderiv u ⟨hu.1.le, hu.2.le⟩)
    (hD2cont.intervalIntegrable_of_Icc (by norm_num))
  rw [intervalIntegral.integral_of_le (by norm_num),
    ← integral_Icc_eq_integral_Ioc, integral_const_mul] at hi
  simpa using hi.symm

/-- Exact `B-C` divided-difference identity. -/
theorem elementaryPhi_paired_dividedDifference
    {q : ℕ} {t w e z : ℝ}
    (ht : 0 < t) (hw : 0 ≤ w) (he : 0 < e) (hz : 0 ≤ z) :
    (elementaryPhi q t z - elementaryPhi q (t + w * e) z) / e =
      -w * ∫ u in Set.Icc (0 : ℝ) 1,
        elementaryPhiD1 q (t + u * (w * e)) z := by
  have hseg := elementaryPhi_add_sub_eq_segment (q := q) ht
    (mul_nonneg hw he.le) hz
  calc
    (elementaryPhi q t z - elementaryPhi q (t + w * e) z) / e =
        -(elementaryPhi q (t + w * e) z - elementaryPhi q t z) / e := by ring
    _ = -(w * e * ∫ u in Set.Icc (0 : ℝ) 1,
        elementaryPhiD1 q (t + u * (w * e)) z) / e := by rw [hseg]
    _ = -w * ∫ u in Set.Icc (0 : ℝ) 1,
        elementaryPhiD1 q (t + u * (w * e)) z := by
      field_simp [ne_of_gt he]

/-- Exact derivative in the displacement parameter of the paired term. -/
theorem hasDerivAt_elementaryPhi_paired_w
    {q : ℕ} {t w e z : ℝ}
    (ht : 0 < t) (hw : 0 ≤ w) (he : 0 < e) (hz : 0 ≤ z) :
    HasDerivAt
      (fun v : ℝ =>
        (elementaryPhi q t z - elementaryPhi q (t + v * e) z) / e)
      (-elementaryPhiD1 q (t + w * e) z) w := by
  have hpos : 0 < t + w * e := by positivity
  have hinner : HasDerivAt (fun v : ℝ => t + v * e) e w := by
    simpa [mul_comm] using ((hasDerivAt_id w).mul_const e).const_add t
  have hright := (hasDerivAt_elementaryPhi (q := q) hpos hz).comp w hinner
  have hraw := ((hasDerivAt_const w (elementaryPhi q t z)).sub hright).div_const e
  have htyped : HasDerivAt
      (fun v : ℝ =>
        (elementaryPhi q t z - elementaryPhi q (t + v * e) z) / e)
      ((0 - elementaryPhiD1 q (t + w * e) z * e) / e) w := by
    simpa [Function.comp_def, mul_comm] using hraw
  apply htyped.congr_deriv
  field_simp [ne_of_gt he]
  ring

/-- Exact derivative in the base parameter of the paired term. -/
theorem hasDerivAt_elementaryPhi_paired_t
    {q : ℕ} {t w e z : ℝ}
    (ht : 0 < t) (hw : 0 ≤ w) (he : 0 < e) (hz : 0 ≤ z) :
    HasDerivAt
      (fun v : ℝ =>
        (elementaryPhi q v z - elementaryPhi q (v + w * e) z) / e)
      ((elementaryPhiD1 q t z - elementaryPhiD1 q (t + w * e) z) / e) t := by
  have hpos : 0 < t + w * e := by positivity
  have hright := (hasDerivAt_elementaryPhi (q := q) hpos hz).comp_add_const t (w * e)
  exact ((hasDerivAt_elementaryPhi (q := q) ht hz).sub hright).div_const e

/-- Exact derivative of the paired `D` boundary in `delta`. -/
theorem hasDerivAt_elementaryPhi_boundary_delta
    {q : ℕ} {delta e z : ℝ}
    (hdelta : 0 ≤ delta) (he : 0 < e) (hz : 0 ≤ z) :
    HasDerivAt
      (fun v : ℝ =>
        (elementaryPhi q 1 z - elementaryPhi q (1 + v * e) z) / e)
      (-elementaryPhiD1 q (1 + delta * e) z) delta := by
  simpa using hasDerivAt_elementaryPhi_paired_w (q := q)
    (t := 1) (w := delta) (e := e) (z := z) (by norm_num) hdelta he hz

/-- A positive lower scale controls every reciprocal-power cube integral. -/
theorem abs_elementaryCubeIntegral_le
    {q p : ℕ} {s s₀ z : ℝ}
    (hs₀ : 0 < s₀) (hs : s₀ ≤ s) (hz : 0 ≤ z) :
    |elementaryCubeIntegral q p s z| ≤ s₀⁻¹ ^ p := by
  change ‖∫ u in unitCube q, elementaryCubeKernel p s z u‖ ≤ s₀⁻¹ ^ p
  apply norm_unitCube_integral_le
  intro u hu
  simpa only [elementaryCubeKernel, Real.norm_eq_abs] using
    cube_reciprocal_power_bound (p := p) hs₀ hs hz hu

theorem abs_elementaryPhi_le
    {q : ℕ} {s s₀ z : ℝ}
    (hs₀ : 0 < s₀) (hs : s₀ ≤ s) (hz : 0 ≤ z) :
    |elementaryPhi q s z| ≤ s₀⁻¹ ^ q := by
  exact abs_elementaryCubeIntegral_le hs₀ hs hz

theorem abs_elementaryPhi_firstDerivative_le
    {q : ℕ} {s s₀ z : ℝ}
    (hs₀ : 0 < s₀) (hs : s₀ ≤ s) (hz : 0 ≤ z) :
    |-(q : ℝ) * elementaryCubeIntegral q (q + 1) s z| ≤
      (q : ℝ) * s₀⁻¹ ^ (q + 1) := by
  rw [abs_mul, abs_neg, abs_of_nonneg (Nat.cast_nonneg q)]
  exact mul_le_mul_of_nonneg_left
    (abs_elementaryCubeIntegral_le hs₀ hs hz) (Nat.cast_nonneg q)

theorem abs_elementaryPhi_secondDerivative_le
    {q : ℕ} {s s₀ z : ℝ}
    (hs₀ : 0 < s₀) (hs : s₀ ≤ s) (hz : 0 ≤ z) :
    |(q : ℝ) * (q + 1) * elementaryCubeIntegral q (q + 2) s z| ≤
      (q : ℝ) * (q + 1) * s₀⁻¹ ^ (q + 2) := by
  rw [abs_mul, abs_mul, abs_of_nonneg (Nat.cast_nonneg q),
    abs_of_nonneg (by positivity : 0 ≤ (q : ℝ) + 1)]
  exact mul_le_mul_of_nonneg_left
    (abs_elementaryCubeIntegral_le hs₀ hs hz)
    (by positivity)

theorem cubeCoordinateSum_nonneg
    {q : ℕ} {u : Fin q → ℝ} (hu : u ∈ unitCube q) :
    0 ≤ ∑ i, u i := by
  exact Finset.sum_nonneg fun i _ => hu.1 i

theorem cubeCoordinateSum_le
    {q : ℕ} {u : Fin q → ℝ} (hu : u ∈ unitCube q) :
    ∑ i, u i ≤ q := by
  calc
    ∑ i, u i ≤ ∑ _i : Fin q, (1 : ℝ) :=
      Finset.sum_le_sum fun i _ => hu.2 i
    _ = q := by simp

theorem hasDerivAt_reciprocalPower
    {p : ℕ} {x : ℝ} (hx : x ≠ 0) :
    HasDerivAt (fun y : ℝ => y⁻¹ ^ p) (-(p : ℝ) * x⁻¹ ^ (p + 1)) x := by
  let u : Fin 0 → ℝ := Fin.elim0
  have h := hasDerivAt_elementaryCubeKernel (q := 0) (p := p)
    (s := x) (z := 0) (u := u) (by simpa [cubeDenominator, u] using hx)
  simpa [elementaryCubeKernel, cubeDenominator, u] using h

/-- Pointwise first-order error of the reciprocal kernel. -/
theorem elementaryCubeKernel_firstOrder_error
    {q p : ℕ} {s s₀ z : ℝ} {u : Fin q → ℝ}
    (hs₀ : 0 < s₀) (hs : s₀ ≤ s) (hz : 0 ≤ z)
    (hu : u ∈ unitCube q) :
    |elementaryCubeKernel p s z u - s⁻¹ ^ p| ≤
      (p : ℝ) * q * z * s₀⁻¹ ^ (p + 1) := by
  let f : ℝ → ℝ := fun x => x⁻¹ ^ p
  let f' : ℝ → ℝ := fun x => -(p : ℝ) * x⁻¹ ^ (p + 1)
  let C : ℝ := (p : ℝ) * s₀⁻¹ ^ (p + 1)
  have hden := cubeDenominator_lower_bound hs hz hu
  have hderiv : ∀ x ∈ Set.Ici s₀, HasDerivWithinAt f (f' x) (Set.Ici s₀) x := by
    intro x hx
    exact (hasDerivAt_reciprocalPower (p := p) (ne_of_gt (hs₀.trans_le hx))).hasDerivWithinAt
  have hderivBound : ∀ x ∈ Set.Ici s₀, ‖f' x‖ ≤ C := by
    intro x hx
    let u₀ : Fin 0 → ℝ := Fin.elim0
    have hu₀ : u₀ ∈ unitCube 0 := by simp [unitCube, u₀]
    simpa [f', C, elementaryCubeKernel, cubeDenominator, u₀, Real.norm_eq_abs] using
      cube_derivative_kernel_bound (q := 0) (p := p + 1) (A := (p : ℝ))
        (s := x) (s₀ := s₀) (z := 0) (u := u₀)
        (Nat.cast_nonneg p) hs₀ hx (by norm_num) hu₀
  have hmvt := (convex_Ici s₀).norm_image_sub_le_of_norm_hasDerivWithin_le
    hderiv hderivBound hs hden
  have hsum0 := cubeCoordinateSum_nonneg hu
  have hsumq := cubeCoordinateSum_le hu
  have hshift : ‖cubeDenominator s z u - s‖ ≤ z * q := by
    rw [cubeDenominator, add_sub_cancel_left, Real.norm_eq_abs,
      abs_of_nonneg (mul_nonneg hz hsum0)]
    exact mul_le_mul_of_nonneg_left hsumq hz
  have hC : 0 ≤ C := mul_nonneg (Nat.cast_nonneg p) (pow_nonneg (le_of_lt (inv_pos.mpr hs₀)) _)
  calc
    |elementaryCubeKernel p s z u - s⁻¹ ^ p|
        = ‖f (cubeDenominator s z u) - f s‖ := by
          rfl
    _ ≤ C * ‖cubeDenominator s z u - s‖ := hmvt
    _ ≤ C * (z * q) := mul_le_mul_of_nonneg_left hshift hC
    _ = (p : ℝ) * q * z * s₀⁻¹ ^ (p + 1) := by
      dsimp [C]
      ring

/-- Integrated first-order error.  This is equation (5) of the elementary
`C¹` proof before inserting the rising-factorial multiplier. -/
theorem elementaryCubeIntegral_firstOrder_error
    {q p : ℕ} {s s₀ z : ℝ}
    (hs₀ : 0 < s₀) (hs : s₀ ≤ s) (hz : 0 ≤ z) :
    |elementaryCubeIntegral q p s z - s⁻¹ ^ p| ≤
      (p : ℝ) * q * z * s₀⁻¹ ^ (p + 1) := by
  have hkernel : IntegrableOn (elementaryCubeKernel p s z) (unitCube q) volume :=
    (continuousOn_elementaryCubeKernel (q := q) (p := p)
      (hs₀.trans_le hs) hz).integrableOn_compact (isCompact_unitCube q)
  have hconst : (∫ _u : Fin q → ℝ in unitCube q, s⁻¹ ^ p) = s⁻¹ ^ p := by
    rw [setIntegral_const, smul_eq_mul]
    have hv : volume.real (unitCube q) = 1 := by
      change (volume (unitCube q)).toReal = 1
      exact unitCube_volume_real q
    rw [hv, one_mul]
  change |(∫ u in unitCube q, elementaryCubeKernel p s z u) - s⁻¹ ^ p| ≤ _
  rw [← hconst, ← integral_sub hkernel
    (integrableOn_const (s := unitCube q) (μ := volume) measure_Icc_lt_top.ne)]
  change ‖∫ u in unitCube q, elementaryCubeKernel p s z u - s⁻¹ ^ p‖ ≤ _
  apply norm_unitCube_integral_le
  intro u hu
  simpa only [Real.norm_eq_abs] using
    elementaryCubeKernel_firstOrder_error hs₀ hs hz hu

theorem elementaryPhi_firstOrder_error
    {q : ℕ} {s s₀ z : ℝ}
    (hs₀ : 0 < s₀) (hs : s₀ ≤ s) (hz : 0 ≤ z) :
    |elementaryPhi q s z - s⁻¹ ^ q| ≤
      (q : ℝ) * q * z * s₀⁻¹ ^ (q + 1) := by
  exact elementaryCubeIntegral_firstOrder_error hs₀ hs hz

theorem elementaryPhiD1_firstOrder_error
    {q : ℕ} {s s₀ z : ℝ}
    (hs₀ : 0 < s₀) (hs : s₀ ≤ s) (hz : 0 ≤ z) :
    |elementaryPhiD1 q s z - (-(q : ℝ) * s⁻¹ ^ (q + 1))| ≤
      (q : ℝ) * (q + 1) * q * z * s₀⁻¹ ^ (q + 2) := by
  have h := elementaryCubeIntegral_firstOrder_error (q := q) (p := q + 1)
    hs₀ hs hz
  calc
    |elementaryPhiD1 q s z - (-(q : ℝ) * s⁻¹ ^ (q + 1))|
        = (q : ℝ) *
          |elementaryCubeIntegral q (q + 1) s z - s⁻¹ ^ (q + 1)| := by
            rw [elementaryPhiD1, show
              -(q : ℝ) * elementaryCubeIntegral q (q + 1) s z -
                  (-(q : ℝ) * s⁻¹ ^ (q + 1)) =
                -(q : ℝ) *
                  (elementaryCubeIntegral q (q + 1) s z - s⁻¹ ^ (q + 1)) by ring,
              abs_mul, abs_neg, abs_of_nonneg (Nat.cast_nonneg q)]
    _ ≤ (q : ℝ) * ((q + 1 : ℕ) * q * z * s₀⁻¹ ^ (q + 2)) :=
      mul_le_mul_of_nonneg_left h (Nat.cast_nonneg q)
    _ = (q : ℝ) * (q + 1) * q * z * s₀⁻¹ ^ (q + 2) := by
      push_cast
      ring

theorem elementaryPhiD2_firstOrder_error
    {q : ℕ} {s s₀ z : ℝ}
    (hs₀ : 0 < s₀) (hs : s₀ ≤ s) (hz : 0 ≤ z) :
    |elementaryPhiD2 q s z -
        ((q : ℝ) * (q + 1) * s⁻¹ ^ (q + 2))| ≤
      (q : ℝ) * (q + 1) * (q + 2) * q * z * s₀⁻¹ ^ (q + 3) := by
  have h := elementaryCubeIntegral_firstOrder_error (q := q) (p := q + 2)
    hs₀ hs hz
  have hcoef : 0 ≤ (q : ℝ) * (q + 1) := by positivity
  calc
    |elementaryPhiD2 q s z - ((q : ℝ) * (q + 1) * s⁻¹ ^ (q + 2))|
        = ((q : ℝ) * (q + 1)) *
          |elementaryCubeIntegral q (q + 2) s z - s⁻¹ ^ (q + 2)| := by
            rw [elementaryPhiD2, show
              (q : ℝ) * (q + 1) * elementaryCubeIntegral q (q + 2) s z -
                  (q : ℝ) * (q + 1) * s⁻¹ ^ (q + 2) =
                ((q : ℝ) * (q + 1)) *
                  (elementaryCubeIntegral q (q + 2) s z - s⁻¹ ^ (q + 2)) by ring,
              abs_mul, abs_of_nonneg hcoef]
    _ ≤ ((q : ℝ) * (q + 1)) *
        ((q + 2 : ℕ) * q * z * s₀⁻¹ ^ (q + 3)) :=
      mul_le_mul_of_nonneg_left h hcoef
    _ = (q : ℝ) * (q + 1) * (q + 2) * q * z * s₀⁻¹ ^ (q + 3) := by
      push_cast
      ring

/-- Quantitative remote-boundary estimate in the only surviving `q=1`
coordinate. -/
theorem elementaryPhi_remote_q1_error
    {alpha alpha₀ x e : ℝ}
    (halpha₀ : 0 < alpha₀) (halpha : alpha₀ ≤ alpha)
    (hx : 0 ≤ x) (he : 0 ≤ e) :
    |elementaryPhi 1 alpha (x * e) - alpha⁻¹| ≤
      x * e * alpha₀⁻¹ ^ 2 := by
  simpa [pow_one] using
    elementaryPhi_firstOrder_error (q := 1) halpha₀ halpha (mul_nonneg hx he)

/-- Every remote coordinate of order at least two carries the explicit
factor `e^(q-1)`. -/
theorem abs_elementaryPhi_remote_le
    {q : ℕ} {alpha alpha₀ x e : ℝ}
    (halpha₀ : 0 < alpha₀) (halpha : alpha₀ ≤ alpha)
    (hx : 0 ≤ x) (he : 0 ≤ e) :
    |e ^ (q - 1) * elementaryPhi q alpha (x * e)| ≤
      e ^ (q - 1) * alpha₀⁻¹ ^ q := by
  rw [abs_mul, abs_of_nonneg (pow_nonneg he _)]
  exact mul_le_mul_of_nonneg_left
    (abs_elementaryPhi_le halpha₀ halpha (mul_nonneg hx he))
    (pow_nonneg he _)

/-- The same explicit remote factor controls the `alpha` derivative. -/
theorem abs_elementaryPhiD1_remote_le
    {q : ℕ} {alpha alpha₀ x e : ℝ}
    (halpha₀ : 0 < alpha₀) (halpha : alpha₀ ≤ alpha)
    (hx : 0 ≤ x) (he : 0 ≤ e) :
    |e ^ (q - 1) * elementaryPhiD1 q alpha (x * e)| ≤
      e ^ (q - 1) * (q : ℝ) * alpha₀⁻¹ ^ (q + 1) := by
  rw [abs_mul, abs_of_nonneg (pow_nonneg he _)]
  have h := abs_elementaryPhi_firstDerivative_le (q := q)
    halpha₀ halpha (mul_nonneg hx he)
  change |elementaryPhiD1 q alpha (x * e)| ≤ _ at h
  simpa only [mul_assoc] using
    mul_le_mul_of_nonneg_left h (pow_nonneg he (q - 1))

/-- The unmatched half-shift between `1+x/2` and `1` is explicitly of
size at most `q*x/e`.  This is the source of the paper's `x/e` term. -/
theorem elementaryPhi_halfShift_div_bound
    {q : ℕ} {x e : ℝ} (hx : 0 ≤ x) (he : 0 < e) :
    |(elementaryPhi q (1 + x / 2) x - elementaryPhi q 1 x) / e| ≤
      (q : ℝ) * (x / e) := by
  have hseg := elementaryPhi_add_sub_eq_segment (q := q) (z := x)
    (s := 1) (h := x / 2) (by norm_num) (by positivity) hx
  have hInt :
      |∫ u in Set.Icc (0 : ℝ) 1, elementaryPhiD1 q (1 + u * (x / 2)) x| ≤
        (q : ℝ) := by
    have hnorm := norm_setIntegral_le_of_norm_le_const
      (μ := volume)
      (f := fun u : ℝ => elementaryPhiD1 q (1 + u * (x / 2)) x)
      (s := Set.Icc (0 : ℝ) 1) (C := (q : ℝ)) measure_Icc_lt_top
      (fun u hu => by
        have hs : (1 : ℝ) ≤ 1 + u * (x / 2) := by
          nlinarith [mul_nonneg hu.1 (by positivity : 0 ≤ x / 2)]
        simpa [elementaryPhiD1, Real.norm_eq_abs, inv_one, one_pow] using
          abs_elementaryPhi_firstDerivative_le (q := q)
            (s₀ := 1) (s := 1 + u * (x / 2)) (z := x) (by norm_num) hs hx)
    have hvol : volume.real (Set.Icc (0 : ℝ) 1) = 1 := by
      rw [Real.volume_real_Icc_of_le (by norm_num)]
      norm_num
    simpa only [Real.norm_eq_abs, hvol, mul_one] using hnorm
  rw [hseg, abs_div, abs_mul, abs_of_nonneg (by positivity : 0 ≤ x / 2),
    abs_of_pos he]
  calc
    (x / 2 * |∫ u in Set.Icc (0 : ℝ) 1,
        elementaryPhiD1 q (1 + u * (x / 2)) x|) / e ≤
        (x / 2 * (q : ℝ)) / e := by
          gcongr
    _ ≤ (q : ℝ) * (x / e) := by
      field_simp [ne_of_gt he]
      nlinarith [mul_nonneg hx (Nat.cast_nonneg q)]

end Zeta23.Research.JensenWedge
