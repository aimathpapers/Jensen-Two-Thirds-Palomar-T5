import Zeta23.Research.JensenWedge.ElementaryParameterIdentity

/-!
# Quantitative elementary boundary estimates

This module turns the exact cube calculus into the pointwise estimates used
by the elementary `C¹` parameter map.  The estimates retain both sources of
error: the cube scale `z` and the displacement `h` in the first argument.
-/

namespace Zeta23.Research.JensenWedge

open MeasureTheory Set

noncomputable section

/-- Moving the base of a reciprocal power by a nonnegative amount has the
expected explicit mean-value bound. -/
theorem reciprocalPower_add_error
    {p : ℕ} {s s₀ h : ℝ}
    (hs₀ : 0 < s₀) (hs : s₀ ≤ s) (hh : 0 ≤ h) :
    |(s + h)⁻¹ ^ p - s⁻¹ ^ p| ≤
      (p : ℝ) * h * s₀⁻¹ ^ (p + 1) := by
  let u : Fin 1 → ℝ := fun _ => 1
  have hu : u ∈ unitCube 1 := by
    exact ⟨fun _ => by norm_num [u], fun _ => by norm_num [u]⟩
  have hkernel := elementaryCubeKernel_firstOrder_error
    (q := 1) (p := p) (s := s) (s₀ := s₀) (z := h) (u := u)
    hs₀ hs hh hu
  simpa [elementaryCubeKernel, cubeDenominator, u] using hkernel

/-- The first `s`-derivative of `Phi_q`, evaluated after a nonnegative
displacement, differs from its base reciprocal power by an explicit sum of
the cube-scale and displacement errors. -/
theorem elementaryPhiD1_base_error
    {q : ℕ} {s s₀ h z : ℝ}
    (hs₀ : 0 < s₀) (hs : s₀ ≤ s) (hh : 0 ≤ h) (hz : 0 ≤ z) :
    |elementaryPhiD1 q (s + h) z -
        (-(q : ℝ) * s⁻¹ ^ (q + 1))| ≤
      (q : ℝ) * (q + 1) * ((q : ℝ) * z + h) *
        s₀⁻¹ ^ (q + 2) := by
  have hsh : s₀ ≤ s + h := by linarith
  have hlocal := elementaryPhiD1_firstOrder_error
    (q := q) hs₀ hsh hz
  have hpower := reciprocalPower_add_error
    (p := q + 1) hs₀ hs hh
  have hcoef : 0 ≤ (q : ℝ) := Nat.cast_nonneg q
  have hshift :
      |(-(q : ℝ) * (s + h)⁻¹ ^ (q + 1)) -
          (-(q : ℝ) * s⁻¹ ^ (q + 1))| ≤
        (q : ℝ) * ((q + 1 : ℕ) * h * s₀⁻¹ ^ (q + 2)) := by
    rw [show (-(q : ℝ) * (s + h)⁻¹ ^ (q + 1)) -
        (-(q : ℝ) * s⁻¹ ^ (q + 1)) =
      -(q : ℝ) * ((s + h)⁻¹ ^ (q + 1) - s⁻¹ ^ (q + 1)) by ring,
      abs_mul, abs_neg, abs_of_nonneg hcoef]
    exact mul_le_mul_of_nonneg_left hpower hcoef
  calc
    |elementaryPhiD1 q (s + h) z -
        (-(q : ℝ) * s⁻¹ ^ (q + 1))| ≤
        |elementaryPhiD1 q (s + h) z -
          (-(q : ℝ) * (s + h)⁻¹ ^ (q + 1))| +
        |(-(q : ℝ) * (s + h)⁻¹ ^ (q + 1)) -
          (-(q : ℝ) * s⁻¹ ^ (q + 1))| := abs_sub_le _ _ _
    _ ≤ (q : ℝ) * (q + 1) * q * z * s₀⁻¹ ^ (q + 2) +
        (q : ℝ) * ((q + 1 : ℕ) * h * s₀⁻¹ ^ (q + 2)) :=
      add_le_add hlocal hshift
    _ = (q : ℝ) * (q + 1) * ((q : ℝ) * z + h) *
        s₀⁻¹ ^ (q + 2) := by
      push_cast
      ring

/-- The corresponding explicit estimate for the second `s`-derivative. -/
theorem elementaryPhiD2_base_error
    {q : ℕ} {s s₀ h z : ℝ}
    (hs₀ : 0 < s₀) (hs : s₀ ≤ s) (hh : 0 ≤ h) (hz : 0 ≤ z) :
    |elementaryPhiD2 q (s + h) z -
        ((q : ℝ) * (q + 1) * s⁻¹ ^ (q + 2))| ≤
      (q : ℝ) * (q + 1) * (q + 2) * ((q : ℝ) * z + h) *
        s₀⁻¹ ^ (q + 3) := by
  have hsh : s₀ ≤ s + h := by linarith
  have hlocal := elementaryPhiD2_firstOrder_error
    (q := q) hs₀ hsh hz
  have hpower := reciprocalPower_add_error
    (p := q + 2) hs₀ hs hh
  have hcoef : 0 ≤ (q : ℝ) * (q + 1) := by positivity
  have hshift :
      |(q : ℝ) * (q + 1) * (s + h)⁻¹ ^ (q + 2) -
          (q : ℝ) * (q + 1) * s⁻¹ ^ (q + 2)| ≤
        ((q : ℝ) * (q + 1)) *
          ((q + 2 : ℕ) * h * s₀⁻¹ ^ (q + 3)) := by
    rw [show (q : ℝ) * (q + 1) * (s + h)⁻¹ ^ (q + 2) -
        (q : ℝ) * (q + 1) * s⁻¹ ^ (q + 2) =
      ((q : ℝ) * (q + 1)) *
        ((s + h)⁻¹ ^ (q + 2) - s⁻¹ ^ (q + 2)) by ring,
      abs_mul, abs_of_nonneg hcoef]
    exact mul_le_mul_of_nonneg_left hpower hcoef
  calc
    |elementaryPhiD2 q (s + h) z -
        ((q : ℝ) * (q + 1) * s⁻¹ ^ (q + 2))| ≤
        |elementaryPhiD2 q (s + h) z -
          ((q : ℝ) * (q + 1) * (s + h)⁻¹ ^ (q + 2))| +
        |(q : ℝ) * (q + 1) * (s + h)⁻¹ ^ (q + 2) -
          (q : ℝ) * (q + 1) * s⁻¹ ^ (q + 2)| := abs_sub_le _ _ _
    _ ≤ (q : ℝ) * (q + 1) * (q + 2) * q * z *
          s₀⁻¹ ^ (q + 3) +
        ((q : ℝ) * (q + 1)) *
          ((q + 2 : ℕ) * h * s₀⁻¹ ^ (q + 3)) :=
      add_le_add hlocal hshift
    _ = (q : ℝ) * (q + 1) * (q + 2) * ((q : ℝ) * z + h) *
        s₀⁻¹ ^ (q + 3) := by
      push_cast
      ring

/-- A continuous function on `[0,1]` whose pointwise error from a constant
is bounded by `C` has the same bound after averaging. -/
theorem abs_integral_Icc_zero_one_sub_const_le
    {f : ℝ → ℝ} {c C : ℝ}
    (hf : IntegrableOn f (Set.Icc (0 : ℝ) 1) volume)
    (hC : ∀ u ∈ Set.Icc (0 : ℝ) 1, |f u - c| ≤ C) :
    |(∫ u in Set.Icc (0 : ℝ) 1, f u) - c| ≤ C := by
  have hconst : (∫ _u : ℝ in Set.Icc (0 : ℝ) 1, c) = c := by
    rw [setIntegral_const, smul_eq_mul]
    simp [Real.volume_real_Icc_of_le]
  rw [← hconst, ← integral_sub hf
    (integrableOn_const (s := Set.Icc (0 : ℝ) 1)
      (μ := volume) measure_Icc_lt_top.ne)]
  have hnorm := norm_setIntegral_le_of_norm_le_const
    (μ := volume) (s := Set.Icc (0 : ℝ) 1)
    (f := fun u => f u - c) (C := C) measure_Icc_lt_top
    (fun u hu => by simpa [Real.norm_eq_abs] using hC u hu)
  simpa [Real.norm_eq_abs, Real.volume_real_Icc_of_le] using hnorm

/-- Averaging the displaced first derivative retains the same explicit
uniform error. -/
theorem elementaryPhiD1_average_base_error
    {q : ℕ} {t t₀ w e x : ℝ}
    (ht₀ : 0 < t₀) (ht : t₀ ≤ t) (hw : 0 ≤ w)
    (he : 0 ≤ e) (hx : 0 ≤ x) :
    |(∫ u in Set.Icc (0 : ℝ) 1,
        elementaryPhiD1 q (t + u * (w * e)) x) -
        (-(q : ℝ) * t⁻¹ ^ (q + 1))| ≤
      (q : ℝ) * (q + 1) * ((q : ℝ) * x + w * e) *
        t₀⁻¹ ^ (q + 2) := by
  let f : ℝ → ℝ := fun u => elementaryPhiD1 q (t + u * (w * e)) x
  have htpos : 0 < t := ht₀.trans_le ht
  have hfcont : ContinuousOn f (Set.Icc (0 : ℝ) 1) := by
    intro u hu
    have hh : 0 ≤ u * (w * e) := mul_nonneg hu.1 (mul_nonneg hw he)
    have hpos : 0 < t + u * (w * e) := by linarith
    have hinner : HasDerivAt (fun v : ℝ => t + v * (w * e)) (w * e) u := by
      simpa [mul_comm] using ((hasDerivAt_id u).mul_const (w * e)).const_add t
    have hcomp := (hasDerivAt_elementaryPhi_firstDerivative
      (q := q) hpos hx).comp u hinner
    simpa [f, Function.comp_def] using hcomp.continuousAt.continuousWithinAt
  apply abs_integral_Icc_zero_one_sub_const_le
    (hfcont.integrableOn_compact isCompact_Icc)
  intro u hu
  have huwe : 0 ≤ u * (w * e) :=
    mul_nonneg hu.1 (mul_nonneg hw he)
  have huwe_le : u * (w * e) ≤ w * e := by
    have hwe : 0 ≤ w * e := mul_nonneg hw he
    nlinarith [mul_le_mul_of_nonneg_right hu.2 hwe]
  have hraw := elementaryPhiD1_base_error
    (q := q) ht₀ ht huwe hx
  change |f u - (-(q : ℝ) * t⁻¹ ^ (q + 1))| ≤ _
  calc
    |f u - (-(q : ℝ) * t⁻¹ ^ (q + 1))| ≤
        (q : ℝ) * (q + 1) * ((q : ℝ) * x + u * (w * e)) *
          t₀⁻¹ ^ (q + 2) := hraw
    _ ≤ (q : ℝ) * (q + 1) * ((q : ℝ) * x + w * e) *
          t₀⁻¹ ^ (q + 2) := by
      gcongr

/-- Quantitative `B-C` divided-difference estimate. -/
theorem elementaryPhi_paired_value_error
    {q : ℕ} {t t₀ w e x : ℝ}
    (ht₀ : 0 < t₀) (ht : t₀ ≤ t) (hw : 0 ≤ w)
    (he : 0 < e) (hx : 0 ≤ x) :
    |(elementaryPhi q t x - elementaryPhi q (t + w * e) x) / e -
        (q : ℝ) * w * t⁻¹ ^ (q + 1)| ≤
      w * ((q : ℝ) * (q + 1) * ((q : ℝ) * x + w * e) *
        t₀⁻¹ ^ (q + 2)) := by
  have htpos : 0 < t := ht₀.trans_le ht
  rw [elementaryPhi_paired_dividedDifference
    (q := q) htpos hw he hx]
  have havg := elementaryPhiD1_average_base_error
    (q := q) ht₀ ht hw he.le hx
  rw [show -w * (∫ u in Set.Icc (0 : ℝ) 1,
      elementaryPhiD1 q (t + u * (w * e)) x) -
        (q : ℝ) * w * t⁻¹ ^ (q + 1) =
      -w * ((∫ u in Set.Icc (0 : ℝ) 1,
        elementaryPhiD1 q (t + u * (w * e)) x) -
          (-(q : ℝ) * t⁻¹ ^ (q + 1))) by ring,
    abs_mul, abs_neg, abs_of_nonneg hw]
  exact mul_le_mul_of_nonneg_left havg hw

/-- Quantitative pairing of the `D` boundary with the exact gamma
half-shift.  The first summand on the right is precisely the unavoidable
`x/e` term. -/
theorem elementaryPhi_boundary_value_error
    {q : ℕ} {delta e x : ℝ}
    (hdelta : 0 ≤ delta) (he : 0 < e) (hx : 0 ≤ x) :
    |(elementaryPhi q (1 + x / 2) x -
          elementaryPhi q (1 + delta * e) x) / e -
        (q : ℝ) * delta| ≤
      (q : ℝ) * (x / e) +
        delta * ((q : ℝ) * (q + 1) *
          ((q : ℝ) * x + delta * e)) := by
  have hhalf := elementaryPhi_halfShift_div_bound (q := q) hx he
  have hpair := elementaryPhi_paired_value_error
    (q := q) (t₀ := 1) (t := 1) (w := delta) (e := e) (x := x)
    (by norm_num) (by norm_num) hdelta he hx
  simp only [inv_one, one_pow, mul_one] at hpair
  have hsplit :
      (elementaryPhi q (1 + x / 2) x -
          elementaryPhi q (1 + delta * e) x) / e -
          (q : ℝ) * delta =
        (elementaryPhi q (1 + x / 2) x - elementaryPhi q 1 x) / e +
        ((elementaryPhi q 1 x - elementaryPhi q (1 + delta * e) x) / e -
          (q : ℝ) * delta) := by ring
  rw [hsplit]
  calc
    |(elementaryPhi q (1 + x / 2) x - elementaryPhi q 1 x) / e +
        ((elementaryPhi q 1 x - elementaryPhi q (1 + delta * e) x) / e -
          (q : ℝ) * delta)| ≤
      |(elementaryPhi q (1 + x / 2) x - elementaryPhi q 1 x) / e| +
        |(elementaryPhi q 1 x - elementaryPhi q (1 + delta * e) x) / e -
          (q : ℝ) * delta| := abs_add_le _ _
    _ ≤ (q : ℝ) * (x / e) +
        delta * ((q : ℝ) * (q + 1) *
          ((q : ℝ) * x + delta * e)) :=
      add_le_add hhalf hpair

end

end Zeta23.Research.JensenWedge
