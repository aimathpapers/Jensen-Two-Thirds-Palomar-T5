import Zeta23.Research.JensenWedge.HermiteGenocchiCube

/-!
# Differentiating complex segment moments

This file supplies the repeated differentiation-under-the-integral step used
in the complex Hermite--Genocchi proof.  Compactness of a local complex ball
times the real unit interval provides the domination required by Mathlib's
parametric Bochner-integral theorem.
-/

open scoped Interval

namespace Zeta23.Research.JensenWedge

/-- A weighted derivative average along the segment from `a` to `z`. -/
noncomputable def complexSegmentMoment (k : ℕ) (g : ℂ → ℂ) (a z : ℂ) : ℂ :=
  ∫ t : ℝ in (0 : ℝ)..1, ((t ^ k : ℝ) : ℂ) * g (AffineMap.lineMap a z t)

/-- Recursively associated powers of the segment parameter.  The recursive
form makes the differentiation rule definitionally visible. -/
def segmentWeight : ℕ → ℝ → ℂ
  | 0 => fun _ => 1
  | k + 1 => fun t => segmentWeight k t * (t : ℂ)

theorem continuous_segmentWeight (k : ℕ) : Continuous (segmentWeight k) := by
  induction k with
  | zero => exact continuous_const
  | succ k ih =>
      simp only [segmentWeight]
      fun_prop

theorem segmentWeight_eq_pow (k : ℕ) (t : ℝ) :
    segmentWeight k t = (t : ℂ) ^ k := by
  induction k with
  | zero => simp [segmentWeight]
  | succ k ih => simp [segmentWeight, ih, pow_succ]

private theorem norm_segmentWeight_integral_le
    {g : ℝ → ℂ} {C : ℝ} (r : ℕ) (hC : 0 ≤ C)
    (hg : ∀ t ∈ Set.uIcc (0 : ℝ) 1, ‖g t‖ ≤ C) :
    ‖∫ t : ℝ in (0 : ℝ)..1, segmentWeight r t * g t‖ ≤ C / (r + 1 : ℝ) := by
  calc
    ‖∫ t : ℝ in (0 : ℝ)..1, segmentWeight r t * g t‖
        ≤ ∫ t : ℝ in (0 : ℝ)..1, t ^ r * C := by
      apply intervalIntegral.norm_integral_le_of_norm_le zero_le_one
      · filter_upwards [] with t ht
        have htcc : t ∈ Set.uIcc (0 : ℝ) 1 := by
          rw [Set.uIcc_of_le zero_le_one]
          exact ⟨ht.1.le, ht.2⟩
        have htw : ‖segmentWeight r t‖ = t ^ r := by
          rw [segmentWeight_eq_pow, norm_pow, Complex.norm_real, Real.norm_eq_abs,
            abs_of_nonneg ht.1.le]
        rw [norm_mul, htw]
        exact mul_le_mul_of_nonneg_left (hg t htcc) (pow_nonneg ht.1.le r)
      · exact ((by fun_prop : Continuous (fun t : ℝ => t ^ r * C))).intervalIntegrable 0 1
    _ = C / (r + 1 : ℝ) := by
      rw [intervalIntegral.integral_mul_const, integral_pow]
      norm_num
      ring

/-- Recursive mass of row `i`, column `r` of the moment triangle. -/
noncomputable def hermiteGenocchiTriangleMass : ℕ → ℕ → ℝ
  | 0, r => 1 / (r + 1 : ℝ)
  | i + 1, r => hermiteGenocchiTriangleMass i (r + 1) / (r + 1 : ℝ)

theorem hermiteGenocchiTriangleMass_nonneg (i r : ℕ) :
    0 ≤ hermiteGenocchiTriangleMass i r := by
  induction i generalizing r with
  | zero =>
      simp only [hermiteGenocchiTriangleMass]
      exact div_nonneg zero_le_one (by positivity)
  | succ i ih =>
      simp only [hermiteGenocchiTriangleMass]
      exact div_nonneg (ih (r + 1)) (by positivity)

theorem hermiteGenocchiTriangleMass_five_zero :
    hermiteGenocchiTriangleMass 5 0 = 1 / 720 := by
  norm_num [hermiteGenocchiTriangleMass]

/-- The triangular family of nested segment moments.  Row `i`, column `r`
uses nodes `0,...,i` and the derivative of order `i+r+1`. -/
noncomputable def hermiteGenocchiTriangle
    (derivs : ℕ → ℂ → ℂ) (nodes : ℕ → ℂ) : ℕ → ℕ → ℂ → ℂ
  | 0, r, z => ∫ t : ℝ in (0 : ℝ)..1,
      segmentWeight r t * derivs (r + 1) (AffineMap.lineMap (nodes 0) z t)
  | i + 1, r, z => ∫ t : ℝ in (0 : ℝ)..1,
      segmentWeight r t *
        hermiteGenocchiTriangle derivs nodes i (r + 1)
          (AffineMap.lineMap (nodes (i + 1)) z t)

/-- A derivative bound on a convex set controls every compatible row of the
moment triangle by its exact recursive simplex mass. -/
theorem norm_hermiteGenocchiTriangle_le
    (derivs : ℕ → ℂ → ℂ) (nodes : ℕ → ℂ) {s : Set ℂ}
    (hs : Convex ℝ s) {M : ℝ} (hM : 0 ≤ M)
    (i r : ℕ) {z : ℂ} (hz : z ∈ s)
    (hnodes : ∀ j, j ≤ i → nodes j ∈ s)
    (hbound : ∀ w ∈ s, ‖derivs (i + r + 1) w‖ ≤ M) :
    ‖hermiteGenocchiTriangle derivs nodes i r z‖ ≤
      M * hermiteGenocchiTriangleMass i r := by
  induction i generalizing r z with
  | zero =>
      refine (norm_segmentWeight_integral_le
        (g := fun t : ℝ => derivs (r + 1) (AffineMap.lineMap (nodes 0) z t))
        r hM ?_).trans_eq ?_
      · intro t ht
        simpa using hbound (AffineMap.lineMap (nodes 0) z t)
          (hs.lineMap_mem (hnodes 0 le_rfl) hz (by
            simpa [Set.uIcc_of_le zero_le_one] using ht))
      · simp [hermiteGenocchiTriangle, hermiteGenocchiTriangleMass]
        ring
  | succ i ih =>
      let C := M * hermiteGenocchiTriangleMass i (r + 1)
      have hC : 0 ≤ C := mul_nonneg hM (hermiteGenocchiTriangleMass_nonneg i (r + 1))
      refine (norm_segmentWeight_integral_le
        (g := fun t : ℝ => hermiteGenocchiTriangle derivs nodes i (r + 1)
          (AffineMap.lineMap (nodes (i + 1)) z t)) r hC ?_).trans_eq ?_
      · intro t ht
        apply ih (r + 1)
        · exact hs.lineMap_mem (hnodes (i + 1) le_rfl) hz (by
            simpa [Set.uIcc_of_le zero_le_one] using ht)
        · intro j hj
          exact hnodes j (hj.trans i.le_succ)
        · intro w hw
          simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hbound w hw
      · simp only [hermiteGenocchiTriangle, hermiteGenocchiTriangleMass, C]
        ring

/-- The one-step Newton factorization obtained from complex FTC on a line
segment. -/
theorem complexSegment_factor_of_eq_zero
    (g g' : ℂ → ℂ) (a z : ℂ)
    (hg : ∀ w : ℂ, HasDerivAt g (g' w) w)
    (hg' : Continuous g') (hga : g a = 0) :
    g z = (z - a) * ∫ t : ℝ in (0 : ℝ)..1, g' (AffineMap.lineMap a z t) := by
  have hderiv : ∀ t ∈ Set.uIcc (0 : ℝ) 1,
      HasDerivAt (fun s : ℝ => g (AffineMap.lineMap a z s))
        ((z - a) * g' (AffineMap.lineMap a z t)) t := by
    intro t _
    have hline : HasDerivAt (fun s : ℝ => AffineMap.lineMap a z s) (z - a) t := by
      exact AffineMap.hasDerivAt_lineMap
    have hcomp := (hg (AffineMap.lineMap a z t)).scomp t hline
    simpa [Function.comp_def, smul_eq_mul] using hcomp
  have hint : IntervalIntegrable
      (fun t : ℝ => (z - a) * g' (AffineMap.lineMap a z t))
      MeasureTheory.volume 0 1 := by
    apply Continuous.intervalIntegrable
    fun_prop (disch := assumption)
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint
  rw [intervalIntegral.integral_const_mul] at hFTC
  rw [AffineMap.lineMap_apply_one, AffineMap.lineMap_apply_zero, hga, sub_zero] at hFTC
  exact hFTC.symm

/-- Local complex FTC factorization on a convex domain. -/
theorem complexSegment_factor_of_eq_zeroOn
    (u : Set ℂ) (hconv : Convex ℝ u)
    (g g' : ℂ → ℂ) (a z : ℂ)
    (ha : a ∈ u) (hz : z ∈ u)
    (hg : ∀ w ∈ u, HasDerivAt g (g' w) w)
    (hg' : ContinuousOn g' u) (hga : g a = 0) :
    g z = (z - a) * ∫ t : ℝ in (0 : ℝ)..1,
      g' (AffineMap.lineMap a z t) := by
  have hmap : Set.MapsTo (fun t : ℝ => AffineMap.lineMap a z t)
      (Set.Icc (0 : ℝ) 1) u := fun t ht => hconv.lineMap_mem ha hz ht
  have hlineContinuous : Continuous
      (fun t : ℝ => AffineMap.lineMap a z t) := by fun_prop
  have hderiv : ∀ t ∈ Set.uIcc (0 : ℝ) 1,
      HasDerivAt (fun s : ℝ => g (AffineMap.lineMap a z s))
        ((z - a) * g' (AffineMap.lineMap a z t)) t := by
    intro t ht
    have htIcc : t ∈ Set.Icc (0 : ℝ) 1 := by
      simpa [Set.uIcc_of_le zero_le_one] using ht
    have hcomp := (hg _ (hmap htIcc)).scomp t AffineMap.hasDerivAt_lineMap
    simpa [Function.comp_def, smul_eq_mul] using hcomp
  have hint : IntervalIntegrable
      (fun t : ℝ => (z - a) * g' (AffineMap.lineMap a z t))
      MeasureTheory.volume 0 1 := by
    have hc := hg'.comp' hlineContinuous.continuousOn hmap
    exact (continuous_const.continuousOn.mul hc).intervalIntegrable_of_Icc zero_le_one
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint
  rw [intervalIntegral.integral_const_mul] at hFTC
  rw [AffineMap.lineMap_apply_one, AffineMap.lineMap_apply_zero, hga, sub_zero] at hFTC
  exact hFTC.symm

/-- Differentiation of a segment integral multiplies its scalar weight by
the segment parameter.  The proof obtains the dominating constant from
compactness, rather than taking it as an additional hypothesis. -/
theorem hasDerivAt_complexSegmentWeighted
    (weight : ℝ → ℂ) (g g' : ℂ → ℂ) (a z : ℂ)
    (hweight : Continuous weight)
    (hg : ∀ w : ℂ, HasDerivAt g (g' w) w)
    (hg' : Continuous g') :
    HasDerivAt
      (fun x : ℂ => ∫ t : ℝ in (0 : ℝ)..1,
        weight t * g (AffineMap.lineMap a x t))
      (∫ t : ℝ in (0 : ℝ)..1,
        (weight t * (t : ℂ)) * g' (AffineMap.lineMap a z t)) z := by
  let F : ℂ → ℝ → ℂ := fun x t =>
    weight t * g (AffineMap.lineMap a x t)
  let F' : ℂ → ℝ → ℂ := fun x t =>
    (weight t * (t : ℂ)) * g' (AffineMap.lineMap a x t)
  let K : Set (ℂ × ℝ) := Metric.closedBall z 1 ×ˢ Set.Icc (0 : ℝ) 1
  have hgcont : Continuous g := continuous_iff_continuousAt.2 fun w => (hg w).continuousAt
  have hK : IsCompact K := (isCompact_closedBall z 1).prod isCompact_Icc
  have hF'cont : Continuous (fun p : ℂ × ℝ => F' p.1 p.2) := by
    dsimp [F']
    fun_prop (disch := assumption)
  obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn hF'cont.continuousOn
  have hparam := intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (𝕜 := ℂ) (E := ℂ) (μ := MeasureTheory.volume)
    (F := F) (F' := F') (x₀ := z) (s := Metric.ball z 1)
    (bound := fun _ : ℝ => C) (a := 0) (b := 1)
    (Metric.ball_mem_nhds z zero_lt_one)
    (by
      filter_upwards [] with x
      exact ((by
        dsimp [F]
        fun_prop (disch := assumption) : Continuous (F x))).aestronglyMeasurable)
    ((by
      dsimp [F]
      fun_prop (disch := assumption) : Continuous (F z)).intervalIntegrable 0 1)
    ((by
      dsimp [F']
      fun_prop : Continuous (F' z)).aestronglyMeasurable)
    (by
      filter_upwards [] with t ht x hx
      apply hC (x, t)
      rw [Set.uIoc_of_le zero_le_one] at ht
      exact ⟨Metric.mem_closedBall.2 (Metric.mem_ball.1 hx).le, ⟨ht.1.le, ht.2⟩⟩)
    ((continuous_const.intervalIntegrable 0 1))
    (by
      filter_upwards [] with t ht x hx
      have hline : HasDerivAt (fun y : ℂ => AffineMap.lineMap a y t) (t : ℂ) x := by
        have hlinear : HasDerivAt
            (fun y : ℂ => (t : ℂ) * y + ((1 - t : ℝ) : ℂ) * a) (t : ℂ) x := by
          simpa using ((hasDerivAt_id x).const_mul (t : ℂ)).add_const
            (((1 - t : ℝ) : ℂ) * a)
        convert hlinear using 1 <;> simp [AffineMap.lineMap_apply_module] <;> ring
      have hcomp := (hg (AffineMap.lineMap a x t)).comp x hline
      have hmul := hcomp.const_mul (weight t)
      have hmul' : HasDerivAt
          (fun y : ℂ => weight t * g (AffineMap.lineMap a y t))
          ((weight t * (t : ℂ)) * g' (AffineMap.lineMap a x t)) x := by
        apply hmul.congr_deriv
        ring
      simpa only [F, F', Function.comp_apply] using hmul')
  exact hparam.2

/-- Localized differentiation of a weighted complex segment integral.  An
open convex domain contains every perturbed segment needed by the parametric
integral theorem, so no global analyticity hypothesis is required. -/
theorem hasDerivAt_complexSegmentWeightedOn
    (u : Set ℂ) (hu : IsOpen u) (hconv : Convex ℝ u)
    (weight : ℝ → ℂ) (g g' : ℂ → ℂ) (a z : ℂ)
    (hweight : Continuous weight)
    (ha : a ∈ u) (hz : z ∈ u)
    (hg : ∀ w ∈ u, HasDerivAt g (g' w) w)
    (hg' : ContinuousOn g' u) :
    HasDerivAt
      (fun x : ℂ => ∫ t : ℝ in (0 : ℝ)..1,
        weight t * g (AffineMap.lineMap a x t))
      (∫ t : ℝ in (0 : ℝ)..1,
        (weight t * (t : ℂ)) * g' (AffineMap.lineMap a z t)) z := by
  obtain ⟨ε, hεpos, hε⟩ := Metric.isOpen_iff.mp hu z hz
  let r : ℝ := ε / 2
  have hrpos : 0 < r := by dsimp [r]; positivity
  have hrlt : r < ε := by dsimp [r]; linarith
  have hclosed : Metric.closedBall z r ⊆ u :=
    (Metric.closedBall_subset_ball hrlt).trans hε
  let F : ℂ → ℝ → ℂ := fun x t =>
    weight t * g (AffineMap.lineMap a x t)
  let F' : ℂ → ℝ → ℂ := fun x t =>
    (weight t * (t : ℂ)) * g' (AffineMap.lineMap a x t)
  let K : Set (ℂ × ℝ) := Metric.closedBall z r ×ˢ Set.Icc (0 : ℝ) 1
  have hlineMaps : Set.MapsTo
      (fun p : ℂ × ℝ => AffineMap.lineMap a p.1 p.2) K u := by
    rintro ⟨x, t⟩ ⟨hx, ht⟩
    exact hconv.lineMap_mem ha (hclosed hx) ht
  have hlineContinuous : Continuous
      (fun p : ℂ × ℝ => AffineMap.lineMap a p.1 p.2) := by
    fun_prop
  have hF'cont : ContinuousOn (fun p : ℂ × ℝ => F' p.1 p.2) K := by
    have hcomp := hg'.comp' hlineContinuous.continuousOn hlineMaps
    have hw : Continuous (fun p : ℂ × ℝ => weight p.2 * (p.2 : ℂ)) := by
      fun_prop
    exact hw.continuousOn.mul hcomp
  have hK : IsCompact K := (isCompact_closedBall z r).prod isCompact_Icc
  obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn hF'cont
  have hgcont : ContinuousOn g u := fun w hw => (hg w hw).continuousAt.continuousWithinAt
  have hparam := intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (𝕜 := ℂ) (E := ℂ) (μ := MeasureTheory.volume)
    (F := F) (F' := F') (x₀ := z) (s := Metric.ball z r)
    (bound := fun _ : ℝ => C) (a := 0) (b := 1)
    (Metric.ball_mem_nhds z hrpos)
    (by
      filter_upwards [Metric.ball_mem_nhds z hrpos] with x hx
      have hxU : x ∈ u := hclosed (Metric.mem_closedBall.2 (Metric.mem_ball.1 hx).le)
      have hmap : Set.MapsTo (fun t : ℝ => AffineMap.lineMap a x t)
          (Set.uIoc (0 : ℝ) 1) u := by
        intro t ht
        exact hconv.lineMap_mem ha hxU (by
          rw [Set.uIoc_of_le zero_le_one] at ht
          exact ⟨ht.1.le, ht.2⟩)
      have hline : Continuous (fun t : ℝ => AffineMap.lineMap a x t) := by fun_prop
      have hc := hgcont.comp' hline.continuousOn hmap
      exact (hweight.continuousOn.mul hc).aestronglyMeasurable measurableSet_uIoc)
    (by
      have hmap : Set.MapsTo (fun t : ℝ => AffineMap.lineMap a z t)
          (Set.Icc (0 : ℝ) 1) u := fun t ht => hconv.lineMap_mem ha hz ht
      have hline : Continuous (fun t : ℝ => AffineMap.lineMap a z t) := by fun_prop
      exact (hweight.continuousOn.mul
        (hgcont.comp' hline.continuousOn hmap)).intervalIntegrable_of_Icc zero_le_one)
    (by
      have hmap : Set.MapsTo (fun t : ℝ => AffineMap.lineMap a z t)
          (Set.uIoc (0 : ℝ) 1) u := by
        intro t ht
        exact hconv.lineMap_mem ha hz (by
          rw [Set.uIoc_of_le zero_le_one] at ht
          exact ⟨ht.1.le, ht.2⟩)
      have hline : Continuous (fun t : ℝ => AffineMap.lineMap a z t) := by fun_prop
      have hc := hg'.comp' hline.continuousOn hmap
      have hw : Continuous (fun t : ℝ => weight t * (t : ℂ)) := by fun_prop
      exact (hw.continuousOn.mul hc).aestronglyMeasurable measurableSet_uIoc)
    (by
      filter_upwards [] with t ht x hx
      apply hC (x, t)
      rw [Set.uIoc_of_le zero_le_one] at ht
      exact ⟨Metric.mem_closedBall.2 (Metric.mem_ball.1 hx).le, ⟨ht.1.le, ht.2⟩⟩)
    (continuous_const.intervalIntegrable 0 1)
    (by
      filter_upwards [] with t ht x hx
      have hxU : x ∈ u := hclosed (Metric.mem_closedBall.2 (Metric.mem_ball.1 hx).le)
      have htIcc : t ∈ Set.Icc (0 : ℝ) 1 := by
        rw [Set.uIoc_of_le zero_le_one] at ht
        exact ⟨ht.1.le, ht.2⟩
      have hlineMem := hconv.lineMap_mem ha hxU htIcc
      have hline : HasDerivAt (fun y : ℂ => AffineMap.lineMap a y t) (t : ℂ) x := by
        have hlinear : HasDerivAt
            (fun y : ℂ => (t : ℂ) * y + ((1 - t : ℝ) : ℂ) * a) (t : ℂ) x := by
          simpa using ((hasDerivAt_id x).const_mul (t : ℂ)).add_const
            (((1 - t : ℝ) : ℂ) * a)
        convert hlinear using 1 <;> simp [AffineMap.lineMap_apply_module] <;> ring
      have hcomp := (hg _ hlineMem).comp x hline
      have hmul := hcomp.const_mul (weight t)
      apply hmul.congr_deriv
      ring)
  exact hparam.2

/-- Every entry of the Hermite--Genocchi triangle differentiates to the next
column. -/
theorem hasDerivAt_hermiteGenocchiTriangle
    (derivs : ℕ → ℂ → ℂ) (nodes : ℕ → ℂ)
    (hderiv : ∀ n w, HasDerivAt (derivs n) (derivs (n + 1) w) w)
    (hcont : ∀ n, Continuous (derivs n))
    (i r : ℕ) (z : ℂ) :
    HasDerivAt (hermiteGenocchiTriangle derivs nodes i r)
      (hermiteGenocchiTriangle derivs nodes i (r + 1) z) z := by
  induction i generalizing r z with
  | zero =>
      simpa only [hermiteGenocchiTriangle, segmentWeight] using
        hasDerivAt_complexSegmentWeighted (segmentWeight r) (derivs (r + 1))
          (derivs (r + 2)) (nodes 0) z (continuous_segmentWeight r)
          (by
            intro w
            simpa [Nat.add_assoc] using hderiv (r + 1) w)
          (by simpa [Nat.add_assoc] using hcont (r + 2))
  | succ i ih =>
      have hg : ∀ w, HasDerivAt
          (hermiteGenocchiTriangle derivs nodes i (r + 1))
          (hermiteGenocchiTriangle derivs nodes i (r + 2) w) w := by
        intro w
        simpa [Nat.add_assoc] using ih (r := r + 1) (z := w)
      have hg' : Continuous (hermiteGenocchiTriangle derivs nodes i (r + 2)) :=
        continuous_iff_continuousAt.2 fun w =>
          (ih (r := r + 2) (z := w)).continuousAt
      simpa only [hermiteGenocchiTriangle, segmentWeight] using
        hasDerivAt_complexSegmentWeighted (segmentWeight r)
          (hermiteGenocchiTriangle derivs nodes i (r + 1))
          (hermiteGenocchiTriangle derivs nodes i (r + 2))
          (nodes (i + 1)) z (continuous_segmentWeight r) hg hg'

/-- The moment triangle differentiates inside any open convex domain
containing the active nodes. -/
theorem hasDerivAt_hermiteGenocchiTriangleOn
    (u : Set ℂ) (hu : IsOpen u) (hconv : Convex ℝ u)
    (derivs : ℕ → ℂ → ℂ) (nodes : ℕ → ℂ)
    (hderiv : ∀ n w, w ∈ u → HasDerivAt (derivs n) (derivs (n + 1) w) w)
    (hcont : ∀ n, ContinuousOn (derivs n) u)
    (i r : ℕ) (z : ℂ)
    (hnodes : ∀ j, j ≤ i → nodes j ∈ u) (hz : z ∈ u) :
    HasDerivAt (hermiteGenocchiTriangle derivs nodes i r)
      (hermiteGenocchiTriangle derivs nodes i (r + 1) z) z := by
  induction i generalizing r z with
  | zero =>
      simpa only [hermiteGenocchiTriangle, segmentWeight] using
        hasDerivAt_complexSegmentWeightedOn u hu hconv
          (segmentWeight r) (derivs (r + 1)) (derivs (r + 2)) (nodes 0) z
          (continuous_segmentWeight r) (hnodes 0 le_rfl) hz
          (by
            intro w hw
            simpa [Nat.add_assoc] using hderiv (r + 1) w hw)
          (by simpa [Nat.add_assoc] using hcont (r + 2))
  | succ i ih =>
      have hnodes' : ∀ j, j ≤ i → nodes j ∈ u := fun j hj =>
        hnodes j (hj.trans i.le_succ)
      have hg : ∀ w ∈ u, HasDerivAt
          (hermiteGenocchiTriangle derivs nodes i (r + 1))
          (hermiteGenocchiTriangle derivs nodes i (r + 2) w) w := by
        intro w hw
        simpa [Nat.add_assoc] using ih (r := r + 1) (z := w) hnodes' hw
      have hg' : ContinuousOn (hermiteGenocchiTriangle derivs nodes i (r + 2)) u :=
        fun w hw => (ih (r := r + 2) (z := w) hnodes' hw).continuousAt.continuousWithinAt
      simpa only [hermiteGenocchiTriangle, segmentWeight] using
        hasDerivAt_complexSegmentWeightedOn u hu hconv
          (segmentWeight r)
          (hermiteGenocchiTriangle derivs nodes i (r + 1))
          (hermiteGenocchiTriangle derivs nodes i (r + 2))
          (nodes (i + 1)) z (continuous_segmentWeight r)
          (hnodes (i + 1) le_rfl) hz hg hg'

/-- One row of the triangle supplies the next Newton factor. -/
theorem hermiteGenocchiTriangle_factor
    (derivs : ℕ → ℂ → ℂ) (nodes : ℕ → ℂ)
    (hderiv : ∀ n w, HasDerivAt (derivs n) (derivs (n + 1) w) w)
    (hcont : ∀ n, Continuous (derivs n))
    (i : ℕ)
    (hzero : hermiteGenocchiTriangle derivs nodes i 0 (nodes (i + 1)) = 0)
    (z : ℂ) :
    hermiteGenocchiTriangle derivs nodes i 0 z =
      (z - nodes (i + 1)) * hermiteGenocchiTriangle derivs nodes (i + 1) 0 z := by
  have hg : ∀ w, HasDerivAt (hermiteGenocchiTriangle derivs nodes i 0)
      (hermiteGenocchiTriangle derivs nodes i 1 w) w := by
    intro w
    simpa using hasDerivAt_hermiteGenocchiTriangle derivs nodes hderiv hcont i 0 w
  have hg' : Continuous (hermiteGenocchiTriangle derivs nodes i 1) :=
    continuous_iff_continuousAt.2 fun w =>
      (hasDerivAt_hermiteGenocchiTriangle derivs nodes hderiv hcont i 1 w).continuousAt
  simpa only [hermiteGenocchiTriangle, segmentWeight, one_mul] using
    complexSegment_factor_of_eq_zero
      (hermiteGenocchiTriangle derivs nodes i 0)
      (hermiteGenocchiTriangle derivs nodes i 1)
      (nodes (i + 1)) z hg hg' hzero

/-- A row of the moment triangle supplies the next Newton factor inside an
open convex analytic domain. -/
theorem hermiteGenocchiTriangle_factorOn
    (u : Set ℂ) (hu : IsOpen u) (hconv : Convex ℝ u)
    (derivs : ℕ → ℂ → ℂ) (nodes : ℕ → ℂ)
    (hderiv : ∀ n w, w ∈ u → HasDerivAt (derivs n) (derivs (n + 1) w) w)
    (hcont : ∀ n, ContinuousOn (derivs n) u)
    (i : ℕ) (hnodes : ∀ j, j ≤ i + 1 → nodes j ∈ u)
    (hzero : hermiteGenocchiTriangle derivs nodes i 0 (nodes (i + 1)) = 0)
    (z : ℂ) (hz : z ∈ u) :
    hermiteGenocchiTriangle derivs nodes i 0 z =
      (z - nodes (i + 1)) * hermiteGenocchiTriangle derivs nodes (i + 1) 0 z := by
  have hnodes' : ∀ j, j ≤ i → nodes j ∈ u := fun j hj =>
    hnodes j (hj.trans (Nat.le_add_right i 1))
  have hg : ∀ w ∈ u, HasDerivAt (hermiteGenocchiTriangle derivs nodes i 0)
      (hermiteGenocchiTriangle derivs nodes i 1 w) w := by
    intro w hw
    simpa using hasDerivAt_hermiteGenocchiTriangleOn u hu hconv derivs nodes
      hderiv hcont i 0 w hnodes' hw
  have hg' : ContinuousOn (hermiteGenocchiTriangle derivs nodes i 1) u :=
    fun w hw =>
      (hasDerivAt_hermiteGenocchiTriangleOn u hu hconv derivs nodes
        hderiv hcont i 1 w hnodes' hw).continuousAt.continuousWithinAt
  simpa only [hermiteGenocchiTriangle, segmentWeight, one_mul] using
    complexSegment_factor_of_eq_zeroOn u hconv
      (hermiteGenocchiTriangle derivs nodes i 0)
      (hermiteGenocchiTriangle derivs nodes i 1)
      (nodes (i + 1)) z (hnodes (i + 1) le_rfl) hz hg hg' hzero

/-- The exact six-node Newton identity obtained by six repeated complex FTC
steps.  No divided-difference or Hermite--Genocchi equality is assumed. -/
theorem hermiteGenocchiSix_newton_identity
    (derivs : ℕ → ℂ → ℂ)
    (hderiv : ∀ n w, HasDerivAt (derivs n) (derivs (n + 1) w) w)
    (hcont : ∀ n, Continuous (derivs n))
    (hzero : derivs 0 0 = 0 ∧ derivs 0 1 = 0 ∧ derivs 0 2 = 0 ∧
      derivs 0 3 = 0 ∧ derivs 0 4 = 0 ∧ derivs 0 5 = 0)
    (z : ℂ) :
    derivs 0 z =
      (z * (z - 1) * (z - 2) * (z - 3) * (z - 4) * (z - 5)) *
        hermiteGenocchiTriangle derivs (fun n => (n : ℂ)) 5 0 z := by
  let nodes : ℕ → ℂ := fun n => (n : ℂ)
  let q : ℕ → ℂ → ℂ := fun i => hermiteGenocchiTriangle derivs nodes i 0
  rcases hzero with ⟨hf0, hf1, hf2, hf3, hf4, hf5⟩
  have hbase : ∀ w, derivs 0 w = (w - nodes 0) * q 0 w := by
    intro w
    simpa [q, nodes, hermiteGenocchiTriangle, segmentWeight] using
      complexSegment_factor_of_eq_zero (derivs 0) (derivs 1) (nodes 0) w
        (hderiv 0) (hcont 1) (by simpa [nodes] using hf0)
  have propagate {g r : ℂ → ℂ} {a b : ℂ}
      (hfac : g b = (b - a) * r b) (hgb : g b = 0) (hba : b ≠ a) : r b = 0 := by
    rw [hgb] at hfac
    exact (mul_eq_zero.mp hfac.symm).resolve_left (sub_ne_zero.mpr hba)
  have hq0_1 : q 0 1 = 0 :=
    propagate (hbase 1) hf1 (by norm_num [nodes])
  have hfac0 : ∀ w, q 0 w = (w - nodes 1) * q 1 w := by
    intro w
    simpa [q] using hermiteGenocchiTriangle_factor derivs nodes hderiv hcont 0
      (by simpa [q, nodes] using hq0_1) w
  have hq0_2 : q 0 2 = 0 :=
    propagate (hbase 2) hf2 (by norm_num [nodes])
  have hq1_2 : q 1 2 = 0 :=
    propagate (hfac0 2) hq0_2 (by norm_num [nodes])
  have hfac1 : ∀ w, q 1 w = (w - nodes 2) * q 2 w := by
    intro w
    simpa [q] using hermiteGenocchiTriangle_factor derivs nodes hderiv hcont 1
      (by simpa [q, nodes] using hq1_2) w
  have hq0_3 : q 0 3 = 0 :=
    propagate (hbase 3) hf3 (by norm_num [nodes])
  have hq1_3 : q 1 3 = 0 :=
    propagate (hfac0 3) hq0_3 (by norm_num [nodes])
  have hq2_3 : q 2 3 = 0 :=
    propagate (hfac1 3) hq1_3 (by norm_num [nodes])
  have hfac2 : ∀ w, q 2 w = (w - nodes 3) * q 3 w := by
    intro w
    simpa [q] using hermiteGenocchiTriangle_factor derivs nodes hderiv hcont 2
      (by simpa [q, nodes] using hq2_3) w
  have hq0_4 : q 0 4 = 0 :=
    propagate (hbase 4) hf4 (by norm_num [nodes])
  have hq1_4 : q 1 4 = 0 :=
    propagate (hfac0 4) hq0_4 (by norm_num [nodes])
  have hq2_4 : q 2 4 = 0 :=
    propagate (hfac1 4) hq1_4 (by norm_num [nodes])
  have hq3_4 : q 3 4 = 0 :=
    propagate (hfac2 4) hq2_4 (by norm_num [nodes])
  have hfac3 : ∀ w, q 3 w = (w - nodes 4) * q 4 w := by
    intro w
    simpa [q] using hermiteGenocchiTriangle_factor derivs nodes hderiv hcont 3
      (by simpa [q, nodes] using hq3_4) w
  have hq0_5 : q 0 5 = 0 :=
    propagate (hbase 5) hf5 (by norm_num [nodes])
  have hq1_5 : q 1 5 = 0 :=
    propagate (hfac0 5) hq0_5 (by norm_num [nodes])
  have hq2_5 : q 2 5 = 0 :=
    propagate (hfac1 5) hq1_5 (by norm_num [nodes])
  have hq3_5 : q 3 5 = 0 :=
    propagate (hfac2 5) hq2_5 (by norm_num [nodes])
  have hq4_5 : q 4 5 = 0 :=
    propagate (hfac3 5) hq3_5 (by norm_num [nodes])
  have hfac4 : ∀ w, q 4 w = (w - nodes 5) * q 5 w := by
    intro w
    simpa [q] using hermiteGenocchiTriangle_factor derivs nodes hderiv hcont 4
      (by simpa [q, nodes] using hq4_5) w
  rw [hbase z, hfac0 z, hfac1 z, hfac2 z, hfac3 z, hfac4 z]
  simp only [nodes, q, Nat.cast_zero, Nat.cast_one, Nat.cast_ofNat, sub_zero]
  ring

/-- The exact six-node Newton identity on an open convex analytic domain.
This is the application-ready local form of repeated complex FTC. -/
theorem hermiteGenocchiSix_newton_identityOn
    (u : Set ℂ) (hu : IsOpen u) (hconv : Convex ℝ u)
    (derivs : ℕ → ℂ → ℂ)
    (hderiv : ∀ n w, w ∈ u → HasDerivAt (derivs n) (derivs (n + 1) w) w)
    (hcont : ∀ n, ContinuousOn (derivs n) u)
    (hzero : derivs 0 0 = 0 ∧ derivs 0 1 = 0 ∧ derivs 0 2 = 0 ∧
      derivs 0 3 = 0 ∧ derivs 0 4 = 0 ∧ derivs 0 5 = 0)
    (hnodes : ∀ j, j ≤ 5 → ((j : ℕ) : ℂ) ∈ u)
    (z : ℂ) (hz : z ∈ u) :
    derivs 0 z =
      (z * (z - 1) * (z - 2) * (z - 3) * (z - 4) * (z - 5)) *
        hermiteGenocchiTriangle derivs (fun n => (n : ℂ)) 5 0 z := by
  let nodes : ℕ → ℂ := fun n => (n : ℂ)
  let q : ℕ → ℂ → ℂ := fun i => hermiteGenocchiTriangle derivs nodes i 0
  have hnode : ∀ j, j ≤ 5 → nodes j ∈ u := by
    intro j hj
    simpa [nodes] using hnodes j hj
  rcases hzero with ⟨hf0, hf1, hf2, hf3, hf4, hf5⟩
  have hbase : ∀ w ∈ u, derivs 0 w = (w - nodes 0) * q 0 w := by
    intro w hw
    simpa [q, nodes, hermiteGenocchiTriangle, segmentWeight] using
      complexSegment_factor_of_eq_zeroOn u hconv
        (derivs 0) (derivs 1) (nodes 0) w (hnode 0 (by omega)) hw
        (hderiv 0) (hcont 1) (by simpa [nodes] using hf0)
  have propagate {g r : ℂ → ℂ} {a b : ℂ}
      (hfac : g b = (b - a) * r b) (hgb : g b = 0) (hba : b ≠ a) : r b = 0 := by
    rw [hgb] at hfac
    exact (mul_eq_zero.mp hfac.symm).resolve_left (sub_ne_zero.mpr hba)
  have hq0_1 : q 0 1 = 0 :=
    propagate (hbase 1 (by simpa [nodes] using hnode 1 (by omega))) hf1
      (by norm_num [nodes])
  have hfac0 : ∀ w ∈ u, q 0 w = (w - nodes 1) * q 1 w := by
    intro w hw
    simpa [q] using hermiteGenocchiTriangle_factorOn u hu hconv derivs nodes
      hderiv hcont 0 (fun j hj => hnode j (by omega))
      (by simpa [q, nodes] using hq0_1) w hw
  have hq0_2 : q 0 2 = 0 :=
    propagate (hbase 2 (by simpa [nodes] using hnode 2 (by omega))) hf2
      (by norm_num [nodes])
  have hq1_2 : q 1 2 = 0 :=
    propagate (hfac0 2 (by simpa [nodes] using hnode 2 (by omega))) hq0_2
      (by norm_num [nodes])
  have hfac1 : ∀ w ∈ u, q 1 w = (w - nodes 2) * q 2 w := by
    intro w hw
    simpa [q] using hermiteGenocchiTriangle_factorOn u hu hconv derivs nodes
      hderiv hcont 1 (fun j hj => hnode j (by omega))
      (by simpa [q, nodes] using hq1_2) w hw
  have hq0_3 : q 0 3 = 0 :=
    propagate (hbase 3 (by simpa [nodes] using hnode 3 (by omega))) hf3
      (by norm_num [nodes])
  have hq1_3 : q 1 3 = 0 :=
    propagate (hfac0 3 (by simpa [nodes] using hnode 3 (by omega))) hq0_3
      (by norm_num [nodes])
  have hq2_3 : q 2 3 = 0 :=
    propagate (hfac1 3 (by simpa [nodes] using hnode 3 (by omega))) hq1_3
      (by norm_num [nodes])
  have hfac2 : ∀ w ∈ u, q 2 w = (w - nodes 3) * q 3 w := by
    intro w hw
    simpa [q] using hermiteGenocchiTriangle_factorOn u hu hconv derivs nodes
      hderiv hcont 2 (fun j hj => hnode j (by omega))
      (by simpa [q, nodes] using hq2_3) w hw
  have hq0_4 : q 0 4 = 0 :=
    propagate (hbase 4 (by simpa [nodes] using hnode 4 (by omega))) hf4
      (by norm_num [nodes])
  have hq1_4 : q 1 4 = 0 :=
    propagate (hfac0 4 (by simpa [nodes] using hnode 4 (by omega))) hq0_4
      (by norm_num [nodes])
  have hq2_4 : q 2 4 = 0 :=
    propagate (hfac1 4 (by simpa [nodes] using hnode 4 (by omega))) hq1_4
      (by norm_num [nodes])
  have hq3_4 : q 3 4 = 0 :=
    propagate (hfac2 4 (by simpa [nodes] using hnode 4 (by omega))) hq2_4
      (by norm_num [nodes])
  have hfac3 : ∀ w ∈ u, q 3 w = (w - nodes 4) * q 4 w := by
    intro w hw
    simpa [q] using hermiteGenocchiTriangle_factorOn u hu hconv derivs nodes
      hderiv hcont 3 (fun j hj => hnode j (by omega))
      (by simpa [q, nodes] using hq3_4) w hw
  have hq0_5 : q 0 5 = 0 :=
    propagate (hbase 5 (by simpa [nodes] using hnode 5 (by omega))) hf5
      (by norm_num [nodes])
  have hq1_5 : q 1 5 = 0 :=
    propagate (hfac0 5 (by simpa [nodes] using hnode 5 (by omega))) hq0_5
      (by norm_num [nodes])
  have hq2_5 : q 2 5 = 0 :=
    propagate (hfac1 5 (by simpa [nodes] using hnode 5 (by omega))) hq1_5
      (by norm_num [nodes])
  have hq3_5 : q 3 5 = 0 :=
    propagate (hfac2 5 (by simpa [nodes] using hnode 5 (by omega))) hq2_5
      (by norm_num [nodes])
  have hq4_5 : q 4 5 = 0 :=
    propagate (hfac3 5 (by simpa [nodes] using hnode 5 (by omega))) hq3_5
      (by norm_num [nodes])
  have hfac4 : ∀ w ∈ u, q 4 w = (w - nodes 5) * q 5 w := by
    intro w hw
    simpa [q] using hermiteGenocchiTriangle_factorOn u hu hconv derivs nodes
      hderiv hcont 4 (fun j hj => hnode j (by omega))
      (by simpa [q, nodes] using hq4_5) w hw
  rw [hbase z hz, hfac0 z hz, hfac1 z hz, hfac2 z hz, hfac3 z hz, hfac4 z hz]
  simp only [nodes, q, Nat.cast_zero, Nat.cast_one, Nat.cast_ofNat, sub_zero]
  ring

end Zeta23.Research.JensenWedge
