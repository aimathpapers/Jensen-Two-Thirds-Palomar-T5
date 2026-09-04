import Zeta23.Research.JensenWedge.HermiteGenocchiFTC

/-!
# Complex line-segment calculus for Hermite--Genocchi

This file proves the complex line-segment fundamental theorem used in an
iteration of Hermite--Genocchi.  It also makes the downstream order-six
adapter explicit: the Newton product and the `1 / 6!` simplex mass are kept
visible, so no interpolation constant can be lost silently.  The
six-dimensional integral estimate is kernel checked in
`HermiteGenocchiCube`; the Newton identity below states explicitly where the
integral representation is connected to the function.
-/

open scoped Interval

namespace Zeta23.Research.JensenWedge

/-- The affine segment from `x` to `y`, parametrized by the real unit
interval. -/
noncomputable def complexSegment (x y : ℂ) (t : ℝ) : ℂ :=
  AffineMap.lineMap x y t

theorem hasDerivAt_complexSegment (x y : ℂ) (t : ℝ) :
    HasDerivAt (complexSegment x y) (y - x) t := by
  exact AffineMap.hasDerivAt_lineMap

/-- Complex fundamental theorem of calculus on a line segment.  This is the
induction step in the Hermite--Genocchi formula. -/
theorem complexSegment_integral_deriv
    (f f' : ℂ → ℂ) (x y : ℂ)
    (hf : ∀ t : ℝ, HasDerivAt f (f' (complexSegment x y t))
      (complexSegment x y t))
    (hint : IntervalIntegrable
      (fun t : ℝ => (y - x) * f' (complexSegment x y t))
      MeasureTheory.volume 0 1) :
    (∫ t : ℝ in 0..1, (y - x) * f' (complexSegment x y t)) = f y - f x := by
  have hderiv : ∀ t ∈ Set.uIcc (0 : ℝ) 1,
      HasDerivAt (fun s : ℝ => f (complexSegment x y s))
        ((y - x) * f' (complexSegment x y t)) t := by
    intro t _
    have hcomp := (hf t).scomp t (hasDerivAt_complexSegment x y t)
    simpa [Function.comp_def, smul_eq_mul] using hcomp
  simpa [complexSegment] using
    intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint

/-- The Newton product for the nodes `0,1,...,5`. -/
def sixNodeProduct (z : ℂ) : ℂ :=
  z * (z - 1) * (z - 2) * (z - 3) * (z - 4) * (z - 5)

theorem sixNodeProduct_eq_zero_iff {z : ℂ} :
    sixNodeProduct z = 0 ↔ z = 0 ∨ z = 1 ∨ z = 2 ∨ z = 3 ∨ z = 4 ∨ z = 5 := by
  simp only [sixNodeProduct, mul_eq_zero, sub_eq_zero]
  tauto

/-- The exact coefficient multiplying the six-node Newton product.  At a
node it is set to zero; when the function vanishes at all six nodes this
convention gives an unconditional Newton identity. -/
noncomputable def sixNodeDividedDifference (f : ℂ → ℂ) (z : ℂ) : ℂ :=
  if sixNodeProduct z = 0 then 0 else f z / sixNodeProduct z

/-- Six zeros give the exact Newton product identity, including the cases in
which `z` itself is one of the interpolation nodes. -/
theorem sixNode_newton_identity
    (f : ℂ → ℂ) {z : ℂ}
    (hzero : f 0 = 0 ∧ f 1 = 0 ∧ f 2 = 0 ∧
      f 3 = 0 ∧ f 4 = 0 ∧ f 5 = 0) :
    f z = sixNodeDividedDifference f z * sixNodeProduct z := by
  by_cases hp : sixNodeProduct z = 0
  · rw [sixNodeProduct_eq_zero_iff] at hp
    rcases hp with rfl | rfl | rfl | rfl | rfl | rfl
    all_goals simp [sixNodeDividedDifference, sixNodeProduct, hzero]
  · simp [sixNodeDividedDifference, hp]

theorem norm_sixNodeProduct_le
    {z : ℂ} {ρ : ℝ} (hρ : 0 ≤ ρ)
    (h : ‖z‖ ≤ ρ ∧ ‖z - 1‖ ≤ ρ ∧ ‖z - 2‖ ≤ ρ ∧
      ‖z - 3‖ ≤ ρ ∧ ‖z - 4‖ ≤ ρ ∧ ‖z - 5‖ ≤ ρ) :
    ‖sixNodeProduct z‖ ≤ ρ ^ 6 := by
  rcases h with ⟨h0, h1, h2, h3, h4, h5⟩
  simp only [sixNodeProduct, norm_mul]
  calc
    ‖z‖ * ‖z - 1‖ * ‖z - 2‖ * ‖z - 3‖ * ‖z - 4‖ * ‖z - 5‖
        ≤ ρ * ρ * ρ * ρ * ρ * ρ := by gcongr
    _ = ρ ^ 6 := by ring

/-- The exact order-six Hermite--Genocchi/Newton remainder adapter.  Unlike
the earlier interface, the divided-difference norm is not a hypothesis: it
is derived from the explicit six-cube integrand and the kernel-checked
simplex-mass estimate. -/
theorem hermiteGenocchiSix_remainder_bound
    (f : ℂ → ℂ) {z : ℂ} {M ρ : ℝ}
    (hM : 0 ≤ M) (hρ : 0 ≤ ρ)
    (hzero : f 0 = 0 ∧ f 1 = 0 ∧ f 2 = 0 ∧
      f 3 = 0 ∧ f 4 = 0 ∧ f 5 = 0)
    (f₆ : ℂ → ℂ)
    (hIntegral : sixNodeDividedDifference f z =
      hermiteGenocchiIntegralSix f₆ 0 1 2 3 4 5 z)
    (hf₆ : ∀ u₀ ∈ Set.uIcc (0 : ℝ) 1,
      ∀ u₁ ∈ Set.uIcc (0 : ℝ) 1,
      ∀ u₂ ∈ Set.uIcc (0 : ℝ) 1,
      ∀ u₃ ∈ Set.uIcc (0 : ℝ) 1,
      ∀ u₄ ∈ Set.uIcc (0 : ℝ) 1,
      ∀ u₅ ∈ Set.uIcc (0 : ℝ) 1,
        ‖f₆ (hermiteGenocchiCubePoint 0 1 2 3 4 5 z u₀ u₁ u₂ u₃ u₄ u₅)‖ ≤ M)
    (hnodes : ‖z‖ ≤ ρ ∧ ‖z - 1‖ ≤ ρ ∧ ‖z - 2‖ ≤ ρ ∧
      ‖z - 3‖ ≤ ρ ∧ ‖z - 4‖ ≤ ρ ∧ ‖z - 5‖ ≤ ρ) :
    ‖f z‖ ≤ M * ρ ^ 6 / 720 := by
  rw [sixNode_newton_identity f hzero, hIntegral, norm_mul]
  have hIntegralBound := norm_hermiteGenocchiIntegralSix_le hM hf₆
  have hp := norm_sixNodeProduct_le hρ hnodes
  calc
    ‖hermiteGenocchiIntegralSix f₆ 0 1 2 3 4 5 z‖ * ‖sixNodeProduct z‖
        ≤ (M / 720) * (ρ ^ 6) :=
      mul_le_mul hIntegralBound hp (norm_nonneg _) (by positivity)
    _ = M * ρ ^ 6 / 720 := by ring

/-- A fully derived order-six Hermite--Genocchi remainder theorem for a
global complex derivative tower.  Repeated FTC constructs the Newton
coefficient, while `norm_hermiteGenocchiTriangle_le` supplies its exact
`1/720` mass.  No divided-difference, Newton, or integral equality is an
input. -/
theorem hermiteGenocchiSix_remainder_bound_of_derivative_tower
    (derivs : ℕ → ℂ → ℂ) {z : ℂ} {M ρ : ℝ} {s : Set ℂ}
    (hM : 0 ≤ M) (hρ : 0 ≤ ρ)
    (hderiv : ∀ n w, HasDerivAt (derivs n) (derivs (n + 1) w) w)
    (hcont : ∀ n, Continuous (derivs n))
    (hzero : derivs 0 0 = 0 ∧ derivs 0 1 = 0 ∧ derivs 0 2 = 0 ∧
      derivs 0 3 = 0 ∧ derivs 0 4 = 0 ∧ derivs 0 5 = 0)
    (hs : Convex ℝ s)
    (hs₀ : (0 : ℂ) ∈ s) (hs₁ : (1 : ℂ) ∈ s) (hs₂ : (2 : ℂ) ∈ s)
    (hs₃ : (3 : ℂ) ∈ s) (hs₄ : (4 : ℂ) ∈ s) (hs₅ : (5 : ℂ) ∈ s)
    (hz : z ∈ s)
    (hbound : ∀ w ∈ s, ‖derivs 6 w‖ ≤ M)
    (hnodes : ‖z‖ ≤ ρ ∧ ‖z - 1‖ ≤ ρ ∧ ‖z - 2‖ ≤ ρ ∧
      ‖z - 3‖ ≤ ρ ∧ ‖z - 4‖ ≤ ρ ∧ ‖z - 5‖ ≤ ρ) :
    ‖derivs 0 z‖ ≤ M * ρ ^ 6 / 720 := by
  have hFactorization :=
    hermiteGenocchiSix_newton_identity derivs hderiv hcont hzero z
  have hnodeMem : ∀ j, j ≤ 5 → ((j : ℕ) : ℂ) ∈ s := by
    intro j hj
    interval_cases j <;> norm_num <;> assumption
  have hTriangle :
      ‖hermiteGenocchiTriangle derivs (fun n => (n : ℂ)) 5 0 z‖ ≤ M / 720 := by
    have h := norm_hermiteGenocchiTriangle_le derivs (fun n => (n : ℂ)) hs hM 5 0 hz
      hnodeMem (by
        intro w hw
        simpa using hbound w hw)
    rw [hermiteGenocchiTriangleMass_five_zero] at h
    convert h using 1 <;> ring
  have hp := norm_sixNodeProduct_le hρ hnodes
  rw [hFactorization, norm_mul]
  change ‖sixNodeProduct z‖ *
      ‖hermiteGenocchiTriangle derivs (fun n => (n : ℂ)) 5 0 z‖ ≤
    M * ρ ^ 6 / 720
  calc
    ‖sixNodeProduct z‖ *
        ‖hermiteGenocchiTriangle derivs (fun n => (n : ℂ)) 5 0 z‖
        ≤ (ρ ^ 6) * (M / 720) :=
      mul_le_mul hp hTriangle (norm_nonneg _) (by positivity)
    _ = M * ρ ^ 6 / 720 := by ring

/-- Application-ready order-six remainder theorem on an open convex analytic
domain.  The smaller convex set `s` carries the sixth-derivative bound; `u`
provides the open neighborhood needed for differentiation under the nested
integrals.  No global extension or Hermite--Genocchi identity is assumed. -/
theorem hermiteGenocchiSix_remainder_bound_on
    (u s : Set ℂ) (hu : IsOpen u) (hconvU : Convex ℝ u)
    (derivs : ℕ → ℂ → ℂ) {z : ℂ} {M ρ : ℝ}
    (hM : 0 ≤ M) (hρ : 0 ≤ ρ)
    (hderiv : ∀ n w, w ∈ u → HasDerivAt (derivs n) (derivs (n + 1) w) w)
    (hcont : ∀ n, ContinuousOn (derivs n) u)
    (hzero : derivs 0 0 = 0 ∧ derivs 0 1 = 0 ∧ derivs 0 2 = 0 ∧
      derivs 0 3 = 0 ∧ derivs 0 4 = 0 ∧ derivs 0 5 = 0)
    (hs : Convex ℝ s) (hsu : s ⊆ u)
    (hs₀ : (0 : ℂ) ∈ s) (hs₁ : (1 : ℂ) ∈ s) (hs₂ : (2 : ℂ) ∈ s)
    (hs₃ : (3 : ℂ) ∈ s) (hs₄ : (4 : ℂ) ∈ s) (hs₅ : (5 : ℂ) ∈ s)
    (hz : z ∈ s)
    (hbound : ∀ w ∈ s, ‖derivs 6 w‖ ≤ M)
    (hnodes : ‖z‖ ≤ ρ ∧ ‖z - 1‖ ≤ ρ ∧ ‖z - 2‖ ≤ ρ ∧
      ‖z - 3‖ ≤ ρ ∧ ‖z - 4‖ ≤ ρ ∧ ‖z - 5‖ ≤ ρ) :
    ‖derivs 0 z‖ ≤ M * ρ ^ 6 / 720 := by
  have hnodeMem : ∀ j, j ≤ 5 → ((j : ℕ) : ℂ) ∈ s := by
    intro j hj
    interval_cases j <;> norm_num <;> assumption
  have hFactorization := hermiteGenocchiSix_newton_identityOn u hu hconvU
    derivs hderiv hcont hzero (fun j hj => hsu (hnodeMem j hj)) z (hsu hz)
  have hTriangle :
      ‖hermiteGenocchiTriangle derivs (fun n => (n : ℂ)) 5 0 z‖ ≤ M / 720 := by
    have h := norm_hermiteGenocchiTriangle_le derivs (fun n => (n : ℂ)) hs hM 5 0 hz
      hnodeMem (by
        intro w hw
        simpa using hbound w hw)
    rw [hermiteGenocchiTriangleMass_five_zero] at h
    convert h using 1 <;> ring
  have hp := norm_sixNodeProduct_le hρ hnodes
  rw [hFactorization, norm_mul]
  change ‖sixNodeProduct z‖ *
      ‖hermiteGenocchiTriangle derivs (fun n => (n : ℂ)) 5 0 z‖ ≤
    M * ρ ^ 6 / 720
  calc
    ‖sixNodeProduct z‖ *
        ‖hermiteGenocchiTriangle derivs (fun n => (n : ℂ)) 5 0 z‖
        ≤ (ρ ^ 6) * (M / 720) :=
      mul_le_mul hp hTriangle (norm_nonneg _) (by positivity)
    _ = M * ρ ^ 6 / 720 := by ring

end Zeta23.Research.JensenWedge
