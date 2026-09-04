import Mathlib

/-!
# The order-six Hermite--Genocchi cube

The six-dimensional standard simplex is parametrized by stick breaking from
the unit cube.  The Jacobian is

`(1-u₀)^5 (1-u₁)^4 (1-u₂)^3 (1-u₃)^2 (1-u₄)`.

This file keeps that density explicit and proves, by six successive Bochner
integral estimates, that its total mass is exactly `1 / 720`.  This is the
normalization used by the order-six complex Hermite--Genocchi formula.
-/

open scoped Interval

namespace Zeta23.Research.JensenWedge

/-- The stick-breaking form of the six-dimensional Hermite--Genocchi
integral. -/
noncomputable def hermiteGenocchiCubeSix
    (φ : ℝ → ℝ → ℝ → ℝ → ℝ → ℝ → ℂ) : ℂ :=
  ∫ u₀ in (0 : ℝ)..1, ((1 - u₀) ^ 5 : ℂ) *
    ∫ u₁ in (0 : ℝ)..1, ((1 - u₁) ^ 4 : ℂ) *
      ∫ u₂ in (0 : ℝ)..1, ((1 - u₂) ^ 3 : ℂ) *
        ∫ u₃ in (0 : ℝ)..1, ((1 - u₃) ^ 2 : ℂ) *
          ∫ u₄ in (0 : ℝ)..1, ((1 - u₄) : ℂ) *
            ∫ u₅ in (0 : ℝ)..1, φ u₀ u₁ u₂ u₃ u₄ u₅

/-- Stick-breaking coordinates for a point of the convex hull of seven
complex nodes.  The order agrees with the density in
`hermiteGenocchiCubeSix`. -/
noncomputable def hermiteGenocchiCubePoint
    (x₀ x₁ x₂ x₃ x₄ x₅ x₆ : ℂ)
    (u₀ u₁ u₂ u₃ u₄ u₅ : ℝ) : ℂ :=
  AffineMap.lineMap
    (AffineMap.lineMap
      (AffineMap.lineMap
        (AffineMap.lineMap
          (AffineMap.lineMap
            (AffineMap.lineMap x₆ x₅ u₅) x₄ u₄) x₃ u₃) x₂ u₂) x₁ u₁) x₀ u₀

/-- The order-six Hermite--Genocchi integral for seven complex nodes. -/
noncomputable def hermiteGenocchiIntegralSix
    (f₆ : ℂ → ℂ) (x₀ x₁ x₂ x₃ x₄ x₅ x₆ : ℂ) : ℂ :=
  hermiteGenocchiCubeSix (fun u₀ u₁ u₂ u₃ u₄ u₅ =>
    f₆ (hermiteGenocchiCubePoint x₀ x₁ x₂ x₃ x₄ x₅ x₆ u₀ u₁ u₂ u₃ u₄ u₅))

/-- Every stick-breaking point stays in a convex set containing the seven
nodes. -/
theorem hermiteGenocchiCubePoint_mem_convex
    {s : Set ℂ} (hs : Convex ℝ s) {x₀ x₁ x₂ x₃ x₄ x₅ x₆ : ℂ}
    (hx₀ : x₀ ∈ s) (hx₁ : x₁ ∈ s) (hx₂ : x₂ ∈ s) (hx₃ : x₃ ∈ s)
    (hx₄ : x₄ ∈ s) (hx₅ : x₅ ∈ s) (hx₆ : x₆ ∈ s)
    {u₀ u₁ u₂ u₃ u₄ u₅ : ℝ}
    (hu₀ : u₀ ∈ Set.Icc (0 : ℝ) 1) (hu₁ : u₁ ∈ Set.Icc (0 : ℝ) 1)
    (hu₂ : u₂ ∈ Set.Icc (0 : ℝ) 1) (hu₃ : u₃ ∈ Set.Icc (0 : ℝ) 1)
    (hu₄ : u₄ ∈ Set.Icc (0 : ℝ) 1) (hu₅ : u₅ ∈ Set.Icc (0 : ℝ) 1) :
    hermiteGenocchiCubePoint x₀ x₁ x₂ x₃ x₄ x₅ x₆ u₀ u₁ u₂ u₃ u₄ u₅ ∈ s := by
  exact hs.lineMap_mem
    (hs.lineMap_mem
      (hs.lineMap_mem
        (hs.lineMap_mem
          (hs.lineMap_mem
            (hs.lineMap_mem hx₆ hx₅ hu₅) hx₄ hu₄) hx₃ hu₃) hx₂ hu₂) hx₁ hu₁) hx₀ hu₀

private theorem one_sub_pow_nonneg {u : ℝ} (hu : u ∈ Set.uIcc (0 : ℝ) 1) (n : ℕ) :
    0 ≤ (1 - u) ^ n := by
  have hu' : u ≤ 1 := by simpa [Set.uIcc_of_le zero_le_one] using hu.2
  positivity

private theorem integral_one_sub_pow (n : ℕ) :
    (∫ u : ℝ in (0 : ℝ)..1, (1 - u) ^ n) = 1 / (n + 1 : ℝ) := by
  have hderiv : ∀ u : ℝ, HasDerivAt
      (fun x : ℝ => -((1 - x) ^ (n + 1)) / (n + 1 : ℝ))
      ((1 - u) ^ n) u := by
    intro u
    have hn : (n + 1 : ℝ) ≠ 0 := by positivity
    have hbase : HasDerivAt (fun x : ℝ => 1 - x) (-1) u := by
      simpa using (hasDerivAt_id u).const_sub (1 : ℝ)
    have hpow := (hbase.pow (n + 1)).neg.div_const (n + 1 : ℝ)
    simpa [Nat.add_sub_cancel, hn] using hpow
  calc
    (∫ u : ℝ in (0 : ℝ)..1, (1 - u) ^ n) =
        (-((1 - (1 : ℝ)) ^ (n + 1)) / (n + 1 : ℝ)) -
          (-((1 - (0 : ℝ)) ^ (n + 1)) / (n + 1 : ℝ)) :=
      intervalIntegral.integral_eq_sub_of_hasDerivAt
        (fun u _ => hderiv u) ((by fun_prop : Continuous
          (fun u : ℝ => (1 - u) ^ n)).intervalIntegrable 0 1)
    _ = 1 / (n + 1 : ℝ) := by
      norm_num [show n + 1 ≠ 0 by omega, div_eq_mul_inv]

private theorem norm_integral_weighted_le
    {F : ℝ → ℂ} {C : ℝ} (n : ℕ) (_hC : 0 ≤ C)
    (hF : ∀ u ∈ Set.uIcc (0 : ℝ) 1, ‖F u‖ ≤ C) :
    ‖∫ u : ℝ in (0 : ℝ)..1, ((1 - u) ^ n : ℂ) * F u‖ ≤ C / (n + 1 : ℝ) := by
  calc
    ‖∫ u : ℝ in (0 : ℝ)..1, ((1 - u) ^ n : ℂ) * F u‖
        ≤ ∫ u : ℝ in (0 : ℝ)..1, (1 - u) ^ n * C := by
      apply intervalIntegral.norm_integral_le_of_norm_le zero_le_one
      · filter_upwards [] with u hu
        have hucc : u ∈ Set.uIcc (0 : ℝ) 1 := by
          rw [Set.uIcc_of_le zero_le_one]
          exact ⟨hu.1.le, hu.2⟩
        have hw : ‖((1 - u) ^ n : ℂ)‖ = (1 - u) ^ n := by
          have hule : u ≤ 1 := hu.2
          rw [show (1 : ℂ) - (u : ℂ) = ((1 - u : ℝ) : ℂ) by norm_num,
            norm_pow, Complex.norm_real, Real.norm_eq_abs,
            abs_of_nonneg (by linarith : 0 ≤ 1 - u)]
        rw [norm_mul, hw]
        exact mul_le_mul_of_nonneg_left (hF u hucc) (one_sub_pow_nonneg hucc n)
      · exact ((by fun_prop : Continuous (fun t : ℝ => (1 - t) ^ n * C))).intervalIntegrable 0 1
    _ = C / (n + 1 : ℝ) := by
      rw [intervalIntegral.integral_mul_const, integral_one_sub_pow]
      ring

/-- The exact order-six simplex-mass estimate in cube coordinates. -/
theorem norm_hermiteGenocchiCubeSix_le
    {φ : ℝ → ℝ → ℝ → ℝ → ℝ → ℝ → ℂ} {M : ℝ} (hM : 0 ≤ M)
    (hφ : ∀ u₀ ∈ Set.uIcc (0 : ℝ) 1,
      ∀ u₁ ∈ Set.uIcc (0 : ℝ) 1,
      ∀ u₂ ∈ Set.uIcc (0 : ℝ) 1,
      ∀ u₃ ∈ Set.uIcc (0 : ℝ) 1,
      ∀ u₄ ∈ Set.uIcc (0 : ℝ) 1,
      ∀ u₅ ∈ Set.uIcc (0 : ℝ) 1,
        ‖φ u₀ u₁ u₂ u₃ u₄ u₅‖ ≤ M) :
    ‖hermiteGenocchiCubeSix φ‖ ≤ M / 720 := by
  let I₅ := fun u₀ u₁ u₂ u₃ u₄ =>
    ∫ u₅ : ℝ in (0 : ℝ)..1, φ u₀ u₁ u₂ u₃ u₄ u₅
  let I₄ := fun u₀ u₁ u₂ u₃ =>
    ∫ u₄ : ℝ in (0 : ℝ)..1, ((1 - u₄) : ℂ) * I₅ u₀ u₁ u₂ u₃ u₄
  let I₃ := fun u₀ u₁ u₂ =>
    ∫ u₃ : ℝ in (0 : ℝ)..1, ((1 - u₃) ^ 2 : ℂ) * I₄ u₀ u₁ u₂ u₃
  let I₂ := fun u₀ u₁ =>
    ∫ u₂ : ℝ in (0 : ℝ)..1, ((1 - u₂) ^ 3 : ℂ) * I₃ u₀ u₁ u₂
  let I₁ := fun u₀ =>
    ∫ u₁ : ℝ in (0 : ℝ)..1, ((1 - u₁) ^ 4 : ℂ) * I₂ u₀ u₁
  have h₅ : ∀ u₀ ∈ Set.uIcc (0 : ℝ) 1,
      ∀ u₁ ∈ Set.uIcc (0 : ℝ) 1,
      ∀ u₂ ∈ Set.uIcc (0 : ℝ) 1,
      ∀ u₃ ∈ Set.uIcc (0 : ℝ) 1,
      ∀ u₄ ∈ Set.uIcc (0 : ℝ) 1,
        ‖I₅ u₀ u₁ u₂ u₃ u₄‖ ≤ M := by
    intro u₀ hu₀ u₁ hu₁ u₂ hu₂ u₃ hu₃ u₄ hu₄
    convert norm_integral_weighted_le 0 hM
      (fun u₅ hu₅ => hφ u₀ hu₀ u₁ hu₁ u₂ hu₂ u₃ hu₃ u₄ hu₄ u₅ hu₅) using 1 <;>
      simp [I₅]
  have h₄ : ∀ u₀ ∈ Set.uIcc (0 : ℝ) 1,
      ∀ u₁ ∈ Set.uIcc (0 : ℝ) 1,
      ∀ u₂ ∈ Set.uIcc (0 : ℝ) 1,
      ∀ u₃ ∈ Set.uIcc (0 : ℝ) 1,
        ‖I₄ u₀ u₁ u₂ u₃‖ ≤ M / 2 := by
    intro u₀ hu₀ u₁ hu₁ u₂ hu₂ u₃ hu₃
    convert norm_integral_weighted_le 1 hM
      (fun u₄ hu₄ => h₅ u₀ hu₀ u₁ hu₁ u₂ hu₂ u₃ hu₃ u₄ hu₄) using 1 <;>
      simp [I₄] <;> ring
  have hM₂ : 0 ≤ M / 2 := div_nonneg hM (by norm_num)
  have h₃ : ∀ u₀ ∈ Set.uIcc (0 : ℝ) 1,
      ∀ u₁ ∈ Set.uIcc (0 : ℝ) 1,
      ∀ u₂ ∈ Set.uIcc (0 : ℝ) 1,
        ‖I₃ u₀ u₁ u₂‖ ≤ M / 6 := by
    intro u₀ hu₀ u₁ hu₁ u₂ hu₂
    convert norm_integral_weighted_le 2 hM₂
      (fun u₃ hu₃ => h₄ u₀ hu₀ u₁ hu₁ u₂ hu₂ u₃ hu₃) using 1 <;> simp [I₃] <;> ring
  have hM₆ : 0 ≤ M / 6 := div_nonneg hM (by norm_num)
  have h₂ : ∀ u₀ ∈ Set.uIcc (0 : ℝ) 1,
      ∀ u₁ ∈ Set.uIcc (0 : ℝ) 1,
        ‖I₂ u₀ u₁‖ ≤ M / 24 := by
    intro u₀ hu₀ u₁ hu₁
    convert norm_integral_weighted_le 3 hM₆
      (fun u₂ hu₂ => h₃ u₀ hu₀ u₁ hu₁ u₂ hu₂) using 1 <;> simp [I₂] <;> ring
  have hM₂₄ : 0 ≤ M / 24 := div_nonneg hM (by norm_num)
  have h₁ : ∀ u₀ ∈ Set.uIcc (0 : ℝ) 1, ‖I₁ u₀‖ ≤ M / 120 := by
    intro u₀ hu₀
    convert norm_integral_weighted_le 4 hM₂₄
      (fun u₁ hu₁ => h₂ u₀ hu₀ u₁ hu₁) using 1 <;> simp [I₁] <;> ring
  have hM₁₂₀ : 0 ≤ M / 120 := div_nonneg hM (by norm_num)
  convert norm_integral_weighted_le 5 hM₁₂₀ h₁ using 1 <;>
    simp [hermiteGenocchiCubeSix, I₁, I₂, I₃, I₄, I₅] <;> ring

/-- Supremum control of a sixth derivative on all stick-breaking points
gives the standard `M / 6!` Hermite--Genocchi bound. -/
theorem norm_hermiteGenocchiIntegralSix_le
    {f₆ : ℂ → ℂ} {x₀ x₁ x₂ x₃ x₄ x₅ x₆ : ℂ} {M : ℝ} (hM : 0 ≤ M)
    (hf₆ : ∀ u₀ ∈ Set.uIcc (0 : ℝ) 1,
      ∀ u₁ ∈ Set.uIcc (0 : ℝ) 1,
      ∀ u₂ ∈ Set.uIcc (0 : ℝ) 1,
      ∀ u₃ ∈ Set.uIcc (0 : ℝ) 1,
      ∀ u₄ ∈ Set.uIcc (0 : ℝ) 1,
      ∀ u₅ ∈ Set.uIcc (0 : ℝ) 1,
        ‖f₆ (hermiteGenocchiCubePoint x₀ x₁ x₂ x₃ x₄ x₅ x₆
          u₀ u₁ u₂ u₃ u₄ u₅)‖ ≤ M) :
    ‖hermiteGenocchiIntegralSix f₆ x₀ x₁ x₂ x₃ x₄ x₅ x₆‖ ≤ M / 720 := by
  exact norm_hermiteGenocchiCubeSix_le hM hf₆

end Zeta23.Research.JensenWedge
