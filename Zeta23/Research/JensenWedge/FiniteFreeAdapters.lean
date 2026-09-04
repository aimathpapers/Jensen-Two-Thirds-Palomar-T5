import Zeta23.Research.JensenWedge.QuantitativeBranch
import Mathlib.Algebra.Polynomial.Reverse
import Mathlib.LinearAlgebra.Matrix.Gershgorin

/-!
# Finite-free normalization, Jacobi, and source adapters

This module formalizes the convention changes and finite implications around
the two external finite-free inputs.  The ascending constant-term-one
convolution and descending monic convolution are defined coefficientwise and
shown to commute exactly with fixed-degree reflection.  Reciprocal roots,
positive interval reversal, the two-sided MSS consequence, strict logarithmic
mesh, and the Gershgorin constant `8` are then checked in Lean.

The module does not reproduce the general theorems of Marcus--Spielman--
Srivastava or Martínez-Finkelshtein--Morales--Perales.  Their exact consumed
conclusions, and the classical identification of Jacobi roots with the
transported matrix eigenvalues, remain explicit typed inputs.  In particular,
the MMP input below is attached to the two factor polynomials and their
positive-root certificates; it is not an assumption about the final xi
comparison function.
-/

namespace Zeta23.Research.JensenWedge

open Finset Metric Polynomial Set
open scoped Polynomial

/-! ## Ascending and descending finite-free conventions -/

/-- Multiplicative finite-free convolution in the ascending,
constant-term-one convention.  The sign is forced by the terminating
hypergeometric identity. -/
noncomputable def finiteFreeAscending (d : ℕ) (p q : ℝ[X]) : ℝ[X] :=
  ∑ k ∈ range (d + 1),
    monomial k (((-1 : ℝ) ^ k * p.coeff k * q.coeff k) / (Nat.choose d k : ℝ))

/-- The same operation in the monic descending convention: exponent `k`
corresponds to elementary-symmetric index `d-k`. -/
noncomputable def finiteFreeDescending (d : ℕ) (p q : ℝ[X]) : ℝ[X] :=
  ∑ k ∈ range (d + 1),
    monomial k
      (((-1 : ℝ) ^ (d - k) * p.coeff k * q.coeff k) / (Nat.choose d k : ℝ))

theorem coeff_finiteFreeAscending (d k : ℕ) (p q : ℝ[X]) :
    (finiteFreeAscending d p q).coeff k =
      if k ≤ d then
        ((-1 : ℝ) ^ k * p.coeff k * q.coeff k) / (Nat.choose d k : ℝ)
      else 0 := by
  simp [finiteFreeAscending, coeff_monomial]

theorem coeff_finiteFreeDescending (d k : ℕ) (p q : ℝ[X]) :
    (finiteFreeDescending d p q).coeff k =
      if k ≤ d then
        ((-1 : ℝ) ^ (d - k) * p.coeff k * q.coeff k) / (Nat.choose d k : ℝ)
      else 0 := by
  simp [finiteFreeDescending, coeff_monomial]

theorem finiteFreeAscending_coeff_zero (d : ℕ) (p q : ℝ[X]) :
    (finiteFreeAscending d p q).coeff 0 = p.coeff 0 * q.coeff 0 := by
  rw [coeff_finiteFreeAscending, if_pos (Nat.zero_le d)]
  simp

theorem finiteFreeDescending_monic_of_monic
    (d : ℕ) (p q : ℝ[X])
    (hp : p.coeff d = 1) (hq : q.coeff d = 1) :
    (finiteFreeDescending d p q).coeff d = 1 := by
  rw [coeff_finiteFreeDescending, if_pos le_rfl, Nat.sub_self, hp, hq]
  simp

/-- Fixed-degree reflection converts the ascending convention into the monic
descending convention exactly.  This is the normalization seam used before
invoking the finite-free literature. -/
theorem reflect_finiteFreeAscending
    (d : ℕ) (p q : ℝ[X]) :
    (finiteFreeAscending d p q).reflect d =
      finiteFreeDescending d (p.reflect d) (q.reflect d) := by
  ext k
  by_cases hk : k ≤ d
  · have hsub : d - k ≤ d := Nat.sub_le d k
    rw [coeff_reflect, revAt_le hk, coeff_finiteFreeAscending,
      if_pos hsub, coeff_finiteFreeDescending, if_pos hk,
      coeff_reflect, coeff_reflect]
    rw [Nat.choose_symm hk]
    simp only [revAt_le hk]
  · have hdk : d < k := Nat.lt_of_not_ge hk
    rw [coeff_reflect, Polynomial.revAt_eq_self_of_lt hdk,
      coeff_finiteFreeAscending, if_neg hk,
      coeff_finiteFreeDescending, if_neg hk]

/-- Reflecting back gives the converse convention change. -/
theorem reflect_finiteFreeDescending
    (d : ℕ) (p q : ℝ[X]) :
    (finiteFreeDescending d p q).reflect d =
      finiteFreeAscending d (p.reflect d) (q.reflect d) := by
  rw [← reflect_reflect (N := d) (p := finiteFreeAscending d (p.reflect d) (q.reflect d)),
    reflect_finiteFreeAscending, reflect_reflect, reflect_reflect]

/-! ## Reciprocal-root and interval conversion -/

/-- A root of a degree-at-most-`d` polynomial becomes its reciprocal under
fixed-degree reflection. -/
theorem eval_reflect_reciprocal_eq_zero_iff
    {p : ℝ[X]} {d : ℕ} (hp : p.natDegree ≤ d)
    {x : ℝ} (hx : x ≠ 0) :
    (p.reflect d).eval x⁻¹ = 0 ↔ p.eval x = 0 := by
  letI : Invertible x := invertibleOfNonzero hx
  simpa [eval₂_at_apply, invOf_eq_inv] using
    (eval₂_reflect_eq_zero_iff (RingHom.id ℝ) x d p hp)

/-- Positive reciprocal reverses a positive interval exactly. -/
theorem reciprocal_mem_interval
    {m M x : ℝ} (hm : 0 < m) (hx : m ≤ x) (hM : x ≤ M) :
    1 / M ≤ 1 / x ∧ 1 / x ≤ 1 / m := by
  have hxpos : 0 < x := lt_of_lt_of_le hm hx
  exact ⟨one_div_le_one_div_of_le hxpos hM,
    one_div_le_one_div_of_le hm hx⟩

/-- Scaling a root by a positive constant scales its positive interval. -/
theorem positive_scale_mem_interval
    {m M x c : ℝ} (hc : 0 < c) (hx : m ≤ x ∧ x ≤ M) :
    c * m ≤ c * x ∧ c * x ≤ c * M :=
  ⟨mul_le_mul_of_nonneg_left hx.1 hc.le, mul_le_mul_of_nonneg_left hx.2 hc.le⟩

/-! ## Gershgorin and the ratio-free constant eight -/

/-- Entrywise certificate sufficient for the consumed Gershgorin interval. -/
structure JacobiGershgorinCertificate
    {d : ℕ} (A : Matrix (Fin d) (Fin d) ℝ) (V r : ℝ) : Prop where
  radius_nonneg : 0 ≤ r
  diagonal : ∀ k, |A k k - V| ≤ 4 * r
  offDiagonal : ∀ k, ∑ j ∈ univ.erase k, ‖A k j‖ ≤ 4 * r

/-- Gershgorin's theorem plus `4+4=8`: every real eigenvalue lies in the
ratio-free interval centered at `V`. -/
theorem eigenvalue_mem_jacobi_interval
    {d : ℕ} {A : Matrix (Fin d) (Fin d) ℝ} {V r μ : ℝ}
    (C : JacobiGershgorinCertificate A V r)
    (hμ : Module.End.HasEigenvalue (Matrix.toLin' A) μ) :
    V - 8 * r ≤ μ ∧ μ ≤ V + 8 * r := by
  obtain ⟨k, hk⟩ := eigenvalue_mem_ball hμ
  have heig : |μ - A k k| ≤ ∑ j ∈ univ.erase k, ‖A k j‖ := by
    simpa [Real.dist_eq] using hk
  have htotal : |μ - V| ≤ 8 * r := by
    calc
      |μ - V| = |(μ - A k k) + (A k k - V)| := by ring_nf
      _ ≤ |μ - A k k| + |A k k - V| := abs_add_le _ _
      _ ≤ 4 * r + 4 * r := add_le_add (heig.trans (C.offDiagonal k)) (C.diagonal k)
      _ = 8 * r := by ring
  rcases abs_le.mp htotal with ⟨hlower, hupper⟩
  constructor <;> linarith

/-- Parameters occurring in the transported Jacobi matrix. -/
noncomputable def jacobiH (U : ℝ) (d : ℕ) : ℝ := U - d - 1

noncomputable def transportedJacobiDiagonal
    (U V : ℝ) (d k : ℕ) : ℝ :=
  U * (jacobiH U d * (V + 2 * k) + 2 * k * (k + 1)) /
    ((jacobiH U d + 2 * k) * (jacobiH U d + 2 * k + 2))

noncomputable def transportedJacobiOffDiagonal
    (U V : ℝ) (d k : ℕ) : ℝ :=
  U / (2 * k + jacobiH U d) *
    Real.sqrt
      ((k * (k + V - 1) * (k + (U - V - d)) * (k + jacobiH U d)) /
        ((2 * k + jacobiH U d - 1) * (2 * k + jacobiH U d + 1)))

/-- Exact algebraic form of the transported diagonal displacement. -/
theorem transportedJacobiDiagonal_sub
    {U V : ℝ} {d k : ℕ}
    (h₀ : jacobiH U d + 2 * k ≠ 0)
    (h₂ : jacobiH U d + 2 * k + 2 ≠ 0) :
    transportedJacobiDiagonal U V d k - V =
      (2 * k * (k + jacobiH U d + 1) * (U - 2 * V) +
        V * jacobiH U d * ((d : ℝ) - 1)) /
      ((jacobiH U d + 2 * k) * (jacobiH U d + 2 * k + 2)) := by
  dsimp [transportedJacobiDiagonal, jacobiH] at h₀ h₂ ⊢
  field_simp [h₀, h₂]
  ring

/-- Typed classical seam: every zero of the Jacobi factor is an eigenvalue
of the displayed transported matrix, whose entry bounds have been checked. -/
structure RatioFreeJacobiInput
    (q : ℝ[X]) (d : ℕ) (U V : ℝ) where
  matrix : Matrix (Fin d) (Fin d) ℝ
  scale_radius : ℝ
  scale_radius_eq : scale_radius = Real.sqrt (V * d)
  entry_certificate : JacobiGershgorinCertificate matrix V scale_radius
  root_is_eigenvalue : ∀ y, q.eval y = 0 →
    Module.End.HasEigenvalue (Matrix.toLin' matrix) y

/-- Once the classical Jacobi matrix identification and its entry bounds are
supplied, the advertised constant-eight interval is a kernel-checked
consequence. -/
theorem RatioFreeJacobiInput.root_interval
    {q : ℝ[X]} {d : ℕ} {U V : ℝ}
    (I : RatioFreeJacobiInput q d U V)
    {y : ℝ} (hy : q.eval y = 0) :
    V - 8 * Real.sqrt (V * d) ≤ y ∧
      y ≤ V + 8 * Real.sqrt (V * d) := by
  simpa [I.scale_radius_eq] using
    eigenvalue_mem_jacobi_interval I.entry_certificate (I.root_is_eigenvalue y hy)

/-! ## MSS product interval and localization arithmetic -/

/-- Exact two-sided consequence consumed from MSS Theorem 1.6: the original
orientation supplies the upper bound and the reciprocal orientation supplies
the lower bound. -/
structure MSSProductRootInput
    (z uLower uUpper vLower vUpper : ℝ) : Prop where
  first_lower_pos : 0 < uLower
  second_lower_pos : 0 < vLower
  root_pos : 0 < z
  largest_root : z ≤ uUpper * vUpper
  reciprocal_largest_root : 1 / z ≤ (1 / uLower) * (1 / vLower)

theorem MSSProductRootInput.product_interval
    {z uLower uUpper vLower vUpper : ℝ}
    (I : MSSProductRootInput z uLower uUpper vLower vUpper) :
    uLower * vLower ≤ z ∧ z ≤ uUpper * vUpper := by
  have hprod : 0 < uLower * vLower := mul_pos I.first_lower_pos I.second_lower_pos
  have hrecip : 1 / z ≤ 1 / (uLower * vLower) := by
    calc
      1 / z ≤ (1 / uLower) * (1 / vLower) := I.reciprocal_largest_root
      _ = 1 / (uLower * vLower) := by field_simp
  exact ⟨(one_div_le_one_div I.root_pos hprod).mp hrecip, I.largest_root⟩

/-- Exact arithmetic behind the product localization constant.  Here `r` is
`sqrt(Bd)`, `s` is `sqrt(d/D)`, and `q` is `sqrt(B/D)`; the identities tying
those radicals together are explicit hypotheses rather than simplifier
guesses. -/
theorem productDeviation_le_localizationConstant
    {B r s q u v : ℝ}
    (hB : 0 ≤ B) (hr : 0 ≤ r) (_hs : 0 ≤ s)
    (hu : |u| ≤ 8 * r) (hv : |v| ≤ 8 * s)
    (hBs : B * s = r * q)
    (hq : q ≤ Real.sqrt 6) (hs16 : s ≤ 1 / 16) :
    |(B + u) * (1 + v) - B| ≤ localizationConstant * r := by
  have hsqrt : 0 ≤ Real.sqrt 6 := Real.sqrt_nonneg 6
  have habs :
      |(B + u) * (1 + v) - B| ≤ |u| + B * |v| + |u| * |v| := by
    calc
      |(B + u) * (1 + v) - B| = |u + B * v + u * v| := by ring_nf
      _ ≤ |u| + |B * v| + |u * v| := by
        calc
          |u + B * v + u * v| ≤ |u + B * v| + |u * v| := abs_add_le _ _
          _ ≤ (|u| + |B * v|) + |u * v| :=
            add_le_add (abs_add_le u (B * v)) le_rfl
      _ = |u| + B * |v| + |u| * |v| := by
        rw [abs_mul, abs_mul, abs_of_nonneg hB]
  have hBv : B * |v| ≤ 8 * r * q := by
    calc
      B * |v| ≤ B * (8 * s) := mul_le_mul_of_nonneg_left hv hB
      _ = 8 * (B * s) := by ring
      _ = 8 * r * q := by
        rw [hBs]
        ring
  have huv : |u| * |v| ≤ 64 * r * s := by
    calc
      |u| * |v| ≤ (8 * r) * (8 * s) :=
        mul_le_mul hu hv (abs_nonneg _) (by positivity)
      _ = 64 * r * s := by ring
  have hqterm : 8 * r * q ≤ 8 * r * Real.sqrt 6 := by
    exact mul_le_mul_of_nonneg_left hq (by positivity)
  have hsterm : 64 * r * s ≤ 4 * r := by
    nlinarith
  calc
    |(B + u) * (1 + v) - B| ≤ |u| + B * |v| + |u| * |v| := habs
    _ ≤ 8 * r + (8 * r * q) + (64 * r * s) := add_le_add (add_le_add hu hBv) huv
    _ ≤ 8 * r + (8 * r * Real.sqrt 6) + 4 * r :=
      add_le_add (add_le_add le_rfl hqterm) hsterm
    _ = localizationConstant * r := by
      dsimp [localizationConstant]
      ring

/-! ## MMP logarithmic-mesh adapter -/

/-- Pairwise form of strict logarithmic mesh for a positive descending root
list.  It is equivalent to the adjacent-ratio convention in the paper, but
is the most direct form for the consumed distinctness consequence. -/
structure StrictLogMesh {d : ℕ} (roots : Fin d → ℝ) : Prop where
  positive : ∀ i, 0 < roots i
  ratio_gt_one : ∀ i j, i < j → 1 < roots i / roots j

theorem StrictLogMesh.strictAnti
    {d : ℕ} {roots : Fin d → ℝ} (h : StrictLogMesh roots) :
    StrictAnti roots := by
  intro i j hij
  have hj := h.positive j
  have hratio := h.ratio_gt_one i j hij
  rw [lt_div_iff₀ hj] at hratio
  simpa using hratio

theorem StrictLogMesh.injective
    {d : ℕ} {roots : Fin d → ℝ} (h : StrictLogMesh roots) :
    Function.Injective roots :=
  h.strictAnti.injective

theorem StrictLogMesh.positive_scale
    {d : ℕ} {roots : Fin d → ℝ} (h : StrictLogMesh roots)
    {c : ℝ} (hc : 0 < c) :
    StrictLogMesh (fun i => c * roots i) := by
  constructor
  · intro i
    exact mul_pos hc (h.positive i)
  · intro i j hij
    have hci : c * roots i / (c * roots j) = roots i / roots j := by
      field_simp [ne_of_gt hc]
    rw [hci]
    exact h.ratio_gt_one i j hij

/-- Exact factor-level MMP seam used downstream.  The two degree bounds and
complete positive simple-root lists are the hypotheses needed to place the
factors in the positive-rooted class.  The final three fields are the
specialized conclusion of MMP Proposition 2.17 for the exact ascending
finite-free convolution defined in this module.

The external input therefore concerns `finiteFreeAscending d p q`, not a
paper-specific `_3F_2` or xi function.  The latter identification is proved
coefficientwise in `XiNaturalFiniteFreeSpecialization`. -/
structure MMPFiniteFreeLogMeshInput (p q : ℝ[X]) (d : ℕ) where
  first_factor : HasDistinctPositiveRoots p.eval d
  first_degree : p.natDegree ≤ d
  second_factor : HasDistinctPositiveRoots q.eval d
  second_degree : q.natDegree ≤ d
  roots : Fin d → ℝ
  strict_log_mesh : StrictLogMesh roots
  roots_are_zeros : ∀ i, (finiteFreeAscending d p q).eval (roots i) = 0

theorem MMPFiniteFreeLogMeshInput.hasDistinctPositiveRoots
    {p q : ℝ[X]} {d : ℕ} (I : MMPFiniteFreeLogMeshInput p q d) :
    HasDistinctPositiveRoots (finiteFreeAscending d p q).eval d :=
  ⟨I.roots, I.strict_log_mesh.injective,
    fun i => ⟨I.strict_log_mesh.positive i, I.roots_are_zeros i⟩⟩

end Zeta23.Research.JensenWedge
