import Zeta23.XiPrime.Defs
import Mathlib.Analysis.Complex.Liouville
import Mathlib.Topology.MetricSpace.Contracting

/-!
# Analytic adapters for the Jensen two-thirds argument

This module kernel-checks the analytic glue that can be stated independently
of the long theta-kernel contour calculation:

* the centered Riemann-xi normalization and its evenness;
* the exact Taylor-coefficient normalization used by the Jensen polynomials;
* a typed factor-eight adapter from a half-line moment identity;
* a closed-disc contraction theorem suitable for a saddle branch; and
* Cauchy transport of a holomorphic relative error through order six.

The theorem connecting Mathlib's completed zeta to Riemann's theta-kernel
integral is deliberately not asserted in this adapter module.  It is proved
downstream in `XiMellin` through `XiOmegaCoefficients`, where
`centeredXiCoefficient_eq_factorEightMoment` is instantiated with the concrete
kernel from the manuscript.
-/

namespace Zeta23.Research.JensenWedge

open Complex Filter Function MeasureTheory Set Topology

noncomputable section

/-! ## Centered xi and the coefficient convention -/

/-- Riemann's entire xi function, expressed using Mathlib's pole-removed
completed zeta. -/
abbrev riemannXi : ℂ → ℂ := Zeta23.XiPrime.xi

theorem riemannXi_differentiable : Differentiable ℂ riemannXi := by
  unfold riemannXi Zeta23.XiPrime.xi
  exact (((differentiable_id.mul (differentiable_id.sub_const 1)).div_const 2).mul
    differentiable_completedZeta₀).add_const _

theorem riemannXi_one_sub (s : ℂ) : riemannXi (1 - s) = riemannXi s := by
  unfold riemannXi Zeta23.XiPrime.xi
  rw [completedRiemannZeta₀_one_sub]
  ring

/-- The centered entire function `w ↦ xi(1/2+w)`. -/
def centeredXi (w : ℂ) : ℂ := riemannXi (1 / 2 + w)

theorem centeredXi_differentiable : Differentiable ℂ centeredXi := by
  exact riemannXi_differentiable.comp
    ((differentiable_const (c := (1 / 2 : ℂ))).add differentiable_id)

theorem centeredXi_even (w : ℂ) : centeredXi (-w) = centeredXi w := by
  have h := riemannXi_one_sub (1 / 2 + w)
  unfold centeredXi
  convert h using 1
  ring_nf

/-- The manuscript convention
`xi(1/2+w) = sum gamma(n) * w^(2n) / n!`, expressed directly through
the even derivatives of Mathlib's xi. -/
def centeredXiCoefficient (n : ℕ) : ℂ :=
  (n.factorial : ℂ) / ((2 * n).factorial : ℂ) *
    iteratedDeriv (2 * n) centeredXi 0

theorem centeredXiCoefficient_taylor_normalization (n : ℕ) :
    centeredXiCoefficient n / (n.factorial : ℂ) =
      iteratedDeriv (2 * n) centeredXi 0 / ((2 * n).factorial : ℂ) := by
  unfold centeredXiCoefficient
  have hn : (n.factorial : ℂ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero n
  field_simp [hn]

/-! ## The exact factor-eight seam -/

/-- A half-line moment with the power used in the centered-xi expansion. -/
def halfLineMoment (kernel : ℝ → ℂ) (n : ℕ) : ℂ :=
  ∫ u in Ioi (0 : ℝ), kernel u * (u : ℂ) ^ (2 * n)

/-- Once the analytic theta-kernel identity identifies the `2n`-th
derivative of centered xi with eight times the half-line moment, the
factor-eight coefficient formula follows by exact algebra. -/
theorem centeredXiCoefficient_eq_factorEightMoment
    (kernel : ℝ → ℂ) (n : ℕ)
    (hMellin : iteratedDeriv (2 * n) centeredXi 0 =
      8 * halfLineMoment kernel n) :
    centeredXiCoefficient n =
      8 * (n.factorial : ℂ) / ((2 * n).factorial : ℂ) *
        halfLineMoment kernel n := by
  rw [centeredXiCoefficient, hMellin]
  ring

/-! ## A quantitative closed-disc branch adapter -/

/-- A contraction of a closed complex disc has a unique fixed point in that
disc.  This is the Banach alternative to the existence/uniqueness portion of
the manuscript's Rouche argument.  Instantiation still requires a uniform
self-map and contraction certificate for the concrete saddle equation. -/
theorem complexClosedBall_existsUnique_fixedPoint
    {T : ℂ → ℂ} {center : ℂ} {radius : ℝ} {K : NNReal}
    (hradius : 0 ≤ radius)
    (hmaps : MapsTo T (Metric.closedBall center radius) (Metric.closedBall center radius))
    (hcontract : ContractingWith K
      (hmaps.restrict T (Metric.closedBall center radius) (Metric.closedBall center radius))) :
    ∃ z ∈ Metric.closedBall center radius, IsFixedPt T z ∧
      ∀ w ∈ Metric.closedBall center radius, IsFixedPt T w → w = z := by
  have hcomplete : IsComplete (Metric.closedBall center radius) :=
    Metric.isClosed_closedBall.isComplete
  have hcenter : center ∈ Metric.closedBall center radius := by simpa using hradius
  have hfinite : edist center (T center) ≠ ⊤ := edist_ne_top _ _
  rcases hcontract.exists_fixedPoint' hcomplete hmaps hcenter hfinite with
    ⟨z, hzmem, hzfixed, _⟩
  refine ⟨z, hzmem, hzfixed, ?_⟩
  intro w hwmem hwfixed
  have hzrestricted : IsFixedPt
      (hmaps.restrict T (Metric.closedBall center radius) (Metric.closedBall center radius))
      ⟨z, hzmem⟩ := Subtype.ext hzfixed
  have hwrestricted : IsFixedPt
      (hmaps.restrict T (Metric.closedBall center radius) (Metric.closedBall center radius))
      ⟨w, hwmem⟩ := Subtype.ext hwfixed
  exact congrArg Subtype.val (hcontract.fixedPoint_unique' hwrestricted hzrestricted)

/-! ## Holomorphic relative-error transport -/

/-- Relative error in the convention `actual = main * (1 + error)`. -/
def holomorphicRelativeError (actual main : ℂ → ℂ) (z : ℂ) : ℂ :=
  actual z / main z - 1

/-- Cauchy's estimate transports a uniform relative-error bound on a larger
domain to every derivative at the center of an enclosed disc. -/
theorem relativeError_iteratedDeriv_le
    {actual main : ℂ → ℂ} {domain : Set ℂ} {center : ℂ}
    {radius epsilon : ℝ} (n : ℕ)
    (hradius : 0 < radius)
    (hball : Metric.closedBall center radius ⊆ domain)
    (hactual : DifferentiableOn ℂ actual domain)
    (hmain : DifferentiableOn ℂ main domain)
    (hmain_ne : ∀ z ∈ domain, main z ≠ 0)
    (herror : ∀ z ∈ domain, ‖holomorphicRelativeError actual main z‖ ≤ epsilon) :
    ‖iteratedDeriv n (holomorphicRelativeError actual main) center‖ ≤
      n.factorial * epsilon / radius ^ n := by
  have hdifferentiable : DifferentiableOn ℂ
      (holomorphicRelativeError actual main) domain := by
    unfold holomorphicRelativeError
    exact (hactual.div hmain hmain_ne).sub_const 1
  have hdisc : DiffContOnCl ℂ (holomorphicRelativeError actual main)
      (Metric.ball center radius) :=
    hdifferentiable.diffContOnCl_ball hball
  apply Complex.norm_iteratedDeriv_le_of_forall_mem_sphere_norm_le
    n hradius hdisc
  intro z hz
  exact herror z (hball (Metric.sphere_subset_closedBall hz))

/-- The precise order-six form consumed by the sixth-order saddle tower.  The
generic theorem is stronger; this corollary records the manuscript cutoff in
the type. -/
theorem relativeError_derivatives_through_six
    {actual main : ℂ → ℂ} {domain : Set ℂ} {center : ℂ}
    {radius epsilon : ℝ}
    (hradius : 0 < radius)
    (hball : Metric.closedBall center radius ⊆ domain)
    (hactual : DifferentiableOn ℂ actual domain)
    (hmain : DifferentiableOn ℂ main domain)
    (hmain_ne : ∀ z ∈ domain, main z ≠ 0)
    (herror : ∀ z ∈ domain, ‖holomorphicRelativeError actual main z‖ ≤ epsilon) :
    ∀ n ≤ 6,
      ‖iteratedDeriv n (holomorphicRelativeError actual main) center‖ ≤
        n.factorial * epsilon / radius ^ n := by
  intro n _hn
  exact relativeError_iteratedDeriv_le n hradius hball hactual hmain hmain_ne herror

/-! ## Honest analytic certificate boundary -/

/-- A distinguished saddle branch on a parameter domain.  The set
`admissible s` is part of the certificate: uniqueness is asserted only in the
certified moving neighbourhood containing the distinguished root, not among
all complex roots of a transcendental saddle equation. -/
structure SectorialSaddleCertificate
    (domain : Set ℂ) (equation curvature : ℂ → ℂ → ℂ) where
  branch : ℂ → ℂ
  admissible : ℂ → Set ℂ
  branch_mem : ∀ s ∈ domain, branch s ∈ admissible s
  branch_differentiable : DifferentiableOn ℂ branch domain
  equation_zero : ∀ s ∈ domain, equation s (branch s) = 0
  root_unique : ∀ s ∈ domain, ∀ z ∈ admissible s,
    equation s z = 0 → z = branch s
  curvature_ne_zero : ∀ s ∈ domain, curvature s (branch s) ≠ 0

end

end Zeta23.Research.JensenWedge
