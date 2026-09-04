/-
Zeta23/PairCeiling/CeilingLaw256Distinct.lean — NEW (this research program): the FIRST bandwidth-one
ceiling for DISTINCT zeros, as the affine image of the simple-zeros ceiling.

Mathematical content: for every grid form factor S inside the kernel-checked enclosures of LawN256 —
in particular the law's own — and every bandwidth-one certificate (c₀, r) with r(1) ≥ 0 that is valid
against the law at its DISTINCT fraction pd₀ (i.e. c₀ + Σ_{j=1}^{256} (S(j)/256)·r(j/256) ≤ pd₀),
the certificate's value satisfies
      c₀ + ∫₀¹ r(x)·x dx ≤ pd₀ + 2.5431316e-6·(|r′(1)| + ∫₀¹|r″|),   pd₀ = (1 + p₀)/2 = 0.8409143….

The affine identity (proved here as rational arithmetic): for a marks-{1,2} configuration with
d double points, #occupied = N − d and #simple = N − 2d, hence p_d = (1 + p_simple)/2; by linearity
the identity holds for mixtures, hence for the champion law. See
/mnt/agents/output/numerics_alpha/dist_report.md for the LP evidence (marks {1,2,3}: triples never
activate in either objective; N = 64/128/256).

Extra-Lean meta-inputs (parallel to CeilingLaw256P0): EnclOK (external interval arithmetic) and the
existence/admissibility of the law as a marked configuration mixture with the stated fractions
(external LP certificate). The meta-claim that distinct-zeros certificates are valid configuration by
configuration at distinct fractions is external, exactly parallel to the paper's Remark 1.1 for simple
zeros; gate-reviewed before authoring (see SPEC.md and ledger.md).
-/
import Zeta23.PairCeiling.Signed
import Zeta23.PairCeiling.CeilingLaw256P0

open scoped BigOperators Interval
open MeasureTheory Set

noncomputable section

namespace Zeta23
namespace PairCeiling

/-- **The N = 256 law's distinct-point fraction**: pd₀ = (1 + p₀)/2, the affine image of its simple
fraction p₀ under the marks-{1,2} identity p_d = (1 + p_simple)/2. -/
def lawN256_pd0 : ℚ := (1 + lawN256_p0) / 2

/-- pd₀ rounded UP at the seventh decimal: pd₀ = 0.84091434… ≤ 0.8409144. -/
theorem lawN256_pd0_le_decimal : (lawN256_pd0 : ℝ) ≤ 0.8409144 := by
  norm_num [lawN256_pd0, lawN256_p0]

/-- pd₀ rounded DOWN at the eighth decimal. -/
theorem decimal_le_lawN256_pd0 : (0.84091434 : ℝ) ≤ lawN256_pd0 := by
  norm_num [lawN256_pd0, lawN256_p0]

/-- **SIGNED DISTINCT-ZEROS CEILING AT pd₀**: certificates with r(1) ≥ 0 valid against the N = 256 law
at its distinct fraction pd₀ certify at most pd₀ + 2.5431316·10⁻⁶·(|r′(1)| + ∫₀¹|r″|). -/
theorem ceiling_law256_signed_distinct_at_pd0 (S : ℕ → ℝ) (hS : EnclOK LawN256.K S 0 LawN256.encl)
    {r g h : ℝ → ℝ} {T : Set ℝ} (hT : T.Countable) {c₀ : ℝ}
    (hr : ∀ x ∈ Icc (0:ℝ) 1, HasDerivAt r (g x) x) (hg : ContinuousOn g (Icc (0:ℝ) 1))
    (hgh : ∀ x ∈ Ioo (0:ℝ) 1 \ T, HasDerivAt g (h x) x) (hh : IntervalIntegrable h volume 0 1)
    (hr1 : 0 ≤ r 1)
    (hvalid : c₀ + ∑ j ∈ Finset.Icc 1 256, massOf S 256 j * r ((j:ℝ)/256) ≤ lawN256_pd0) :
    c₀ + ∫ x in (0:ℝ)..1, r x * x
      ≤ lawN256_pd0 + 2.5431316e-6 * |g 1| + 2.5431316e-6 * ∫ x in (0:ℝ)..1, |h x| := by
  exact ceiling_law256_signed S hS hT hr hg hgh hh hr1 hvalid

/-- **HEADLINE FORM (distinct zeros)**: … ≤ 0.8409144 + 2.5431316·10⁻⁶·(|r′(1)| + ∫₀¹|r″|). -/
theorem ceiling_law256_signed_distinct_headline (S : ℕ → ℝ) (hS : EnclOK LawN256.K S 0 LawN256.encl)
    {r g h : ℝ → ℝ} {T : Set ℝ} (hT : T.Countable) {c₀ : ℝ}
    (hr : ∀ x ∈ Icc (0:ℝ) 1, HasDerivAt r (g x) x) (hg : ContinuousOn g (Icc (0:ℝ) 1))
    (hgh : ∀ x ∈ Ioo (0:ℝ) 1 \ T, HasDerivAt g (h x) x) (hh : IntervalIntegrable h volume 0 1)
    (hr1 : 0 ≤ r 1)
    (hvalid : c₀ + ∑ j ∈ Finset.Icc 1 256, massOf S 256 j * r ((j:ℝ)/256) ≤ lawN256_pd0) :
    c₀ + ∫ x in (0:ℝ)..1, r x * x
      ≤ 0.8409144 + 2.5431316e-6 * |g 1| + 2.5431316e-6 * ∫ x in (0:ℝ)..1, |h x| := by
  have h0 := ceiling_law256_signed_distinct_at_pd0 S hS hT hr hg hgh hh hr1 hvalid
  have hp := lawN256_pd0_le_decimal
  have hb : 0 ≤ |g 1| := abs_nonneg _
  have hI : 0 ≤ ∫ x in (0:ℝ)..1, |h x| :=
    intervalIntegral.integral_nonneg zero_le_one fun x _ => abs_nonneg _
  nlinarith

end PairCeiling
end Zeta23

end
