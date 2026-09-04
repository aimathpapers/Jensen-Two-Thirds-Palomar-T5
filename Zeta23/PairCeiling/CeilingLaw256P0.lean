/-
Zeta23/PairCeiling/CeilingLaw256P0.lean — NEW (this research program): instantiate the signed ceiling
at the law's own simple-point fraction p₀, upgrading the headline constant 0.6818287 from a docstring
comment to a Lean theorem (modulo the designed displayed hypothesis EnclOK, as with the rest of
Zeta23/PairCeiling).

Mathematical content: for every grid form factor S inside the kernel-checked enclosures of LawN256 —
in particular the law's own — and every bandwidth-one certificate (c₀, r) with r(1) ≥ 0 that is valid
against the law at its own simple fraction p₀ (i.e. c₀ + Σ_{j=1}^{256} (S(j)/256)·r(j/256) ≤ p₀),
the certificate's value satisfies
      c₀ + ∫₀¹ r(x)·x dx ≤ p₀ + 2.5431316e-6·(|r′(1)| + ∫₀¹|r″|)  ≤  0.6818287 + 2.5431316e-6·(...).

The extra-Lean meta-inputs (unchanged from the rest of the PairCeiling pipeline):
  * EnclOK: the law's true S lies in the enclosures (interval arithmetic, external);
  * the existence of the law as an admissible marked configuration mixture with simple fraction p₀
    (external exact-rational LP certificate, sha256 cc3de991…, cf. LawN256.lean header).
-/
import Zeta23.PairCeiling.Signed

open scoped BigOperators Interval
open MeasureTheory Set

noncomputable section

namespace Zeta23
namespace PairCeiling

/-- **The N = 256 law's exact simple-point fraction** (from the external exact-rational LP certificate;
recorded in LawN256.lean's docstring, here promoted to a definition). -/
def lawN256_p0 : ℚ :=
  10909258999421303588095230195816054408197 / 16000000000000000000000000000000000000000

/-- p₀ rounded UP at the seventh decimal: p₀ = 0.68182868746… ≤ 0.6818287. -/
theorem lawN256_p0_le_decimal : (lawN256_p0 : ℝ) ≤ 0.6818287 := by
  norm_num [lawN256_p0]

/-- p₀ rounded DOWN at the eighth decimal: 0.68182868 ≤ p₀ (so both bounds sandwich p₀ to 8 digits). -/
theorem decimal_le_lawN256_p0 : (0.68182868 : ℝ) ≤ lawN256_p0 := by
  norm_num [lawN256_p0]

/-- **SIGNED CEILING INSTANTIATED AT p₀** (Theorem 1′ at the law's own simple fraction):
certificates with r(1) ≥ 0 valid against the N = 256 law at p₀ certify at most
p₀ + 2.5431316·10⁻⁶·(|r′(1)| + ∫₀¹|r″|). -/
theorem ceiling_law256_signed_at_p0 (S : ℕ → ℝ) (hS : EnclOK LawN256.K S 0 LawN256.encl)
    {r g h : ℝ → ℝ} {T : Set ℝ} (hT : T.Countable) {c₀ : ℝ}
    (hr : ∀ x ∈ Icc (0:ℝ) 1, HasDerivAt r (g x) x) (hg : ContinuousOn g (Icc (0:ℝ) 1))
    (hgh : ∀ x ∈ Ioo (0:ℝ) 1 \ T, HasDerivAt g (h x) x) (hh : IntervalIntegrable h volume 0 1)
    (hr1 : 0 ≤ r 1)
    (hvalid : c₀ + ∑ j ∈ Finset.Icc 1 256, massOf S 256 j * r ((j:ℝ)/256) ≤ lawN256_p0) :
    c₀ + ∫ x in (0:ℝ)..1, r x * x
      ≤ lawN256_p0 + 2.5431316e-6 * |g 1| + 2.5431316e-6 * ∫ x in (0:ℝ)..1, |h x| := by
  exact ceiling_law256_signed S hS hT hr hg hgh hh hr1 hvalid

/-- **HEADLINE FORM**: … ≤ 0.6818287 + 2.5431316·10⁻⁶·(|r′(1)| + ∫₀¹|r″|). -/
theorem ceiling_law256_signed_headline (S : ℕ → ℝ) (hS : EnclOK LawN256.K S 0 LawN256.encl)
    {r g h : ℝ → ℝ} {T : Set ℝ} (hT : T.Countable) {c₀ : ℝ}
    (hr : ∀ x ∈ Icc (0:ℝ) 1, HasDerivAt r (g x) x) (hg : ContinuousOn g (Icc (0:ℝ) 1))
    (hgh : ∀ x ∈ Ioo (0:ℝ) 1 \ T, HasDerivAt g (h x) x) (hh : IntervalIntegrable h volume 0 1)
    (hr1 : 0 ≤ r 1)
    (hvalid : c₀ + ∑ j ∈ Finset.Icc 1 256, massOf S 256 j * r ((j:ℝ)/256) ≤ lawN256_p0) :
    c₀ + ∫ x in (0:ℝ)..1, r x * x
      ≤ 0.6818287 + 2.5431316e-6 * |g 1| + 2.5431316e-6 * ∫ x in (0:ℝ)..1, |h x| := by
  have h0 := ceiling_law256_signed_at_p0 S hS hT hr hg hgh hh hr1 hvalid
  have hp := lawN256_p0_le_decimal
  have hb : 0 ≤ |g 1| := abs_nonneg _
  have hI : 0 ≤ ∫ x in (0:ℝ)..1, |h x| :=
    intervalIntegral.integral_nonneg zero_le_one fun x _ => abs_nonneg _
  nlinarith

end PairCeiling
end Zeta23

end
