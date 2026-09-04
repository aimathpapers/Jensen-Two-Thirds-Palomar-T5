import Zeta23.Research.JensenWedge.LeadingSaddleContour

/-!
# The distinguished saddle on the positive real axis

The complex saddle is selected by uniqueness in a small closed disc.  For a
positive real parameter, both the equation and that disc are invariant under
complex conjugation.  Uniqueness therefore forces the selected saddle to be
real.  This closes the branch ambiguity needed when the analytic logarithm is
specialized back to the positive integer coefficient sequence.
-/

namespace Zeta23.Research.JensenWedge

open Complex Set
open scoped ComplexConjugate

noncomputable section

theorem saddleComparisonCenter_ofReal
    {x : ℝ} (hx : 0 < x) (hs : (x : ℂ) ∈ leanSaddleSector) :
    saddleComparisonCenter (x : ℂ) =
      (Real.log x - Real.log (Real.log x) - Real.log Real.pi : ℝ) := by
  have hlogx : 0 < Real.log x := by
    have hlarge := leanSaddleSector_log_re_gt hs
    rw [Complex.log_re, norm_real, Real.norm_eq_abs, abs_of_pos hx] at hlarge
    linarith
  unfold saddleComparisonCenter
  rw [← Complex.ofReal_log hx.le, ← Complex.ofReal_log hlogx.le,
    ← Complex.ofReal_log Real.pi_pos.le]
  push_cast
  ring

theorem saddleComparisonCenter_ofReal_conj
    {x : ℝ} (hx : 0 < x) (hs : (x : ℂ) ∈ leanSaddleSector) :
    conj (saddleComparisonCenter (x : ℂ)) =
      saddleComparisonCenter (x : ℂ) := by
  rw [saddleComparisonCenter_ofReal hx hs, conj_ofReal]

theorem sectorialSaddleEquation_conj_ofReal
    {x : ℝ} {L : ℂ}
    (hroot : sectorialSaddleEquation (x : ℂ) L = 0) :
    sectorialSaddleEquation (x : ℂ) (conj L) = 0 := by
  have hc := congrArg conj hroot
  unfold sectorialSaddleEquation saddleParameterMap at hc ⊢
  simpa only [map_sub, map_mul, map_add, map_div₀, map_ofNat,
    conj_ofReal, exp_conj, map_zero] using hc

/-- The contraction-selected saddle is real for every positive real
parameter in the fixed sector. -/
theorem quantitativeSaddleBranch_ofReal_conj
    {x : ℝ} (hx : 0 < x) (hs : (x : ℂ) ∈ leanSaddleSector) :
    conj (quantitativeSaddleBranch (x : ℂ)) =
      quantitativeSaddleBranch (x : ℂ) := by
  let L := quantitativeSaddleBranch (x : ℂ)
  let C := saddleComparisonCenter (x : ℂ)
  have hq : (x : ℂ) ∈ quantitativeSaddleDomain :=
    leanSaddleSector_quantitative hs
  have hspec := quantitativeSaddleBranch_spec hq
  have hC : conj C = C := by
    simpa only [C] using saddleComparisonCenter_ofReal_conj hx hs
  have hconjmem : conj L ∈ Metric.closedBall C (1 / 20) := by
    rw [Metric.mem_closedBall] at hspec ⊢
    calc
      dist (conj L) C = dist (conj L) (conj C) := by rw [hC]
      _ = dist L C := Complex.dist_conj_conj L C
      _ ≤ 1 / 20 := hspec.1
  have hroot : sectorialSaddleEquation (x : ℂ) L = 0 := hspec.2.1
  have hconjroot : sectorialSaddleEquation (x : ℂ) (conj L) = 0 :=
    sectorialSaddleEquation_conj_ofReal hroot
  simpa only [L] using hspec.2.2 (conj L) hconjmem hconjroot

theorem quantitativeSaddleBranch_ofReal_im
    {x : ℝ} (hx : 0 < x) (hs : (x : ℂ) ∈ leanSaddleSector) :
    (quantitativeSaddleBranch (x : ℂ)).im = 0 :=
  Complex.conj_eq_iff_im.mp (quantitativeSaddleBranch_ofReal_conj hx hs)

theorem quantitativeSaddleBranch_ofReal_eq_re
    {x : ℝ} (hx : 0 < x) (hs : (x : ℂ) ∈ leanSaddleSector) :
    quantitativeSaddleBranch (x : ℂ) =
      ((quantitativeSaddleBranch (x : ℂ)).re : ℂ) := by
  exact (Complex.conj_eq_iff_re.mp
    (quantitativeSaddleBranch_ofReal_conj hx hs)).symm

end

end Zeta23.Research.JensenWedge
