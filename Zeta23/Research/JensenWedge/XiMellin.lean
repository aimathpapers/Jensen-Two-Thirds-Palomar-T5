import Zeta23.Research.JensenWedge.AnalyticAdapters

/-!
# The concrete Mellin kernel for Riemann xi

This file exposes the exact Mellin-transform object already used by Mathlib
to define the pole-removed completed Riemann zeta function.  In particular,
the representation below has no user-supplied Mellin hypothesis: it is a
definitional consequence of Mathlib's theta-kernel construction.

This is the first, deliberately narrow, milestone in the formal proof of T1.
Differentiation under the integral and the integration-by-parts conversion to
the manuscript's positive `omega` kernel are proved in subsequent milestones.
-/

namespace Zeta23.Research.JensenWedge

open Complex Filter Function MeasureTheory Set Topology
open HurwitzZeta

noncomputable section

/-- The weak functional-equation pair built from Riemann's theta series. -/
abbrev riemannThetaFEPair : WeakFEPair ℂ := hurwitzEvenFEPair 0

/-- Mathlib's rapidly decaying, piecewise modified Riemann theta kernel.
It is the actual function whose Mellin transform defines
`completedRiemannZeta₀`. -/
def riemannThetaModifiedKernel : ℝ → ℂ := riemannThetaFEPair.f_modif

/-- The exact Mellin representation underlying Mathlib's entire completed
zeta.  The argument is scaled by `1/2`, and the transform by `1/2`, exactly as
in the even-Hurwitz-zeta specialization. -/
theorem completedRiemannZeta₀_eq_mellin_riemannThetaModifiedKernel (s : ℂ) :
    completedRiemannZeta₀ s =
      mellin riemannThetaModifiedKernel (s / 2) / 2 := by
  rfl

/-- On the upper branch, the modified kernel is theta minus its constant
term. -/
theorem riemannThetaModifiedKernel_of_one_lt {t : ℝ} (ht : 1 < t) :
    riemannThetaModifiedKernel t = (evenKernel 0 t : ℂ) - 1 := by
  simp [riemannThetaModifiedKernel, riemannThetaFEPair, WeakFEPair.f_modif,
    hurwitzEvenFEPair, mem_Ioi.mpr ht, notMem_Ioo_of_ge ht.le]

/-- On the lower branch, the modular singular term `t^(-1/2)` is subtracted
from theta. -/
theorem riemannThetaModifiedKernel_of_mem_Ioo {t : ℝ} (ht : t ∈ Ioo 0 1) :
    riemannThetaModifiedKernel t =
      (evenKernel 0 t : ℂ) - ((t ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) := by
  simp [riemannThetaModifiedKernel, riemannThetaFEPair, WeakFEPair.f_modif,
    hurwitzEvenFEPair, ht, notMem_Ioi.mpr ht.2.le]

/-- The concrete kernel is locally integrable on the positive half-line. -/
theorem riemannThetaModifiedKernel_locallyIntegrableOn :
    LocallyIntegrableOn riemannThetaModifiedKernel (Ioi 0) :=
  riemannThetaFEPair.hf_modif_int

/-- The concrete kernel decays faster than every real power at infinity. -/
theorem riemannThetaModifiedKernel_isBigO_atTop (r : ℝ) :
    riemannThetaModifiedKernel =O[atTop] (· ^ r) := by
  change riemannThetaFEPair.toStrongFEPair.f =O[atTop] (· ^ r)
  exact riemannThetaFEPair.isStrongFEPair_toStrongFEPair.hf_top r

/-- The concrete kernel decays faster than every real power at zero. -/
theorem riemannThetaModifiedKernel_isBigO_zero (r : ℝ) :
    riemannThetaModifiedKernel =O[𝓝[>] 0] (· ^ r) := by
  change riemannThetaFEPair.toStrongFEPair.f =O[𝓝[>] 0] (· ^ r)
  exact riemannThetaFEPair.isStrongFEPair_toStrongFEPair.hf_zero r

/-- The modified Riemann kernel inherits the exact weight-one-half modular
symmetry. -/
theorem riemannThetaModifiedKernel_one_div {t : ℝ} (ht : 0 < t) :
    riemannThetaModifiedKernel (1 / t) =
      ((t ^ (1 / 2 : ℝ) : ℝ) : ℂ) * riemannThetaModifiedKernel t := by
  have h := riemannThetaFEPair.hf_modif_FE t ht
  change riemannThetaFEPair.f_modif (1 / t) =
    (riemannThetaFEPair.ε * ((t ^ riemannThetaFEPair.k : ℝ) : ℂ)) •
      riemannThetaFEPair.symm.f_modif t at h
  rw [hurwitzEvenFEPair_zero_symm] at h
  change riemannThetaModifiedKernel (1 / t) =
    (1 * ((t ^ (1 / 2 : ℝ) : ℝ) : ℂ)) • riemannThetaModifiedKernel t at h
  simpa [smul_eq_mul] using h

end

end Zeta23.Research.JensenWedge
