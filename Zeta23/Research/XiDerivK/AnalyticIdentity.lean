/-
# Exact xi'' factorization on the right half-plane

This is the analytic algebra preceding the frozen coefficient model.  It does
not perform the freezing approximation or prove a contour error estimate.
-/
import Zeta23.Research.XiDerivK.Defs
import Zeta23.XiPrime.ExplicitFormula.Expansion

noncomputable section

namespace Zeta23.Research.XiDerivK

open Complex Filter Topology
open Zeta23.XiPrime

/-- If `E = xi'/xi`, then the exact residual factor for `xi''` is
`E^2 + E'`. -/
def xiDeriv2Factor (s : ℂ) : ℂ := Efn s ^ 2 + deriv Efn s

/-- Exact factorization `xi'' = xi (E^2 + E')` on `Re s > 1`. -/
theorem xiDeriv2_eq_xi_mul_factor {s : ℂ} (hs : 1 < s.re) :
    xiDeriv2 s = xi s * xiDeriv2Factor s := by
  have hev : xiDeriv =ᶠ[𝓝 s] fun z => xi z * Efn z := by
    filter_upwards [isOpen_one_lt_re.mem_nhds hs] with z hz
    exact xiDeriv_eq_xi_mul_Efn hz
  unfold xiDeriv2 xiDeriv2Factor
  rw [hev.deriv_eq]
  have hprod : HasDerivAt (fun z => xi z * Efn z)
      (deriv xi s * Efn s + xi s * deriv Efn s) s :=
    (xi_differentiable s).hasDerivAt.mul
      (differentiableAt_Efn hs).hasDerivAt
  have hxi : deriv xi s = xi s * Efn s := by
    simpa [xiDeriv] using xiDeriv_eq_xi_mul_Efn hs
  rw [hprod.deriv, hxi]
  ring

end Zeta23.Research.XiDerivK
