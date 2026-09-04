import Zeta23.Research.JensenWedge.ElementaryComponentValue

/-!
# Remote alpha column of the elementary differential

Only component zero retains a nonzero alpha derivative in the limiting map.
This module formalizes that case split and its exact error bound.
-/

namespace Zeta23.Research.JensenWedge

noncomputable section

def leadingElementaryCoordinatePartialAlpha
    (j : Fin 4) (alpha : ℝ) : ℝ :=
  if j = 0 then -alpha⁻¹ ^ 2 else 0

def elementaryRemoteDerivativeErrorBound
    (j : Fin 4) (alpha₀ e x : ℝ) : ℝ :=
  |elementaryComponentCoefficient j| *
    if j = 0 then 2 * x * e * alpha₀⁻¹ ^ 3
    else e ^ (elementaryComponentOrder j - 1) *
      (elementaryComponentOrder j : ℝ) *
      alpha₀⁻¹ ^ (elementaryComponentOrder j + 1)

theorem elementaryCoordinatePartialAlpha_error
    {j : Fin 4} {alpha alpha₀ e x : ℝ}
    (halpha₀ : 0 < alpha₀) (halpha : alpha₀ ≤ alpha)
    (he : 0 ≤ e) (hx : 0 ≤ x) :
    |elementaryCoordinatePartialAlpha j alpha e x -
        leadingElementaryCoordinatePartialAlpha j alpha| ≤
      elementaryRemoteDerivativeErrorBound j alpha₀ e x := by
  fin_cases j
  · have h := elementaryRemoteTerm_alpha_q1_error halpha₀ halpha hx he
    simpa [elementaryCoordinatePartialAlpha,
      leadingElementaryCoordinatePartialAlpha,
      elementaryRemoteDerivativeErrorBound, elementaryComponentOrder,
      elementaryComponentCoefficient, elementaryWeight, componentScale,
      logRatioLeading] using h
  · have h := abs_elementaryPhiD1_remote_le
      (q := 2) halpha₀ halpha hx he
    simpa [elementaryCoordinatePartialAlpha,
      leadingElementaryCoordinatePartialAlpha,
      elementaryRemoteDerivativeErrorBound, elementaryComponentOrder,
      elementaryComponentCoefficient, elementaryWeight, componentScale,
      logRatioLeading, abs_mul] using
      (mul_le_mul_of_nonneg_left h (by norm_num : 0 ≤ (1 / 2 : ℝ)))
  · have h := abs_elementaryPhiD1_remote_le
      (q := 3) halpha₀ halpha hx he
    simpa [elementaryCoordinatePartialAlpha,
      leadingElementaryCoordinatePartialAlpha,
      elementaryRemoteDerivativeErrorBound, elementaryComponentOrder,
      elementaryComponentCoefficient, elementaryWeight, componentScale,
      logRatioLeading] using h
  · have h := abs_elementaryPhiD1_remote_le
      (q := 4) halpha₀ halpha hx he
    simpa [elementaryCoordinatePartialAlpha,
      leadingElementaryCoordinatePartialAlpha,
      elementaryRemoteDerivativeErrorBound, elementaryComponentOrder,
      elementaryComponentCoefficient, elementaryWeight, componentScale,
      logRatioLeading] using h

end

end Zeta23.Research.JensenWedge
