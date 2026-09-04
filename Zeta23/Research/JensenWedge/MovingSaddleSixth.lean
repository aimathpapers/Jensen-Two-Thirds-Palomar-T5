import Zeta23.Research.JensenWedge.ResidualParameterGeometry
import Zeta23.Research.JensenWedge.SaddleOrderSixAlgebra
import Zeta23.Research.JensenWedge.SectorialSaddle

/-!
# Moving-saddle sixth derivative certificate

This module connects the exact `H₆` bidisc certificate to the concrete
sectorial saddle branch.  Lean proves the scaled coordinates lie in the
certified bidisc, proves the lower bound `|L_N| ≥ log |N| / 2`, and derives
the manuscript bound `20000 / (|N|^5 log |N|)`.

The single symbolic identity which starts this calculation is represented by
the explicitly named `ManuscriptG0SixthIdentification` record.  The downstream
`MovingSaddleDerivativeIdentification` module constructs that record in Lean;
SymPy and Mathematica independently corroborate the same identity.
-/

noncomputable section

namespace Zeta23.Research.JensenWedge

open Complex Metric

/-- The reduced inverse-saddle coordinate `r=1/L_N`. -/
def manuscriptSaddleR (N : ℂ) : ℂ :=
  1 / quantitativeSaddleBranch N

/-- The reduced parameter coordinate `sigma=L_N/N`. -/
def manuscriptSaddleSigma (N : ℂ) : ℂ :=
  quantitativeSaddleBranch N / N

/-- The curvature denominator used in the displayed saddle main. -/
def manuscriptSaddleQ (N : ℂ) : ℂ :=
  (1 + quantitativeSaddleBranch N) * N -
    (3 / 4) * quantitativeSaddleBranch N ^ 2

/-- The manuscript's moving-saddle logarithm `G₀(N)`. -/
def manuscriptSaddleG0 (N : ℂ) : ℂ :=
  (N + 1) * log (quantitativeSaddleBranch N) +
    quantitativeSaddleBranch N / 4 - N / quantitativeSaddleBranch N -
      log (manuscriptSaddleQ N) / 2

/-- The exact reduced value on the right side of the displayed identity
`G₀⁽⁶⁾(N)=H₆(r,sigma)/(N⁵ L_N)`. -/
def manuscriptSaddleMainSix (N : ℂ) : ℂ :=
  saddleH6 (manuscriptSaddleR N) (manuscriptSaddleSigma N) /
    (N ^ 5 * quantitativeSaddleBranch N)

/-- The one deliberately explicit symbolic seam.  The two independent CAS
reconstructions certify this equality in the release evidence; all bounds
deduced from it below are kernel checked. -/
structure ManuscriptG0SixthIdentification (N : ℂ) : Prop where
  exact_value :
    iteratedDeriv 6 manuscriptSaddleG0 N = manuscriptSaddleMainSix N

/-- The concrete saddle branch supplies both reduced coordinates in the
whole-bidisc `H₆` certificate. -/
theorem manuscriptSaddle_scaled_coordinates_in_box
    {N : ℂ} (hN : N ∈ leanSaddleSector) :
    ‖manuscriptSaddleR N‖ ≤ 7 / 50 ∧
      ‖manuscriptSaddleSigma N‖ ≤ 7 / 50 := by
  have hquant : N ∈ quantitativeSaddleDomain :=
    leanSaddleSector_quantitative hN
  have hbounds := quantitativeSaddleBranch_scaled_bounds hquant
  simpa only [manuscriptSaddleR, manuscriptSaddleSigma] using hbounds.2

/-- The fixed Newton disc gives the manuscript lower bound
`|L_N| ≥ log |N| / 2`; no asymptotic notation is used. -/
theorem quantitativeSaddleBranch_norm_lower_half_realLog
    {N : ℂ} (hN : N ∈ leanSaddleSector) :
    Real.log ‖N‖ / 2 ≤ ‖quantitativeSaddleBranch N‖ := by
  have hinput : SaddleQuantitativeInput N :=
    leanSaddleSector_quantitative hN
  have hquant : N ∈ quantitativeSaddleDomain := hinput
  let correction : ℂ := log (log N) + log (Real.pi : ℂ)
  have hcenterIdentity :
      log N = saddleComparisonCenter N + correction := by
    simp only [saddleComparisonCenter, correction]
    ring
  have hlogTriangle :
      ‖log N‖ ≤ ‖saddleComparisonCenter N‖ + ‖correction‖ := by
    rw [hcenterIdentity]
    exact norm_add_le _ _
  have hcorrection : ‖correction‖ ≤ ‖log N‖ / 100 := by
    simpa only [correction] using hinput.logCorrection_le
  have hcenterLower :
      (99 / 100 : ℝ) * ‖log N‖ ≤ ‖saddleComparisonCenter N‖ := by
    nlinarith
  have hdist := quantitativeSaddleBranch_dist_center_le hquant
  have hcenterUpper :
      ‖saddleComparisonCenter N‖ ≤
        ‖quantitativeSaddleBranch N‖ +
          dist (quantitativeSaddleBranch N) (saddleComparisonCenter N) := by
    calc
      ‖saddleComparisonCenter N‖ =
          ‖quantitativeSaddleBranch N +
            (saddleComparisonCenter N - quantitativeSaddleBranch N)‖ := by
        congr 1
        ring
      _ ≤ ‖quantitativeSaddleBranch N‖ +
          ‖saddleComparisonCenter N - quantitativeSaddleBranch N‖ :=
        norm_add_le _ _
      _ = ‖quantitativeSaddleBranch N‖ +
          dist (quantitativeSaddleBranch N) (saddleComparisonCenter N) := by
        rw [dist_eq, show saddleComparisonCenter N - quantitativeSaddleBranch N =
          -(quantitativeSaddleBranch N - saddleComparisonCenter N) by ring, norm_neg]
  have hrealLog : Real.log ‖N‖ ≤ ‖log N‖ := by
    rw [← Complex.log_re]
    exact Complex.re_le_norm (log N)
  nlinarith [hinput.logParameter_norm_lower]

/-- The exact `H₆` value on the concrete branch is strictly below `10000`. -/
theorem manuscriptSaddleH6_norm_lt_tenThousand
    {N : ℂ} (hN : N ∈ leanSaddleSector) :
    ‖saddleH6 (manuscriptSaddleR N) (manuscriptSaddleSigma N)‖ < 10000 := by
  rcases manuscriptSaddle_scaled_coordinates_in_box hN with ⟨hr, hsigma⟩
  exact saddleH6_norm_lt_tenThousand hr hsigma

/-- Fully instantiated analytic bound for the reduced sixth-order value. -/
theorem manuscriptSaddleMainSix_norm_le
    {N : ℂ} (hN : N ∈ leanSaddleSector) :
    ‖manuscriptSaddleMainSix N‖ ≤
      20000 / (‖N‖ ^ 5 * Real.log ‖N‖) := by
  have hinput := leanSaddleSector_quantitative hN
  have hNpos : 0 < ‖N‖ := norm_pos_iff.mpr hinput.parameter_ne_zero
  have hlogRadial : leanSaddleCutoff < Real.log ‖N‖ :=
    (Real.lt_log_iff_exp_lt hNpos).2 hN.1
  have hlogpos : 0 < Real.log ‖N‖ :=
    (by norm_num [leanSaddleCutoff] : (0 : ℝ) < leanSaddleCutoff).trans hlogRadial
  have hLne : quantitativeSaddleBranch N ≠ 0 := by
    have hquant : N ∈ quantitativeSaddleDomain := hinput
    exact (quantitativeSaddleBranch_scaled_bounds hquant).1
  have hLpos : 0 < ‖quantitativeSaddleBranch N‖ := norm_pos_iff.mpr hLne
  have hpowpos : 0 < ‖N‖ ^ 5 := pow_pos hNpos 5
  have hH := manuscriptSaddleH6_norm_lt_tenThousand hN
  have hLlower := quantitativeSaddleBranch_norm_lower_half_realLog hN
  unfold manuscriptSaddleMainSix
  rw [norm_div, norm_mul, norm_pow]
  calc
    ‖saddleH6 (manuscriptSaddleR N) (manuscriptSaddleSigma N)‖ /
          (‖N‖ ^ 5 * ‖quantitativeSaddleBranch N‖) ≤
        10000 / (‖N‖ ^ 5 * ‖quantitativeSaddleBranch N‖) := by
      exact div_le_div_of_nonneg_right hH.le (by positivity)
    _ ≤ 10000 / (‖N‖ ^ 5 * (Real.log ‖N‖ / 2)) := by
      apply div_le_div_of_nonneg_left (by norm_num) (by positivity)
      exact mul_le_mul_of_nonneg_left hLlower hpowpos.le
    _ = 20000 / (‖N‖ ^ 5 * Real.log ‖N‖) := by
      field_simp [ne_of_gt hpowpos, ne_of_gt hlogpos]
      norm_num

/-- Once the independently checked symbolic equality is supplied, the same
kernel bound applies to the actual sixth derivative of the displayed `G₀`. -/
theorem iteratedDeriv_six_manuscriptSaddleG0_norm_le
    {N : ℂ} (hN : N ∈ leanSaddleSector)
    (I : ManuscriptG0SixthIdentification N) :
    ‖iteratedDeriv 6 manuscriptSaddleG0 N‖ ≤
      20000 / (‖N‖ ^ 5 * Real.log ‖N‖) := by
  rw [I.exact_value]
  exact manuscriptSaddleMainSix_norm_le hN

end Zeta23.Research.JensenWedge
