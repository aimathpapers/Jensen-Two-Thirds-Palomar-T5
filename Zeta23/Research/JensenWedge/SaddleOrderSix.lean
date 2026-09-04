import Zeta23.Research.JensenWedge.SaddleBounds

/-!
# Exact order-six saddle certificate

This module kernel-checks the frozen reduced numerator of the sixth saddle
derivative and its coefficientwise bound on the full complex bidisc.  The
large integer coefficient list is mathematical data, not generated proof
code: the generic majorant theorem below proves the bound for every list of
integer bivariate monomials, and `norm_num` checks the exact rational sum for
this concrete list.

The identification of this reduced rational function with the sixth iterate
of the saddle differential operator is kept as a separate theorem surface.
No analytic saddle branch or contour statement is asserted here.
-/

namespace Zeta23.Research.JensenWedge

open Complex

noncomputable section

/-- One integer monomial `coeff * r^rPow * sigma^sigmaPow`. -/
structure BivariateTerm where
  coeff : ℤ
  rPow : ℕ
  sigmaPow : ℕ
deriving DecidableEq, Repr

def BivariateTerm.eval (term : BivariateTerm) (r sigma : ℂ) : ℂ :=
  (term.coeff : ℂ) * r ^ term.rPow * sigma ^ term.sigmaPow

def BivariateTerm.majorant (term : BivariateTerm) (radius : ℝ) : ℝ :=
  |(term.coeff : ℝ)| * radius ^ term.rPow * radius ^ term.sigmaPow

def evalBivariateTerms (terms : List BivariateTerm) (r sigma : ℂ) : ℂ :=
  (terms.map fun term => term.eval r sigma).sum

def bivariateTermsMajorant (terms : List BivariateTerm) (radius : ℝ) : ℝ :=
  (terms.map fun term => term.majorant radius).sum

private theorem BivariateTerm.norm_eval_le_majorant
    (term : BivariateTerm) {r sigma : ℂ} {radius : ℝ}
    (hradius : 0 ≤ radius) (hr : ‖r‖ ≤ radius) (hsigma : ‖sigma‖ ≤ radius) :
    ‖term.eval r sigma‖ ≤ term.majorant radius := by
  unfold BivariateTerm.eval BivariateTerm.majorant
  rw [norm_mul, norm_mul, norm_pow, norm_pow, Complex.norm_intCast]
  have hrpow : ‖r‖ ^ term.rPow ≤ radius ^ term.rPow :=
    pow_le_pow_left₀ (norm_nonneg r) hr _
  have hsigmapow : ‖sigma‖ ^ term.sigmaPow ≤ radius ^ term.sigmaPow :=
    pow_le_pow_left₀ (norm_nonneg sigma) hsigma _
  exact mul_le_mul (mul_le_mul_of_nonneg_left hrpow (abs_nonneg _)) hsigmapow
    (pow_nonneg (norm_nonneg sigma) _)
    (mul_nonneg (abs_nonneg _) (pow_nonneg hradius _))

/-- Coefficientwise majorization for an arbitrary finite integer bivariate
polynomial on a closed complex bidisc. -/
theorem norm_evalBivariateTerms_le_majorant
    (terms : List BivariateTerm) {r sigma : ℂ} {radius : ℝ}
    (hradius : 0 ≤ radius) (hr : ‖r‖ ≤ radius) (hsigma : ‖sigma‖ ≤ radius) :
    ‖evalBivariateTerms terms r sigma‖ ≤ bivariateTermsMajorant terms radius := by
  induction terms with
  | nil => simp [evalBivariateTerms, bivariateTermsMajorant]
  | cons term terms ih =>
      simp only [evalBivariateTerms, bivariateTermsMajorant, List.map_cons, List.sum_cons]
      exact (norm_add_le _ _).trans
        (add_le_add (term.norm_eval_le_majorant hradius hr hsigma) ih)

/-! ## The exact reduced numerator -/

/-- Coefficients of the reduced numerator `P_13(r,sigma)`.  The ordering is
descending lexicographic order and is fixed to make mutations and independent
CAS comparisons straightforward. -/
def h6Terms : List BivariateTerm := [
  ⟨-1006632960, 12, 1⟩,
  ⟨9059696640, 11, 2⟩,
  ⟨-12079595520, 11, 1⟩,
  ⟨402653184, 11, 0⟩,
  ⟨-37371248640, 10, 3⟩,
  ⟨99656663040, 10, 2⟩,
  ⟨-70061654016, 10, 1⟩,
  ⟨4831838208, 10, 0⟩,
  ⟨93428121600, 9, 4⟩,
  ⟨-373712486400, 9, 3⟩,
  ⟨513231814656, 9, 2⟩,
  ⟨-261321916416, 9, 1⟩,
  ⟨26575110144, 9, 0⟩,
  ⟨-157659955200, 8, 5⟩,
  ⟨840853094400, 8, 4⟩,
  ⟨-1719077437440, 8, 3⟩,
  ⟨1644334940160, 8, 2⟩,
  ⟨-697596641280, 8, 1⟩,
  ⟨88583700480, 8, 0⟩,
  ⟨189191946240, 7, 6⟩,
  ⟨-1261279641600, 7, 5⟩,
  ⟨3426476359680, 7, 4⟩,
  ⟨-4820891074560, 7, 3⟩,
  ⟨3662382366720, 7, 2⟩,
  ⟨-1395193282560, 7, 1⟩,
  ⟨199313326080, 7, 0⟩,
  ⟨284146237440, 6, 7⟩,
  ⟨-1298544721920, 6, 6⟩,
  ⟨1695624855552, 6, 5⟩,
  ⟨846586183680, 6, 4⟩,
  ⟨-4279805411328, 6, 3⟩,
  ⟨4330144923648, 6, 2⟩,
  ⟨-1886493081600, 6, 1⟩,
  ⟨308415561728, 6, 0⟩,
  ⟨369784258560, 5, 7⟩,
  ⟨-1850927874048, 5, 6⟩,
  ⟨3111920861184, 5, 5⟩,
  ⟨-971390582784, 5, 4⟩,
  ⟨-3094773497856, 5, 3⟩,
  ⟨4009894084608, 5, 2⟩,
  ⟨-1898442653696, 5, 1⟩,
  ⟨324253253632, 5, 0⟩,
  ⟨181255200768, 4, 7⟩,
  ⟨-877616529408, 4, 6⟩,
  ⟨1270585294848, 4, 5⟩,
  ⟨349591044096, 4, 4⟩,
  ⟨-2836659437568, 4, 3⟩,
  ⟨3066811121664, 4, 2⟩,
  ⟨-1381599543296, 4, 1⟩,
  ⟨227985588224, 4, 0⟩,
  ⟨33323581440, 3, 7⟩,
  ⟨-109525893120, 3, 6⟩,
  ⟨-119598612480, 3, 5⟩,
  ⟨1043296616448, 3, 4⟩,
  ⟨-1925496963072, 3, 3⟩,
  ⟨1651828064256, 3, 2⟩,
  ⟨-678990708736, 3, 1⟩,
  ⟨105277030400, 3, 0⟩,
  ⟨-2906855424, 2, 7⟩,
  ⟨46362378240, 2, 6⟩,
  ⟨-233519874048, 2, 5⟩,
  ⟨568793235456, 2, 4⟩,
  ⟨-758471196672, 2, 3⟩,
  ⟨561361453056, 2, 2⟩,
  ⟨-212491829248, 2, 1⟩,
  ⟨30870077440, 2, 0⟩,
  ⟨-2051371008, 1, 7⟩,
  ⟨18136866816, 1, 6⟩,
  ⟨-67459350528, 1, 5⟩,
  ⟨136267038720, 1, 4⟩,
  ⟨-160384942080, 1, 3⟩,
  ⟨108772982784, 1, 2⟩,
  ⟨-38554042368, 1, 1⟩,
  ⟨5268045824, 1, 0⟩,
  ⟨-232906752, 0, 7⟩,
  ⟨1934917632, 0, 6⟩,
  ⟨-6784155648, 0, 5⟩,
  ⟨12952535040, 0, 4⟩,
  ⟨-14438891520, 0, 3⟩,
  ⟨9286189056, 0, 2⟩,
  ⟨-3120562176, 0, 1⟩,
  ⟨402653184, 0, 0⟩
]

def h6Numerator (r sigma : ℂ) : ℂ := evalBivariateTerms h6Terms r sigma

def h6ReducedDenominator (r sigma : ℂ) : ℂ := (4 + 4 * r - 3 * sigma) ^ 12

def saddleH6 (r sigma : ℂ) : ℂ :=
  h6Numerator r sigma / h6ReducedDenominator r sigma

def h6NumeratorMajorant : ℝ :=
  bivariateTermsMajorant h6Terms (7 / 50)

def h6DenominatorLower : ℝ := ((151 : ℝ) / 50) ^ 12

def h6Majorant : ℝ := h6NumeratorMajorant / h6DenominatorLower

theorem h6_term_count : h6Terms.length = 82 := by norm_num [h6Terms]

theorem h6_total_degree_le_thirteen :
    ∀ term ∈ h6Terms, term.rPow + term.sigmaPow ≤ 13 := by
  norm_num [h6Terms]

theorem h6_has_total_degree_thirteen :
    ∃ term ∈ h6Terms, term.rPow + term.sigmaPow = 13 := by
  norm_num [h6Terms]

theorem h6NumeratorMajorant_exact :
    h6NumeratorMajorant =
      (1567905226016829000008919324 : ℝ) / 298023223876953125 := by
  norm_num [h6NumeratorMajorant, bivariateTermsMajorant, h6Terms,
    BivariateTerm.majorant]

theorem h6DenominatorLower_exact :
    h6DenominatorLower =
      (140515219945627518837736801 : ℝ) / 244140625000000000000 := by
  norm_num [h6DenominatorLower]

theorem h6Majorant_exact :
    h6Majorant =
      (6422139805764931584036533551104 : ℝ) /
        702576099728137594188684005 := by
  rw [h6Majorant, h6NumeratorMajorant_exact, h6DenominatorLower_exact]
  norm_num

theorem h6Majorant_lt_tenThousand : h6Majorant < 10000 := by
  rw [h6Majorant_exact]
  norm_num

theorem h6Numerator_norm_le
    {r sigma : ℂ} (hr : ‖r‖ ≤ 7 / 50) (hsigma : ‖sigma‖ ≤ 7 / 50) :
    ‖h6Numerator r sigma‖ ≤ h6NumeratorMajorant := by
  exact norm_evalBivariateTerms_le_majorant h6Terms (by norm_num) hr hsigma

theorem h6ReducedDenominator_norm_lower
    {r sigma : ℂ} (hr : ‖r‖ ≤ 7 / 50) (hsigma : ‖sigma‖ ≤ 7 / 50) :
    h6DenominatorLower ≤ ‖h6ReducedDenominator r sigma‖ := by
  unfold h6ReducedDenominator h6DenominatorLower
  rw [norm_pow]
  exact pow_le_pow_left₀ (by norm_num) (saddle_reduced_denominator_norm_lower hr hsigma) _

theorem h6ReducedDenominator_ne_zero
    {r sigma : ℂ} (hr : ‖r‖ ≤ 7 / 50) (hsigma : ‖sigma‖ ≤ 7 / 50) :
    h6ReducedDenominator r sigma ≠ 0 := by
  intro hzero
  have hlower := h6ReducedDenominator_norm_lower hr hsigma
  rw [hzero, norm_zero] at hlower
  have hpositive : 0 < h6DenominatorLower := by
    norm_num [h6DenominatorLower]
  linarith

/-- The exact whole-bidisc sixth-order certificate. -/
theorem saddleH6_norm_lt_tenThousand
    {r sigma : ℂ} (hr : ‖r‖ ≤ 7 / 50) (hsigma : ‖sigma‖ ≤ 7 / 50) :
    ‖saddleH6 r sigma‖ < 10000 := by
  have hnum := h6Numerator_norm_le hr hsigma
  have hden := h6ReducedDenominator_norm_lower hr hsigma
  have hdenpos : 0 < h6DenominatorLower := by
    norm_num [h6DenominatorLower]
  have hmajorantnonneg : 0 ≤ h6NumeratorMajorant :=
    (norm_nonneg (h6Numerator r sigma)).trans hnum
  calc
    ‖saddleH6 r sigma‖ = ‖h6Numerator r sigma‖ / ‖h6ReducedDenominator r sigma‖ := by
      simp [saddleH6]
    _ ≤ h6Majorant := by
      unfold h6Majorant
      exact div_le_div₀ hmajorantnonneg hnum hdenpos hden
    _ < 10000 := h6Majorant_lt_tenThousand

end

end Zeta23.Research.JensenWedge
