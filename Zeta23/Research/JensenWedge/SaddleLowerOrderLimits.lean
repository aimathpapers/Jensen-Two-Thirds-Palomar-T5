import Zeta23.Research.JensenWedge.SaddleLowerOrders

/-!
# Quantitative limiting values for the lower saddle tower

For each reduced saddle function, subtract its limiting constant and clear
the denominator.  The resulting polynomial has no constant term.  The four
coefficient tables below are checked by the kernel against the original
numerators and denominator powers.  A common tiny bidisc then gives one
explicit error bound for all four orders.
-/

namespace Zeta23.Research.JensenWedge

open Complex

noncomputable section

def h2LimitErrorTerms : List BivariateTerm := [
  ⟨-128, 4, 1⟩, ⟨-256, 4, 0⟩, ⟨384, 3, 2⟩, ⟨256, 3, 1⟩,
  ⟨-768, 3, 0⟩, ⟨360, 2, 3⟩, ⟨-1056, 2, 2⟩, ⟨1344, 2, 1⟩,
  ⟨-768, 2, 0⟩, ⟨432, 1, 3⟩, ⟨-1008, 1, 2⟩, ⟨768, 1, 1⟩,
  ⟨-256, 1, 0⟩, ⟨-81, 0, 4⟩, ⟨252, 0, 3⟩, ⟨-240, 0, 2⟩,
  ⟨64, 0, 1⟩
]

def h3LimitErrorTerms : List BivariateTerm := [
  ⟨4096, 6, 1⟩, ⟨4096, 6, 0⟩, ⟨-18432, 5, 2⟩, ⟨6144, 5, 1⟩,
  ⟨20480, 5, 0⟩, ⟨34560, 4, 3⟩, ⟨-57600, 4, 2⟩, ⟨-12288, 4, 1⟩,
  ⟨36864, 4, 0⟩, ⟨38016, 3, 4⟩, ⟨-96768, 3, 3⟩, ⟨90624, 3, 2⟩,
  ⟨-60416, 3, 1⟩, ⟨28672, 3, 0⟩, ⟨34992, 2, 4⟩, ⟨-102528, 2, 3⟩,
  ⟨96000, 2, 2⟩, ⟨-34816, 2, 1⟩, ⟨8192, 2, 0⟩, ⟨-5832, 1, 5⟩,
  ⟨32400, 1, 4⟩, ⟨-59328, 1, 3⟩, ⟨40704, 1, 2⟩, ⟨-7168, 1, 1⟩,
  ⟨729, 0, 6⟩, ⟨-5832, 0, 5⟩, ⟨16416, 0, 4⟩, ⟨-20736, 0, 3⟩,
  ⟨11520, 0, 2⟩, ⟨-2048, 0, 1⟩
]

def h4LimitErrorTerms : List BivariateTerm := [
  ⟨-196608, 8, 1⟩, ⟨-131072, 8, 0⟩, ⟨1179648, 7, 2⟩,
  ⟨-786432, 7, 1⟩, ⟨-917504, 7, 0⟩, ⟨-3096576, 6, 3⟩,
  ⟨6193152, 6, 2⟩, ⟨-786432, 6, 1⟩, ⟨-2621440, 6, 0⟩,
  ⟨4644864, 5, 4⟩, ⟨-15482880, 5, 3⟩, ⟨14450688, 5, 2⟩,
  ⟨-3670016, 5, 0⟩, ⟨5785344, 4, 5⟩, ⟨-18164736, 4, 4⟩,
  ⟨17915904, 4, 3⟩, ⟨-6733824, 4, 2⟩, ⟨3719168, 4, 1⟩,
  ⟨-2424832, 4, 0⟩, ⟨5971968, 3, 5⟩, ⟨-21911040, 3, 4⟩,
  ⟨27353088, 3, 3⟩, ⟨-12890112, 3, 2⟩, ⟨1966080, 3, 1⟩,
  ⟨-458752, 3, 0⟩, ⟨-653184, 2, 6⟩, ⟨5577984, 2, 5⟩,
  ⟨-15178752, 2, 4⟩, ⟨17150976, 2, 3⟩, ⟨-7237632, 2, 2⟩,
  ⟨114688, 2, 1⟩, ⟨196608, 2, 0⟩, ⟨139968, 1, 7⟩,
  ⟨-1306368, 1, 6⟩, ⟨4831488, 1, 5⟩, ⟨-8854272, 1, 4⟩,
  ⟨8183808, 1, 3⟩, ⟨-3268608, 1, 2⟩, ⟨196608, 1, 1⟩,
  ⟨65536, 1, 0⟩, ⟨-13122, 0, 8⟩, ⟨139968, 0, 7⟩,
  ⟨-653184, 0, 6⟩, ⟨1648512, 0, 5⟩, ⟨-2363904, 0, 4⟩,
  ⟨1880064, 0, 3⟩, ⟨-737280, 0, 2⟩, ⟨98304, 0, 1⟩
]

def h5LimitErrorTerms : List BivariateTerm := [
  ⟨12582912, 10, 1⟩, ⟨6291456, 10, 0⟩, ⟨-94371840, 9, 2⟩,
  ⟨78643200, 9, 1⟩, ⟨56623104, 9, 0⟩, ⟨318504960, 8, 3⟩,
  ⟨-690094080, 8, 2⟩, ⟨188743680, 8, 1⟩, ⟨220200960, 8, 0⟩,
  ⟨-637009920, 7, 4⟩, ⟨2229534720, 7, 3⟩, ⟨-2282618880, 7, 2⟩,
  ⟨235929600, 7, 1⟩, ⟨471859200, 7, 0⟩, ⟨836075520, 6, 5⟩,
  ⟨-4041031680, 6, 4⟩, ⟨7007109120, 6, 3⟩, ⟨-4742184960, 6, 2⟩,
  ⟨377487360, 6, 1⟩, ⟨566231040, 6, 0⟩, ⟨1152589824, 5, 6⟩,
  ⟨-4536705024, 5, 5⟩, ⟨5727559680, 5, 4⟩, ⟨-1678049280, 5, 3⟩,
  ⟨-1077608448, 5, 2⟩, ⟨76283904, 5, 1⟩, ⟨331350016, 5, 0⟩,
  ⟨1414609920, 4, 6⟩, ⟨-6410907648, 4, 5⟩, ⟨10565959680, 4, 4⟩,
  ⟨-7258079232, 4, 3⟩, ⟨1446051840, 4, 2⟩, ⟨215482368, 4, 1⟩,
  ⟨19922944, 4, 0⟩, ⟨-100776960, 3, 7⟩, ⟨1313210880, 3, 6⟩,
  ⟨-4858859520, 3, 5⟩, ⟨7784792064, 3, 4⟩, ⟨-5605244928, 3, 3⟩,
  ⟨1249443840, 3, 2⟩, ⟨293863424, 3, 1⟩, ⟨-78643200, 3, 0⟩,
  ⟨28343520, 2, 8⟩, ⟨-302330880, 2, 7⟩, ⟨1403412480, 2, 6⟩,
  ⟨-3421771776, 2, 5⟩, ⟨4538806272, 2, 4⟩, ⟨-3082420224, 2, 3⟩,
  ⟨787611648, 2, 2⟩, ⟨85458944, 2, 1⟩, ⟨-36700160, 2, 0⟩,
  ⟨-4723920, 1, 9⟩, ⟨56687040, 1, 8⟩, ⟨-302330880, 1, 7⟩,
  ⟨914146560, 1, 6⟩, ⟨-1674473472, 1, 5⟩, ⟨1854296064, 1, 4⟩,
  ⟨-1163132928, 1, 3⟩, ⟨337575936, 1, 2⟩, ⟨-12582912, 1, 1⟩,
  ⟨-5242880, 1, 0⟩, ⟨354294, 0, 10⟩, ⟨-4723920, 0, 9⟩,
  ⟨28343520, 0, 8⟩, ⟨-100776960, 0, 7⟩, ⟨231040512, 0, 6⟩,
  ⟨-347369472, 0, 5⟩, ⟨335093760, 0, 4⟩, ⟨-194641920, 0, 3⟩,
  ⟨58982400, 0, 2⟩, ⟨-6291456, 0, 1⟩
]

def h2LimitErrorNumerator (r sigma : ℂ) : ℂ :=
  evalBivariateTerms h2LimitErrorTerms r sigma

def h3LimitErrorNumerator (r sigma : ℂ) : ℂ :=
  evalBivariateTerms h3LimitErrorTerms r sigma

def h4LimitErrorNumerator (r sigma : ℂ) : ℂ :=
  evalBivariateTerms h4LimitErrorTerms r sigma

def h5LimitErrorNumerator (r sigma : ℂ) : ℂ :=
  evalBivariateTerms h5LimitErrorTerms r sigma

set_option maxHeartbeats 2000000 in
theorem h2LimitErrorNumerator_identity (r sigma : ℂ) :
    h2LimitErrorNumerator r sigma =
      h2Numerator r sigma - h2ReducedDenominator r sigma := by
  simp [h2LimitErrorNumerator, h2LimitErrorTerms, h2Numerator, h2Terms,
    h2ReducedDenominator, evalBivariateTerms, BivariateTerm.eval]
  ring

set_option maxHeartbeats 2000000 in
theorem h3LimitErrorNumerator_identity (r sigma : ℂ) :
    h3LimitErrorNumerator r sigma =
      h3Numerator r sigma + h3ReducedDenominator r sigma := by
  simp [h3LimitErrorNumerator, h3LimitErrorTerms, h3Numerator, h3Terms,
    h3ReducedDenominator, evalBivariateTerms, BivariateTerm.eval]
  ring

set_option maxHeartbeats 2000000 in
theorem h4LimitErrorNumerator_identity (r sigma : ℂ) :
    h4LimitErrorNumerator r sigma =
      h4Numerator r sigma - 2 * h4ReducedDenominator r sigma := by
  simp [h4LimitErrorNumerator, h4LimitErrorTerms, h4Numerator, h4Terms,
    h4ReducedDenominator, evalBivariateTerms, BivariateTerm.eval]
  ring

set_option maxHeartbeats 2000000 in
theorem h5LimitErrorNumerator_identity (r sigma : ℂ) :
    h5LimitErrorNumerator r sigma =
      h5Numerator r sigma + 6 * h5ReducedDenominator r sigma := by
  simp [h5LimitErrorNumerator, h5LimitErrorTerms, h5Numerator, h5Terms,
    h5ReducedDenominator, evalBivariateTerms, BivariateTerm.eval]
  ring

/-- Common radius used by the explicit lower-order limiting certificate. -/
def saddleLowerLimitRadius : ℝ := 1 / 10000000

/-- Common error budget for all four reduced limiting values. -/
def saddleLowerLimitError : ℝ := 1 / 500000

theorem saddleReducedBase_norm_lower_of_radius
    {r sigma : ℂ} {rho : ℝ} (_hrho : 0 ≤ rho)
    (hr : ‖r‖ ≤ rho) (hsigma : ‖sigma‖ ≤ rho) :
    4 - 7 * rho ≤ ‖4 + 4 * r - 3 * sigma‖ := by
  have hperturb : ‖4 * r - 3 * sigma‖ ≤ 7 * rho := by
    calc
      ‖4 * r - 3 * sigma‖ ≤ ‖4 * r‖ + ‖3 * sigma‖ := norm_sub_le _ _
      _ = 4 * ‖r‖ + 3 * ‖sigma‖ := by norm_num [norm_mul]
      _ ≤ 4 * rho + 3 * rho := by gcongr
      _ = 7 * rho := by ring
  have hfour : (4 : ℝ) ≤
      ‖4 + 4 * r - 3 * sigma‖ + ‖4 * r - 3 * sigma‖ := by
    calc
      (4 : ℝ) = ‖(4 : ℂ)‖ := by norm_num
      _ = ‖(4 + 4 * r - 3 * sigma) - (4 * r - 3 * sigma)‖ := by
        congr 1
        ring
      _ ≤ ‖4 + 4 * r - 3 * sigma‖ + ‖4 * r - 3 * sigma‖ :=
        norm_sub_le _ _
  linarith

private theorem lowerLimitErrorNumerator_norm_le
    (terms : List BivariateTerm) {r sigma : ℂ}
    (hr : ‖r‖ ≤ saddleLowerLimitRadius)
    (hsigma : ‖sigma‖ ≤ saddleLowerLimitRadius) :
    ‖evalBivariateTerms terms r sigma‖ ≤
      bivariateTermsMajorant terms saddleLowerLimitRadius := by
  exact norm_evalBivariateTerms_le_majorant terms
    (by norm_num [saddleLowerLimitRadius]) hr hsigma

private theorem saddleLowerLimit_denominator_norm_lower
    {r sigma : ℂ}
    (hr : ‖r‖ ≤ saddleLowerLimitRadius)
    (hsigma : ‖sigma‖ ≤ saddleLowerLimitRadius) (q : ℕ) :
    (4 - 7 * saddleLowerLimitRadius) ^ q ≤
      ‖(4 + 4 * r - 3 * sigma) ^ q‖ := by
  rw [norm_pow]
  exact pow_le_pow_left₀ (by norm_num [saddleLowerLimitRadius])
    (saddleReducedBase_norm_lower_of_radius
      (by norm_num [saddleLowerLimitRadius]) hr hsigma) q

private theorem saddleLowerLimit_denominator_ne_zero
    {r sigma : ℂ}
    (hr : ‖r‖ ≤ saddleLowerLimitRadius)
    (hsigma : ‖sigma‖ ≤ saddleLowerLimitRadius) (q : ℕ) :
    (4 + 4 * r - 3 * sigma) ^ q ≠ 0 := by
  have h := saddleLowerLimit_denominator_norm_lower hr hsigma q
  intro hzero
  rw [hzero, norm_zero] at h
  have hpos : 0 < (4 - 7 * saddleLowerLimitRadius) ^ q := by
    exact pow_pos (by norm_num [saddleLowerLimitRadius]) q
  linarith

private theorem h2LimitMajorant_lt :
    bivariateTermsMajorant h2LimitErrorTerms saddleLowerLimitRadius /
        (4 - 7 * saddleLowerLimitRadius) ^ 4 < saddleLowerLimitError := by
  norm_num [bivariateTermsMajorant, h2LimitErrorTerms,
    BivariateTerm.majorant, saddleLowerLimitRadius, saddleLowerLimitError]

private theorem h3LimitMajorant_lt :
    bivariateTermsMajorant h3LimitErrorTerms saddleLowerLimitRadius /
        (4 - 7 * saddleLowerLimitRadius) ^ 6 < saddleLowerLimitError := by
  norm_num [bivariateTermsMajorant, h3LimitErrorTerms,
    BivariateTerm.majorant, saddleLowerLimitRadius, saddleLowerLimitError]

private theorem h4LimitMajorant_lt :
    bivariateTermsMajorant h4LimitErrorTerms saddleLowerLimitRadius /
        (4 - 7 * saddleLowerLimitRadius) ^ 8 < saddleLowerLimitError := by
  norm_num [bivariateTermsMajorant, h4LimitErrorTerms,
    BivariateTerm.majorant, saddleLowerLimitRadius, saddleLowerLimitError]

private theorem h5LimitMajorant_lt :
    bivariateTermsMajorant h5LimitErrorTerms saddleLowerLimitRadius /
        (4 - 7 * saddleLowerLimitRadius) ^ 10 < saddleLowerLimitError := by
  norm_num [bivariateTermsMajorant, h5LimitErrorTerms,
    BivariateTerm.majorant, saddleLowerLimitRadius, saddleLowerLimitError]

private theorem norm_div_lt_lowerLimitError
    {z d : ℂ} {terms : List BivariateTerm} {q : ℕ}
    (hz : ‖z‖ ≤ bivariateTermsMajorant terms saddleLowerLimitRadius)
    (hd : (4 - 7 * saddleLowerLimitRadius) ^ q ≤ ‖d‖)
    (hstrict : bivariateTermsMajorant terms saddleLowerLimitRadius /
        (4 - 7 * saddleLowerLimitRadius) ^ q < saddleLowerLimitError) :
    ‖z / d‖ < saddleLowerLimitError := by
  rw [norm_div]
  have hbasepos : 0 < (4 - 7 * saddleLowerLimitRadius) ^ q :=
    pow_pos (by norm_num [saddleLowerLimitRadius]) q
  have hmajorant : 0 ≤ bivariateTermsMajorant terms saddleLowerLimitRadius :=
    (norm_nonneg z).trans hz
  exact (div_le_div₀ hmajorant hz hbasepos hd).trans_lt hstrict

theorem saddleH2_sub_one_norm_lt
    {r sigma : ℂ} (hr : ‖r‖ ≤ saddleLowerLimitRadius)
    (hsigma : ‖sigma‖ ≤ saddleLowerLimitRadius) :
    ‖saddleH2 r sigma - 1‖ < saddleLowerLimitError := by
  have hden := saddleLowerLimit_denominator_ne_zero hr hsigma 4
  have hidentity : saddleH2 r sigma - 1 =
      h2LimitErrorNumerator r sigma / h2ReducedDenominator r sigma := by
    rw [saddleH2, h2LimitErrorNumerator_identity]
    field_simp [h2ReducedDenominator, hden]
  rw [hidentity]
  exact norm_div_lt_lowerLimitError
    (lowerLimitErrorNumerator_norm_le h2LimitErrorTerms hr hsigma)
    (saddleLowerLimit_denominator_norm_lower hr hsigma 4) h2LimitMajorant_lt

theorem saddleH3_add_one_norm_lt
    {r sigma : ℂ} (hr : ‖r‖ ≤ saddleLowerLimitRadius)
    (hsigma : ‖sigma‖ ≤ saddleLowerLimitRadius) :
    ‖saddleH3 r sigma + 1‖ < saddleLowerLimitError := by
  have hden := saddleLowerLimit_denominator_ne_zero hr hsigma 6
  have hidentity : saddleH3 r sigma + 1 =
      h3LimitErrorNumerator r sigma / h3ReducedDenominator r sigma := by
    rw [saddleH3, h3LimitErrorNumerator_identity]
    field_simp [h3ReducedDenominator, hden]
  rw [hidentity]
  exact norm_div_lt_lowerLimitError
    (lowerLimitErrorNumerator_norm_le h3LimitErrorTerms hr hsigma)
    (saddleLowerLimit_denominator_norm_lower hr hsigma 6) h3LimitMajorant_lt

theorem saddleH4_sub_two_norm_lt
    {r sigma : ℂ} (hr : ‖r‖ ≤ saddleLowerLimitRadius)
    (hsigma : ‖sigma‖ ≤ saddleLowerLimitRadius) :
    ‖saddleH4 r sigma - 2‖ < saddleLowerLimitError := by
  have hden := saddleLowerLimit_denominator_ne_zero hr hsigma 8
  have hidentity : saddleH4 r sigma - 2 =
      h4LimitErrorNumerator r sigma / h4ReducedDenominator r sigma := by
    rw [saddleH4, h4LimitErrorNumerator_identity]
    field_simp [h4ReducedDenominator, hden]
  rw [hidentity]
  exact norm_div_lt_lowerLimitError
    (lowerLimitErrorNumerator_norm_le h4LimitErrorTerms hr hsigma)
    (saddleLowerLimit_denominator_norm_lower hr hsigma 8) h4LimitMajorant_lt

theorem saddleH5_add_six_norm_lt
    {r sigma : ℂ} (hr : ‖r‖ ≤ saddleLowerLimitRadius)
    (hsigma : ‖sigma‖ ≤ saddleLowerLimitRadius) :
    ‖saddleH5 r sigma + 6‖ < saddleLowerLimitError := by
  have hden := saddleLowerLimit_denominator_ne_zero hr hsigma 10
  have hidentity : saddleH5 r sigma + 6 =
      h5LimitErrorNumerator r sigma / h5ReducedDenominator r sigma := by
    rw [saddleH5, h5LimitErrorNumerator_identity]
    field_simp [h5ReducedDenominator, hden]
  rw [hidentity]
  exact norm_div_lt_lowerLimitError
    (lowerLimitErrorNumerator_norm_le h5LimitErrorTerms hr hsigma)
    (saddleLowerLimit_denominator_norm_lower hr hsigma 10) h5LimitMajorant_lt

/-! ## Final narrow box used by the effective xi interval certificate -/

/-- The lower-order demonstration box above is deliberately readable.  The
finite branch needs a much smaller numerical error, so Step 4 uses this
second exact rational radius. -/
def saddleFinalLimitRadius : ℝ := 1 / 100000000000000

/-- Common reduced-value error on the final narrow box. -/
def saddleFinalLimitError : ℝ := 1 / 1000000000000

private theorem finalLimitErrorNumerator_norm_le
    (terms : List BivariateTerm) {r sigma : ℂ}
    (hr : ‖r‖ ≤ saddleFinalLimitRadius)
    (hsigma : ‖sigma‖ ≤ saddleFinalLimitRadius) :
    ‖evalBivariateTerms terms r sigma‖ ≤
      bivariateTermsMajorant terms saddleFinalLimitRadius := by
  exact norm_evalBivariateTerms_le_majorant terms
    (by norm_num [saddleFinalLimitRadius]) hr hsigma

private theorem saddleFinalLimit_denominator_norm_lower
    {r sigma : ℂ}
    (hr : ‖r‖ ≤ saddleFinalLimitRadius)
    (hsigma : ‖sigma‖ ≤ saddleFinalLimitRadius) (q : ℕ) :
    (4 - 7 * saddleFinalLimitRadius) ^ q ≤
      ‖(4 + 4 * r - 3 * sigma) ^ q‖ := by
  rw [norm_pow]
  exact pow_le_pow_left₀ (by norm_num [saddleFinalLimitRadius])
    (saddleReducedBase_norm_lower_of_radius
      (by norm_num [saddleFinalLimitRadius]) hr hsigma) q

private theorem finalH2Majorant_lt :
    bivariateTermsMajorant h2LimitErrorTerms saddleFinalLimitRadius /
        (4 - 7 * saddleFinalLimitRadius) ^ 4 < saddleFinalLimitError := by
  norm_num [bivariateTermsMajorant, h2LimitErrorTerms,
    BivariateTerm.majorant, saddleFinalLimitRadius, saddleFinalLimitError]

private theorem finalH3Majorant_lt :
    bivariateTermsMajorant h3LimitErrorTerms saddleFinalLimitRadius /
        (4 - 7 * saddleFinalLimitRadius) ^ 6 < saddleFinalLimitError := by
  norm_num [bivariateTermsMajorant, h3LimitErrorTerms,
    BivariateTerm.majorant, saddleFinalLimitRadius, saddleFinalLimitError]

private theorem finalH4Majorant_lt :
    bivariateTermsMajorant h4LimitErrorTerms saddleFinalLimitRadius /
        (4 - 7 * saddleFinalLimitRadius) ^ 8 < saddleFinalLimitError := by
  norm_num [bivariateTermsMajorant, h4LimitErrorTerms,
    BivariateTerm.majorant, saddleFinalLimitRadius, saddleFinalLimitError]

private theorem finalH5Majorant_lt :
    bivariateTermsMajorant h5LimitErrorTerms saddleFinalLimitRadius /
        (4 - 7 * saddleFinalLimitRadius) ^ 10 < saddleFinalLimitError := by
  norm_num [bivariateTermsMajorant, h5LimitErrorTerms,
    BivariateTerm.majorant, saddleFinalLimitRadius, saddleFinalLimitError]

private theorem norm_div_lt_finalLimitError
    {z d : ℂ} {terms : List BivariateTerm} {q : ℕ}
    (hz : ‖z‖ ≤ bivariateTermsMajorant terms saddleFinalLimitRadius)
    (hd : (4 - 7 * saddleFinalLimitRadius) ^ q ≤ ‖d‖)
    (hstrict : bivariateTermsMajorant terms saddleFinalLimitRadius /
        (4 - 7 * saddleFinalLimitRadius) ^ q < saddleFinalLimitError) :
    ‖z / d‖ < saddleFinalLimitError := by
  rw [norm_div]
  have hbasepos : 0 < (4 - 7 * saddleFinalLimitRadius) ^ q :=
    pow_pos (by norm_num [saddleFinalLimitRadius]) q
  have hmajorant : 0 ≤ bivariateTermsMajorant terms saddleFinalLimitRadius :=
    (norm_nonneg z).trans hz
  exact (div_le_div₀ hmajorant hz hbasepos hd).trans_lt hstrict

theorem saddleH2_sub_one_norm_lt_final
    {r sigma : ℂ} (hr : ‖r‖ ≤ saddleFinalLimitRadius)
    (hsigma : ‖sigma‖ ≤ saddleFinalLimitRadius) :
    ‖saddleH2 r sigma - 1‖ < saddleFinalLimitError := by
  rw [saddleH2, show h2Numerator r sigma / h2ReducedDenominator r sigma - 1 =
      h2LimitErrorNumerator r sigma / h2ReducedDenominator r sigma by
    rw [h2LimitErrorNumerator_identity]
    have hne := saddleLowerLimit_denominator_ne_zero
      (hr.trans (by norm_num [saddleFinalLimitRadius, saddleLowerLimitRadius]))
      (hsigma.trans (by norm_num [saddleFinalLimitRadius, saddleLowerLimitRadius])) 4
    field_simp [h2ReducedDenominator, hne]]
  exact norm_div_lt_finalLimitError
    (finalLimitErrorNumerator_norm_le h2LimitErrorTerms hr hsigma)
    (saddleFinalLimit_denominator_norm_lower hr hsigma 4) finalH2Majorant_lt

theorem saddleH3_add_one_norm_lt_final
    {r sigma : ℂ} (hr : ‖r‖ ≤ saddleFinalLimitRadius)
    (hsigma : ‖sigma‖ ≤ saddleFinalLimitRadius) :
    ‖saddleH3 r sigma + 1‖ < saddleFinalLimitError := by
  rw [saddleH3, show h3Numerator r sigma / h3ReducedDenominator r sigma + 1 =
      h3LimitErrorNumerator r sigma / h3ReducedDenominator r sigma by
    rw [h3LimitErrorNumerator_identity]
    have hne := saddleLowerLimit_denominator_ne_zero
      (hr.trans (by norm_num [saddleFinalLimitRadius, saddleLowerLimitRadius]))
      (hsigma.trans (by norm_num [saddleFinalLimitRadius, saddleLowerLimitRadius])) 6
    field_simp [h3ReducedDenominator, hne]]
  exact norm_div_lt_finalLimitError
    (finalLimitErrorNumerator_norm_le h3LimitErrorTerms hr hsigma)
    (saddleFinalLimit_denominator_norm_lower hr hsigma 6) finalH3Majorant_lt

theorem saddleH4_sub_two_norm_lt_final
    {r sigma : ℂ} (hr : ‖r‖ ≤ saddleFinalLimitRadius)
    (hsigma : ‖sigma‖ ≤ saddleFinalLimitRadius) :
    ‖saddleH4 r sigma - 2‖ < saddleFinalLimitError := by
  rw [saddleH4, show h4Numerator r sigma / h4ReducedDenominator r sigma - 2 =
      h4LimitErrorNumerator r sigma / h4ReducedDenominator r sigma by
    rw [h4LimitErrorNumerator_identity]
    have hne := saddleLowerLimit_denominator_ne_zero
      (hr.trans (by norm_num [saddleFinalLimitRadius, saddleLowerLimitRadius]))
      (hsigma.trans (by norm_num [saddleFinalLimitRadius, saddleLowerLimitRadius])) 8
    field_simp [h4ReducedDenominator, hne]]
  exact norm_div_lt_finalLimitError
    (finalLimitErrorNumerator_norm_le h4LimitErrorTerms hr hsigma)
    (saddleFinalLimit_denominator_norm_lower hr hsigma 8) finalH4Majorant_lt

theorem saddleH5_add_six_norm_lt_final
    {r sigma : ℂ} (hr : ‖r‖ ≤ saddleFinalLimitRadius)
    (hsigma : ‖sigma‖ ≤ saddleFinalLimitRadius) :
    ‖saddleH5 r sigma + 6‖ < saddleFinalLimitError := by
  rw [saddleH5, show h5Numerator r sigma / h5ReducedDenominator r sigma + 6 =
      h5LimitErrorNumerator r sigma / h5ReducedDenominator r sigma by
    rw [h5LimitErrorNumerator_identity]
    have hne := saddleLowerLimit_denominator_ne_zero
      (hr.trans (by norm_num [saddleFinalLimitRadius, saddleLowerLimitRadius]))
      (hsigma.trans (by norm_num [saddleFinalLimitRadius, saddleLowerLimitRadius])) 10
    field_simp [h5ReducedDenominator, hne]]
  exact norm_div_lt_finalLimitError
    (finalLimitErrorNumerator_norm_le h5LimitErrorTerms hr hsigma)
    (saddleFinalLimit_denominator_norm_lower hr hsigma 10) finalH5Majorant_lt

end

end Zeta23.Research.JensenWedge
