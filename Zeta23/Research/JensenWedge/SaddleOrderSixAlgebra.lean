import Zeta23.Research.JensenWedge.SaddleOrderSix

/-!
# Kernel computation of the reduced saddle recurrence

Let `B = 4 + 4*r - 3*sigma`.  If

`H_k(r,sigma) = P_k(r,sigma) / B^(2*k)`

is the normalized `k`-th saddle derivative, differentiating along the
implicit saddle equation gives

`P_(k+1) = -4 [r^2 (P_r B - 8kP) + krPB]
             + (3sigma-4) [(k-1)PB + sigma(P_sigma B + 6kP)]`.

This module evaluates that exact recurrence in a canonical bounded dense
integer polynomial representation. Starting from the order-two numerator, four
kernel reductions produce exactly the frozen 82-term order-six numerator.
No CAS output is read by Lean and no native-decision proof shortcut is used.
-/

namespace Zeta23.Research.JensenWedge

/-- Coefficients with room for every monomial occurring through order six.
The two bounds are deliberately one larger than the observed maxima. -/
abbrev DenseBivariatePolynomial := Fin 14 → Fin 8 → ℤ

def denseZero : DenseBivariatePolynomial := fun _ _ => 0

def denseMonomial (coefficient : ℤ) (rPower sigmaPower : ℕ) :
    DenseBivariatePolynomial := fun i j =>
  if i.val = rPower ∧ j.val = sigmaPower then coefficient else 0

def denseAdd (left right : DenseBivariatePolynomial) : DenseBivariatePolynomial :=
  fun i j => left i j + right i j

def denseSub (left right : DenseBivariatePolynomial) : DenseBivariatePolynomial :=
  fun i j => left i j - right i j

def denseScale (coefficient : ℤ) (polynomial : DenseBivariatePolynomial) :
    DenseBivariatePolynomial :=
  fun i j => coefficient * polynomial i j

def densePolynomialOfTerms (terms : List BivariateTerm) :
    DenseBivariatePolynomial :=
  terms.foldl (fun polynomial term =>
    denseAdd polynomial (denseMonomial term.coeff term.rPow term.sigmaPow)) denseZero

def denseR : DenseBivariatePolynomial := denseMonomial 1 1 0
def denseSigma : DenseBivariatePolynomial := denseMonomial 1 0 1
def denseB : DenseBivariatePolynomial :=
  denseSub (denseAdd (denseMonomial 4 0 0) (denseScale 4 denseR))
    (denseScale 3 denseSigma)

def denseShiftR (power : ℕ) (polynomial : DenseBivariatePolynomial) :
    DenseBivariatePolynomial := fun i j =>
  if _h : power ≤ i.val then
    polynomial ⟨i.val - power, lt_of_le_of_lt (Nat.sub_le _ _) i.isLt⟩ j
  else 0

def denseShiftSigma (power : ℕ) (polynomial : DenseBivariatePolynomial) :
    DenseBivariatePolynomial := fun i j =>
  if _h : power ≤ j.val then
    polynomial i ⟨j.val - power, lt_of_le_of_lt (Nat.sub_le _ _) j.isLt⟩
  else 0

/-- Multiplication by `B = 4 + 4r - 3sigma`, implemented by exact shifts. -/
def denseMulB (polynomial : DenseBivariatePolynomial) : DenseBivariatePolynomial :=
  denseSub (denseAdd (denseScale 4 polynomial) (denseScale 4 (denseShiftR 1 polynomial)))
    (denseScale 3 (denseShiftSigma 1 polynomial))

/-- Multiplication by `3sigma-4`, implemented by exact shifts. -/
def denseMulThreeSigmaSubFour (polynomial : DenseBivariatePolynomial) :
    DenseBivariatePolynomial :=
  denseSub (denseScale 3 (denseShiftSigma 1 polynomial)) (denseScale 4 polynomial)

/-- Formal partial derivative with respect to `r`. -/
def denseDerivR (polynomial : DenseBivariatePolynomial) :
    DenseBivariatePolynomial := fun i j =>
  if h : i.val + 1 < 14 then
    (i.val + 1 : ℤ) * polynomial ⟨i.val + 1, h⟩ j
  else 0

/-- Formal partial derivative with respect to `sigma`. -/
def denseDerivSigma (polynomial : DenseBivariatePolynomial) :
    DenseBivariatePolynomial := fun i j =>
  if h : j.val + 1 < 8 then
    (j.val + 1 : ℤ) * polynomial i ⟨j.val + 1, h⟩
  else 0

/-- Denominator-cleared reduced saddle recurrence. -/
def saddleNumeratorStep (k : ℕ) (polynomial : DenseBivariatePolynomial) :
    DenseBivariatePolynomial :=
  denseAdd
    (denseScale (-4)
      (denseAdd
        (denseShiftR 2
          (denseSub (denseMulB (denseDerivR polynomial))
            (denseScale (8 * (k : ℤ)) polynomial)))
        (denseScale (k : ℤ) (denseShiftR 1 (denseMulB polynomial)))))
    (denseMulThreeSigmaSubFour
      (denseAdd
        (denseScale ((k : ℤ) - 1) (denseMulB polynomial))
        (denseShiftSigma 1
          (denseAdd (denseMulB (denseDerivSigma polynomial))
            (denseScale (6 * (k : ℤ)) polynomial)))))

/-- The normalized order-two numerator `P_2`. -/
def h2Terms : List BivariateTerm := [
  ⟨-128, 4, 1⟩,
  ⟨384, 3, 2⟩,
  ⟨-512, 3, 1⟩,
  ⟨256, 3, 0⟩,
  ⟨360, 2, 3⟩,
  ⟨-192, 2, 2⟩,
  ⟨-960, 2, 1⟩,
  ⟨768, 2, 0⟩,
  ⟨720, 1, 2⟩,
  ⟨-1536, 1, 1⟩,
  ⟨768, 1, 0⟩,
  ⟨-180, 0, 3⟩,
  ⟨624, 0, 2⟩,
  ⟨-704, 0, 1⟩,
  ⟨256, 0, 0⟩
]

def h3Terms : List BivariateTerm := [
  ⟨4096, 6, 1⟩,
  ⟨-18432, 5, 2⟩,
  ⟨24576, 5, 1⟩,
  ⟨-4096, 5, 0⟩,
  ⟨34560, 4, 3⟩,
  ⟨-92160, 4, 2⟩,
  ⟨79872, 4, 1⟩,
  ⟨-24576, 4, 0⟩,
  ⟨38016, 3, 4⟩,
  ⟨-62208, 3, 3⟩,
  ⟨-47616, 3, 2⟩,
  ⟨123904, 3, 1⟩,
  ⟨-53248, 3, 0⟩,
  ⟨15552, 2, 4⟩,
  ⟨1152, 2, 3⟩,
  ⟨-111360, 2, 2⟩,
  ⟨149504, 2, 1⟩,
  ⟨-53248, 2, 0⟩,
  ⟨-6480, 1, 4⟩,
  ⟨44352, 1, 3⟩,
  ⟨-97536, 1, 2⟩,
  ⟨84992, 1, 1⟩,
  ⟨-24576, 1, 0⟩,
  ⟨-3024, 0, 4⟩,
  ⟨13824, 0, 3⟩,
  ⟨-23040, 0, 2⟩,
  ⟨16384, 0, 1⟩,
  ⟨-4096, 0, 0⟩
]

def h4Terms : List BivariateTerm := [
  ⟨-196608, 8, 1⟩,
  ⟨1179648, 7, 2⟩,
  ⟨-1572864, 7, 1⟩,
  ⟨131072, 7, 0⟩,
  ⟨-3096576, 6, 3⟩,
  ⟨8257536, 6, 2⟩,
  ⟨-6291456, 6, 1⟩,
  ⟨1048576, 6, 0⟩,
  ⟨4644864, 5, 4⟩,
  ⟨-18579456, 5, 3⟩,
  ⟨26836992, 5, 2⟩,
  ⟨-16515072, 5, 1⟩,
  ⟨3670016, 5, 0⟩,
  ⟨5785344, 4, 5⟩,
  ⟨-15261696, 4, 4⟩,
  ⟨2433024, 4, 3⟩,
  ⟨24231936, 4, 2⟩,
  ⟨-23805952, 4, 1⟩,
  ⟨6750208, 4, 0⟩,
  ⟨4230144, 3, 5⟩,
  ⟨-10298880, 3, 4⟩,
  ⟨-3612672, 3, 3⟩,
  ⟨28397568, 3, 2⟩,
  ⟨-25559040, 3, 1⟩,
  ⟨6881280, 3, 0⟩,
  ⟨352512, 2, 5⟩,
  ⟨2239488, 2, 4⟩,
  ⟨-13814784, 2, 3⟩,
  ⟨23728128, 2, 2⟩,
  ⟨-16400384, 2, 1⟩,
  ⟨3866624, 2, 0⟩,
  ⟨-393984, 1, 5⟩,
  ⟨2757888, 1, 4⟩,
  ⟨-7299072, 1, 3⟩,
  ⟨9117696, 1, 2⟩,
  ⟨-5308416, 1, 1⟩,
  ⟨1114112, 1, 0⟩,
  ⟨-93312, 0, 5⟩,
  ⟨539136, 0, 4⟩,
  ⟨-1216512, 0, 3⟩,
  ⟨1327104, 0, 2⟩,
  ⟨-688128, 0, 1⟩,
  ⟨131072, 0, 0⟩
]

def h5Terms : List BivariateTerm := [
  ⟨12582912, 10, 1⟩,
  ⟨-94371840, 9, 2⟩,
  ⟨125829120, 9, 1⟩,
  ⟨-6291456, 9, 0⟩,
  ⟨318504960, 8, 3⟩,
  ⟨-849346560, 8, 2⟩,
  ⟨613416960, 8, 1⟩,
  ⟨-62914560, 8, 0⟩,
  ⟨-637009920, 7, 4⟩,
  ⟨2548039680, 7, 3⟩,
  ⟨-3556638720, 7, 2⟩,
  ⟨1934622720, 7, 1⟩,
  ⟨-283115520, 7, 0⟩,
  ⟨836075520, 6, 5⟩,
  ⟨-4459069440, 6, 4⟩,
  ⟨9236643840, 6, 3⟩,
  ⟨-9201254400, 6, 2⟩,
  ⟨4341104640, 6, 1⟩,
  ⟨-754974720, 6, 0⟩,
  ⟨1152589824, 5, 6⟩,
  ⟨-4160471040, 5, 5⟩,
  ⟨3219333120, 5, 4⟩,
  ⟨5010554880, 5, 3⟩,
  ⟨-9995747328, 5, 2⟩,
  ⟨6021709824, 5, 1⟩,
  ⟨-1254096896, 5, 0⟩,
  ⟨1179463680, 4, 6⟩,
  ⟨-4529737728, 4, 5⟩,
  ⟨4295393280, 4, 4⟩,
  ⟨3889594368, 4, 3⟩,
  ⟨-9701621760, 4, 2⟩,
  ⟨6160908288, 4, 1⟩,
  ⟨-1301282816, 4, 0⟩,
  ⟨372625920, 3, 6⟩,
  ⟨-1096519680, 3, 5⟩,
  ⟨-575963136, 3, 4⟩,
  ⟨5542428672, 3, 3⟩,
  ⟨-7668695040, 3, 2⟩,
  ⟨4257480704, 3, 1⟩,
  ⟨-833617920, 3, 0⟩,
  ⟨-7464960, 2, 6⟩,
  ⟨340568064, 2, 5⟩,
  ⟨-1731760128, 2, 4⟩,
  ⟨3606183936, 2, 3⟩,
  ⟨-3671457792, 2, 2⟩,
  ⟨1784152064, 2, 1⟩,
  ⟨-319815680, 2, 0⟩,
  ⟨-26438400, 1, 6⟩,
  ⟨206696448, 1, 5⟩,
  ⟨-653930496, 1, 4⟩,
  ⟨1066401792, 1, 3⟩,
  ⟨-936443904, 1, 2⟩,
  ⟨412090368, 1, 1⟩,
  ⟨-68157440, 1, 0⟩,
  ⟨-4105728, 0, 6⟩,
  ⟨28864512, 0, 5⟩,
  ⟨-82944000, 0, 4⟩,
  ⟨123863040, 0, 3⟩,
  ⟨-100270080, 0, 2⟩,
  ⟨40894464, 0, 1⟩,
  ⟨-6291456, 0, 0⟩
]

def h2DensePolynomial : DenseBivariatePolynomial :=
  densePolynomialOfTerms h2Terms

def h3DensePolynomial : DenseBivariatePolynomial :=
  densePolynomialOfTerms h3Terms

def h4DensePolynomial : DenseBivariatePolynomial :=
  densePolynomialOfTerms h4Terms

def h5DensePolynomial : DenseBivariatePolynomial :=
  densePolynomialOfTerms h5Terms

def h6GeneratedDensePolynomial : DenseBivariatePolynomial :=
  saddleNumeratorStep 5 h5DensePolynomial

def h6FrozenDensePolynomial : DenseBivariatePolynomial :=
  densePolynomialOfTerms h6Terms

macro "verify_dense_step" : tactic =>
  `(tactic|
    (funext i j
     fin_cases i <;> fin_cases j <;>
       rfl))

set_option maxHeartbeats 2000000 in
theorem h3DensePolynomial_recurrence :
    saddleNumeratorStep 2 h2DensePolynomial = h3DensePolynomial := by
  verify_dense_step

set_option maxHeartbeats 2000000 in
theorem h4DensePolynomial_recurrence :
    saddleNumeratorStep 3 h3DensePolynomial = h4DensePolynomial := by
  verify_dense_step

set_option maxHeartbeats 2000000 in
theorem h5DensePolynomial_recurrence :
    saddleNumeratorStep 4 h4DensePolynomial = h5DensePolynomial := by
  verify_dense_step

set_option maxHeartbeats 2000000 in
set_option maxRecDepth 100000 in
/-- The fourth exact recurrence step produces every coefficient of the frozen
degree-thirteen numerator. -/
theorem h6GeneratedDensePolynomial_eq_frozen :
    h6GeneratedDensePolynomial = h6FrozenDensePolynomial := by
  verify_dense_step

theorem h2_term_count : h2Terms.length = 15 := by norm_num [h2Terms]

end Zeta23.Research.JensenWedge
