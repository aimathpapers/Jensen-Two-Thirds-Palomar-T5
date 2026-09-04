import Mathlib

/-!
# Finite core of Holland's multiplier-stability argument

This module formalizes the elementary part of Holland's Proposition 2.2 that
is consumed by the Jensen-wedge argument:

* the exact geometric tail beginning at order five;
* the sharp sufficient threshold `epsilon < 16`;
* preservation of sign under a relative error of modulus less than one; and
* the intermediate-value construction of one distinct positive root in each
  of a family of disjoint sign-changing intervals.

It does not formalize the holomorphic Cauchy estimate that supplies the
finite-difference bounds, nor does it assert that a particular xi multiplier
satisfies them.  Those analytic inputs remain explicit theorem hypotheses.
-/

namespace Zeta23.Research.JensenWedge

open Finset Set

/-- Sum of `n` consecutive powers of `1/2`, beginning with `(1/2)^5`. -/
def fifthOrderTail : ℕ → ℚ
  | 0 => 0
  | n + 1 => fifthOrderTail n + (1 / 2 : ℚ) ^ (n + 5)

theorem fifthOrderTail_eq (n : ℕ) :
    fifthOrderTail n = (1 / 16 : ℚ) * (1 - (1 / 2 : ℚ) ^ n) := by
  induction n with
  | zero => norm_num [fifthOrderTail]
  | succ n ih =>
      rw [fifthOrderTail, ih, pow_succ]
      ring

theorem fifthOrderTail_lt (n : ℕ) :
    fifthOrderTail n < (1 / 16 : ℚ) := by
  rw [fifthOrderTail_eq]
  have hpow : 0 < (1 / 2 : ℚ) ^ n := pow_pos (by norm_num) _
  nlinarith

theorem sum_half_powers_eq_fifthOrderTail (n : ℕ) :
    ∑ k ∈ range n, (1 / 2 : ℝ) ^ (k + 5) = ((fifthOrderTail n : ℚ) : ℝ) := by
  induction n with
  | zero => simp [fifthOrderTail]
  | succ n ih =>
      rw [sum_range_succ, fifthOrderTail, Rat.cast_add, Rat.cast_pow,
        Rat.cast_div, Rat.cast_one, Rat.cast_ofNat, ih]

/-- Holland's printed constant `16` is exactly the reciprocal of the infinite
geometric tail beginning at order five. -/
theorem fifthOrderGeometricError_lt_one
    {epsilon : ℝ} (hepsilon_nonneg : 0 ≤ epsilon) (hepsilon : epsilon < 16)
    (n : ℕ) :
    epsilon * ((fifthOrderTail n : ℚ) : ℝ) < 1 := by
  have htail : ((fifthOrderTail n : ℚ) : ℝ) < (1 / 16 : ℝ) := by
    rw [fifthOrderTail_eq]
    push_cast
    have hpow : 0 < (1 / 2 : ℝ) ^ n := pow_pos (by norm_num) _
    nlinarith
  rcases hepsilon_nonneg.eq_or_lt with rfl | hepsilon_pos
  · norm_num
  · have hmul := mul_lt_mul_of_pos_left htail hepsilon_pos
    nlinarith

/-- If a finite error is termwise dominated by the order-five geometric
majorant, then its total modulus is less than one.  The analytic Cauchy and
critical-point estimates enter only through `hterm`. -/
theorem finiteMultiplierError_lt_one
    {epsilon : ℝ} (hepsilon_nonneg : 0 ≤ epsilon) (hepsilon : epsilon < 16)
    {term : ℕ → ℝ} {n : ℕ}
    (hterm : ∀ k < n, |term k| ≤ epsilon * (1 / 2 : ℝ) ^ (k + 5)) :
    |∑ k ∈ range n, term k| < 1 := by
  calc
    |∑ k ∈ range n, term k| ≤ ∑ k ∈ range n, |term k| := abs_sum_le_sum_abs _ _
    _ ≤ ∑ k ∈ range n, epsilon * (1 / 2 : ℝ) ^ (k + 5) := by
      exact sum_le_sum fun k hk => hterm k (mem_range.mp hk)
    _ = epsilon * ((fifthOrderTail n : ℚ) : ℝ) := by
      rw [← mul_sum]
      rw [sum_half_powers_eq_fifthOrderTail]
    _ < 1 := fifthOrderGeometricError_lt_one hepsilon_nonneg hepsilon n

/-- A relative perturbation of modulus less than one preserves the sign of a
nonzero real value. -/
theorem mul_pos_of_relativeError_lt_one
    {p P : ℝ} (hp : p ≠ 0) (hrel : |P / p - 1| < 1) :
    0 < p * P := by
  have hratio : 0 < P / p := by
    have := (abs_lt.mp hrel).1
    linarith
  have hp_sq : 0 < p ^ 2 := sq_pos_of_ne_zero hp
  have hid : p * P = p ^ 2 * (P / p) := by
    field_simp [hp]
  rw [hid]
  positivity

/-- `f` has at least `d` pairwise distinct positive real zeros.  For a
degree-`d` polynomial this is the form needed to conclude that all roots are
simple and positive. -/
def HasDistinctPositiveRoots (f : ℝ → ℝ) (d : ℕ) : Prop :=
  ∃ x : Fin d → ℝ, Function.Injective x ∧ ∀ i, 0 < x i ∧ f (x i) = 0

/-- `f` has at least `d` pairwise distinct negative real zeros. -/
def HasDistinctNegativeRoots (f : ℝ → ℝ) (d : ℕ) : Prop :=
  ∃ x : Fin d → ℝ, Function.Injective x ∧ ∀ i, x i < 0 ∧ f (x i) = 0

/-- `f` has exactly `d` distinct negative real zeros, expressed as existence
of `d` such zeros together with nonexistence of `d+1`. -/
def HasExactlyDistinctNegativeRoots (f : ℝ → ℝ) (d : ℕ) : Prop :=
  HasDistinctNegativeRoots f d ∧ ¬ HasDistinctNegativeRoots f (d + 1)

theorem exists_root_Ioo_of_mul_neg
    {f : ℝ → ℝ} (hf : Continuous f) {a b : ℝ} (hab : a < b)
    (hneg : f a * f b < 0) :
    ∃ x ∈ Ioo a b, f x = 0 := by
  rcases (mul_neg_iff.mp hneg) with h | h
  · have hzero : (0 : ℝ) ∈ Icc (f b) (f a) := ⟨h.2.le, h.1.le⟩
    rcases intermediate_value_Icc' hab.le hf.continuousOn hzero with ⟨x, hx, hfx⟩
    refine ⟨x, ?_, hfx⟩
    constructor
    · exact lt_of_le_of_ne hx.1 fun hax =>
        h.1.ne' (by simpa [hax] using hfx)
    · exact lt_of_le_of_ne hx.2 fun hxb =>
        h.2.ne (by simpa [hxb] using hfx)
  · have hzero : (0 : ℝ) ∈ Icc (f a) (f b) := ⟨h.1.le, h.2.le⟩
    rcases intermediate_value_Icc hab.le hf.continuousOn hzero with ⟨x, hx, hfx⟩
    refine ⟨x, ?_, hfx⟩
    constructor
    · exact lt_of_le_of_ne hx.1 fun hax =>
        h.1.ne (by simpa [hax] using hfx)
    · exact lt_of_le_of_ne hx.2 fun hxb =>
        h.2.ne' (by simpa [hxb] using hfx)

/-- A continuous function with sign changes on `d` ordered intervals with
nonnegative left endpoints and disjoint interiors has `d` distinct positive
roots.  Allowing a shared endpoint is exactly what is needed for adjacent
Rolle-critical intervals. -/
theorem hasDistinctPositiveRoots_of_signChangingIntervals
    {f : ℝ → ℝ} (hf : Continuous f) {d : ℕ}
    (a b : Fin d → ℝ)
    (hpos : ∀ i, 0 ≤ a i)
    (hab : ∀ i, a i < b i)
    (hsep : ∀ i j, i < j → b i ≤ a j)
    (hchange : ∀ i, f (a i) * f (b i) < 0) :
    HasDistinctPositiveRoots f d := by
  choose x hxmem hxzero using fun i =>
    exists_root_Ioo_of_mul_neg hf (hab i) (hchange i)
  refine ⟨x, ?_, fun i => ⟨lt_of_le_of_lt (hpos i) (hxmem i).1, hxzero i⟩⟩
  intro i j hij
  by_contra hne
  have hij' : i < j ∨ j < i := lt_or_gt_of_ne hne
  rcases hij' with hijlt | hjilt
  · have : x i < x j :=
      lt_trans (hxmem i).2 (lt_of_le_of_lt (hsep i j hijlt) (hxmem j).1)
    exact (ne_of_lt this) hij
  · have : x j < x i :=
      lt_trans (hxmem j).2 (lt_of_le_of_lt (hsep j i hjilt) (hxmem i).1)
    exact (ne_of_gt this) hij

/-- The exact sign-transfer interface used downstream: the comparison model
changes sign on each interval, and the actual multiplier has relative error
less than one at every endpoint. -/
structure MultiplierIntervalCertificate (p P : ℝ → ℝ) (d : ℕ) where
  a : Fin d → ℝ
  b : Fin d → ℝ
  nonnegative_left : ∀ i, 0 ≤ a i
  ordered : ∀ i, a i < b i
  separated : ∀ i j, i < j → b i ≤ a j
  model_change : ∀ i, p (a i) * p (b i) < 0
  relative_left : ∀ i, |P (a i) / p (a i) - 1| < 1
  relative_right : ∀ i, |P (b i) / p (b i) - 1| < 1

theorem MultiplierIntervalCertificate.actual_change
    {p P : ℝ → ℝ} {d : ℕ} (C : MultiplierIntervalCertificate p P d)
    (i : Fin d) : P (C.a i) * P (C.b i) < 0 := by
  have hpa : p (C.a i) ≠ 0 := by
    intro hzero
    simpa [hzero] using C.model_change i
  have hpb : p (C.b i) ≠ 0 := by
    intro hzero
    simpa [hzero] using C.model_change i
  have hleft := mul_pos_of_relativeError_lt_one hpa (C.relative_left i)
  have hright := mul_pos_of_relativeError_lt_one hpb (C.relative_right i)
  nlinarith [C.model_change i]

theorem MultiplierIntervalCertificate.actual_hasDistinctPositiveRoots
    {p P : ℝ → ℝ} {d : ℕ} (C : MultiplierIntervalCertificate p P d)
    (hP : Continuous P) : HasDistinctPositiveRoots P d := by
  exact hasDistinctPositiveRoots_of_signChangingIntervals hP C.a C.b
    C.nonnegative_left C.ordered C.separated C.actual_change

end Zeta23.Research.JensenWedge
