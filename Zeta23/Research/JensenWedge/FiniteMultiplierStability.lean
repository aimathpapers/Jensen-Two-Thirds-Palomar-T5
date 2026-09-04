import Zeta23.Research.JensenWedge.LocalForwardDifferenceCalculus
import Zeta23.Research.JensenWedge.MultiplierStability
import Zeta23.Research.JensenWedge.Terminating3F2CriticalRadius
import Mathlib.Algebra.Group.ForwardDiff
import Mathlib.Algebra.Polynomial.HasseDeriv
import Mathlib.Analysis.Complex.Liouville

/-!
# Finite Newton--Cauchy multiplier stability

This module closes the finite algebraic and local analytic seam in Holland's
multiplier argument.  In particular, the Gregory--Newton formula is applied
to polynomial coefficients through Hasse derivatives, and Cauchy's estimate
is combined with the local repeated-FTC adapter to bound the corresponding
unit forward differences.
-/

namespace Zeta23.Research.JensenWedge

open Finset Set
open fwdDiff
open Polynomial

noncomputable section

/-- Coefficientwise multiplication of a polynomial by a scalar sequence. -/
def coefficientMultiplierTransform {R : Type*} [Semiring R]
    (p : Polynomial R) (c : ℕ → R) : Polynomial R :=
  ∑ j ∈ p.support, Polynomial.monomial j (p.coeff j * c j)

theorem coeff_coefficientMultiplierTransform {R : Type*} [Semiring R]
    (p : Polynomial R) (c : ℕ → R) (j : ℕ) :
    (coefficientMultiplierTransform p c).coeff j = p.coeff j * c j := by
  rw [coefficientMultiplierTransform, Polynomial.finsetSum_coeff]
  by_cases hj : j ∈ p.support
  · rw [Finset.sum_eq_single j]
    · simp [Polynomial.coeff_monomial]
    · intro i hi hij
      simp [Polynomial.coeff_monomial, hij]
    · exact fun h => (h hj).elim
  · have hpj : p.coeff j = 0 := Polynomial.notMem_support_iff.mp hj
    simp only [hpj, zero_mul]
    apply Finset.sum_eq_zero
    intro i hi
    have hij : i ≠ j := by
      intro hij
      subst i
      exact hj hi
    simp [Polynomial.coeff_monomial, hij]

/-- The coefficient form of the Hasse derivative after restoring the lost
power of `X`. -/
theorem coeff_X_pow_mul_hasseDeriv {R : Type*} [Semiring R]
    (p : Polynomial R) (k j : ℕ) :
    (Polynomial.X ^ k * Polynomial.hasseDeriv k p).coeff j =
      if k ≤ j then (j.choose k : R) * p.coeff j else 0 := by
  rw [Polynomial.coeff_X_pow_mul']
  split_ifs with hkj
  · rw [Polynomial.hasseDeriv_coeff]
    have hsum : j - k + k = j := Nat.sub_add_cancel hkj
    rw [hsum]
  · rfl

/-- Kernel-checked Gregory--Newton identity for coefficient multipliers.
The right side is the finite Newton series expressed with Hasse derivatives.
-/
theorem coefficientMultiplierTransform_eq_newton_hasse
    {R : Type*} [CommRing R]
    (p : Polynomial R) (c : ℕ → R) (d : ℕ) (hdeg : p.natDegree ≤ d) :
    coefficientMultiplierTransform p c =
      ∑ k ∈ range (d + 1),
        Polynomial.C (((fwdDiff 1)^[k] c) 0) *
          (Polynomial.X ^ k * Polynomial.hasseDeriv k p) := by
  ext j
  rw [coeff_coefficientMultiplierTransform]
  rw [Polynomial.finsetSum_coeff]
  by_cases hj : j ≤ d
  · have hc : c j = ∑ k ∈ range (j + 1),
        (j.choose k : R) * ((fwdDiff 1)^[k] c) 0 := by
      simpa using
        shift_eq_sum_fwdDiff_iter (h := 1) c j 0
    simp only [Polynomial.coeff_C_mul, coeff_X_pow_mul_hasseDeriv]
    calc
      p.coeff j * c j = p.coeff j *
          (∑ k ∈ range (j + 1),
            (j.choose k : R) * ((fwdDiff 1)^[k] c) 0) := by rw [hc]
      _ = ∑ k ∈ range (j + 1),
          ((fwdDiff 1)^[k] c) 0 *
            (if k ≤ j then (j.choose k : R) * p.coeff j else 0) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro k hk
        rw [if_pos (Nat.lt_succ_iff.mp (mem_range.mp hk))]
        ring
      _ = ∑ k ∈ range (d + 1),
          ((fwdDiff 1)^[k] c) 0 *
            (if k ≤ j then (j.choose k : R) * p.coeff j else 0) := by
        apply Finset.sum_subset (Finset.range_mono (Nat.succ_le_succ hj))
        intro k hkd hkj
        have hjk : j < k := Nat.lt_of_not_ge fun hle =>
          hkj (Finset.mem_range.mpr (Nat.lt_succ_of_le hle))
        rw [if_neg (Nat.not_le_of_lt hjk)]
        simp
  · have hpj : p.coeff j = 0 := by
      apply Polynomial.coeff_eq_zero_of_natDegree_lt
      exact lt_of_not_ge (fun hjdeg => hj (hjdeg.trans hdeg))
    simp only [hpj, zero_mul, Polynomial.coeff_C_mul,
      coeff_X_pow_mul_hasseDeriv, mul_zero, ite_self, Finset.sum_const_zero]

/-- Evaluation form of the finite Newton multiplier identity. -/
theorem eval_coefficientMultiplierTransform_eq_newton_hasse
    {R : Type*} [CommRing R]
    (p : Polynomial R) (c : ℕ → R) (d : ℕ) (hdeg : p.natDegree ≤ d)
    (z : R) :
    Polynomial.eval z (coefficientMultiplierTransform p c) =
      ∑ k ∈ range (d + 1),
        ((fwdDiff 1)^[k] c) 0 * z ^ k *
          Polynomial.eval z (Polynomial.hasseDeriv k p) := by
  rw [coefficientMultiplierTransform_eq_newton_hasse p c d hdeg]
  simp only [Polynomial.eval_finsetSum, Polynomial.eval_mul,
    Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  apply sum_congr rfl
  intro k hk
  ring

/-- The project's recursive complex forward difference agrees at natural
nodes with Mathlib's iterated forward-difference operator. -/
theorem complexForwardDiff_nat_eq_fwdDiff_iter
    (c : ℂ → ℂ) (q j : ℕ) :
    complexForwardDiff q c (j : ℂ) =
      ((fwdDiff 1)^[q] (fun m : ℕ => c (m : ℂ))) j := by
  induction q generalizing j with
  | zero => simp [complexForwardDiff]
  | succ q ih =>
      rw [complexForwardDiff, Function.iterate_succ_apply']
      simp only [fwdDiff]
      rw [← ih (j + 1), ← ih j]
      push_cast
      rfl

theorem re_fwdDiff_iter_nat (c : ℕ → ℂ) (q j : ℕ) :
    (((fwdDiff 1)^[q] c) j).re =
      ((fwdDiff 1)^[q] (fun m => (c m).re)) j := by
  induction q generalizing j with
  | zero => simp
  | succ q ih =>
      rw [Function.iterate_succ_apply', Function.iterate_succ_apply']
      simp only [fwdDiff, Complex.sub_re]
      rw [ih, ih]

/-- A positive-order forward difference vanishes when the function is
constant on all integer nodes that it consumes. -/
theorem complexForwardDiff_eq_zero_of_eq_const_on_nat_segment
    (c : ℂ → ℂ) (a : ℂ) :
    ∀ q : ℕ, 0 < q → ∀ x : ℕ,
      (∀ j : ℕ, j ≤ q → c ((x + j : ℕ) : ℂ) = a) →
      complexForwardDiff q c (x : ℂ) = 0 := by
  intro q hq
  induction q with
  | zero => omega
  | succ q ih =>
      intro x hnodes
      rw [complexForwardDiff]
      by_cases hq0 : q = 0
      · subst q
        simp only [complexForwardDiff]
        have h0 := hnodes 0 (by omega)
        have h1 := hnodes 1 (by omega)
        have h0' : c (x : ℂ) = a := by simpa using h0
        push_cast
        rw [show (x : ℂ) + 1 = ((x + 1 : ℕ) : ℂ) by push_cast; ring,
          h0', h1]
        simp
      · have hqpos : 0 < q := Nat.pos_of_ne_zero hq0
        have hshift : ∀ j : ℕ, j ≤ q →
            c (((x + 1) + j : ℕ) : ℂ) = a := by
          intro j hj
          simpa only [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
            hnodes (j + 1) (by omega)
        have hbase : ∀ j : ℕ, j ≤ q →
            c ((x + j : ℕ) : ℂ) = a := by
          exact fun j hj => hnodes j (hj.trans (Nat.le_succ q))
        rw [show (x : ℂ) + 1 = ((x + 1 : ℕ) : ℂ) by push_cast; ring,
          ih hqpos (x + 1) hshift, ih hqpos x hbase]
        simp

/-- The Hasse derivative is exactly the ordinary iterated derivative divided
by the factorial, after polynomial evaluation. -/
theorem factorial_mul_eval_hasseDeriv
    (p : ℝ[X]) (x : ℝ) (k : ℕ) :
    (k.factorial : ℝ) * Polynomial.eval x (Polynomial.hasseDeriv k p) =
      Polynomial.eval x (Polynomial.derivative^[k] p) := by
  have hpoly := congrFun (Polynomial.factorial_smul_hasseDeriv
    (R := ℝ) k) p
  have heval := congrArg (Polynomial.eval x) hpoly
  simpa [nsmul_eq_mul] using heval

/-- Exact bridge from the Hasse term in Gregory--Newton to the derivative
ratio used by the terminating hypergeometric critical-radius theorem. -/
theorem eval_hasseDeriv_div_eq_polynomialDerivativeRatio_div_factorial
    (p : ℝ[X]) (x : ℝ) (k : ℕ) (hp : p.eval x ≠ 0) :
    x ^ k * Polynomial.eval x (Polynomial.hasseDeriv k p) / p.eval x =
      polynomialDerivativeRatio p x k / (k.factorial : ℝ) := by
  have hfact : (k.factorial : ℝ) ≠ 0 := by positivity
  unfold polynomialDerivativeRatio polynomialEulerJet
  rw [← factorial_mul_eval_hasseDeriv p x k]
  field_simp

/-- Complete finite multiplier estimate at a nonzero comparison value.  It
combines the exact Newton identity, vanishing through order four, Cauchy
forward-difference bounds, and the critical derivative radius. -/
theorem finiteNewtonRelativeError_lt_one
    (p P : ℝ[X]) (c : ℕ → ℝ) (d : ℕ) (x epsilon R S : ℝ)
    (hd : 5 ≤ d)
    (hdeg : p.natDegree ≤ d)
    (hP : P = coefficientMultiplierTransform p c)
    (hp : p.eval x ≠ 0)
    (hc0 : c 0 = 1)
    (hzero : ∀ k, 1 ≤ k → k ≤ 4 → ((fwdDiff 1)^[k] c) 0 = 0)
    (hfd : ∀ k, 5 ≤ k → k ≤ d →
      |((fwdDiff 1)^[k] c) 0| ≤
        (k.factorial : ℝ) * epsilon / R ^ k)
    (hcritical : ∀ k ≤ d,
      |polynomialDerivativeRatio p x k| ≤ S ^ k)
    (hepsilon0 : 0 ≤ epsilon) (hepsilon16 : epsilon < 16)
    (hS : 0 ≤ S) (hR : 0 < R) (hscale : 2 * S ≤ R) :
    |P.eval x / p.eval x - 1| < 1 := by
  let term : ℕ → ℝ := fun k =>
    ((fwdDiff 1)^[k] c) 0 *
      (x ^ k * Polynomial.eval x (Polynomial.hasseDeriv k p) / p.eval x)
  have hratio : P.eval x / p.eval x = ∑ k ∈ range (d + 1), term k := by
    rw [hP, eval_coefficientMultiplierTransform_eq_newton_hasse p c d hdeg]
    rw [Finset.sum_div]
    apply Finset.sum_congr rfl
    intro k hk
    dsimp only [term]
    ring
  have hterm0 : term 0 = 1 := by
    dsimp only [term]
    simp [hc0, hp]
  have htermSmall : ∀ k ∈ Finset.Ico 1 5, term k = 0 := by
    intro k hk
    have hk1 : 1 ≤ k := (Finset.mem_Ico.mp hk).1
    have hk5 : k < 5 := (Finset.mem_Ico.mp hk).2
    have hk4 : k ≤ 4 := by omega
    dsimp only [term]
    rw [hzero k hk1 hk4]
    simp
  have hfactorial (k : ℕ) : 0 < (k.factorial : ℝ) := by positivity
  have hterm : ∀ k, 5 ≤ k → k ≤ d →
      |term k| ≤ epsilon * (1 / 2 : ℝ) ^ k := by
    intro k hk5 hkd
    have hhasse :=
      eval_hasseDeriv_div_eq_polynomialDerivativeRatio_div_factorial p x k hp
    have hfdNorm : |((fwdDiff 1)^[k] c) 0| / (k.factorial : ℝ) ≤
        epsilon / R ^ k := by
      calc
        |((fwdDiff 1)^[k] c) 0| / (k.factorial : ℝ) ≤
            ((k.factorial : ℝ) * epsilon / R ^ k) /
              (k.factorial : ℝ) :=
          div_le_div_of_nonneg_right (hfd k hk5 hkd) (hfactorial k).le
        _ = epsilon / R ^ k := by field_simp
    have hcrit := hcritical k hkd
    have hRpow : 0 < R ^ k := pow_pos hR k
    have hhalf : S / R ≤ (1 : ℝ) / 2 := by
      rw [div_le_iff₀ hR]
      nlinarith
    have hSR : 0 ≤ S / R := div_nonneg hS hR.le
    calc
      |term k| =
          (|((fwdDiff 1)^[k] c) 0| / (k.factorial : ℝ)) *
            |polynomialDerivativeRatio p x k| := by
        dsimp only [term]
        rw [abs_mul, hhasse, abs_div, abs_of_pos (hfactorial k)]
        field_simp
      _ ≤ (epsilon / R ^ k) * S ^ k :=
        mul_le_mul hfdNorm hcrit (abs_nonneg _) (div_nonneg hepsilon0 hRpow.le)
      _ = epsilon * (S / R) ^ k := by
        rw [div_pow]
        field_simp
      _ ≤ epsilon * (1 / 2 : ℝ) ^ k := by
        exact mul_le_mul_of_nonneg_left
          (pow_le_pow_left₀ hSR hhalf k) hepsilon0
  have hsplit :
      ∑ k ∈ range (d + 1), term k =
        term 0 + ∑ k ∈ Finset.Ico 1 5, term k +
          ∑ k ∈ Finset.Ico 5 (d + 1), term k := by
    have h1d : 1 ≤ d + 1 := by omega
    have h5d : 5 ≤ d + 1 := by omega
    calc
      ∑ k ∈ range (d + 1), term k =
          (∑ k ∈ range 1, term k) +
            ∑ k ∈ Finset.Ico 1 (d + 1), term k :=
        (Finset.sum_range_add_sum_Ico term h1d).symm
      _ = term 0 + ∑ k ∈ Finset.Ico 1 5, term k +
          ∑ k ∈ Finset.Ico 5 (d + 1), term k := by
        rw [Finset.sum_range_one,
          ← Finset.sum_Ico_consecutive term (by omega : 1 ≤ 5) h5d]
        abel
  have hsmallSum : ∑ k ∈ Finset.Ico 1 5, term k = 0 :=
    Finset.sum_eq_zero htermSmall
  have htailRewrite :
      ∑ k ∈ Finset.Ico 5 (d + 1), term k =
        ∑ i ∈ range (d + 1 - 5), term (i + 5) := by
    rw [Finset.sum_Ico_eq_sum_range]
    apply Finset.sum_congr rfl
    intro i hi
    congr 1
    omega
  rw [hratio, hsplit, hterm0, hsmallSum, htailRewrite]
  have hfinal := finiteMultiplierError_lt_one
    (n := d + 1 - 5) (term := fun i => term (i + 5))
    hepsilon0 hepsilon16 (fun i hi => by
      have hid : i + 5 ≤ d := by
        omega
      simpa [Nat.add_comm] using hterm (i + 5) (by omega) hid)
  convert hfinal using 1 <;> ring

/-- Cauchy's estimate on radius `R`, followed by repeated FTC on a real
unit-step interval, bounds the order-`q` forward difference by
`q! C / R^q`.  The hypotheses state exactly the local holomorphy and tube
bound needed by the calculation. -/
theorem norm_complexForwardDiff_le_of_cauchy_tube
    (f : ℂ → ℂ) (q : ℕ) (x R C : ℝ)
    (hR : 0 < R)
    (hdisc : ∀ y ∈ Set.Icc x (x + (q : ℝ)),
      DiffContOnCl ℂ f (Metric.ball (y : ℂ) R))
    (hbound : ∀ y ∈ Set.Icc x (x + (q : ℝ)),
      ∀ z ∈ Metric.sphere (y : ℂ) R, ‖f z‖ ≤ C) :
    ‖complexForwardDiff q f (x : ℂ)‖ ≤
      q.factorial * C / R ^ q := by
  let derivs : ℕ → ℂ → ℂ := fun k => iteratedDeriv k f
  have hderiv : ∀ s y, y ∈ Set.Icc x (x + (q : ℝ)) →
      HasDerivAt (derivs s) (derivs (s + 1) (y : ℂ)) (y : ℂ) := by
    intro s y hy
    have hs : DifferentiableAt ℂ (iteratedDeriv s f) (y : ℂ) := by
      simpa only [iteratedDeriv_eq_iterate] using
        (((hdisc y hy).differentiableOn.analyticAt
          (Metric.isOpen_ball.mem_nhds
            (Metric.mem_ball_self hR))).iterated_deriv s).differentiableAt
    simpa [derivs, iteratedDeriv_succ] using hs.hasDerivAt
  have hq : ∀ y, y ∈ Set.Icc x (x + (q : ℝ)) →
      ‖derivs q (y : ℂ)‖ ≤ q.factorial * C / R ^ q := by
    intro y hy
    exact Complex.norm_iteratedDeriv_le_of_forall_mem_sphere_norm_le q hR
      (hdisc y hy) (hbound y hy)
  simpa [derivs, iteratedDeriv_zero] using
    norm_complexForwardDiff_sub_constant_le_on_real_interval
      derivs q 0 x 0 hderiv (by simpa using hq)

end

end Zeta23.Research.JensenWedge
