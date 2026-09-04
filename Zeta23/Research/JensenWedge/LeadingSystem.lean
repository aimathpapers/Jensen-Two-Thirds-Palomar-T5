import Mathlib

/-!
# Leading system for the proposed sixth-order Jensen comparison

This module checks only the finite algebra obtained after matching the leading
coefficients of the four quotient equations.  It makes no analytic claim
about Riemann's xi function and no claim that an asymptotic parameter branch
exists.
-/

namespace Zeta23.Research.JensenWedge

/-- The denominator-cleared leading equations for the free two-Jacobi model.

`t` is the common leading split point, `w` is the first-order separation of
the two boundaries, `delta` is the first-order lower-boundary shift, and
`alpha` is the scale of the remote upper boundary. -/
structure SixthOrderLeadingSystem (t w delta alpha : ℝ) : Prop where
  orderTwo : w + delta * t ^ 3 = t ^ 3
  orderThree : 3 * (w + delta * t ^ 4) = 2 * t ^ 4
  orderFour : 4 * (w + delta * t ^ 5) = 2 * t ^ 5
  orderOne : alpha * w + alpha * delta * t ^ 2 + t ^ 2 = 2 * alpha * t ^ 2

/-- The candidate values satisfy the leading quotient system exactly. -/
theorem sixthOrderLeadingSystem_candidate :
    SixthOrderLeadingSystem 2 (16 / 3) (1 / 3) 3 := by
  constructor <;> norm_num

/-- Jacobian of the rational leading map at the candidate branch, with
columns ordered as `(t, w, delta, alpha)`. -/
def leadingJacobian : Matrix (Fin 4) (Fin 4) ℚ :=
  !![-4 / 3, 1 / 4, 1, -1 / 9;
     -1, 1 / 8, 1, 0;
     -2, 3 / 16, 3, 0;
     -5 / 3, 1 / 8, 4, 0]

/-- The candidate branch is nondegenerate at leading order. -/
theorem leadingJacobian_det : leadingJacobian.det = 1 / 144 := by
  simp only [leadingJacobian, norm_det]

/-- Exact inverse of the limiting Jacobian, with rows and columns ordered as
`(t, w, delta, alpha)`.  This is the preconditioner for a later quantitative
contraction argument; it contains no asymptotic input. -/
def leadingJacobianInv : Matrix (Fin 4) (Fin 4) ℚ :=
  !![0, 6, -6, 3;
     0, 48, -112 / 3, 16;
     0, 1, -4 / 3, 1;
     -9, 45, -24, 9]

/-- The displayed rational preconditioner is a right inverse. -/
theorem leadingJacobian_mul_inv :
    leadingJacobian * leadingJacobianInv = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [leadingJacobian, leadingJacobianInv, Matrix.mul_apply,
      Fin.sum_univ_succ]

/-- The displayed rational preconditioner is also a left inverse. -/
theorem leadingJacobian_inv_mul :
    leadingJacobianInv * leadingJacobian = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [leadingJacobian, leadingJacobianInv, Matrix.mul_apply,
      Fin.sum_univ_succ]

/-- Jacobian of the limiting residual map in the analytic gauge order
`(alpha, t, w, delta)`.  The older `leadingJacobian` uses the algebraic order
`(t, w, delta, alpha)`; keeping this matrix explicit prevents silently using
the inverse with the wrong coordinate permutation. -/
def gaugeJacobian : Matrix (Fin 4) (Fin 4) ℚ :=
  !![-1 / 9, -4 / 3, 1 / 4, 1;
     0, -1, 1 / 8, 1;
     0, -2, 3 / 16, 3;
     0, -5 / 3, 1 / 8, 4]

/-- The determinant changes sign under the odd column permutation from
`leadingJacobian` to the analytic gauge order. -/
theorem gaugeJacobian_det : gaugeJacobian.det = -1 / 144 := by
  simp only [gaugeJacobian, norm_det]

/-- Exact inverse in the analytic gauge order `(alpha, t, w, delta)`. -/
def gaugeJacobianInv : Matrix (Fin 4) (Fin 4) ℚ :=
  !![-9, 45, -24, 9;
     0, 6, -6, 3;
     0, 48, -112 / 3, 16;
     0, 1, -4 / 3, 1]

theorem gaugeJacobian_mul_inv :
    gaugeJacobian * gaugeJacobianInv = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [gaugeJacobian, gaugeJacobianInv, Matrix.mul_apply,
      Fin.sum_univ_succ]

theorem gaugeJacobian_inv_mul :
    gaugeJacobianInv * gaugeJacobian = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [gaugeJacobian, gaugeJacobianInv, Matrix.mul_apply,
      Fin.sum_univ_succ]

/-- The positive leading branch is unique. -/
theorem sixthOrderLeadingSystem_unique
    {t w delta alpha : ℝ}
    (ht : 1 < t)
    (h : SixthOrderLeadingSystem t w delta alpha) :
    t = 2 ∧ w = 16 / 3 ∧ delta = 1 / 3 ∧ alpha = 3 := by
  rcases h with ⟨h2, h3, h4, h1⟩
  have ht0 : t ≠ 0 := by nlinarith
  have htm1 : t - 1 ≠ 0 := by nlinarith
  have h23 : t ^ 3 * (3 * delta * (t - 1) - (2 * t - 3)) = 0 := by
    nlinarith [h2, h3]
  have h24 : t ^ 3 * (4 * delta * (t ^ 2 - 1) - (2 * t ^ 2 - 4)) = 0 := by
    nlinarith [h2, h4]
  have e23 : 3 * delta * (t - 1) = 2 * t - 3 := by
    have hz := (mul_eq_zero.mp h23).resolve_left (pow_ne_zero 3 ht0)
    linarith
  have e24 : 4 * delta * (t ^ 2 - 1) = 2 * t ^ 2 - 4 := by
    have hz := (mul_eq_zero.mp h24).resolve_left (pow_ne_zero 3 ht0)
    linarith
  have htpoly : t * (t - 2) = 0 := by
    nlinarith [mul_pos (sub_pos.mpr ht) (show 0 < t + 1 by nlinarith)]
  have ht2 : t = 2 := by
    rcases mul_eq_zero.mp htpoly with htzero | htminus
    · exact (ht0 htzero).elim
    · nlinarith
  subst t
  have hdelta : delta = 1 / 3 := by
    norm_num at e23 ⊢
    linarith
  subst delta
  have hw : w = 16 / 3 := by
    norm_num at h2 ⊢
    linarith
  subst w
  have halpha : alpha = 3 := by
    norm_num at h1 ⊢
    nlinarith
  exact ⟨rfl, rfl, rfl, halpha⟩

/-- Positivity of the first two coordinates already forces `t > 1`.

This removes the only externally supplied domain hypothesis from
`sixthOrderLeadingSystem_unique`: subtracting the order-two and order-three
equations gives `3 * w * (t - 1) = t^4`, whose two sides can be positive only
when `t > 1`. -/
theorem sixthOrderLeadingSystem_t_gt_one_of_pos
    {t w delta alpha : ℝ}
    (ht : 0 < t)
    (hw : 0 < w)
    (h : SixthOrderLeadingSystem t w delta alpha) :
    1 < t := by
  have h2scaled := congrArg (fun value : ℝ => 3 * t * value) h.orderTwo
  have hdiff : 3 * w * (t - 1) = t ^ 4 := by
    nlinarith [h2scaled, h.orderThree]
  by_contra hnot
  have hle : t - 1 ≤ 0 := by
    linarith
  have hprod : 3 * w * (t - 1) ≤ 0 :=
    mul_nonpos_of_nonneg_of_nonpos (by positivity) hle
  nlinarith [pow_pos ht 4]

/-- Positivity of the two shape coordinates already forces the displayed
branch; positivity of `delta` and `alpha` is a consequence, not an input. -/
theorem sixthOrderLeadingSystem_unique_of_t_w_pos
    {t w delta alpha : ℝ}
    (ht : 0 < t)
    (hw : 0 < w)
    (h : SixthOrderLeadingSystem t w delta alpha) :
    t = 2 ∧ w = 16 / 3 ∧ delta = 1 / 3 ∧ alpha = 3 := by
  exact sixthOrderLeadingSystem_unique
    (sixthOrderLeadingSystem_t_gt_one_of_pos ht hw h) h

/-- Compatibility name with the minimal positive shape hypotheses.  Positivity
of `delta` and `alpha` follows from the leading system and is not assumed. -/
theorem sixthOrderLeadingSystem_unique_positive
    {t w delta alpha : ℝ}
    (ht : 0 < t)
    (hw : 0 < w)
    (h : SixthOrderLeadingSystem t w delta alpha) :
    t = 2 ∧ w = 16 / 3 ∧ delta = 1 / 3 ∧ alpha = 3 := by
  exact sixthOrderLeadingSystem_unique_of_t_w_pos ht hw h

end Zeta23.Research.JensenWedge
