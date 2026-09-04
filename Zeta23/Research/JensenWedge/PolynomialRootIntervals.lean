import Zeta23.Research.JensenWedge.MultiplierStability

/-!
# Polynomial interval signs from a complete root list

This module formalizes the elementary real-polynomial step between a complete
ordered list of simple roots and the sign-changing intervals used by the
multiplier certificate.  No special-function input occurs here.
-/

namespace Zeta23.Research.JensenWedge

open Finset Polynomial Set

noncomputable section

/-- A degree bound together with `d` distinct listed zeros determines the
complete multiset of roots. -/
theorem roots_eq_image_of_complete_root_list
    {p : ℝ[X]} {d : ℕ} {roots : Fin d → ℝ}
    (hinj : Function.Injective roots)
    (hzeros : ∀ i, p.eval (roots i) = 0)
    (hdegree : p.natDegree ≤ d) (hp : p ≠ 0) :
    let S : Finset ℝ := Finset.univ.image roots
    p.roots = S.val ∧ p.natDegree = d ∧ p.Splits := by
  classical
  let S : Finset ℝ := Finset.univ.image roots
  have hcard : S.card = d := by
    dsimp [S]
    rw [Finset.card_image_of_injective _ hinj, Finset.card_univ,
      Fintype.card_fin]
  have hSzeros : ∀ z ∈ S, p.eval z = 0 := by
    intro z hz
    rcases Finset.mem_image.mp hz with ⟨i, _, rfl⟩
    exact hzeros i
  have hroots : p.roots = S.val :=
    Polynomial.roots_eq_of_natDegree_le_card_of_ne_zero hSzeros
      (by simpa [hcard] using hdegree) hp
  have hcard_le : S.card ≤ p.natDegree := by
    rw [Finset.card_def, ← hroots]
    exact Polynomial.card_roots' p
  have hnatDegree : p.natDegree = d := by omega
  have hsplits : p.Splits := by
    rw [Polynomial.splits_iff_card_roots, hroots, ← Finset.card_def,
      hcard, hnatDegree]
  exact ⟨hroots, hnatDegree, hsplits⟩

/-- If exactly one root lies between two nonroot endpoints, a real polynomial
with the supplied complete simple-root list changes sign there. -/
theorem eval_mul_eval_neg_of_one_root
    {p : ℝ[X]} {S : Finset ℝ} {a b r : ℝ}
    (hroots : p.roots = S.val) (hsplits : p.Splits)
    (hrS : r ∈ S) (hr : a < r ∧ r < b)
    (hother : ∀ z ∈ S, z ≠ r → 0 < (a - z) * (b - z)) :
    p.eval a * p.eval b < 0 := by
  classical
  rw [hsplits.eval_eq_prod_roots, hsplits.eval_eq_prod_roots, hroots]
  change p.leadingCoeff * (∏ z ∈ S, (a - z)) *
      (p.leadingCoeff * (∏ z ∈ S, (b - z))) < 0
  rw [show p.leadingCoeff * (∏ z ∈ S, (a - z)) *
      (p.leadingCoeff * (∏ z ∈ S, (b - z))) =
        p.leadingCoeff ^ 2 *
          ((∏ z ∈ S, (a - z)) * (∏ z ∈ S, (b - z))) by ring]
  rw [← Finset.prod_mul_distrib]
  have hrneg : (a - r) * (b - r) < 0 :=
    mul_neg_of_neg_of_pos (sub_neg.mpr hr.1) (sub_pos.mpr hr.2)
  have herase : 0 < ∏ z ∈ S.erase r, ((a - z) * (b - z)) := by
    apply Finset.prod_pos
    intro z hz
    have hzS : z ∈ S := Finset.mem_of_mem_erase hz
    have hzr : z ≠ r := Finset.ne_of_mem_erase hz
    exact hother z hzS hzr
  have hprod :
      ∏ z ∈ S, ((a - z) * (b - z)) =
        ((a - r) * (b - r)) *
          ∏ z ∈ S.erase r, ((a - z) * (b - z)) := by
    symm
    exact Finset.mul_prod_erase S
      (fun z : ℝ => (a - z) * (b - z)) hrS
  rw [hprod]
  have hlc : 0 < p.leadingCoeff ^ 2 := by
    have hmem : r ∈ p.roots := by simpa [hroots] using hrS
    have hp0 : p ≠ 0 := Polynomial.ne_zero_of_mem_roots hmem
    exact sq_pos_of_ne_zero (Polynomial.leadingCoeff_ne_zero.mpr hp0)
  exact mul_neg_of_pos_of_neg hlc
    (mul_neg_of_neg_of_pos hrneg herase)

/-- Rolle's theorem, specialized to polynomial evaluation and retaining the
open-interval location needed by the interval constructor. -/
theorem exists_polynomial_critical_between_roots
    {p : ℝ[X]} {a b : ℝ} (hab : a < b)
    (ha : p.eval a = 0) (hb : p.eval b = 0) :
    ∃ c ∈ Ioo a b, p.derivative.eval c = 0 := by
  rcases exists_deriv_eq_zero hab p.continuousOn (ha.trans hb.symm) with
    ⟨c, hc, hderiv⟩
  exact ⟨c, hc, by simpa [Polynomial.deriv] using hderiv⟩

/-- A canonical (noncomputably chosen) Rolle point between two consecutive
members of a strictly increasing complete root list. -/
def polynomialRollePoint
    {k : ℕ} (p : ℝ[X]) (roots : Fin (k + 2) → ℝ)
    (hmono : StrictMono roots) (hzeros : ∀ i, p.eval (roots i) = 0)
    (i : Fin (k + 1)) : ℝ :=
  Classical.choose (exists_polynomial_critical_between_roots
    (hmono Fin.castSucc_lt_succ) (hzeros i.castSucc) (hzeros i.succ))

theorem polynomialRollePoint_mem
    {k : ℕ} {p : ℝ[X]} {roots : Fin (k + 2) → ℝ}
    (hmono : StrictMono roots) (hzeros : ∀ i, p.eval (roots i) = 0)
    (i : Fin (k + 1)) :
    polynomialRollePoint p roots hmono hzeros i ∈
      Ioo (roots i.castSucc) (roots i.succ) :=
  (Classical.choose_spec (exists_polynomial_critical_between_roots
    (hmono Fin.castSucc_lt_succ) (hzeros i.castSucc) (hzeros i.succ))).1

theorem polynomialRollePoint_derivative
    {k : ℕ} {p : ℝ[X]} {roots : Fin (k + 2) → ℝ}
    (hmono : StrictMono roots) (hzeros : ∀ i, p.eval (roots i) = 0)
    (i : Fin (k + 1)) :
    p.derivative.eval (polynomialRollePoint p roots hmono hzeros i) = 0 :=
  (Classical.choose_spec (exists_polynomial_critical_between_roots
    (hmono Fin.castSucc_lt_succ) (hzeros i.castSucc) (hzeros i.succ))).2

theorem strictMono_polynomialRollePoint
    {k : ℕ} {p : ℝ[X]} {roots : Fin (k + 2) → ℝ}
    (hmono : StrictMono roots) (hzeros : ∀ i, p.eval (roots i) = 0) :
    StrictMono (polynomialRollePoint p roots hmono hzeros) := by
  intro i j hij
  have hi := (polynomialRollePoint_mem hmono hzeros i).2
  have hj := (polynomialRollePoint_mem hmono hzeros j).1
  have hsucc : i.succ ≤ j.castSucc := by
    apply Fin.le_iff_val_le_val.mpr
    simpa only [Fin.val_succ, Fin.val_castSucc] using
      (show i.val + 1 ≤ j.val by omega)
  exact hi.trans ((hmono.monotone hsucc).trans_lt hj)

/-- Left endpoints: zero followed by the consecutive Rolle points. -/
def polynomialRolleLeft
    {k : ℕ} {p : ℝ[X]} {roots : Fin (k + 2) → ℝ}
    (hmono : StrictMono roots) (hzeros : ∀ i, p.eval (roots i) = 0) :
    Fin (k + 2) → ℝ :=
  Fin.cons 0 (polynomialRollePoint p roots hmono hzeros)

/-- Right endpoints: the consecutive Rolle points followed by an exterior
right endpoint. -/
def polynomialRolleRight
    {k : ℕ} {p : ℝ[X]} {roots : Fin (k + 2) → ℝ}
    (hmono : StrictMono roots) (hzeros : ∀ i, p.eval (roots i) = 0)
    (right : ℝ) : Fin (k + 2) → ℝ :=
  Fin.snoc (polynomialRollePoint p roots hmono hzeros) right

theorem polynomialRolleLeft_lt_root
    {k : ℕ} {p : ℝ[X]} {roots : Fin (k + 2) → ℝ}
    (hmono : StrictMono roots) (hpos : ∀ i, 0 < roots i)
    (hzeros : ∀ i, p.eval (roots i) = 0) (i : Fin (k + 2)) :
    polynomialRolleLeft hmono hzeros i < roots i := by
  refine Fin.cases (hpos 0) (fun j ↦ ?_) i
  exact (polynomialRollePoint_mem hmono hzeros j).2

theorem root_lt_polynomialRolleRight
    {k : ℕ} {p : ℝ[X]} {roots : Fin (k + 2) → ℝ}
    (hmono : StrictMono roots) (hzeros : ∀ i, p.eval (roots i) = 0)
    {right : ℝ} (hright : roots (Fin.last (k + 1)) < right)
    (i : Fin (k + 2)) :
    roots i < polynomialRolleRight hmono hzeros right i := by
  refine Fin.lastCases ?_ (fun j ↦ ?_) i
  · simpa [polynomialRolleRight] using hright
  · simpa [polynomialRolleRight] using
      (polynomialRollePoint_mem hmono hzeros j).1

theorem root_lt_polynomialRolleLeft_of_lt
    {k : ℕ} {p : ℝ[X]} {roots : Fin (k + 2) → ℝ}
    (hmono : StrictMono roots) (hzeros : ∀ i, p.eval (roots i) = 0)
    (j i : Fin (k + 2)) (hji : j < i) :
    roots j < polynomialRolleLeft hmono hzeros i := by
  revert j
  refine Fin.cases ?_ (fun m ↦ ?_) i
  · intro j hj
    exact (Fin.not_lt_zero j hj).elim
  · intro j hj
    change j.val < m.val + 1 at hj
    have hjm : j ≤ m.castSucc := by
      apply Fin.le_iff_val_le_val.mpr
      exact (show j.val ≤ m.val by omega)
    have hroot : roots j ≤ roots m.castSucc := hmono.monotone hjm
    exact hroot.trans_lt (by
      simpa [polynomialRolleLeft] using
        (polynomialRollePoint_mem hmono hzeros m).1)

theorem polynomialRolleRight_lt_root_of_lt
    {k : ℕ} {p : ℝ[X]} {roots : Fin (k + 2) → ℝ}
    (hmono : StrictMono roots) (hzeros : ∀ i, p.eval (roots i) = 0)
    (right : ℝ) (i j : Fin (k + 2)) (hij : i < j) :
    polynomialRolleRight hmono hzeros right i < roots j := by
  revert j
  refine Fin.lastCases ?_ (fun m ↦ ?_) i
  · intro j hj
    have : (Fin.last (k + 1)).val < j.val := hj
    simp only [Fin.val_last] at this
    omega
  · intro j hj
    change m.val < j.val at hj
    have hmj : m.succ ≤ j := by
      apply Fin.le_iff_val_le_val.mpr
      exact (show m.val + 1 ≤ j.val by omega)
    have hroot : roots m.succ ≤ roots j := hmono.monotone hmj
    have hcrit : polynomialRolleRight hmono hzeros right m.castSucc <
        roots m.succ := by
      simpa [polynomialRolleRight] using
        (polynomialRollePoint_mem hmono hzeros m).2
    exact hcrit.trans_le hroot

theorem polynomialRolle_intervals_separated
    {k : ℕ} {p : ℝ[X]} {roots : Fin (k + 2) → ℝ}
    (hmono : StrictMono roots) (hzeros : ∀ i, p.eval (roots i) = 0)
    (right : ℝ) (i j : Fin (k + 2)) (hij : i < j) :
    polynomialRolleRight hmono hzeros right i ≤
      polynomialRolleLeft hmono hzeros j := by
  revert j
  refine Fin.lastCases ?_ (fun m ↦ ?_) i
  · intro j hj
    have : (Fin.last (k + 1)).val < j.val := hj
    simp only [Fin.val_last] at this
    omega
  · intro j hj
    revert m
    refine Fin.cases ?_ (fun ell ↦ ?_) j
    · intro m hm
      exact (Fin.not_lt_zero m.castSucc hm).elim
    · intro m hm
      change m.val < ell.val + 1 at hm
      have hmel : m ≤ ell := by
        apply Fin.le_iff_val_le_val.mpr
        exact (show m.val ≤ ell.val by omega)
      simpa [polynomialRolleRight, polynomialRolleLeft] using
        (strictMono_polynomialRollePoint hmono hzeros).monotone hmel

/-- The canonical Rolle intervals each contain exactly one root, hence the
comparison polynomial changes sign on every interval. -/
theorem polynomialRolle_model_change
    {k : ℕ} {p : ℝ[X]} {roots : Fin (k + 2) → ℝ}
    (hmono : StrictMono roots) (hpos : ∀ i, 0 < roots i)
    (hzeros : ∀ i, p.eval (roots i) = 0)
    (hdegree : p.natDegree ≤ k + 2) (hp : p ≠ 0)
    {right : ℝ} (hright : roots (Fin.last (k + 1)) < right)
    (i : Fin (k + 2)) :
    p.eval (polynomialRolleLeft hmono hzeros i) *
        p.eval (polynomialRolleRight hmono hzeros right i) < 0 := by
  classical
  let S : Finset ℝ := Finset.univ.image roots
  rcases roots_eq_image_of_complete_root_list hmono.injective hzeros
    hdegree hp with ⟨hroots, _, hsplits⟩
  apply eval_mul_eval_neg_of_one_root hroots hsplits
  · exact Finset.mem_image.mpr ⟨i, Finset.mem_univ i, rfl⟩
  · exact ⟨polynomialRolleLeft_lt_root hmono hpos hzeros i,
      root_lt_polynomialRolleRight hmono hzeros hright i⟩
  · intro z hzS hzne
    rcases Finset.mem_image.mp hzS with ⟨j, _, rfl⟩
    have hji : j ≠ i := by
      intro hji
      apply hzne
      rw [hji]
    rcases lt_or_gt_of_ne hji with hji | hij
    · have hza : roots j < polynomialRolleLeft hmono hzeros i :=
        root_lt_polynomialRolleLeft_of_lt hmono hzeros j i hji
      have hab : polynomialRolleLeft hmono hzeros i <
          polynomialRolleRight hmono hzeros right i :=
        (polynomialRolleLeft_lt_root hmono hpos hzeros i).trans
          (root_lt_polynomialRolleRight hmono hzeros hright i)
      exact mul_pos (sub_pos.mpr hza) (sub_pos.mpr (hza.trans hab))
    · have hbz : polynomialRolleRight hmono hzeros right i < roots j :=
        polynomialRolleRight_lt_root_of_lt hmono hzeros right i j hij
      have hab : polynomialRolleLeft hmono hzeros i <
          polynomialRolleRight hmono hzeros right i :=
        (polynomialRolleLeft_lt_root hmono hpos hzeros i).trans
          (root_lt_polynomialRolleRight hmono hzeros hright i)
      exact mul_pos_of_neg_of_neg (sub_neg.mpr (hab.trans hbz))
        (sub_neg.mpr hbz)

theorem polynomialRollePoint_eval_ne_zero
    {k : ℕ} {p : ℝ[X]} {roots : Fin (k + 2) → ℝ}
    (hmono : StrictMono roots) (hzeros : ∀ i, p.eval (roots i) = 0)
    (hdegree : p.natDegree ≤ k + 2) (hp : p ≠ 0)
    (i : Fin (k + 1)) :
    p.eval (polynomialRollePoint p roots hmono hzeros i) ≠ 0 := by
  classical
  let S : Finset ℝ := Finset.univ.image roots
  rcases roots_eq_image_of_complete_root_list hmono.injective hzeros
    hdegree hp with ⟨hroots, _, _⟩
  intro hzero
  have hmem : polynomialRollePoint p roots hmono hzeros i ∈ p.roots :=
    (Polynomial.mem_roots hp).mpr hzero
  rw [hroots] at hmem
  change polynomialRollePoint p roots hmono hzeros i ∈
    (Finset.univ.image roots).val at hmem
  have hmemS : polynomialRollePoint p roots hmono hzeros i ∈
      Finset.univ.image roots := hmem
  rcases Finset.mem_image.mp hmemS with ⟨j, _, hj⟩
  have hgap := polynomialRollePoint_mem hmono hzeros i
  by_cases hji : j ≤ i.castSucc
  · have := (hmono.monotone hji).trans_lt hgap.1
    linarith
  · have hij : i.succ ≤ j := by
      apply Fin.le_iff_val_le_val.mpr
      have hval : i.val < j.val := by
        apply Nat.lt_of_not_ge
        intro hval
        apply hji
        exact Fin.le_iff_val_le_val.mpr hval
      simpa only [Fin.val_succ] using (show i.val + 1 ≤ j.val by omega)
    have := hgap.2.trans_le (hmono.monotone hij)
    linarith

/-- The complete, reusable certificate constructor.  Once the relative error
is known at zero, at every Rolle point, and at one exterior right point, all
ordering and comparison-sign fields are kernel consequences of the complete
root list. -/
def multiplierIntervalCertificate_of_complete_roots
    {k : ℕ} {p P : ℝ[X]} {roots : Fin (k + 2) → ℝ}
    (hmono : StrictMono roots) (hpos : ∀ i, 0 < roots i)
    (hzeros : ∀ i, p.eval (roots i) = 0)
    (hdegree : p.natDegree ≤ k + 2) (hp : p ≠ 0)
    {right : ℝ} (hright : roots (Fin.last (k + 1)) < right)
    (hrelzero : |P.eval 0 / p.eval 0 - 1| < 1)
    (hrelcritical : ∀ i : Fin (k + 1),
      |P.eval (polynomialRollePoint p roots hmono hzeros i) /
          p.eval (polynomialRollePoint p roots hmono hzeros i) - 1| < 1)
    (hrelright : |P.eval right / p.eval right - 1| < 1) :
    MultiplierIntervalCertificate p.eval P.eval (k + 2) where
  a := polynomialRolleLeft hmono hzeros
  b := polynomialRolleRight hmono hzeros right
  nonnegative_left := by
    intro i
    refine Fin.cases (le_refl 0) (fun j ↦ ?_) i
    have hroot : 0 < roots j.castSucc := hpos _
    have hcrit := (polynomialRollePoint_mem hmono hzeros j).1
    simpa [polynomialRolleLeft] using hroot.le.trans hcrit.le
  ordered := by
    intro i
    exact (polynomialRolleLeft_lt_root hmono hpos hzeros i).trans
      (root_lt_polynomialRolleRight hmono hzeros hright i)
  separated := polynomialRolle_intervals_separated hmono hzeros right
  model_change := polynomialRolle_model_change hmono hpos hzeros hdegree hp hright
  relative_left := by
    intro i
    refine Fin.cases ?_ (fun j ↦ ?_) i
    · simpa [polynomialRolleLeft] using hrelzero
    · simpa [polynomialRolleLeft] using hrelcritical j
  relative_right := by
    intro i
    refine Fin.lastCases ?_ (fun j ↦ ?_) i
    · simpa [polynomialRolleRight] using hrelright
    · simpa [polynomialRolleRight] using hrelcritical j

/-- Equal-degree polynomials inherit any strict unit relative-error bound of
their leading-coefficient ratio at a sufficiently large real point. -/
theorem exists_right_relativeError_lt_one
    {p P : ℝ[X]} (hdegree : P.degree = p.degree)
    (hlead : |P.leadingCoeff / p.leadingCoeff - 1| < 1)
    (bound : ℝ) :
    ∃ right : ℝ, bound < right ∧ |P.eval right / p.eval right - 1| < 1 := by
  have htend := Polynomial.div_tendsto_atTop_leadingCoeff_div_of_degree_eq
    P p hdegree
  have hball : P.leadingCoeff / p.leadingCoeff ∈ Metric.ball (1 : ℝ) 1 := by
    simpa [Real.dist_eq] using hlead
  have heventual : ∀ᶠ x in Filter.atTop,
      |P.eval x / p.eval x - 1| < 1 := by
    have hmem := htend.eventually (Metric.isOpen_ball.mem_nhds hball)
    filter_upwards [hmem] with x hx
    simpa [Real.dist_eq] using hx
  have hboth : ∀ᶠ right in Filter.atTop,
      bound < right ∧ |P.eval right / p.eval right - 1| < 1 := by
    filter_upwards [heventual, Filter.eventually_gt_atTop bound] with
      right hrel hright
    exact ⟨hright, hrel⟩
  exact hboth.exists

end

end Zeta23.Research.JensenWedge
