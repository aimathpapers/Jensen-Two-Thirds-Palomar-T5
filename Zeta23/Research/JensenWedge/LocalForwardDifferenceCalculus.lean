import Zeta23.Research.JensenWedge.ForwardDifferenceCalculus

/-!
# Local forward-difference calculus on real intervals

The coefficient estimates are holomorphic only on a fixed sector.  This
module localizes the repeated-FTC adapter: only the real interval swept out
by the unit forward difference must lie in the derivative domain.
-/

namespace Zeta23.Research.JensenWedge

open Set
open scoped Interval

noncomputable section

theorem complexSegment_real_add_one (x t : ℝ) :
    complexSegment (x : ℂ) ((x + 1 : ℝ) : ℂ) t = ((x + t : ℝ) : ℂ) := by
  simp only [complexSegment, AffineMap.lineMap_apply_module']
  simp only [Complex.real_smul]
  push_cast
  ring

/-- Local form of complex FTC; derivative information is required only on
the unit parameter interval used by the integral. -/
theorem complexSegment_integral_deriv_of_uIcc
    (f f' : ℂ → ℂ) (x y : ℂ)
    (hf : ∀ t ∈ Set.uIcc (0 : ℝ) 1,
      HasDerivAt f (f' (complexSegment x y t)) (complexSegment x y t))
    (hint : IntervalIntegrable
      (fun t : ℝ => (y - x) * f' (complexSegment x y t))
      MeasureTheory.volume 0 1) :
    (∫ t : ℝ in 0..1, (y - x) * f' (complexSegment x y t)) = f y - f x := by
  have hderiv : ∀ t ∈ Set.uIcc (0 : ℝ) 1,
      HasDerivAt (fun s : ℝ => f (complexSegment x y s))
        ((y - x) * f' (complexSegment x y t)) t := by
    intro t ht
    have hcomp := (hf t ht).scomp t (hasDerivAt_complexSegment x y t)
    simpa [Function.comp_def, smul_eq_mul] using hcomp
  simpa [complexSegment] using
    intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint

/-- Forward differences commute with a derivative tower when the finitely
many real translates used by that difference lie in the local domain. -/
theorem hasDerivAt_complexForwardDiff_on_real
    (derivs : ℕ → ℂ → ℂ) (S : Set ℝ)
    (hderiv : ∀ r y, y ∈ S →
      HasDerivAt (derivs r) (derivs (r + 1) (y : ℂ)) (y : ℂ))
    (q r : ℕ) (x : ℝ)
    (hpoints : ∀ j ≤ q, x + (j : ℝ) ∈ S) :
    HasDerivAt (complexForwardDiff q (derivs r))
      (complexForwardDiff q (derivs (r + 1)) (x : ℂ)) (x : ℂ) := by
  induction q generalizing r x with
  | zero =>
      have hx : x ∈ S := by simpa using hpoints 0 (Nat.zero_le _)
      simpa [complexForwardDiff] using hderiv r x hx
  | succ q ih =>
      have hbasePoints : ∀ j ≤ q, x + (j : ℝ) ∈ S := by
        intro j hj
        exact hpoints j (hj.trans (Nat.le_succ q))
      have hshiftPoints : ∀ j ≤ q, (x + 1) + (j : ℝ) ∈ S := by
        intro j hj
        convert hpoints (j + 1) (Nat.succ_le_succ hj) using 1 <;>
          push_cast <;> ring
      have hshiftAt := ih (r := r) (x := x + 1) hshiftPoints
      have hcast : (((x + 1 : ℝ) : ℂ)) = (x : ℂ) + 1 := by
        push_cast
        ring
      rw [hcast] at hshiftAt
      have hshift : HasDerivAt
          (fun w : ℂ => complexForwardDiff q (derivs r) (w + 1))
          (complexForwardDiff q (derivs (r + 1)) ((x : ℂ) + 1)) (x : ℂ) := by
        simpa [Function.comp_def] using hshiftAt.comp (x : ℂ)
          ((hasDerivAt_id (x : ℂ)).add_const 1)
      have hbase := ih (r := r) (x := x) hbasePoints
      change HasDerivAt
        ((fun w : ℂ => complexForwardDiff q (derivs r) (w + 1)) -
          complexForwardDiff q (derivs r))
        (complexForwardDiff q (derivs (r + 1)) ((x : ℂ) + 1) -
          complexForwardDiff q (derivs (r + 1)) (x : ℂ)) (x : ℂ)
      exact hshift.sub hbase

/-- Local repeated-FTC adapter. A derivative bound on the real interval
`[x,x+q]` controls the order-`q` forward difference at `x`, with the same
constant and no factorial loss. -/
theorem norm_complexForwardDiff_sub_constant_le_on_real_interval
    (derivs : ℕ → ℂ → ℂ)
    (q r : ℕ) (x : ℝ) (c : ℂ) {M : ℝ}
    (hderiv : ∀ s y, y ∈ Set.Icc x (x + (q : ℝ)) →
      HasDerivAt (derivs s) (derivs (s + 1) (y : ℂ)) (y : ℂ))
    (hbound : ∀ y, y ∈ Set.Icc x (x + (q : ℝ)) →
      ‖derivs (r + q) (y : ℂ) - c‖ ≤ M) :
    ‖complexForwardDiff q (derivs r) (x : ℂ) - c‖ ≤ M := by
  induction q generalizing r x with
  | zero =>
      apply hbound x
      simp
  | succ q ih =>
      let S : Set ℝ := Set.Icc x (x + ((q + 1 : ℕ) : ℝ))
      let g : ℂ → ℂ := complexForwardDiff q (derivs r)
      let g' : ℂ → ℂ := complexForwardDiff q (derivs (r + 1))
      have ht_bounds : ∀ {t : ℝ}, t ∈ Set.uIcc (0 : ℝ) 1 →
          0 ≤ t ∧ t ≤ 1 := by
        intro t ht
        change min (0 : ℝ) 1 ≤ t ∧ t ≤ max (0 : ℝ) 1 at ht
        simpa using ht
      have hpoints : ∀ {t : ℝ}, t ∈ Set.uIcc (0 : ℝ) 1 →
          ∀ j ≤ q, x + t + (j : ℝ) ∈ S := by
        intro t ht j hj
        rcases ht_bounds ht with ⟨ht0, ht1⟩
        have hj0 : (0 : ℝ) ≤ j := Nat.cast_nonneg j
        have hjq : (j : ℝ) ≤ q := by exact_mod_cast hj
        change x ≤ x + t + (j : ℝ) ∧
          x + t + (j : ℝ) ≤ x + ((q + 1 : ℕ) : ℝ)
        constructor <;> push_cast <;> nlinarith
      have hg : ∀ t ∈ Set.uIcc (0 : ℝ) 1,
          HasDerivAt g (g' (complexSegment (x : ℂ) ((x + 1 : ℝ) : ℂ) t))
            (complexSegment (x : ℂ) ((x + 1 : ℝ) : ℂ) t) := by
        intro t ht
        rw [complexSegment_real_add_one]
        exact hasDerivAt_complexForwardDiff_on_real derivs S hderiv q r
          (x + t) (hpoints ht)
      have hg'continuous : ContinuousOn
          (fun t : ℝ => g' (complexSegment (x : ℂ) ((x + 1 : ℝ) : ℂ) t))
          (Set.uIcc (0 : ℝ) 1) := by
        intro t ht
        have hlocal := hasDerivAt_complexForwardDiff_on_real derivs S hderiv
          q (r + 1) (x + t) (hpoints ht)
        have hsegment := (hasDerivAt_complexSegment
          (x : ℂ) ((x + 1 : ℝ) : ℂ) t).continuousAt
        have hlocal' : ContinuousAt g'
            (complexSegment (x : ℂ) ((x + 1 : ℝ) : ℂ) t) := by
          rw [complexSegment_real_add_one]
          exact hlocal.continuousAt
        exact (hlocal'.comp hsegment).continuousWithinAt
      have hint : IntervalIntegrable
          (fun t : ℝ => (((x + 1 : ℝ) : ℂ) - (x : ℂ)) *
            g' (complexSegment (x : ℂ) ((x + 1 : ℝ) : ℂ) t))
          MeasureTheory.volume 0 1 := by
        apply ContinuousOn.intervalIntegrable
        exact continuousOn_const.mul hg'continuous
      have hFTC := complexSegment_integral_deriv_of_uIcc g g'
        (x : ℂ) ((x + 1 : ℝ) : ℂ) hg hint
      have hIntegral :
          (∫ t : ℝ in (0 : ℝ)..1,
              g' (complexSegment (x : ℂ) ((x + 1 : ℝ) : ℂ) t)) =
            g ((x : ℂ) + 1) - g (x : ℂ) := by
        simpa using hFTC
      have havg : ∀ t ∈ Set.uIcc (0 : ℝ) 1,
          ‖g' (complexSegment (x : ℂ) ((x + 1 : ℝ) : ℂ) t) - c‖ ≤ M := by
        intro t ht
        rw [complexSegment_real_add_one]
        apply ih (r := r + 1) (x := x + t)
        · intro s y hy
          apply hderiv s y
          rcases ht_bounds ht with ⟨ht0, ht1⟩
          rcases hy with ⟨hy0, hy1⟩
          constructor <;> push_cast at hy1 ⊢ <;> nlinarith
        · intro y hy
          have htop : r + 1 + q = r + (q + 1) := by omega
          rw [htop]
          apply hbound y
          rcases ht_bounds ht with ⟨ht0, ht1⟩
          rcases hy with ⟨hy0, hy1⟩
          constructor <;> push_cast at hy1 ⊢ <;> nlinarith
      have hsubInt :
          (∫ t : ℝ in (0 : ℝ)..1,
              (g' (complexSegment (x : ℂ) ((x + 1 : ℝ) : ℂ) t) - c)) =
            (∫ t : ℝ in (0 : ℝ)..1,
              g' (complexSegment (x : ℂ) ((x + 1 : ℝ) : ℂ) t)) - c := by
        rw [intervalIntegral.integral_sub]
        · simp
        · exact hg'continuous.intervalIntegrable
        · exact continuousOn_const.intervalIntegrable
      rw [complexForwardDiff, ← hIntegral, ← hsubInt]
      calc
        ‖∫ t : ℝ in (0 : ℝ)..1,
            (g' (complexSegment (x : ℂ) ((x + 1 : ℝ) : ℂ) t) - c)‖ ≤
            M * |(1 : ℝ) - 0| := by
          apply intervalIntegral.norm_integral_le_of_norm_le_const
          intro t ht
          apply havg t
          change min (0 : ℝ) 1 ≤ t ∧ t ≤ max (0 : ℝ) 1
          constructor
          · simpa using ht.1.le
          · simpa using ht.2
        _ = M := by simp

end

end Zeta23.Research.JensenWedge
