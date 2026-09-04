import Zeta23.Research.JensenWedge.XiCoefficientLogBridge
import Zeta23.Research.JensenWedge.ComplexHermiteGenocchi

/-!
# Complex forward-difference calculus

Repeated complex FTC shows that a unit-step forward difference of order `q`
is an average of the `q`th derivative.  The form below is quantitative: if
the derivative stays within `M` of a fixed constant, then the forward
difference stays within the same `M`, with no factorial loss.
-/

namespace Zeta23.Research.JensenWedge

open scoped Interval

noncomputable section

/-- Recursive unit-step forward difference for complex-valued functions. -/
def complexForwardDiff : ℕ → (ℂ → ℂ) → ℂ → ℂ
  | 0, f, z => f z
  | q + 1, f, z => complexForwardDiff q f (z + 1) - complexForwardDiff q f z

/-- Forward differences commute with a global complex derivative tower. -/
theorem hasDerivAt_complexForwardDiff
    (derivs : ℕ → ℂ → ℂ)
    (hderiv : ∀ r z, HasDerivAt (derivs r) (derivs (r + 1) z) z)
    (q r : ℕ) (z : ℂ) :
    HasDerivAt (complexForwardDiff q (derivs r))
      (complexForwardDiff q (derivs (r + 1)) z) z := by
  induction q generalizing r z with
  | zero => simpa [complexForwardDiff] using hderiv r z
  | succ q ih =>
      have hshift : HasDerivAt
          (fun w : ℂ => complexForwardDiff q (derivs r) (w + 1))
          (complexForwardDiff q (derivs (r + 1)) (z + 1)) z := by
        simpa [Function.comp_def] using
          (ih r (z + 1)).comp z ((hasDerivAt_id z).add_const 1)
      have hbase := ih r z
      change HasDerivAt
        ((fun w : ℂ => complexForwardDiff q (derivs r) (w + 1)) -
          complexForwardDiff q (derivs r))
        (complexForwardDiff q (derivs (r + 1)) (z + 1) -
          complexForwardDiff q (derivs (r + 1)) z) z
      exact hshift.sub hbase

/-- A derivative tower is continuous at every level. -/
theorem continuous_complexDerivativeTower
    (derivs : ℕ → ℂ → ℂ)
    (hderiv : ∀ r z, HasDerivAt (derivs r) (derivs (r + 1) z) z)
    (r : ℕ) : Continuous (derivs r) :=
  continuous_iff_continuousAt.2 fun z => (hderiv r z).continuousAt

/-- Quantitative repeated-FTC adapter.  A uniform bound
`||f^(r+q)-c|| <= M` yields the same bound for the order-`q` unit forward
difference of `f^(r)`. -/
theorem norm_complexForwardDiff_sub_constant_le
    (derivs : ℕ → ℂ → ℂ)
    (hderiv : ∀ r z, HasDerivAt (derivs r) (derivs (r + 1) z) z)
    (q r : ℕ) (z c : ℂ) {M : ℝ}
    (hbound : ∀ w, ‖derivs (r + q) w - c‖ ≤ M) :
    ‖complexForwardDiff q (derivs r) z - c‖ ≤ M := by
  induction q generalizing r z with
  | zero => simpa [complexForwardDiff] using hbound z
  | succ q ih =>
      let g : ℂ → ℂ := complexForwardDiff q (derivs r)
      let g' : ℂ → ℂ := complexForwardDiff q (derivs (r + 1))
      have hg : ∀ w, HasDerivAt g (g' w) w := by
        intro w
        exact hasDerivAt_complexForwardDiff derivs hderiv q r w
      have hg' : Continuous g' :=
        continuous_iff_continuousAt.2 fun w => (hasDerivAt_complexForwardDiff
          derivs hderiv q (r + 1) w).continuousAt
      have hsegment : Continuous (fun t : ℝ => complexSegment z (z + 1) t) :=
        continuous_iff_continuousAt.2 fun t =>
          (hasDerivAt_complexSegment z (z + 1) t).continuousAt
      have hint : IntervalIntegrable
          (fun t : ℝ => ((z + 1) - z) * g' (complexSegment z (z + 1) t))
          MeasureTheory.volume 0 1 := by
        apply Continuous.intervalIntegrable
        exact continuous_const.mul (hg'.comp hsegment)
      have hFTC := complexSegment_integral_deriv g g' z (z + 1)
        (fun _ => hg _) hint
      have hIntegral :
          (∫ t : ℝ in (0 : ℝ)..1, g' (complexSegment z (z + 1) t)) =
            g (z + 1) - g z := by
        simpa using hFTC
      have hbound' : ∀ w, ‖derivs ((r + 1) + q) w - c‖ ≤ M := by
        intro w
        simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hbound w
      have havg : ∀ t ∈ Set.uIcc (0 : ℝ) 1,
          ‖g' (complexSegment z (z + 1) t) - c‖ ≤ M := by
        intro t _ht
        exact ih (r + 1) (complexSegment z (z + 1) t) hbound'
      have hsubInt :
          (∫ t : ℝ in (0 : ℝ)..1,
              (g' (complexSegment z (z + 1) t) - c)) =
            (∫ t : ℝ in (0 : ℝ)..1,
              g' (complexSegment z (z + 1) t)) - c := by
        rw [intervalIntegral.integral_sub]
        · simp
        · exact (hg'.comp hsegment).intervalIntegrable 0 1
        · exact continuous_const.intervalIntegrable 0 1
      rw [complexForwardDiff, ← hIntegral, ← hsubInt]
      calc
        ‖∫ t : ℝ in (0 : ℝ)..1,
            (g' (complexSegment z (z + 1) t) - c)‖ ≤
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
