import Zeta23.Research.JensenWedge.XiCoefficientPositivity

/-!
# Integer bridge to the holomorphic coefficient logarithm

Strict positivity fixes the logarithm at every integer coefficient.  This
module identifies the real discrete logarithms used by the exact branch map
with principal complex logarithms of the holomorphic coefficient moment and
transports the second and higher forward differences without changing any
sign or binomial coefficient.
-/

namespace Zeta23.Research.JensenWedge

open Complex

noncomputable section

/-- Principal logarithm of the exact holomorphic coefficient continuation,
sampled at natural arguments. -/
def complexXiDiscreteCoefficientLog (m : ℕ) : ℂ :=
  log (complexXiCoefficientMoment (m : ℂ))

/-- At every positive integer the real exact coefficient logarithm is
literally the complex principal logarithm of the continued moment. -/
theorem ofReal_exactXiCoefficientLog_eq_complex_of_pos
    {m : ℕ} (hm : 0 < m) :
    (exactXiCoefficientLog m : ℂ) = complexXiDiscreteCoefficientLog m := by
  obtain ⟨q, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hm)
  unfold exactXiCoefficientLog complexXiDiscreteCoefficientLog
  rw [complexXiCoefficientMoment_nat_succ, ← ofReal_riemannXiCoefficientReal]
  exact Complex.ofReal_log (riemannXiCoefficientReal_pos (q + 1)).le

/-- Complex second forward difference of the sampled holomorphic log. -/
def complexXiSecondDiff (m : ℕ) : ℂ :=
  complexXiDiscreteCoefficientLog (m + 2) -
    2 * complexXiDiscreteCoefficientLog (m + 1) +
      complexXiDiscreteCoefficientLog m

def complexNatForwardDiff0 (f : ℕ → ℂ) : ℂ := f 0
def complexNatForwardDiff1 (f : ℕ → ℂ) : ℂ := f 1 - f 0
def complexNatForwardDiff2 (f : ℕ → ℂ) : ℂ := f 2 - 2 * f 1 + f 0
def complexNatForwardDiff3 (f : ℕ → ℂ) : ℂ :=
  f 3 - 3 * f 2 + 3 * f 1 - f 0

/-- The real second difference is the complex second difference at every
positive base index. -/
theorem ofReal_secondDiff_exactXiCoefficientLog
    {m : ℕ} (hm : 0 < m) :
    (secondDiff exactXiCoefficientLog m : ℂ) = complexXiSecondDiff m := by
  have hm1 : 0 < m + 1 := by omega
  have hm2 : 0 < m + 2 := by omega
  rw [secondDiff, complexXiSecondDiff]
  push_cast
  rw [ofReal_exactXiCoefficientLog_eq_complex_of_pos hm,
    ofReal_exactXiCoefficientLog_eq_complex_of_pos hm1,
    ofReal_exactXiCoefficientLog_eq_complex_of_pos hm2]

/-- Zeroth through third forward differences commute with the exact
integer-to-holomorphic logarithm bridge. -/
theorem ofReal_exactXi_secondDiff_forwardDiffs
    {n : ℕ} (hn : 0 < n) :
    ((natForwardDiff0 (fun k => secondDiff exactXiCoefficientLog (n + k)) : ℝ) : ℂ) =
        complexNatForwardDiff0 (fun k => complexXiSecondDiff (n + k)) ∧
    ((natForwardDiff1 (fun k => secondDiff exactXiCoefficientLog (n + k)) : ℝ) : ℂ) =
        complexNatForwardDiff1 (fun k => complexXiSecondDiff (n + k)) ∧
    ((natForwardDiff2 (fun k => secondDiff exactXiCoefficientLog (n + k)) : ℝ) : ℂ) =
        complexNatForwardDiff2 (fun k => complexXiSecondDiff (n + k)) ∧
    ((natForwardDiff3 (fun k => secondDiff exactXiCoefficientLog (n + k)) : ℝ) : ℂ) =
        complexNatForwardDiff3 (fun k => complexXiSecondDiff (n + k)) := by
  have h (k : ℕ) :
      ((secondDiff exactXiCoefficientLog (n + k) : ℝ) : ℂ) =
        complexXiSecondDiff (n + k) :=
    ofReal_secondDiff_exactXiCoefficientLog (by omega)
  constructor
  · simpa [natForwardDiff0, complexNatForwardDiff0] using h 0
  constructor
  · simp only [natForwardDiff1, complexNatForwardDiff1]
    push_cast
    rw [h 1, h 0]
  constructor
  · simp only [natForwardDiff2, complexNatForwardDiff2]
    push_cast
    rw [h 2, h 1, h 0]
  · simp only [natForwardDiff3, complexNatForwardDiff3]
    push_cast
    rw [h 3, h 2, h 1, h 0]

end

end Zeta23.Research.JensenWedge
