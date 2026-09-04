import Zeta23.Research.JensenWedge.XiNaturalLogIntegerBridge
import Zeta23.Research.JensenWedge.XiNaturalLogErrorForwardDifferences

/-!
# Exact decomposition of the four natural xi log coordinates

This file turns the integer-node logarithm identification into the form used
by the finite interval certificate.  A single explicit lower bound on `n`
puts all six samples in the paired coefficient sector.  The resulting four
coordinates split exactly into forward differences of the explicit natural
main and forward differences of the controlled logarithmic error.
-/

namespace Zeta23.Research.JensenWedge

open Complex Set

noncomputable section

/-- Every sufficiently large positive integer belongs to the paired
coefficient sector. -/
theorem nat_mem_leanXiCoefficientSector
    {m : ℕ} (hm : Real.exp (leanSaddleCutoff + 2) < (m : ℝ)) :
    (m : ℂ) ∈ leanXiCoefficientSector := by
  apply manuscriptCauchy_closedBall_subset_sector hm
  rw [Metric.mem_closedBall, Complex.ofReal_natCast, dist_self]
  unfold manuscriptCauchyRadius
  exact div_nonneg (Nat.cast_nonneg m) (by norm_num)

/-- One lower bound at the left endpoint supplies all six integer samples
needed by the four certificate coordinates. -/
theorem nat_six_samples_mem_leanXiCoefficientSector
    {n : ℕ} (hn : Real.exp (leanSaddleCutoff + 2) < (n : ℝ)) :
    ∀ j : ℕ, j ≤ 5 → ((n + j : ℕ) : ℂ) ∈ leanXiCoefficientSector := by
  intro j _hj
  apply nat_mem_leanXiCoefficientSector
  apply hn.trans_le
  exact_mod_cast Nat.le_add_right n j

theorem complexForwardDiff_add
    (q : ℕ) (f g : ℂ → ℂ) (z : ℂ) :
    complexForwardDiff q (fun w => f w + g w) z =
      complexForwardDiff q f z + complexForwardDiff q g z := by
  induction q generalizing z with
  | zero => simp [complexForwardDiff]
  | succ q ih =>
      simp only [complexForwardDiff]
      rw [ih, ih]
      ring

theorem complexForwardDiff_comp_forwardDiff
    (p q : ℕ) (f : ℂ → ℂ) (z : ℂ) :
    complexForwardDiff p (complexForwardDiff q f) z =
      complexForwardDiff (p + q) f z := by
  induction p generalizing z with
  | zero => simp [complexForwardDiff]
  | succ p ih =>
      simp only [complexForwardDiff]
      rw [ih, ih]
      simpa [Nat.succ_add] using
        (show complexForwardDiff (p + q) f (z + 1) -
            complexForwardDiff (p + q) f z =
          complexForwardDiff ((p + q) + 1) f z by rfl)

theorem complexXiNaturalAuxiliarySecondDiff_eq_forwardDiff
    (m : ℕ) :
    complexXiNaturalAuxiliarySecondDiff m =
      complexForwardDiff 2 complexXiNaturalAuxiliaryLog (m : ℂ) := by
  simp [complexXiNaturalAuxiliarySecondDiff, complexForwardDiff]
  ring

private theorem complexNatForwardDiff0_second_eq
    (f : ℂ → ℂ) (n : ℕ) :
    complexNatForwardDiff0
        (fun k => complexForwardDiff 2 f (n + k : ℕ)) =
      complexForwardDiff 2 f (n : ℂ) := by
  simp [complexNatForwardDiff0]

private theorem complexNatForwardDiff1_second_eq
    (f : ℂ → ℂ) (n : ℕ) :
    complexNatForwardDiff1
        (fun k => complexForwardDiff 2 f (n + k : ℕ)) =
      complexForwardDiff 3 f (n : ℂ) := by
  simp [complexNatForwardDiff1, complexForwardDiff]

private theorem complexNatForwardDiff2_second_eq
    (f : ℂ → ℂ) (n : ℕ) :
    complexNatForwardDiff2
        (fun k => complexForwardDiff 2 f (n + k : ℕ)) =
      complexForwardDiff 4 f (n : ℂ) := by
  simp [complexNatForwardDiff2, complexForwardDiff]
  ring

private theorem complexNatForwardDiff3_second_eq
    (f : ℂ → ℂ) (n : ℕ) :
    complexNatForwardDiff3
        (fun k => complexForwardDiff 2 f (n + k : ℕ)) =
      complexForwardDiff 5 f (n : ℂ) := by
  simp [complexNatForwardDiff3, complexForwardDiff]
  ring

private theorem complexNatForwardDiff0_naturalSecond_eq
    (n : ℕ) :
    complexNatForwardDiff0
        (fun k => complexXiNaturalAuxiliarySecondDiff (n + k)) =
      complexForwardDiff 2 complexXiNaturalAuxiliaryLog (n : ℂ) := by
  simp only [complexNatForwardDiff0]
  rw [complexXiNaturalAuxiliarySecondDiff_eq_forwardDiff]
  simp

private theorem complexNatForwardDiff1_naturalSecond_eq
    (n : ℕ) :
    complexNatForwardDiff1
        (fun k => complexXiNaturalAuxiliarySecondDiff (n + k)) =
      complexForwardDiff 3 complexXiNaturalAuxiliaryLog (n : ℂ) := by
  rw [show (fun k => complexXiNaturalAuxiliarySecondDiff (n + k)) =
      (fun k => complexForwardDiff 2 complexXiNaturalAuxiliaryLog
        (n + k : ℕ)) by
    funext k
    exact complexXiNaturalAuxiliarySecondDiff_eq_forwardDiff (n + k)]
  exact complexNatForwardDiff1_second_eq _ _

private theorem complexNatForwardDiff2_naturalSecond_eq
    (n : ℕ) :
    complexNatForwardDiff2
        (fun k => complexXiNaturalAuxiliarySecondDiff (n + k)) =
      complexForwardDiff 4 complexXiNaturalAuxiliaryLog (n : ℂ) := by
  rw [show (fun k => complexXiNaturalAuxiliarySecondDiff (n + k)) =
      (fun k => complexForwardDiff 2 complexXiNaturalAuxiliaryLog
        (n + k : ℕ)) by
    funext k
    exact complexXiNaturalAuxiliarySecondDiff_eq_forwardDiff (n + k)]
  exact complexNatForwardDiff2_second_eq _ _

private theorem complexNatForwardDiff3_naturalSecond_eq
    (n : ℕ) :
    complexNatForwardDiff3
        (fun k => complexXiNaturalAuxiliarySecondDiff (n + k)) =
      complexForwardDiff 5 complexXiNaturalAuxiliaryLog (n : ℂ) := by
  rw [show (fun k => complexXiNaturalAuxiliarySecondDiff (n + k)) =
      (fun k => complexForwardDiff 2 complexXiNaturalAuxiliaryLog
        (n + k : ℕ)) by
    funext k
    exact complexXiNaturalAuxiliarySecondDiff_eq_forwardDiff (n + k)]
  exact complexNatForwardDiff3_second_eq _ _

private theorem naturalLog_forwardDiff_decomposition
    (q : ℕ) (n : ℕ) :
    complexForwardDiff q complexXiNaturalAuxiliaryLog (n : ℂ) =
      complexForwardDiff q complexXiNaturalAuxiliaryLogMain (n : ℂ) +
        complexForwardDiff q complexXiNaturalAuxiliaryLogError (n : ℂ) := by
  rw [show complexXiNaturalAuxiliaryLog = fun z =>
      complexXiNaturalAuxiliaryLogMain z +
        complexXiNaturalAuxiliaryLogError z by
    funext z
    rfl]
  exact complexForwardDiff_add q _ _ _

/-- The four exact real xi coordinates are the sum of orders two through
five of the explicit natural main and its holomorphic logarithmic error.
The sector hypotheses have been reduced to one explicit lower bound on `n`.
-/
theorem ofReal_exactXiAuxiliarySecondDiff_forwardDiffs_decomposition
    {n : ℕ} (hn : Real.exp (leanSaddleCutoff + 2) < (n : ℝ)) :
    ((natForwardDiff0 (exactXiAuxiliarySecondDiff n) : ℝ) : ℂ) =
        complexForwardDiff 2 complexXiNaturalAuxiliaryLogMain (n : ℂ) +
          complexForwardDiff 2 complexXiNaturalAuxiliaryLogError (n : ℂ) ∧
    ((natForwardDiff1 (exactXiAuxiliarySecondDiff n) : ℝ) : ℂ) =
        complexForwardDiff 3 complexXiNaturalAuxiliaryLogMain (n : ℂ) +
          complexForwardDiff 3 complexXiNaturalAuxiliaryLogError (n : ℂ) ∧
    ((natForwardDiff2 (exactXiAuxiliarySecondDiff n) : ℝ) : ℂ) =
        complexForwardDiff 4 complexXiNaturalAuxiliaryLogMain (n : ℂ) +
          complexForwardDiff 4 complexXiNaturalAuxiliaryLogError (n : ℂ) ∧
    ((natForwardDiff3 (exactXiAuxiliarySecondDiff n) : ℝ) : ℂ) =
        complexForwardDiff 5 complexXiNaturalAuxiliaryLogMain (n : ℂ) +
          complexForwardDiff 5 complexXiNaturalAuxiliaryLogError (n : ℂ) := by
  have hnpos : 0 < n := by
    have : (0 : ℝ) < n := (Real.exp_pos _).trans hn
    exact_mod_cast this
  have hbridge :=
    ofReal_exactXiAuxiliarySecondDiff_forwardDiffs_natural hnpos
      (nat_six_samples_mem_leanXiCoefficientSector hn)
  constructor
  · rw [hbridge.1]
    rw [complexNatForwardDiff0_naturalSecond_eq,
      naturalLog_forwardDiff_decomposition]
  constructor
  · rw [hbridge.2.1]
    rw [complexNatForwardDiff1_naturalSecond_eq,
      naturalLog_forwardDiff_decomposition]
  constructor
  · rw [hbridge.2.2.1]
    rw [complexNatForwardDiff2_naturalSecond_eq,
      naturalLog_forwardDiff_decomposition]
  · rw [hbridge.2.2.2]
    rw [complexNatForwardDiff3_naturalSecond_eq,
      naturalLog_forwardDiff_decomposition]

/-- Explicit Cauchy bounds for the four error terms appearing in the exact
decomposition. -/
theorem complexXiNaturalAuxiliaryLogError_certificate_bounds
    {n : ℕ} (hn : Real.exp (leanSaddleCutoff + 2) < (n : ℝ)) :
    ‖complexForwardDiff 2 complexXiNaturalAuxiliaryLogError (n : ℂ)‖ ≤
        (2 : ℕ).factorial * ((3 / 2 : ℝ) * naturalXiCauchyEpsilon (n : ℝ)) /
          manuscriptInteriorCauchyRadius (n : ℝ) ^ 2 ∧
    ‖complexForwardDiff 3 complexXiNaturalAuxiliaryLogError (n : ℂ)‖ ≤
        (3 : ℕ).factorial * ((3 / 2 : ℝ) * naturalXiCauchyEpsilon (n : ℝ)) /
          manuscriptInteriorCauchyRadius (n : ℝ) ^ 3 ∧
    ‖complexForwardDiff 4 complexXiNaturalAuxiliaryLogError (n : ℂ)‖ ≤
        (4 : ℕ).factorial * ((3 / 2 : ℝ) * naturalXiCauchyEpsilon (n : ℝ)) /
          manuscriptInteriorCauchyRadius (n : ℝ) ^ 4 ∧
    ‖complexForwardDiff 5 complexXiNaturalAuxiliaryLogError (n : ℂ)‖ ≤
        (5 : ℕ).factorial * ((3 / 2 : ℝ) * naturalXiCauchyEpsilon (n : ℝ)) /
          manuscriptInteriorCauchyRadius (n : ℝ) ^ 5 := by
  exact ⟨complexXiNaturalAuxiliaryLogError_forwardDiff_bound hn (by norm_num),
    complexXiNaturalAuxiliaryLogError_forwardDiff_bound hn (by norm_num),
    complexXiNaturalAuxiliaryLogError_forwardDiff_bound hn (by norm_num),
    complexXiNaturalAuxiliaryLogError_forwardDiff_bound hn (by norm_num)⟩

end

end Zeta23.Research.JensenWedge
