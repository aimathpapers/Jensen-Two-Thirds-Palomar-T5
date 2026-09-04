import Zeta23.Research.JensenWedge.MultiplierStability

/-!
# Conditional assembly of the two-thirds Jensen wedge

This module is the proof firewall between the analytic/special-function
inputs and the advertised root conclusion.  A `JensenWedgeCertificate`
contains only concrete comparison, relative-error, interval, continuity, and
scaling data.  From those data Lean proves that the target Jensen polynomial
has the required number of distinct negative roots.

The module deliberately does not assert that the Riemann-xi coefficients
supply such a certificate.  The sectorial saddle estimate, exact parameter
branch, finite-free positivity, and residual bound must be proved separately
and then used to construct the certificate.
-/

namespace Zeta23.Research.JensenWedge

/-- The proposed sixth-order wedge, written without hiding its coercions. -/
def TwoThirdsWedge (K : ℝ) (n d : ℕ) : Prop :=
  K * (d : ℝ) ^ 3 ≤ (n : ℝ) ^ 2 * Real.log (n + 2 : ℝ)

/-- A deliberately coarse constant that makes the two-thirds wedge empty
below a fixed analytic cutoff.  This is the finite-range absorption used in
the paper's passage from an effective-cutoff theorem to one existential
global constant. -/
def finiteCutoffAbsorptionConstant (N : ℕ) : ℝ :=
  (N : ℝ) ^ 2 * ((N : ℝ) + 2) + 1

/-- If `n < N` and the degree is positive, the wedge with the finite-cutoff
absorption constant is impossible.  No finite Jensen-polynomial computation
is being hidden here: the antecedent is empty in this range. -/
theorem not_twoThirdsWedge_finiteCutoffAbsorption
    {N n d : ℕ} (hn : n < N) (hd : 0 < d) :
    ¬ TwoThirdsWedge (finiteCutoffAbsorptionConstant N) n d := by
  intro hW
  have hnle : n ≤ N := Nat.le_of_lt hn
  have hnleR : (n : ℝ) ≤ N := by exact_mod_cast hnle
  have hn0 : (0 : ℝ) ≤ n := by positivity
  have hN0 : (0 : ℝ) ≤ N := by positivity
  have hd1 : (1 : ℝ) ≤ d := by exact_mod_cast hd
  have hlog0 : 0 ≤ Real.log ((n : ℝ) + 2) := by
    exact Real.log_nonneg (by linarith)
  have hlog : Real.log ((n : ℝ) + 2) ≤ (n : ℝ) + 1 := by
    have h := Real.log_le_sub_one_of_pos
      (show (0 : ℝ) < (n : ℝ) + 2 by positivity)
    linarith
  have hsq : (n : ℝ) ^ 2 ≤ (N : ℝ) ^ 2 := by nlinarith
  have hfactor : (n : ℝ) + 1 ≤ (N : ℝ) + 2 := by linarith
  have hmain :
      (n : ℝ) ^ 2 * Real.log ((n : ℝ) + 2) ≤
        (N : ℝ) ^ 2 * ((N : ℝ) + 2) := by
    calc
      (n : ℝ) ^ 2 * Real.log ((n : ℝ) + 2) ≤
          (n : ℝ) ^ 2 * ((n : ℝ) + 1) :=
        mul_le_mul_of_nonneg_left hlog (sq_nonneg _)
      _ ≤ (N : ℝ) ^ 2 * ((N : ℝ) + 2) :=
        mul_le_mul hsq hfactor (by positivity) (sq_nonneg _)
  have hd3 : (1 : ℝ) ≤ (d : ℝ) ^ 3 := one_le_pow₀ hd1
  unfold TwoThirdsWedge finiteCutoffAbsorptionConstant at hW
  nlinarith [mul_le_mul_of_nonneg_left hd3
    (show 0 ≤ (N : ℝ) ^ 2 * ((N : ℝ) + 2) + 1 by positivity)]

/-- Exact data sufficient for the final Holland-style sign transfer and the
positive-to-negative Jensen change of variables. -/
structure JensenWedgeCertificate (J : ℝ → ℝ) (d : ℕ) where
  comparison : ℝ → ℝ
  transformed : ℝ → ℝ
  intervals : MultiplierIntervalCertificate comparison transformed d
  transformed_continuous : Continuous transformed
  scale : ℝ
  normalization : ℝ
  scale_pos : 0 < scale
  normalization_ne_zero : normalization ≠ 0
  identify : ∀ y,
    transformed y = J (-y / scale) / normalization

theorem JensenWedgeCertificate.transformed_hasDistinctPositiveRoots
    {J : ℝ → ℝ} {d : ℕ} (C : JensenWedgeCertificate J d) :
    HasDistinctPositiveRoots C.transformed d :=
  C.intervals.actual_hasDistinctPositiveRoots C.transformed_continuous

/-- The conditional certificate implies exactly the `d` distinct negative
root conclusion used in the paper. -/
theorem JensenWedgeCertificate.target_hasDistinctNegativeRoots
    {J : ℝ → ℝ} {d : ℕ} (C : JensenWedgeCertificate J d) :
    HasDistinctNegativeRoots J d := by
  rcases C.transformed_hasDistinctPositiveRoots with ⟨x, hxinj, hx⟩
  let z : Fin d → ℝ := fun i => -x i / C.scale
  refine ⟨z, ?_, ?_⟩
  · intro i j hij
    apply hxinj
    dsimp [z] at hij
    have hscale : C.scale ≠ 0 := ne_of_gt C.scale_pos
    field_simp [hscale] at hij
    linarith
  · intro i
    have hxpos := (hx i).1
    have hxzero := (hx i).2
    constructor
    · dsimp [z]
      exact div_neg_of_neg_of_pos (neg_neg_of_pos hxpos) C.scale_pos
    · have hquot : J (-x i / C.scale) / C.normalization = 0 := by
        rw [← C.identify, hxzero]
      have hJ : J (-x i / C.scale) = 0 := by
        rcases (div_eq_zero_iff.mp hquot) with hJ | hnormalization
        · exact hJ
        · exact (C.normalization_ne_zero hnormalization).elim
      simpa [z] using hJ

/-- End-to-end conditional theorem.  Every analytic obligation is concentrated
in the construction of `certificate`; no global assumption declaration or hidden source claim
is introduced into the Lean environment. -/
theorem conditionalTwoThirdsWedge
    (J : ℕ → ℕ → ℝ → ℝ) (K : ℝ)
    (certificate : ∀ n d, TwoThirdsWedge K n d →
      JensenWedgeCertificate (J n d) d) :
    ∀ n d, TwoThirdsWedge K n d → HasDistinctNegativeRoots (J n d) d := by
  intro n d hnd
  exact (certificate n d hnd).target_hasDistinctNegativeRoots

end Zeta23.Research.JensenWedge
