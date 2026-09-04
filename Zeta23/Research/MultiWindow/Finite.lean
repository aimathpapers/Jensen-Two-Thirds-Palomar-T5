/-
# Exact finite-lattice bound for the naive multi-window stack

The zeta detector uses only finitely many points from the Poisson lattice.  This
module records that no limiting argument or unquantified boundary error is
needed for the naive diagonal stack: its finite squared norm is bounded by the
complete-lattice effective-profile symbol term by term.
-/
import Zeta23.Research.MultiWindow.EffectiveProfile

noncomputable section
set_option linter.unusedSectionVars false

open Complex Finset Matrix
open scoped BigOperators

namespace Zeta23.Research.MultiWindow

variable {A K I : Type*}
variable [Fintype A] [Fintype K] [Fintype I]
variable [DecidableEq A] [DecidableEq K] [DecidableEq I]

variable {v : A → ℝ → ℝ} {L : ℝ} {w c : A → ℝ}

/-- Any finite injective selection from the common Poisson lattice has total
naive diagonal mass at most the complete-lattice effective-profile mass. -/
theorem finite_lattice_sum_le_effectiveProfile
    (hV : ∀ a, AdmWindow (v a) L (w a) (c a)) (e : K ↪ ℤ)
    (T γ : ℝ) :
    ∑ k : K, ∑ a,
        AdmWindow.vHatR (v a)
            (γ - (T + (e k : ℝ) * (2 * Real.pi / L))) ^ 2
      ≤ L * effectiveProfileHatR v 0 := by
  have hsum := hasSum_effectiveProfile hV T γ γ
  have hnonneg : ∀ k : ℤ, k ∉ Finset.univ.map e →
      0 ≤ ∑ a,
        AdmWindow.vHatR (v a)
            (γ - (T + (k : ℝ) * (2 * Real.pi / L))) *
          AdmWindow.vHatR (v a)
            (γ - (T + (k : ℝ) * (2 * Real.pi / L))) := by
    intro k hk
    exact Finset.sum_nonneg fun a ha => mul_self_nonneg _
  have hle := sum_le_hasSum (Finset.univ.map e) hnonneg hsum
  rw [Finset.sum_map] at hle
  simpa only [sub_self, pow_two] using hle

/-- Matrix form of `finite_lattice_sum_le_effectiveProfile`: each column of
the finite analytic stack obeys the same exact scalar cap. -/
theorem analyticSamplingMap_column_normSq_le_effectiveProfile
    (hV : ∀ a, AdmWindow (v a) L (w a) (c a))
    (e : K ↪ ℤ) (T : ℝ) (ordinate : I → ℝ) (i : I) :
    ∑ ak : A × K,
        ‖analyticSamplingMap v ordinate
            (fun k => T + (e k : ℝ) * (2 * Real.pi / L)) ak.1 ak.2 i‖ ^ 2
      ≤ L * effectiveProfileHatR v 0 := by
  rw [Fintype.sum_prod_type]
  simp only [analyticSamplingMap, Complex.norm_real, Real.norm_eq_abs, sq_abs]
  rw [Finset.sum_comm]
  exact finite_lattice_sum_le_effectiveProfile hV e T (ordinate i)

end Zeta23.Research.MultiWindow
