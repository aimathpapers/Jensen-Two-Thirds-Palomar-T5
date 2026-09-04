/-
# Analytic sampling maps and the aggregate effective profile

This module connects finite common-space sampling matrices to analytic window
transforms and proves the complete-lattice collapse of the naive diagonal
aggregate to the scalar profile `Σ a, v a ^ 2`.
-/
import Zeta23.Research.MultiWindow.Poisson
import Zeta23.Research.MultiWindow.ChangeBasis
import Zeta23.ThmD.FunctionalOpt

noncomputable section
set_option linter.unusedSectionVars false

open Complex MeasureTheory Matrix Finset
open scoped BigOperators

namespace Zeta23.Research.MultiWindow

variable {A K I : Type*}
variable [Fintype A] [Fintype K] [Fintype I]
variable [DecidableEq A] [DecidableEq K] [DecidableEq I]

/-- Finite analytic sampling maps on one common set of ordinates and lattice
samples. -/
def analyticSamplingMap (v : A → ℝ → ℝ) (ordinate : I → ℝ)
    (sample : K → ℝ) : A → Matrix K I ℂ :=
  fun a k i => (AdmWindow.vHatR (v a) (ordinate i - sample k) : ℂ)

theorem jointGram_analyticSamplingMap_apply (v : A → ℝ → ℝ)
    (ordinate : I → ℝ) (sample : K → ℝ) (a b : A) (k l : K) :
    jointGram (analyticSamplingMap v ordinate sample) (a, k) (b, l) =
      ∑ i, (AdmWindow.vHatR (v a) (ordinate i - sample k) : ℂ) *
        (AdmWindow.vHatR (v b) (ordinate i - sample l) : ℂ) := by
  rw [jointGram_apply]
  congr 1 with i
  simp [analyticSamplingMap]

/-- The scalar profile associated with the naive sum of marginal Grams. -/
def effectiveProfile (v : A → ℝ → ℝ) (x : ℝ) : ℝ :=
  ∑ a, v a x ^ 2

/-- Fourier transform of the aggregate effective profile. -/
def effectiveProfileHat (v : A → ℝ → ℝ) (z : ℂ) : ℂ :=
  paperFT (fun x => (effectiveProfile v x : ℂ)) z

def effectiveProfileHatR (v : A → ℝ → ℝ) (r : ℝ) : ℝ :=
  (effectiveProfileHat v r).re

theorem effectiveProfile_continuous {v : A → ℝ → ℝ}
    (hv : ∀ a, Continuous (v a)) : Continuous (effectiveProfile v) := by
  unfold effectiveProfile
  fun_prop

theorem effectiveProfile_nonneg (v : A → ℝ → ℝ) (x : ℝ) :
    0 ≤ effectiveProfile v x := by
  unfold effectiveProfile
  positivity

variable {v : A → ℝ → ℝ} {L : ℝ} {w c : A → ℝ}

private theorem effectiveProfile_integrand_integrable
    (hV : ∀ a, AdmWindow (v a) L (w a) (c a)) (a : A) (r : ℝ) :
    Integrable (fun x => (((v a x) ^ 2 : ℝ) : ℂ) *
      cexp (Complex.I * (r : ℂ) * x)) := by
  apply Continuous.integrable_of_hasCompactSupport
  · exact (hV a).vSqC_continuous.mul (by fun_prop)
  · exact (hV a).vSqC_hasCompactSupport.mul_right

/-- The Fourier symbol of `Σ a, v_a²` is the sum of the self cross-symbols. -/
theorem effectiveProfileHat_eq_sum_cross
    (hV : ∀ a, AdmWindow (v a) L (w a) (c a)) (r : ℝ) :
    effectiveProfileHat v r = ∑ a, crossPhi (v a) (v a) r := by
  unfold effectiveProfileHat crossPhi paperFT
  have hpoint : (fun x => (effectiveProfile v x : ℂ) *
      cexp (Complex.I * (r : ℂ) * x)) =
      fun x => ∑ a, (((v a x) ^ 2 : ℝ) : ℂ) *
        cexp (Complex.I * (r : ℂ) * x) := by
    funext x
    unfold effectiveProfile
    push_cast
    rw [Finset.sum_mul]
  rw [hpoint, MeasureTheory.integral_finsetSum _
    (fun a _ => effectiveProfile_integrand_integrable hV a r)]
  apply Finset.sum_congr rfl
  intro a ha
  congr 1 with x
  push_cast
  ring

theorem effectiveProfileHatR_eq_sum_cross
    (hV : ∀ a, AdmWindow (v a) L (w a) (c a)) (r : ℝ) :
    effectiveProfileHatR v r = ∑ a, crossPhiR (v a) (v a) r := by
  have h := congrArg (fun z : ℂ => Complex.reCLM z)
    (effectiveProfileHat_eq_sum_cross hV r)
  simpa [effectiveProfileHatR, crossPhiR] using h

/-- Complete-lattice Poisson identity for the naive aggregate. -/
theorem hasSum_effectiveProfile
    (hV : ∀ a, AdmWindow (v a) L (w a) (c a)) (T τ τ' : ℝ) :
    HasSum (fun k : ℤ => ∑ a,
      AdmWindow.vHatR (v a) (τ - (T + k * (2 * Real.pi / L))) *
        AdmWindow.vHatR (v a) (τ' - (T + k * (2 * Real.pi / L))))
      (L * effectiveProfileHatR v (τ - τ')) := by
  have hsum : HasSum (fun k : ℤ => ∑ a,
      AdmWindow.vHatR (v a) (τ - (T + k * (2 * Real.pi / L))) *
        AdmWindow.vHatR (v a) (τ' - (T + k * (2 * Real.pi / L))))
      (∑ a, L * crossPhiR (v a) (v a) (τ - τ')) := by
    apply hasSum_sum
    intro a ha
    exact hasSum_vHatR_mul_bilinear (hV a) (hV a) T τ τ'
  convert hsum using 1
  rw [effectiveProfileHatR_eq_sum_cross hV, Finset.mul_sum]

/-- The aggregate profile lies in the scalar variational class. -/
theorem cFun_effectiveProfile_le_cStar {lam : ℝ}
    (h0 : 0 < lam) (h1 : lam ≤ 1)
    (hV : ∀ a, AdmWindow (v a) L (w a) (c a)) :
    ThmD.cFun lam (effectiveProfile v) ≤ ThmD.cStar lam := by
  exact ThmD.cFun_le_cStar h0 h1
    (effectiveProfile_continuous fun a => (hV a).continuous)

/-- Scale the physical window coordinate to the unit interval used by `cFun`.
For a window supported on `[-L/2,L/2]`, this is the profile that the
scale-free functional actually sees. -/
def scaledEffectiveProfile (L : ℝ) (v : A → ℝ → ℝ) (s : ℝ) : ℝ :=
  effectiveProfile v (L * s)

theorem scaledEffectiveProfile_continuous {v : A → ℝ → ℝ}
    (hv : ∀ a, Continuous (v a)) : Continuous (scaledEffectiveProfile L v) := by
  exact (effectiveProfile_continuous hv).comp (continuous_const.mul continuous_id)

/-- The physically rescaled aggregate profile is also in the sharp scalar
variational class.  Identifying a proposed prime-side moment ratio with this
`cFun` remains a separate semantic theorem. -/
theorem cFun_scaledEffectiveProfile_le_cStar {lam : ℝ}
    (h0 : 0 < lam) (h1 : lam ≤ 1)
    (hV : ∀ a, AdmWindow (v a) L (w a) (c a)) :
    ThmD.cFun lam (scaledEffectiveProfile L v) ≤ ThmD.cStar lam := by
  exact ThmD.cFun_le_cStar h0 h1
    (scaledEffectiveProfile_continuous fun a => (hV a).continuous)

end Zeta23.Research.MultiWindow
