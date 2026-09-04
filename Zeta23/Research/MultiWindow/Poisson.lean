/-
# Admissible-window adapter for bilinear Poisson summation

This file connects the oriented abstract theorem to two `AdmWindow` instances
on one common sampling lattice.  It also records the same-window and adjoint
regressions required by the C01 specification.
-/
import Zeta23.Poisson.Bilinear
import Zeta23.ThmD.WindowCore

noncomputable section

open Complex

namespace Zeta23.Research.MultiWindow

/-- Fourier transform of the pointwise product of two real windows. -/
def crossPhi (v u : ℝ → ℝ) (z : ℂ) : ℂ :=
  paperFT (fun x => ((v x * u x : ℝ) : ℂ)) z

/-- Real restriction of the cross-window product transform. -/
def crossPhiR (v u : ℝ → ℝ) (r : ℝ) : ℝ :=
  (crossPhi v u r).re

theorem crossPhiR_comm (v u : ℝ → ℝ) (r : ℝ) :
    crossPhiR v u r = crossPhiR u v r := by
  unfold crossPhiR crossPhi
  congr 2
  funext x
  push_cast
  ring

theorem crossPhiR_self (v : ℝ → ℝ) (r : ℝ) :
    crossPhiR v v r = AdmWindow.VPhiR v r := by
  unfold crossPhiR crossPhi AdmWindow.VPhiR AdmWindow.VPhi
  congr 2
  funext x
  push_cast
  ring

theorem crossPhiR_neg {v u : ℝ → ℝ}
    (hv : ∀ x, v (-x) = v x) (hu : ∀ x, u (-x) = u x) (r : ℝ) :
    crossPhiR v u (-r) = crossPhiR v u r := by
  unfold crossPhiR crossPhi
  have heven : ∀ x, v (-x) * u (-x) = v x * u x := by
    intro x
    rw [hv, hu]
  have h := Taper.paperFT_neg_of_even
    (v := fun x => v x * u x) heven (r : ℂ)
  simpa using congrArg Complex.re h

/-- Swapping the two even windows and the two ordinate arguments gives the
adjoint block. -/
theorem crossPhiR_adjoint {v u : ℝ → ℝ}
    (hv : ∀ x, v (-x) = v x) (hu : ∀ x, u (-x) = u x) (r : ℝ) :
    crossPhiR v u (-r) = crossPhiR u v r := by
  rw [crossPhiR_neg hv hu, crossPhiR_comm]

variable {v u : ℝ → ℝ} {L wv wu cv cu : ℝ}

/-- Bilinear Poisson identity for two admissible windows on a common lattice. -/
theorem hasSum_vHatR_mul_bilinear
    (hV : AdmWindow v L wv cv) (hU : AdmWindow u L wu cu)
    (T τ τ' : ℝ) :
    HasSum (fun k : ℤ =>
      AdmWindow.vHatR v (τ - (T + k * (2 * Real.pi / L))) *
        AdmWindow.vHatR u (τ' - (T + k * (2 * Real.pi / L))))
      (L * crossPhiR v u (τ - τ')) := by
  have h := Poisson.hasSum_paperFT_mul_paperFT_bilinear
    hV.L_pos hV.continuous hU.continuous hV.support hU.support
    hV.vHat_decay hU.vHat_decay T τ τ'
  have hreal := Complex.reCLM.hasSum h
  convert hreal using 1
  · funext k
    simp only [Complex.reCLM_apply]
    rw [show paperFT (fun x => (v x : ℂ)) = AdmWindow.vHat v from rfl,
      show paperFT (fun x => (u x : ℂ)) = AdmWindow.vHat u from rfl,
      hV.vHat_ofReal', hU.vHat_ofReal']
    norm_cast
  · simp only [Complex.reCLM_apply]
    have hreflect : (fun x => ((v x * u (-x) : ℝ) : ℂ)) =
        fun x => ((v x * u x : ℝ) : ℂ) := by
      funext x
      rw [hU.even]
    rw [hreflect]
    simp [crossPhiR, crossPhi]

/-- Regression: the bilinear theorem specializes to the established
same-window Poisson identity. -/
theorem hasSum_vHatR_mul_bilinear_self
    (hV : AdmWindow v L wv cv) (T τ τ' : ℝ) :
    HasSum (fun k : ℤ =>
      AdmWindow.vHatR v (τ - (T + k * (2 * Real.pi / L))) *
        AdmWindow.vHatR v (τ' - (T + k * (2 * Real.pi / L))))
      (L * AdmWindow.VPhiR v (τ - τ')) := by
  simpa only [crossPhiR_self] using
    hasSum_vHatR_mul_bilinear hV hV T τ τ'

/-- Regression: swapping both windows and ordinates yields the adjoint
sampling block. -/
theorem hasSum_vHatR_mul_bilinear_adjoint
    (hV : AdmWindow v L wv cv) (hU : AdmWindow u L wu cu)
    (T τ τ' : ℝ) :
    HasSum (fun k : ℤ =>
      AdmWindow.vHatR u (τ' - (T + k * (2 * Real.pi / L))) *
        AdmWindow.vHatR v (τ - (T + k * (2 * Real.pi / L))))
      (L * crossPhiR v u (τ - τ')) := by
  have h := hasSum_vHatR_mul_bilinear hU hV T τ' τ
  convert h using 1
  congr 1
  rw [show τ - τ' = -(τ' - τ) by ring,
    crossPhiR_adjoint hV.even hU.even]

end Zeta23.Research.MultiWindow
