import Zeta23.Research.JensenWedge.MellinLogMoments

/-!
# The paper's theta tail and omega kernel

This file fixes the precise theta normalization used in the manuscript and
connects it to Mathlib's Riemann theta kernel.  It also kernel-checks the
second-order chain-rule identity that produces the positive omega kernel
after the Mellin integral is pulled back by `t = exp (2u)`.
-/

namespace Zeta23.Research.JensenWedge

open Complex Filter Function MeasureTheory Set Topology Asymptotics
open HurwitzZeta

noncomputable section

/-- The manuscript theta tail
`Theta(t) = sum_{m >= 1} exp (-pi m^2 t)`, expressed through Mathlib's
two-sided Riemann theta kernel. -/
def riemannThetaTail (t : ℝ) : ℝ := (evenKernel 0 t - 1) / 2

/-- The definition above has exactly the manuscript's one-sided series
normalization. -/
theorem hasSum_nat_riemannThetaTail {t : ℝ} (ht : 0 < t) :
    HasSum (fun n : ℕ => Real.exp (-Real.pi * (n + 1) ^ 2 * t))
      (riemannThetaTail t) := by
  have h := (hasSum_nat_cosKernel₀ 0 ht).div_const 2
  simpa [riemannThetaTail, evenKernel_eq_cosKernel_of_zero] using h

/-- On `t > 1`, Mathlib's modified theta kernel is twice the paper's theta
tail. -/
theorem riemannThetaModifiedKernel_eq_two_mul_thetaTail
    {t : ℝ} (ht : 1 < t) :
    riemannThetaModifiedKernel t = 2 * (riemannThetaTail t : ℂ) := by
  rw [riemannThetaModifiedKernel_of_one_lt ht]
  unfold riemannThetaTail
  push_cast
  ring

/-- The concrete theta tail is twice continuously differentiable on the
positive half-line.  Smoothness is inherited from holomorphy of Mathlib's
Jacobi theta function on the upper half-plane. -/
theorem riemannThetaTail_contDiffOn :
    ContDiffOn ℝ 2 riemannThetaTail (Ioi 0) := by
  let upper : Set ℂ := {z | 0 < z.im}
  have hopen : IsOpen upper := isOpen_lt continuous_const continuous_im
  have hjdiff : DifferentiableOn ℂ (jacobiTheta₂ 0) upper := by
    intro z hz
    exact differentiableAt_jacobiTheta₂_snd 0 hz |>.differentiableWithinAt
  have hjcd : ContDiffOn ℂ 2 (jacobiTheta₂ 0) upper :=
    hjdiff.contDiffOn hopen
  have hline : ContDiffOn ℝ 2 (fun t : ℝ => I * (t : ℂ)) (Ioi 0) := by
    exact contDiffOn_const.mul Complex.ofRealCLM.contDiff.contDiffOn
  have hmap : MapsTo (fun t : ℝ => I * (t : ℂ)) (Ioi 0) upper := by
    intro t ht
    simpa [upper] using ht
  have hpull : ContDiffOn ℝ 2
      (fun t : ℝ => jacobiTheta₂ 0 (I * (t : ℂ))) (Ioi 0) :=
    (hjcd.restrict_scalars ℝ).comp hline hmap
  have hre : ContDiffOn ℝ 2
      (fun t : ℝ => (jacobiTheta₂ 0 (I * (t : ℂ))).re) (Ioi 0) := by
    exact Complex.reCLM.contDiff.comp_contDiffOn hpull
  have hrhs : ContDiffOn ℝ 2
      (fun t : ℝ => ((jacobiTheta₂ 0 (I * (t : ℂ))).re - 1) / 2)
      (Ioi 0) := (hre.sub contDiffOn_const).div_const 2
  apply hrhs.congr
  intro t _ht
  unfold riemannThetaTail
  rw [evenKernel_eq_cosKernel_of_zero]
  have hkernel := congrArg Complex.re (cosKernel_def 0 t)
  simpa using hkernel

/-- First differentiability consequence used by the omega chain rule. -/
theorem riemannThetaTail_differentiableAt
    {t : ℝ} (ht : 0 < t) : DifferentiableAt ℝ riemannThetaTail t :=
  ((riemannThetaTail_contDiffOn.differentiableOn (by norm_num)) t ht).differentiableAt
    (isOpen_Ioi.mem_nhds ht)

/-- The first derivative of the theta tail is differentiable on the positive
half-line. -/
theorem deriv_riemannThetaTail_differentiableAt
    {t : ℝ} (ht : 0 < t) :
    DifferentiableAt ℝ (deriv riemannThetaTail) t := by
  have hwithin :=
    (contDiffOn_nat_iff_continuousOn_differentiableOn_deriv
      (uniqueDiffOn_Ioi 0)).1 riemannThetaTail_contDiffOn |>.2 1 (by norm_num)
  have hwithin' : DifferentiableOn ℝ (deriv riemannThetaTail) (Ioi 0) := by
    apply hwithin.congr
    intro x hx
    simpa [iteratedDerivWithin_one] using
      (iteratedDerivWithin_of_isOpen (f := riemannThetaTail) (n := 1)
        isOpen_Ioi hx).symm
  exact (hwithin' t ht).differentiableAt (isOpen_Ioi.mem_nhds ht)

/-- The paper's positive kernel
`omega(t) = 1/2 (2 t^2 Theta''(t) + 3 t Theta'(t))`. -/
def riemannOmega (t : ℝ) : ℝ :=
  1 / 2 * (2 * t ^ 2 * iteratedDeriv 2 riemannThetaTail t +
    3 * t * deriv riemannThetaTail t)

/-- Positive-half-line theta amplitude after `t = exp (2u)`. -/
def thetaLogAmplitude (u : ℝ) : ℝ :=
  Real.exp (u / 2) * riemannThetaTail (Real.exp (2 * u))

/-- The exact first derivative of the pulled-back theta amplitude. -/
theorem hasDerivAt_thetaLogAmplitude
    {u y₁ : ℝ}
    (hTheta : HasDerivAt riemannThetaTail y₁ (Real.exp (2 * u))) :
    HasDerivAt thetaLogAmplitude
      (Real.exp (u / 2) *
        (1 / 2 * riemannThetaTail (Real.exp (2 * u)) +
          2 * Real.exp (2 * u) * y₁)) u := by
  have hhalf : HasDerivAt (fun x : ℝ => Real.exp (x / 2))
      (1 / 2 * Real.exp (u / 2)) u := by
    simpa [Function.comp_def, mul_comm] using
      (Real.hasDerivAt_exp (u / 2) |>.comp u
        ((hasDerivAt_id u).div_const 2))
  have htwo : HasDerivAt (fun x : ℝ => Real.exp (2 * x))
      (2 * Real.exp (2 * u)) u := by
    simpa [Function.comp_def, mul_comm] using
      (Real.hasDerivAt_exp (2 * u) |>.comp u
        ((hasDerivAt_const u 2).mul (hasDerivAt_id u)))
  have hcomp := hTheta.comp u htwo
  have hprod := hhalf.mul hcomp
  apply (hprod.congr_of_eventuallyEq (Eventually.of_forall fun x => by
    rfl)).congr_deriv
  simp only [Function.comp_apply]
  ring

/-- The exact second derivative of the pulled-back theta amplitude. -/
theorem hasDerivAt_thetaLogAmplitude_first
    {u y₁ y₂ : ℝ}
    (hTheta : HasDerivAt riemannThetaTail y₁ (Real.exp (2 * u)))
    (hTheta' : HasDerivAt (deriv riemannThetaTail) y₂
      (Real.exp (2 * u))) :
    HasDerivAt
      (fun x => Real.exp (x / 2) *
        (1 / 2 * riemannThetaTail (Real.exp (2 * x)) +
          2 * Real.exp (2 * x) * deriv riemannThetaTail (Real.exp (2 * x))))
      (Real.exp (u / 2) *
        (1 / 4 * riemannThetaTail (Real.exp (2 * u)) +
          6 * Real.exp (2 * u) * y₁ +
          4 * Real.exp (2 * u) ^ 2 * y₂)) u := by
  have hhalf : HasDerivAt (fun x : ℝ => Real.exp (x / 2))
      (1 / 2 * Real.exp (u / 2)) u := by
    simpa [Function.comp_def, mul_comm] using
      (Real.hasDerivAt_exp (u / 2) |>.comp u
        ((hasDerivAt_id u).div_const 2))
  have htwo : HasDerivAt (fun x : ℝ => Real.exp (2 * x))
      (2 * Real.exp (2 * u)) u := by
    simpa [Function.comp_def, mul_comm] using
      (Real.hasDerivAt_exp (2 * u) |>.comp u
        ((hasDerivAt_const u 2).mul (hasDerivAt_id u)))
  have hThetaComp := hTheta.comp u htwo
  have hTheta'Comp := hTheta'.comp u htwo
  have hinner := (hThetaComp.const_mul (1 / 2)).add
    ((htwo.const_mul 2).mul hTheta'Comp)
  have hprod := hhalf.mul hinner
  apply (hprod.congr_of_eventuallyEq (Eventually.of_forall fun x => by
    rfl)).congr_deriv
  simp only [Pi.add_apply, Pi.mul_apply, Function.comp_apply]
  rw [hTheta.deriv]
  ring

/-- The differential operator in the xi prefactor is exactly four times the
paper's omega kernel after the logarithmic change of variables. -/
theorem thetaLogAmplitude_second_sub_quarter_eq_omega
    {u : ℝ}
    (hTheta : ∀ t : ℝ, 0 < t → DifferentiableAt ℝ riemannThetaTail t)
    (hTheta' : ∀ t : ℝ, 0 < t →
      DifferentiableAt ℝ (deriv riemannThetaTail) t) :
    iteratedDeriv 2 thetaLogAmplitude u - thetaLogAmplitude u / 4 =
      4 * Real.exp (u / 2) * riemannOmega (Real.exp (2 * u)) := by
  let y₁ := deriv riemannThetaTail (Real.exp (2 * u))
  let y₂ := deriv (deriv riemannThetaTail) (Real.exp (2 * u))
  have hfirstFun : deriv thetaLogAmplitude =
      fun x => Real.exp (x / 2) *
        (1 / 2 * riemannThetaTail (Real.exp (2 * x)) +
          2 * Real.exp (2 * x) * deriv riemannThetaTail (Real.exp (2 * x))) := by
    funext x
    exact (hasDerivAt_thetaLogAmplitude (u := x)
      (hTheta _ (Real.exp_pos _)).hasDerivAt).deriv
  have hsecond := hasDerivAt_thetaLogAmplitude_first
    (u := u) (hTheta _ (Real.exp_pos _)).hasDerivAt
      (hTheta' _ (Real.exp_pos _)).hasDerivAt
  rw [show iteratedDeriv 2 thetaLogAmplitude u =
      deriv (deriv thetaLogAmplitude) u by
    rw [show 2 = 1 + 1 by norm_num, iteratedDeriv_succ, iteratedDeriv_one]]
  rw [hfirstFun]
  rw [hsecond.deriv]
  unfold thetaLogAmplitude riemannOmega
  rw [show iteratedDeriv 2 riemannThetaTail (Real.exp (2 * u)) =
      deriv (deriv riemannThetaTail) (Real.exp (2 * u)) by
    rw [show 2 = 1 + 1 by norm_num, iteratedDeriv_succ, iteratedDeriv_one]]
  ring

/-- Concrete omega-chain identity, with the differentiability hypotheses
discharged by the Jacobi-theta smoothness proof above. -/
theorem thetaLogAmplitude_second_sub_quarter_eq_omega_concrete (u : ℝ) :
    iteratedDeriv 2 thetaLogAmplitude u - thetaLogAmplitude u / 4 =
      4 * Real.exp (u / 2) * riemannOmega (Real.exp (2 * u)) := by
  exact thetaLogAmplitude_second_sub_quarter_eq_omega
    (fun t ht => riemannThetaTail_differentiableAt ht)
    (fun t ht => deriv_riemannThetaTail_differentiableAt ht)

/-- The theta functional equation in the logarithmic variable.  The
inhomogeneous hyperbolic-sine term is the removed constant theta mode. -/
theorem thetaLogAmplitude_neg (u : ℝ) :
    thetaLogAmplitude (-u) = thetaLogAmplitude u +
      (Real.exp (u / 2) - Real.exp (-u / 2)) / 2 := by
  have hkernel : evenKernel 0 (Real.exp (-2 * u)) =
      Real.exp u * evenKernel 0 (Real.exp (2 * u)) := by
    rw [evenKernel_functional_equation]
    rw [← evenKernel_eq_cosKernel_of_zero]
    rw [show 1 / Real.exp (-2 * u) = Real.exp (2 * u) by
      rw [one_div, ← Real.exp_neg]
      congr 1
      ring]
    rw [show Real.exp (-2 * u) ^ (1 / 2 : ℝ) = Real.exp (-u) by
      rw [Real.rpow_def_of_pos (Real.exp_pos _), Real.log_exp]
      congr 1
      ring]
    rw [one_div, ← Real.exp_neg]
    congr 2
    ring
  unfold thetaLogAmplitude riemannThetaTail
  rw [show Real.exp (2 * -u) = Real.exp (-2 * u) by congr 1; ring]
  rw [hkernel]
  have hprod : Real.exp (-u / 2) * Real.exp u = Real.exp (u / 2) := by
    rw [← Real.exp_add]
    congr 1
    ring
  calc
    Real.exp (-u / 2) *
        ((Real.exp u * evenKernel 0 (Real.exp (2 * u)) - 1) / 2) =
      (Real.exp (-u / 2) * Real.exp u *
        evenKernel 0 (Real.exp (2 * u)) - Real.exp (-u / 2)) / 2 := by ring
    _ = Real.exp (u / 2) * ((evenKernel 0 (Real.exp (2 * u)) - 1) / 2) +
        (Real.exp (u / 2) - Real.exp (-u / 2)) / 2 := by rw [hprod]; ring

/-- The endpoint slope responsible for cancelling the standalone `1/2` in
Riemann's entire-xi normalization after two integrations by parts. -/
theorem deriv_thetaLogAmplitude_zero : deriv thetaLogAmplitude 0 = -1 / 4 := by
  have hAraw := hasDerivAt_thetaLogAmplitude (u := 0)
    (riemannThetaTail_differentiableAt (Real.exp_pos (2 * 0))).hasDerivAt
  have hA : HasDerivAt thetaLogAmplitude (deriv thetaLogAmplitude 0) 0 :=
    hAraw.differentiableAt.hasDerivAt
  have hnegId : HasDerivAt (fun u : ℝ => -u) (-1) 0 := hasDerivAt_neg' 0
  have hAneg : HasDerivAt thetaLogAmplitude (deriv thetaLogAmplitude 0) (-0) := by
    simpa using hA
  have hleft : HasDerivAt (fun u : ℝ => thetaLogAmplitude (-u))
      (deriv thetaLogAmplitude 0 * (-1)) 0 := by
    exact hAneg.comp 0 hnegId
  have hhalfId : HasDerivAt (fun u : ℝ => u / 2) (1 / 2) 0 :=
    (hasDerivAt_id (𝕜 := ℝ) 0).div_const 2
  have hExpHalf : HasDerivAt Real.exp 1 (0 / 2 : ℝ) := by
    simpa using Real.hasDerivAt_exp 0
  have hpos : HasDerivAt (fun u : ℝ => Real.exp (u / 2)) (1 / 2) 0 := by
    simpa [Function.comp_def] using hExpHalf.comp 0 hhalfId
  have hnegHalfId : HasDerivAt (fun u : ℝ => -u / 2) (-1 / 2) 0 :=
    hnegId.div_const 2
  have hExpNegHalf : HasDerivAt Real.exp 1 (-0 / 2 : ℝ) := by
    simpa using Real.hasDerivAt_exp 0
  have hneg : HasDerivAt (fun u : ℝ => Real.exp (-u / 2)) (-1 / 2) 0 := by
    simpa [Function.comp_def] using hExpNegHalf.comp 0 hnegHalfId
  have hcorr : HasDerivAt
      (fun u : ℝ => (Real.exp (u / 2) - Real.exp (-u / 2)) / 2)
      (1 / 2) 0 := by
    have hcraw := (hpos.sub hneg).div_const 2
    have hcoeff : (((1 / 2 : ℝ) - (-1 / 2)) / 2) = 1 / 2 := by ring
    rw [hcoeff] at hcraw
    exact hcraw
  have hright : HasDerivAt
      (fun u : ℝ => thetaLogAmplitude u +
        (Real.exp (u / 2) - Real.exp (-u / 2)) / 2)
      (deriv thetaLogAmplitude 0 + 1 / 2) 0 := by
    exact hA.add hcorr
  have hfun : (fun u : ℝ => thetaLogAmplitude (-u)) =
      fun u : ℝ => thetaLogAmplitude u +
        (Real.exp (u / 2) - Real.exp (-u / 2)) / 2 := by
    funext u
    exact thetaLogAmplitude_neg u
  rw [hfun] at hleft
  have hcoeff := hleft.unique hright
  linarith

end

end Zeta23.Research.JensenWedge
