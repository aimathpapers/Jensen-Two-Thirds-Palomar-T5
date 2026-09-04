import Zeta23.Research.JensenWedge.XiMellin

/-!
# Differentiated Mellin moments

This module proves the all-orders log-moment differentiation theorem needed
for T1.  The proof uses Mathlib's dominated differentiation theorem for
Mellin transforms at every order; it does not package differentiation under
the integral as an assumption.
-/

namespace Zeta23.Research.JensenWedge

open Complex Filter Function MeasureTheory Set Topology Asymptotics

noncomputable section

/-- Successive multiplication of a complex-valued kernel by `Real.log`. -/
def iteratedLogKernel (f : ℝ → ℂ) : ℕ → ℝ → ℂ
  | 0 => f
  | n + 1 => fun t => Real.log t • iteratedLogKernel f n t

@[simp]
theorem iteratedLogKernel_zero (f : ℝ → ℂ) : iteratedLogKernel f 0 = f := rfl

@[simp]
theorem iteratedLogKernel_succ (f : ℝ → ℂ) (n : ℕ) :
    iteratedLogKernel f (n + 1) =
      fun t => Real.log t • iteratedLogKernel f n t := rfl

/-- Closed form of the recursively weighted kernel. -/
theorem iteratedLogKernel_apply (f : ℝ → ℂ) (n : ℕ) (t : ℝ) :
    iteratedLogKernel f n t = (Real.log t : ℂ) ^ n * f t := by
  induction n with
  | zero => simp
  | succ n ih =>
      change Real.log t • iteratedLogKernel f n t =
        (Real.log t : ℂ) ^ (n + 1) * f t
      rw [ih, pow_succ]
      rw [Complex.real_smul]
      ring

/-- Local integrability is preserved by every finite logarithmic weight on
the positive half-line. -/
theorem iteratedLogKernel_locallyIntegrableOn
    {f : ℝ → ℂ} (hf : LocallyIntegrableOn f (Ioi 0)) (n : ℕ) :
    LocallyIntegrableOn (iteratedLogKernel f n) (Ioi 0) := by
  induction n with
  | zero => simpa using hf
  | succ n ih =>
      change LocallyIntegrableOn
        (fun t => Real.log t • iteratedLogKernel f n t) (Ioi 0)
      exact ih.continuousOn_smul isOpen_Ioi.isLocallyClosed
        (Real.continuousOn_log.mono
          (subset_compl_singleton_iff.mpr self_notMem_Ioi))

/-- Faster-than-power decay at infinity survives every finite logarithmic
weight. -/
theorem iteratedLogKernel_isBigO_atTop
    {f : ℝ → ℂ} (hf : ∀ r : ℝ, f =O[atTop] (· ^ r))
    (n : ℕ) (r : ℝ) : iteratedLogKernel f n =O[atTop] (· ^ r) := by
  induction n generalizing r with
  | zero => simpa using hf r
  | succ n ih =>
      have hbase : iteratedLogKernel f n =O[atTop]
          (fun x => x ^ (-(-r + 1))) := by
        convert ih (r - 1) using 1
        ring
      have h := isBigO_rpow_top_log_smul
        (a := -r + 1) (b := -r) (by linarith) hbase
      simpa [iteratedLogKernel] using h

/-- Faster-than-power decay at zero survives every finite logarithmic
weight. -/
theorem iteratedLogKernel_isBigO_zero
    {f : ℝ → ℂ} (hf : ∀ r : ℝ, f =O[𝓝[>] 0] (· ^ r))
    (n : ℕ) (r : ℝ) : iteratedLogKernel f n =O[𝓝[>] 0] (· ^ r) := by
  induction n generalizing r with
  | zero => simpa using hf r
  | succ n ih =>
      have hbase : iteratedLogKernel f n =O[𝓝[>] 0]
          (fun x => x ^ (-(-r - 1))) := by
        convert ih (r + 1) using 1
        ring
      have h := isBigO_rpow_zero_log_smul
        (a := -r - 1) (b := -r) (by linarith) hbase
      simpa [iteratedLogKernel] using h

/-- One more complex derivative of the Mellin transform is one more
logarithmic weight.  The endpoint hypotheses are discharged uniformly from
faster-than-power decay. -/
theorem mellin_iteratedLogKernel_hasDerivAt
    {f : ℝ → ℂ}
    (hfLoc : LocallyIntegrableOn f (Ioi 0))
    (hfTop : ∀ r : ℝ, f =O[atTop] (· ^ r))
    (hfZero : ∀ r : ℝ, f =O[𝓝[>] 0] (· ^ r))
    (n : ℕ) (s : ℂ) :
    HasDerivAt (mellin (iteratedLogKernel f n))
      (mellin (iteratedLogKernel f (n + 1)) s) s := by
  have h := mellin_hasDerivAt_of_isBigO_rpow
    (a := s.re + 1) (b := s.re - 1)
    (iteratedLogKernel_locallyIntegrableOn hfLoc n)
    (iteratedLogKernel_isBigO_atTop hfTop n (-(s.re + 1)))
    (by linarith)
    (iteratedLogKernel_isBigO_zero hfZero n (-(s.re - 1)))
    (by linarith)
  simpa [iteratedLogKernel] using h.2

/-- All iterated derivatives of a rapidly decaying Mellin transform are its
successive log moments. -/
theorem iteratedDeriv_mellin_eq_logMoment
    {f : ℝ → ℂ}
    (hfLoc : LocallyIntegrableOn f (Ioi 0))
    (hfTop : ∀ r : ℝ, f =O[atTop] (· ^ r))
    (hfZero : ∀ r : ℝ, f =O[𝓝[>] 0] (· ^ r))
    (n : ℕ) :
    iteratedDeriv n (mellin f) =
      fun s => mellin (iteratedLogKernel f n) s := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [iteratedDeriv_succ, ih]
      funext s
      exact (mellin_iteratedLogKernel_hasDerivAt
        hfLoc hfTop hfZero n s).deriv

/-- Concrete all-orders log-moment formula for the Mellin transform defining
the completed Riemann zeta function. -/
theorem iteratedDeriv_riemannThetaMellin_eq_logMoment (n : ℕ) :
    iteratedDeriv n (mellin riemannThetaModifiedKernel) =
      fun s => mellin (iteratedLogKernel riemannThetaModifiedKernel n) s :=
  iteratedDeriv_mellin_eq_logMoment
    riemannThetaModifiedKernel_locallyIntegrableOn
    riemannThetaModifiedKernel_isBigO_atTop
    riemannThetaModifiedKernel_isBigO_zero n

/-- The Mellin transform of the concrete modified theta kernel is entire. -/
theorem riemannThetaMellin_differentiable :
    Differentiable ℂ (mellin riemannThetaModifiedKernel) := by
  intro s
  exact (mellin_iteratedLogKernel_hasDerivAt
    riemannThetaModifiedKernel_locallyIntegrableOn
    riemannThetaModifiedKernel_isBigO_atTop
    riemannThetaModifiedKernel_isBigO_zero 0 s).differentiableAt

/-- Every derivative of Mathlib's entire completed Riemann zeta is an
explicit log moment of the concrete modified theta kernel.  The two powers of
`1/2` come respectively from the argument scaling and the outer
normalization in the definition of completed zeta. -/
theorem iteratedDeriv_completedRiemannZeta₀_eq_logMoment
    (n : ℕ) (s : ℂ) :
    iteratedDeriv n completedRiemannZeta₀ s =
      (1 / 2 : ℂ) ^ n *
        mellin (iteratedLogKernel riemannThetaModifiedKernel n) (s / 2) / 2 := by
  have hzeta : completedRiemannZeta₀ =
      fun z => mellin riemannThetaModifiedKernel (z / 2) / 2 := by
    funext z
    exact completedRiemannZeta₀_eq_mellin_riemannThetaModifiedKernel z
  rw [hzeta, iteratedDeriv_div_const]
  have harg : (fun z : ℂ => mellin riemannThetaModifiedKernel (z / 2)) =
      fun z => mellin riemannThetaModifiedKernel ((1 / 2 : ℂ) * z) := by
    funext z
    congr 1
    ring
  rw [harg]
  rw [congrFun (iteratedDeriv_comp_const_mul
    (n := n) riemannThetaMellin_differentiable.contDiff (1 / 2 : ℂ)) s]
  rw [congrFun (iteratedDeriv_riemannThetaMellin_eq_logMoment n)
    ((1 / 2 : ℂ) * s)]
  congr 3
  ring

end

end Zeta23.Research.JensenWedge
