import Zeta23.Research.JensenWedge.AnalyticAdapters
import Zeta23.Research.JensenWedge.XiOmegaIntegral
import Zeta23.Research.JensenWedge.ThetaOmegaMoments

/-!
# Centered xi coefficients from the omega moments

This module closes T1 by combining the differentiated Mellin identity, the
even full-line fold, and the exact integrations by parts.
-/

namespace Zeta23.Research.JensenWedge

open Complex Filter Function MeasureTheory Set Topology Asymptotics

noncomputable section

/-! ## A reusable even-integral fold -/

theorem integrable_even_of_integrableOn_Ioi
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : ℝ → E} (heven : ∀ x, f (-x) = f x)
    (hf : IntegrableOn f (Ioi 0)) : Integrable f := by
  have hIic : IntegrableOn f (Iic 0) := by
    rw [← Measure.map_neg_eq_self (volume : Measure ℝ)]
    let emb : MeasurableEmbedding (fun x : ℝ => -x) :=
      (Homeomorph.neg ℝ).measurableEmbedding
    rw [emb.integrableOn_map_iff]
    simp_rw [Function.comp_def, neg_preimage, neg_Iic, neg_zero, heven]
    exact Iff.mpr integrableOn_Ici_iff_integrableOn_Ioi hf
  rw [← integrableOn_univ, ← Iic_union_Ioi (a := (0 : ℝ)), integrableOn_union]
  exact ⟨hIic, hf⟩

theorem integral_even_eq_two_mul_integral_Ioi
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : ℝ → E} (heven : ∀ x, f (-x) = f x)
    (hf : IntegrableOn f (Ioi 0)) :
    (∫ x : ℝ, f x) = 2 • ∫ x in Ioi (0 : ℝ), f x := by
  have hfull := integrable_even_of_integrableOn_Ioi heven hf
  have hIic : IntegrableOn f (Iic 0) := hfull.integrableOn
  have hneg : (∫ x in Iic (0 : ℝ), f x) = ∫ x in Ioi (0 : ℝ), f x := by
    calc
      (∫ x in Iic (0 : ℝ), f x) = ∫ x in Ioi (0 : ℝ), f (-x) := by
        simpa only [neg_zero] using (integral_comp_neg_Ioi 0 f).symm
      _ = ∫ x in Ioi (0 : ℝ), f x := by
        apply setIntegral_congr_fun measurableSet_Ioi
        intro x _hx
        exact heven x
  calc
    (∫ x : ℝ, f x) =
        (∫ x in Iic (0 : ℝ), f x) + ∫ x in Ioi (0 : ℝ), f x := by
      rw [← setIntegral_union (Iic_disjoint_Ioi le_rfl) measurableSet_Ioi hIic hf,
        Iic_union_Ioi, setIntegral_univ]
    _ = 2 • ∫ x in Ioi (0 : ℝ), f x := by rw [hneg, two_smul]

/-! ## Differentiated completed zeta as centered whole-line moments -/

theorem iteratedDeriv_completedRiemannZeta₀_center_eq_fullMoment (n : ℕ) :
    iteratedDeriv n completedRiemannZeta₀ (1 / 2) =
      ∫ u : ℝ, (u : ℂ) ^ n * centeredModifiedThetaAmplitude u := by
  rw [iteratedDeriv_completedRiemannZeta₀_eq_logMoment]
  rw [show (1 / 2 : ℂ) / 2 = 1 / 4 by ring]
  rw [mellin_eq_logIntegral_neg]
  let g : ℝ → ℂ := fun x =>
    Complex.exp (-(1 / 4 : ℂ) * x) *
      iteratedLogKernel riemannThetaModifiedKernel n (Real.exp (-x))
  have hscale := Measure.integral_comp_mul_left g (-2)
  change (1 / 2 : ℂ) ^ n * (∫ x : ℝ, g x) / 2 = _
  calc
    (1 / 2 : ℂ) ^ n * (∫ x : ℝ, g x) / 2 =
        (1 / 2 : ℂ) ^ n * ∫ u : ℝ, g (-2 * u) := by
      rw [hscale]
      norm_num [Complex.real_smul]
      ring
    _ = ∫ u : ℝ, (1 / 2 : ℂ) ^ n * g (-2 * u) := by
      rw [integral_const_mul]
    _ = ∫ u : ℝ, (u : ℂ) ^ n * centeredModifiedThetaAmplitude u := by
      apply integral_congr_ae
      filter_upwards [] with u
      unfold g centeredModifiedThetaAmplitude
      rw [iteratedLogKernel_apply, show -(-2 * u) = 2 * u by ring,
        Real.log_exp]
      rw [show -(1 / 4 : ℂ) * ((-2 * u : ℝ) : ℂ) = ((u / 2 : ℝ) : ℂ) by
        push_cast
        ring]
      rw [← Complex.ofReal_exp]
      push_cast
      rw [mul_pow]
      rw [← mul_assoc, ← mul_pow]
      norm_num
      ring_nf
      conv_lhs => rw [mul_assoc, ← mul_pow]
      norm_num

/-- The even centered amplitude moment is integrable on the positive
half-line, where the modified kernel is exactly twice the paper amplitude. -/
theorem integrableOn_centeredModifiedThetaAmplitude_evenMoment (n : ℕ) :
    IntegrableOn
      (fun u : ℝ => (u : ℂ) ^ (2 * n) * centeredModifiedThetaAmplitude u)
      (Ioi 0) := by
  have hreal := integrableOn_pow_mul_thetaLogAmplitude (2 * n)
  have hcomplex : IntegrableOn
      (fun u : ℝ => ((u ^ (2 * n) * thetaLogAmplitude u : ℝ) : ℂ))
      (Ioi 0) := hreal.ofReal
  have htwo := hcomplex.const_mul (2 : ℂ)
  apply IntegrableOn.congr_fun htwo _ measurableSet_Ioi
  intro u hu
  change 2 * ((u ^ (2 * n) * thetaLogAmplitude u : ℝ) : ℂ) =
    (u : ℂ) ^ (2 * n) * centeredModifiedThetaAmplitude u
  rw [centeredModifiedThetaAmplitude_eq_two_mul_thetaLogAmplitude hu]
  push_cast
  ring

/-- The differentiated completed zeta at the center is four times the
positive-half-line theta moment. -/
theorem iteratedDeriv_completedRiemannZeta₀_center_eq_four_thetaMoment (n : ℕ) :
    iteratedDeriv (2 * n) completedRiemannZeta₀ (1 / 2) =
      4 * ∫ u in Ioi (0 : ℝ),
        ((u ^ (2 * n) * thetaLogAmplitude u : ℝ) : ℂ) := by
  rw [iteratedDeriv_completedRiemannZeta₀_center_eq_fullMoment]
  have heven : ∀ u : ℝ,
      ((-u : ℝ) : ℂ) ^ (2 * n) * centeredModifiedThetaAmplitude (-u) =
        (u : ℂ) ^ (2 * n) * centeredModifiedThetaAmplitude u := by
    intro u
    rw [centeredModifiedThetaAmplitude_even]
    rw [show ((-u : ℝ) : ℂ) = -(u : ℂ) by push_cast; ring]
    rw [neg_pow, Even.neg_one_pow (even_two_mul n)]
    simp
  rw [integral_even_eq_two_mul_integral_Ioi heven
    (integrableOn_centeredModifiedThetaAmplitude_evenMoment n)]
  rw [show (∫ u in Ioi (0 : ℝ),
      (u : ℂ) ^ (2 * n) * centeredModifiedThetaAmplitude u) =
      2 * ∫ u in Ioi (0 : ℝ),
        ((u ^ (2 * n) * thetaLogAmplitude u : ℝ) : ℂ) by
    rw [← integral_const_mul]
    apply integral_congr_ae
    filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with u hu
    rw [centeredModifiedThetaAmplitude_eq_two_mul_thetaLogAmplitude hu]
    push_cast
    ring]
  simp [Complex.real_smul]
  ring

/-! ## The centered-xi quadratic prefactor -/

/-- The completed-zeta factor translated to the symmetry center. -/
def centeredCompletedZeta (w : ℂ) : ℂ :=
  completedRiemannZeta₀ (1 / 2 + w)

/-- The quadratic factor in Riemann's entire xi normalization after the
translation `s = 1/2 + w`. -/
def centeredXiPrefactor (w : ℂ) : ℂ :=
  (w ^ 2 - 1 / 4) / 2

theorem centeredXi_eq_prefactor (w : ℂ) :
    centeredXi w =
      centeredXiPrefactor w * centeredCompletedZeta w + 1 / 2 := by
  unfold centeredXi riemannXi Zeta23.XiPrime.xi centeredXiPrefactor
    centeredCompletedZeta
  ring

theorem centeredCompletedZeta_contDiff (n : ℕ) :
    ContDiff ℂ n centeredCompletedZeta := by
  exact (differentiable_completedZeta₀.comp
    ((differentiable_const (c := (1 / 2 : ℂ))).add differentiable_id)).contDiff

theorem centeredXiPrefactor_contDiff (n : ℕ) :
    ContDiff ℂ n centeredXiPrefactor := by
  unfold centeredXiPrefactor
  fun_prop

theorem iteratedDeriv_centeredCompletedZeta_zero (n : ℕ) :
    iteratedDeriv n centeredCompletedZeta 0 =
      iteratedDeriv n completedRiemannZeta₀ (1 / 2) := by
  unfold centeredCompletedZeta
  simpa using congrFun
    (iteratedDeriv_comp_const_add n completedRiemannZeta₀ (1 / 2)) 0

theorem iteratedDeriv_centeredXiPrefactor_zero (k : ℕ) :
    iteratedDeriv k centeredXiPrefactor 0 =
      if k = 0 then (-1 / 8 : ℂ) else if k = 2 then 1 else 0 := by
  rcases eq_or_ne k 0 with rfl | hk
  · norm_num [centeredXiPrefactor]
  · have hkpos : 0 < k := Nat.pos_of_ne_zero hk
    rw [show centeredXiPrefactor =
        fun w : ℂ => ((-1 / 4 : ℂ) + w ^ 2) / 2 by
      funext w
      unfold centeredXiPrefactor
      ring]
    rw [iteratedDeriv_div_const, iteratedDeriv_const_add hkpos,
      iteratedDeriv_fun_pow_zero]
    simp only [hk, ↓reduceIte]
    split_ifs <;> norm_num

private theorem sum_quadratic_prefactor_leibniz
    (M : ℕ) (hM2 : 2 < M + 1) (D : ℕ → ℂ) :
    (∑ i ∈ Finset.range (M + 1),
      ((M.choose i : ℂ) *
        (if i = 0 then (-1 / 8 : ℂ) else if i = 2 then 1 else 0)) *
          D (M - i)) =
      (-1 / 8 : ℂ) * D M + (M.choose 2 : ℂ) * D (M - 2) := by
  have hterm : ∀ i : ℕ,
      ((M.choose i : ℂ) *
        (if i = 0 then (-1 / 8 : ℂ) else if i = 2 then 1 else 0)) *
          D (M - i) =
        (if i = 0 then (-1 / 8 : ℂ) * D M else 0) +
          (if i = 2 then (M.choose 2 : ℂ) * D (M - 2) else 0) := by
    intro i
    rcases eq_or_ne i 0 with rfl | hi0
    · simp
    rcases eq_or_ne i 2 with rfl | hi2
    · simp
    · simp [hi0, hi2]
  simp_rw [hterm, Finset.sum_add_distrib]
  simp only [Finset.sum_ite_eq', Finset.mem_range]
  simp [hM2]

/-- The positive-order Leibniz expansion of centered xi has only the
zeroth and second derivatives of its quadratic prefactor. -/
theorem iteratedDeriv_centeredXi_zero_succ (n : ℕ) :
    iteratedDeriv (2 * (n + 1)) centeredXi 0 =
      (2 * (2 * (n + 1) : ℕ) * (2 * (n + 1) - 1) : ℂ) *
          (∫ u in Ioi (0 : ℝ),
            ((u ^ (2 * n) * thetaLogAmplitude u : ℝ) : ℂ)) -
        (1 / 2 : ℂ) * (∫ u in Ioi (0 : ℝ),
          ((u ^ (2 * (n + 1)) * thetaLogAmplitude u : ℝ) : ℂ)) := by
  have horder : 0 < 2 * (n + 1) := by omega
  rw [show centeredXi = fun w =>
      (1 / 2 : ℂ) + centeredXiPrefactor w * centeredCompletedZeta w by
    funext w
    rw [centeredXi_eq_prefactor]
    ring]
  rw [iteratedDeriv_const_add horder]
  change iteratedDeriv (2 * (n + 1))
    (centeredXiPrefactor * centeredCompletedZeta) 0 = _
  rw [iteratedDeriv_mul
    ((centeredXiPrefactor_contDiff (2 * (n + 1))).contDiffAt)
    ((centeredCompletedZeta_contDiff (2 * (n + 1))).contDiffAt)]
  simp_rw [iteratedDeriv_centeredXiPrefactor_zero,
    iteratedDeriv_centeredCompletedZeta_zero]
  rw [sum_quadratic_prefactor_leibniz (2 * (n + 1)) (by omega)
    (fun k => iteratedDeriv k completedRiemannZeta₀ (1 / 2))]
  rw [show 2 * (n + 1) - 2 = 2 * n by omega]
  rw [iteratedDeriv_completedRiemannZeta₀_center_eq_four_thetaMoment n,
    iteratedDeriv_completedRiemannZeta₀_center_eq_four_thetaMoment (n + 1)]
  have hchoose : (2 * (n + 1)).choose 2 =
      (n + 1) * (2 * (n + 1) - 1) := by
    rw [Nat.choose_two_right]
    calc
      2 * (n + 1) * (2 * (n + 1) - 1) / 2 =
          ((n + 1) * (2 * (n + 1) - 1)) * 2 / 2 := by
            congr 1
            ring
      _ = (n + 1) * (2 * (n + 1) - 1) :=
        Nat.mul_div_left _ (by norm_num)
  have hsub : 2 * (n + 1) - 1 = 2 * n + 1 := by omega
  rw [hchoose, hsub]
  push_cast
  ring

/-! ## Exact omega moment recurrences -/

theorem eight_mul_integral_omegaLogAmplitude_zero :
    8 * (∫ u in Ioi (0 : ℝ), omegaLogAmplitude u) =
      1 / 2 - 1 / 2 * ∫ u in Ioi (0 : ℝ), thetaLogAmplitude u := by
  have hA2 := integrableOn_pow_mul_iteratedDeriv_two_thetaLogAmplitude 0
  have hA := integrableOn_pow_mul_thetaLogAmplitude 0
  have hA2' : IntegrableOn
      (fun u => iteratedDeriv 2 thetaLogAmplitude u) (Ioi 0) := by
    apply IntegrableOn.congr_fun hA2 _ measurableSet_Ioi
    intro u _hu
    simp
  have hA' : IntegrableOn thetaLogAmplitude (Ioi 0) := by
    apply IntegrableOn.congr_fun hA _ measurableSet_Ioi
    intro u _hu
    simp
  have hscaled : IntegrableOn
      (fun u => (1 / 4 : ℝ) * thetaLogAmplitude u) (Ioi 0) :=
    hA'.const_mul (1 / 4 : ℝ)
  have hfour :
      4 * (∫ u in Ioi (0 : ℝ), omegaLogAmplitude u) =
        (∫ u in Ioi (0 : ℝ), iteratedDeriv 2 thetaLogAmplitude u) -
          (1 / 4 : ℝ) * ∫ u in Ioi (0 : ℝ), thetaLogAmplitude u := by
    calc
      4 * (∫ u in Ioi (0 : ℝ), omegaLogAmplitude u) =
          ∫ u in Ioi (0 : ℝ), 4 * omegaLogAmplitude u := by
            rw [integral_const_mul]
      _ = ∫ u in Ioi (0 : ℝ),
          (iteratedDeriv 2 thetaLogAmplitude u -
            (1 / 4 : ℝ) * thetaLogAmplitude u) := by
              apply integral_congr_ae
              filter_upwards [] with u
              rw [show omegaLogAmplitude u =
                  (iteratedDeriv 2 thetaLogAmplitude u -
                    thetaLogAmplitude u / 4) / 4 by
                linarith [four_mul_omegaLogAmplitude u]]
              ring
      _ = (∫ u in Ioi (0 : ℝ), iteratedDeriv 2 thetaLogAmplitude u) -
          ∫ u in Ioi (0 : ℝ),
            (1 / 4 : ℝ) * thetaLogAmplitude u := by
              rw [integral_sub hA2' hscaled]
      _ = (∫ u in Ioi (0 : ℝ), iteratedDeriv 2 thetaLogAmplitude u) -
          (1 / 4 : ℝ) * ∫ u in Ioi (0 : ℝ), thetaLogAmplitude u := by
            rw [integral_const_mul]
  rw [integral_iteratedDeriv_two_thetaLogAmplitude] at hfour
  linarith

theorem eight_mul_integral_pow_omegaLogAmplitude_succ (n : ℕ) :
    8 * (∫ u in Ioi (0 : ℝ),
      u ^ (2 * (n + 1)) * omegaLogAmplitude u) =
      (2 * (2 * (n + 1) : ℕ) * (2 * (n + 1) - 1) : ℝ) *
          (∫ u in Ioi (0 : ℝ),
            u ^ (2 * n) * thetaLogAmplitude u) -
        (1 / 2 : ℝ) * (∫ u in Ioi (0 : ℝ),
          u ^ (2 * (n + 1)) * thetaLogAmplitude u) := by
  let M : ℕ := 2 * (n + 1)
  have hA2 := integrableOn_pow_mul_iteratedDeriv_two_thetaLogAmplitude M
  have hA := integrableOn_pow_mul_thetaLogAmplitude M
  have hscaled := hA.const_mul (1 / 4 : ℝ)
  have hfour :
      4 * (∫ u in Ioi (0 : ℝ), u ^ M * omegaLogAmplitude u) =
        (∫ u in Ioi (0 : ℝ),
          u ^ M * iteratedDeriv 2 thetaLogAmplitude u) -
          (1 / 4 : ℝ) *
            ∫ u in Ioi (0 : ℝ), u ^ M * thetaLogAmplitude u := by
    calc
      4 * (∫ u in Ioi (0 : ℝ), u ^ M * omegaLogAmplitude u) =
          ∫ u in Ioi (0 : ℝ), 4 * (u ^ M * omegaLogAmplitude u) := by
            rw [integral_const_mul]
      _ = ∫ u in Ioi (0 : ℝ),
          (u ^ M * iteratedDeriv 2 thetaLogAmplitude u -
            (1 / 4 : ℝ) * (u ^ M * thetaLogAmplitude u)) := by
              apply integral_congr_ae
              filter_upwards [] with u
              rw [show omegaLogAmplitude u =
                  (iteratedDeriv 2 thetaLogAmplitude u -
                    thetaLogAmplitude u / 4) / 4 by
                linarith [four_mul_omegaLogAmplitude u]]
              ring
      _ = (∫ u in Ioi (0 : ℝ),
          u ^ M * iteratedDeriv 2 thetaLogAmplitude u) -
          ∫ u in Ioi (0 : ℝ),
            (1 / 4 : ℝ) * (u ^ M * thetaLogAmplitude u) := by
              rw [integral_sub hA2 hscaled]
      _ = (∫ u in Ioi (0 : ℝ),
          u ^ M * iteratedDeriv 2 thetaLogAmplitude u) -
          (1 / 4 : ℝ) *
            ∫ u in Ioi (0 : ℝ), u ^ M * thetaLogAmplitude u := by
              rw [integral_const_mul]
  have hM : M = 2 * n + 2 := by unfold M; omega
  have hrec := integral_pow_add_two_mul_iteratedDeriv_two_thetaLogAmplitude (2 * n)
  rw [← hM] at hrec
  rw [hrec] at hfour
  dsimp [M] at hfour
  push_cast at hfour ⊢
  ring_nf at hfour ⊢
  linarith

theorem halfLineMoment_omegaLogAmplitude_eq_ofReal (n : ℕ) :
    halfLineMoment (fun u => (omegaLogAmplitude u : ℂ)) n =
      ((∫ u in Ioi (0 : ℝ),
        u ^ (2 * n) * omegaLogAmplitude u : ℝ) : ℂ) := by
  unfold halfLineMoment
  rw [show (fun u : ℝ =>
      (omegaLogAmplitude u : ℂ) * (u : ℂ) ^ (2 * n)) =
      fun u : ℝ => ((u ^ (2 * n) * omegaLogAmplitude u : ℝ) : ℂ) by
    funext u
    push_cast
    ring]
  exact integral_complex_ofReal

/-! ## The unconditional factor-eight identity -/

theorem iteratedDeriv_centeredXi_zero_eq_thetaMoment :
    iteratedDeriv 0 centeredXi 0 =
      (1 / 2 : ℂ) - (1 / 2 : ℂ) *
        ((∫ u in Ioi (0 : ℝ), thetaLogAmplitude u : ℝ) : ℂ) := by
  have hL := iteratedDeriv_completedRiemannZeta₀_center_eq_four_thetaMoment 0
  simp only [mul_zero, pow_zero, one_mul, iteratedDeriv_zero] at hL
  rw [iteratedDeriv_zero, centeredXi_eq_prefactor]
  norm_num [centeredXiPrefactor, centeredCompletedZeta]
  rw [hL, integral_complex_ofReal]
  ring

/-- The exact analytic seam T1: every even derivative of centered xi is
eight times the corresponding half-line moment of the concrete omega
amplitude. -/
theorem iteratedDeriv_centeredXi_eq_eight_omegaMoment (n : ℕ) :
    iteratedDeriv (2 * n) centeredXi 0 =
      8 * halfLineMoment (fun u => (omegaLogAmplitude u : ℂ)) n := by
  cases n with
  | zero =>
      rw [mul_zero, iteratedDeriv_centeredXi_zero_eq_thetaMoment,
        halfLineMoment_omegaLogAmplitude_eq_ofReal]
      have hreal := eight_mul_integral_omegaLogAmplitude_zero
      have hcomplex := congrArg (fun x : ℝ => (x : ℂ)) hreal
      push_cast at hcomplex
      simpa using hcomplex.symm
  | succ n =>
      rw [iteratedDeriv_centeredXi_zero_succ,
        halfLineMoment_omegaLogAmplitude_eq_ofReal,
        integral_complex_ofReal, integral_complex_ofReal]
      have hreal := eight_mul_integral_pow_omegaLogAmplitude_succ n
      have hcomplex := congrArg (fun x : ℝ => (x : ℂ)) hreal
      push_cast at hcomplex
      convert hcomplex.symm using 1 <;> norm_num <;> ring

/-- The manuscript's xi coefficient formula with its concrete theta kernel
and factor eight, now with no remaining hypothesis. -/
theorem centeredXiCoefficient_eq_omegaMoment (n : ℕ) :
    centeredXiCoefficient n =
      8 * (n.factorial : ℂ) / ((2 * n).factorial : ℂ) *
        halfLineMoment (fun u => (omegaLogAmplitude u : ℂ)) n := by
  exact centeredXiCoefficient_eq_factorEightMoment
    (fun u => (omegaLogAmplitude u : ℂ)) n
    (iteratedDeriv_centeredXi_eq_eight_omegaMoment n)

end

end Zeta23.Research.JensenWedge
