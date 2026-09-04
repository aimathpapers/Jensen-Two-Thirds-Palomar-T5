import Zeta23.Research.JensenWedge.CriticalRadiusCoefficientBounds
import Zeta23.Research.JensenWedge.XiNaturalFiniteFreeSpecialization

namespace Zeta23.Research.JensenWedge

open Finset Polynomial

private theorem le_sqrt_mul_of_le
    {d B : ℝ} (hd : 0 ≤ d) (hB : d ≤ B) : d ≤ Real.sqrt (B * d) := by
  have hBd : 0 ≤ B * d := mul_nonneg (hd.trans hB) hd
  have hsq : Real.sqrt (B * d) ^ 2 = B * d := Real.sq_sqrt hBd
  have hsqrt : 0 ≤ Real.sqrt (B * d) := Real.sqrt_nonneg _
  nlinarith [mul_nonneg (sub_nonneg.mpr hB) hd]

/-- A coarse exact wedge constant that forces the scale inequality used by
the explicit `K_r=4096` critical-radius proof. -/
def xiNaturalCriticalRadiusWedgeConstant : ℝ := 2 * 824633720832 ^ 3

theorem twoThirdsWedge_n_ge_criticalRadius_mul_degree
    {K : ℝ} (hK : xiNaturalCriticalRadiusWedgeConstant ≤ K)
    {n d : ℕ} (hn : 0 < n) (hW : TwoThirdsWedge K n d) :
    824633720832 * d ≤ n := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hnOne : (1 : ℝ) ≤ n := by
    exact_mod_cast (Nat.one_le_iff_ne_zero.mpr hn.ne')
  have hlog : Real.log ((n : ℝ) + 2) ≤ 2 * n := by
    have hbase := Real.log_le_sub_one_of_pos
      (show (0 : ℝ) < (n : ℝ) + 2 by positivity)
    nlinarith
  have hd3 : 0 ≤ (d : ℝ) ^ 3 := by positivity
  have hKlower : xiNaturalCriticalRadiusWedgeConstant * (d : ℝ) ^ 3 ≤
      K * (d : ℝ) ^ 3 := mul_le_mul_of_nonneg_right hK hd3
  have hcube : ((824633720832 : ℝ) * d) ^ 3 ≤ (n : ℝ) ^ 3 := by
    unfold TwoThirdsWedge at hW
    dsimp [xiNaturalCriticalRadiusWedgeConstant] at hKlower
    nlinarith [mul_le_mul_of_nonneg_left hlog (sq_nonneg (n : ℝ))]
  have hlinear : (824633720832 : ℝ) * d ≤ n := by
    exact le_of_pow_le_pow_left₀ (by norm_num : (3 : ℕ) ≠ 0) hnR.le hcube
  exact_mod_cast hlinear

theorem criticalRadiusScale_small_of_degree_cap
    {n d : ℕ} (hn : 0 < n) {L : ℝ} (hL : 0 < L)
    (hL12 : 1 / L ≤ (1 : ℝ) / 12)
    {y : BranchPoint} (hy : InOuterParameterBox y)
    (hcap : 824633720832 * d ≤ n) :
    524288 * Real.sqrt (residualParameterB y n (1 / L) * d) ≤ n := by
  rcases hy with ⟨_, _, _, ht1, _, hw1, _, _⟩
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hd0 : (0 : ℝ) ≤ d := Nat.cast_nonneg d
  have hcapR : (824633720832 : ℝ) * d ≤ n := by exact_mod_cast hcap
  have he0 : 0 ≤ (1 / L : ℝ) := (one_div_pos.mpr hL).le
  have hwe1 : y 2 * (1 / L) ≤ 1 / 2 := by
    have hmul := mul_le_mul hw1 hL12 he0 (by norm_num : (0 : ℝ) ≤ 6)
    nlinarith
  have hBupper : residualParameterB y n (1 / L) ≤ 11 / 4 * n := by
    unfold residualParameterB
    nlinarith [mul_nonneg hnR.le
      (by nlinarith : 0 ≤ 11 / 4 - (y 1 + y 2 * (1 / L)))]
  have hBpos : 0 < residualParameterB y n (1 / L) := by
    unfold residualParameterB
    have ht0 : 0 < y 1 := by nlinarith
    positivity
  have hsq : Real.sqrt (residualParameterB y n (1 / L) * d) ^ 2 =
      residualParameterB y n (1 / L) * d := by
    rw [Real.sq_sqrt]
    positivity
  have hcapMul := mul_le_mul_of_nonneg_left hcapR hnR.le
  have hBmul := mul_le_mul_of_nonneg_right hBupper hd0
  have hsqrt0 := Real.sqrt_nonneg (residualParameterB y n (1 / L) * d)
  nlinarith

theorem polynomial_critical_mem_interval_of_complete_roots
    {p : ℝ[X]} {d : ℕ} {roots : Fin d → ℝ} {lo hi x : ℝ}
    (hinj : Function.Injective roots)
    (hzeros : ∀ i, p.eval (roots i) = 0)
    (hdegree : p.natDegree ≤ d)
    (hd : 0 < d)
    (hrootBounds : ∀ i, lo ≤ roots i ∧ roots i ≤ hi)
    (hx : p.eval x ≠ 0)
    (hcritical : p.derivative.eval x = 0) :
    lo ≤ x ∧ x ≤ hi := by
  classical
  let S : Finset ℝ := Finset.univ.image roots
  have hcard : S.card = d := by
    dsimp [S]
    rw [Finset.card_image_of_injective _ hinj, Finset.card_univ,
      Fintype.card_fin]
  have hSzeros : ∀ z ∈ S, p.eval z = 0 := by
    intro z hz
    rcases Finset.mem_image.mp hz with ⟨i, _, rfl⟩
    exact hzeros i
  have hp : p ≠ 0 := by
    intro hp
    simp [hp] at hx
  have hroots : p.roots = S.val :=
    Polynomial.roots_eq_of_natDegree_le_card_of_ne_zero hSzeros
      (by simpa [hcard] using hdegree) hp
  have hcard_le : S.card ≤ p.natDegree := by
    rw [Finset.card_def, ← hroots]
    exact Polynomial.card_roots' p
  have hnatDegree : p.natDegree = d := by omega
  have hsplits : p.Splits := by
    rw [Polynomial.splits_iff_card_roots, hroots, ← Finset.card_def,
      hcard, hnatDegree]
  have hlog := hsplits.eval_derivative_div_eval_of_ne_zero hx
  rw [hcritical, zero_div, hroots] at hlog
  have hsum : ∑ z ∈ S, 1 / (x - z) = 0 := by
    simpa using hlog.symm
  have hSnonempty : S.Nonempty := Finset.card_pos.mp (by omega)
  constructor
  · by_contra hnot
    have hxlo : x < lo := lt_of_not_ge hnot
    have hneg : ∑ z ∈ S, 1 / (x - z) < 0 := by
      apply Finset.sum_neg
      · intro z hz
        rcases Finset.mem_image.mp hz with ⟨i, _, rfl⟩
        exact one_div_neg.mpr (by nlinarith [(hrootBounds i).1])
      · exact hSnonempty
    linarith
  · by_contra hnot
    have hhix : hi < x := lt_of_not_ge hnot
    have hpos : 0 < ∑ z ∈ S, 1 / (x - z) := by
      apply Finset.sum_pos
      · intro z hz
        rcases Finset.mem_image.mp hz with ⟨i, _, rfl⟩
        exact one_div_pos.mpr (by nlinarith [(hrootBounds i).2])
      · exact hSnonempty
    linarith

theorem XiNaturalClassicalRootInputs.comparison_critical_localization
    {n d : ℕ} {L : ℝ} {y : BranchPoint}
    (I : XiNaturalClassicalRootInputs n d L y)
    (hn : 0 < n) (hL : 0 < L)
    (hL12 : 1 / L ≤ (1 : ℝ) / 12)
    (hy : InOuterParameterBox y)
    (G : XiNaturalFiniteFreeGeometry n d L y)
    (hd : 0 < d) {x : ℝ}
    (hx : (xiNaturalComparisonPolynomial n d L y).eval x ≠ 0)
    (hcritical : (xiNaturalComparisonPolynomial n d L y).derivative.eval x = 0) :
    let B := residualParameterB y n (1 / L)
    |x - B| ≤ localizationConstant * Real.sqrt (B * d) := by
  let B := residualParameterB y n (1 / L)
  let E := localizationConstant * Real.sqrt (B * d)
  have hrootBounds : ∀ i, B - E ≤ I.mmp.roots i ∧ I.mmp.roots i ≤ B + E := by
    intro i
    have hi := I.comparison_root_localization hn hL hL12 hy G i
    dsimp only at hi
    rw [abs_le] at hi
    exact ⟨by nlinarith, by nlinarith⟩
  have hzero : ∀ i,
      (xiNaturalComparisonPolynomial n d L y).eval (I.mmp.roots i) = 0 := by
    intro i
    rw [xiNaturalComparisonPolynomial_eq_finiteFree hn hL hL12 hy d]
    exact I.mmp.roots_are_zeros i
  have hinterval := polynomial_critical_mem_interval_of_complete_roots
    I.mmp.strict_log_mesh.injective hzero
    (terminating3F2Polynomial_natDegree_le d
      (residualParameterA y n (1 / L))
      (residualParameterB y n (1 / L))
      (residualParameterC y n)
      (residualParameterD y n (1 / L))
      (residualParameterD y n (1 / L) /
        (residualParameterA y n (1 / L) * residualParameterC y n)))
    hd hrootBounds hx hcritical
  dsimp only [B, E] at hinterval ⊢
  rw [abs_le]
  constructor <;> nlinarith

theorem XiNaturalClassicalRootInputs.comparison_critical_localization_of_explicitCutoff
    {K : ℝ} (hK : xiNaturalFiniteFreeWedgeConstant ≤ K)
    {n d : ℕ} (hn : xiNaturalExplicitCutoffIndex ≤ n)
    (hW : TwoThirdsWedge K n d)
    (I : XiNaturalClassicalRootInputs n d (xiNaturalSaddleScale n)
      (exactXiPositiveParameterBranch_of_explicitCutoff hn).parameters)
    (hd : 0 < d) {x : ℝ}
    (hx : (xiNaturalComparisonPolynomial n d (xiNaturalSaddleScale n)
      (exactXiPositiveParameterBranch_of_explicitCutoff hn).parameters).eval x ≠ 0)
    (hcritical : (xiNaturalComparisonPolynomial n d (xiNaturalSaddleScale n)
      (exactXiPositiveParameterBranch_of_explicitCutoff hn).parameters).derivative.eval x = 0) :
    let B := residualParameterB
      (exactXiPositiveParameterBranch_of_explicitCutoff hn).parameters n
      (1 / xiNaturalSaddleScale n)
    |x - B| ≤ localizationConstant * Real.sqrt (B * d) := by
  let P := exactXiPositiveParameterBranch_of_explicitCutoff hn
  let C := xiNaturalSaddleIntervalConditions_of_explicitCutoff hn
  exact I.comparison_critical_localization C.n_pos C.saddleScale_pos
    (explicitCutoff_inverse_xiNaturalSaddleScale_le_twelve hn) P.in_outer_box
    (xiNaturalFiniteFreeGeometry_of_explicitCutoff hK hn hW) hd hx hcritical

theorem criticalRadiusParameterGeometry_of_outerBox
    {n d : ℕ} (hn : 0 < n) {L : ℝ} (hL : 0 < L)
    (hL12 : 1 / L ≤ (1 : ℝ) / 12)
    {y : BranchPoint} (hy : InOuterParameterBox y)
    (hd : 0 < d)
    {x : ℝ} (hlocal :
      |x - residualParameterB y n (1 / L)| ≤
        localizationConstant * Real.sqrt (residualParameterB y n (1 / L) * d))
    (hnd : d ≤ n)
    (hsmall : 524288 * Real.sqrt (residualParameterB y n (1 / L) * d) ≤ n) :
    CriticalRadiusParameterGeometry
      (residualParameterA y n (1 / L))
      (residualParameterB y n (1 / L))
      (residualParameterC y n)
      (residualParameterD y n (1 / L)) x d n
      (Real.sqrt (residualParameterB y n (1 / L) * d)) := by
  rcases hy with ⟨ha0, ha1, ht0, ht1, hw0, hw1, hdelta0, hdelta1⟩
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hdR : (d : ℝ) ≤ n := by exact_mod_cast hnd
  have he : 0 < (1 / L : ℝ) := one_div_pos.mpr hL
  have he0 : 0 ≤ (1 / L : ℝ) := he.le
  have hw0' : 0 ≤ y 2 := by nlinarith
  have hdelta0' : 0 ≤ y 3 := by nlinarith
  have hwe0 : 0 ≤ y 2 * (1 / L) := mul_nonneg hw0' he0
  have hde0 : 0 ≤ y 3 * (1 / L) := mul_nonneg hdelta0' he0
  have hwe1 : y 2 * (1 / L) ≤ 1 / 2 := by
    have hmul := mul_le_mul hw1 hL12 he0 (by norm_num : (0 : ℝ) ≤ 6)
    nlinarith
  have hde1 : y 3 * (1 / L) ≤ 5 / 144 := by
    have hmul := mul_le_mul hdelta1 hL12 he0 (by norm_num : (0 : ℝ) ≤ 5 / 12)
    nlinarith
  have hBpos : 0 < residualParameterB y n (1 / L) := by
    unfold residualParameterB
    positivity
  have hSpos : 0 < Real.sqrt (residualParameterB y n (1 / L) * d) := by
    apply Real.sqrt_pos.2
    exact mul_pos hBpos (by exact_mod_cast hd)
  refine {
    n_pos := hnR
    scale_pos := hSpos
    A_lower := ?_
    B_lower := ?_
    B_upper := ?_
    C_lower := ?_
    C_upper := ?_
    D_lower := ?_
    D_upper := ?_
    localized := ?_
    degree_le_scale := ?_
    scale_small := hsmall
  }
  · unfold residualParameterA
    apply (le_div_iff₀ he).2
    have he30 : 30 * (1 / L) ≤ 5 / 2 := by nlinarith
    nlinarith [mul_nonneg hnR.le (sub_nonneg.mpr he30)]
  · unfold residualParameterB
    nlinarith [mul_nonneg hnR.le (by nlinarith : 0 ≤ y 1 + y 2 * (1 / L) - 1)]
  · unfold residualParameterB
    nlinarith [mul_nonneg hnR.le
      (by nlinarith : 0 ≤ 11 / 4 - (y 1 + y 2 * (1 / L)))]
  · unfold residualParameterC
    nlinarith [mul_nonneg hnR.le (sub_nonneg.mpr ht0)]
  · unfold residualParameterC
    nlinarith [mul_nonneg hnR.le (sub_nonneg.mpr ht1)]
  · unfold residualParameterD
    nlinarith [mul_nonneg hnR.le hde0]
  · unfold residualParameterD
    have hbase : 1 + y 3 * (1 / L) ≤ 3 / 2 := by nlinarith
    nlinarith [mul_nonneg hnR.le (sub_nonneg.mpr hbase)]
  · exact hlocal.trans (mul_le_mul_of_nonneg_right localizationConstant_lt_32.le
      (Real.sqrt_nonneg _))
  · have hBge : (d : ℝ) ≤ residualParameterB y n (1 / L) := by
      unfold residualParameterB
      have hbase : 1 ≤ y 1 + y 2 * (1 / L) := by nlinarith
      nlinarith [mul_nonneg hnR.le (sub_nonneg.mpr hbase)]
    have hd0 : (0 : ℝ) ≤ d := Nat.cast_nonneg d
    exact le_sqrt_mul_of_le hd0 hBge

theorem criticalRadiusParameterGeometry_of_explicitCutoff
    {K : ℝ} (hK : xiNaturalCriticalRadiusWedgeConstant ≤ K)
    {n d : ℕ} (hn : xiNaturalExplicitCutoffIndex ≤ n)
    (hW : TwoThirdsWedge K n d)
    (I : XiNaturalClassicalRootInputs n d (xiNaturalSaddleScale n)
      (exactXiPositiveParameterBranch_of_explicitCutoff hn).parameters)
    (hd : 0 < d) {x : ℝ}
    (hx : (xiNaturalComparisonPolynomial n d (xiNaturalSaddleScale n)
      (exactXiPositiveParameterBranch_of_explicitCutoff hn).parameters).eval x ≠ 0)
    (hcritical : (xiNaturalComparisonPolynomial n d (xiNaturalSaddleScale n)
      (exactXiPositiveParameterBranch_of_explicitCutoff hn).parameters).derivative.eval x = 0) :
    let y := (exactXiPositiveParameterBranch_of_explicitCutoff hn).parameters
    let L := xiNaturalSaddleScale n
    CriticalRadiusParameterGeometry
      (residualParameterA y n (1 / L))
      (residualParameterB y n (1 / L))
      (residualParameterC y n)
      (residualParameterD y n (1 / L)) x d n
      (Real.sqrt (residualParameterB y n (1 / L) * d)) := by
  let P := exactXiPositiveParameterBranch_of_explicitCutoff hn
  let C := xiNaturalSaddleIntervalConditions_of_explicitCutoff hn
  have hfinite : xiNaturalFiniteFreeWedgeConstant ≤ K := by
    exact (show xiNaturalFiniteFreeWedgeConstant ≤
      xiNaturalCriticalRadiusWedgeConstant by
        norm_num [xiNaturalFiniteFreeWedgeConstant,
          xiNaturalCriticalRadiusWedgeConstant]).trans hK
  have hcap := twoThirdsWedge_n_ge_criticalRadius_mul_degree hK C.n_pos hW
  have hnd : d ≤ n := by omega
  have hlocal := I.comparison_critical_localization_of_explicitCutoff
    hfinite hn hW hd hx hcritical
  exact criticalRadiusParameterGeometry_of_outerBox C.n_pos C.saddleScale_pos
    (explicitCutoff_inverse_xiNaturalSaddleScale_le_twelve hn) P.in_outer_box hd
    hlocal hnd
    (criticalRadiusScale_small_of_degree_cap C.n_pos C.saddleScale_pos
      (explicitCutoff_inverse_xiNaturalSaddleScale_le_twelve hn) P.in_outer_box hcap)

theorem xiNaturalComparison_critical_radius_of_explicitCutoff
    {K : ℝ} (hK : xiNaturalCriticalRadiusWedgeConstant ≤ K)
    {n d : ℕ} (hn : xiNaturalExplicitCutoffIndex ≤ n)
    (hW : TwoThirdsWedge K n d)
    (I : XiNaturalClassicalRootInputs n d (xiNaturalSaddleScale n)
      (exactXiPositiveParameterBranch_of_explicitCutoff hn).parameters)
    (hd : 0 < d) {x : ℝ}
    (hx : (xiNaturalComparisonPolynomial n d (xiNaturalSaddleScale n)
      (exactXiPositiveParameterBranch_of_explicitCutoff hn).parameters).eval x ≠ 0)
    (hcritical : (xiNaturalComparisonPolynomial n d (xiNaturalSaddleScale n)
      (exactXiPositiveParameterBranch_of_explicitCutoff hn).parameters).derivative.eval x = 0) :
    let y := (exactXiPositiveParameterBranch_of_explicitCutoff hn).parameters
    let L := xiNaturalSaddleScale n
    let B := residualParameterB y n (1 / L)
    ∀ k ≤ d,
      |polynomialDerivativeRatio (xiNaturalComparisonPolynomial n d L y) x k| ≤
        (4096 * Real.sqrt (B * d)) ^ k := by
  let y := (exactXiPositiveParameterBranch_of_explicitCutoff hn).parameters
  let L := xiNaturalSaddleScale n
  let A := residualParameterA y n (1 / L)
  let B := residualParameterB y n (1 / L)
  let C := residualParameterC y n
  let D := residualParameterD y n (1 / L)
  let S := Real.sqrt (B * d)
  have G : CriticalRadiusParameterGeometry A B C D x d n S :=
    criticalRadiusParameterGeometry_of_explicitCutoff hK hn hW I hd hx hcritical
  have hBd : 0 ≤ B * (d : ℝ) := by
    exact mul_nonneg (G.basic_bounds.2.1.le) (Nat.cast_nonneg d)
  have hscaleSq : (n : ℝ) * d ≤ S ^ 2 := by
    have hsq : S ^ 2 = B * d := by
      dsimp only [S]
      exact Real.sq_sqrt hBd
    have hprod := mul_le_mul_of_nonneg_right G.B_lower (Nat.cast_nonneg d)
    nlinarith
  simpa only [xiNaturalComparisonPolynomial] using
    (terminating3F2_critical_radius_of_geometry hx hcritical G hscaleSq)

end Zeta23.Research.JensenWedge
