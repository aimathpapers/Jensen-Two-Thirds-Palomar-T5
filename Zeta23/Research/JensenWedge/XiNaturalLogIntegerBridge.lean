import Zeta23.Research.JensenWedge.PositiveRealSaddle
import Zeta23.Research.JensenWedge.XiNaturalLogMain
import Zeta23.Research.JensenWedge.XiAuxiliaryLogBridge

/-!
# Integer-node identification of the analytic auxiliary logarithm

The sectorial construction produces a holomorphic logarithm of the exact
auxiliary moment.  This file removes the remaining `2 pi i` ambiguity on the
positive real axis and identifies that logarithm with the principal discrete
logarithm used by the exact finite-difference certificate.
-/

namespace Zeta23.Research.JensenWedge

open Complex Set
open scoped ComplexConjugate

noncomputable section

theorem saddleLeadingLog_ofReal_im
    {x : ℝ} (hx : 0 < x) (hs : (x : ℂ) ∈ leanSaddleSector) :
    (saddleLeadingLog (x : ℂ)).im = 0 := by
  let L := quantitativeSaddleBranch (x : ℂ)
  have hLpos : 0 < L.re := by
    exact lt_trans (by norm_num : (0 : ℝ) < 1000) (by
      simpa only [L] using quantitativeSaddleBranch_re_gt hs)
  have hL : L = (L.re : ℂ) := by
    simpa only [L] using quantitativeSaddleBranch_ofReal_eq_re hx hs
  unfold saddleLeadingLog leadingLogIntegrand
  change ((x : ℂ) * log L + L / 4 - (Real.pi : ℂ) * exp L).im = 0
  rw [hL, ← Complex.ofReal_log hLpos.le, ← Complex.ofReal_exp]
  push_cast
  simp

theorem saddleCurvatureAlong_ofReal_im
    {x : ℝ} (hx : 0 < x) (hs : (x : ℂ) ∈ leanSaddleSector) :
    (saddleCurvatureAlong (x : ℂ)).im = 0 := by
  apply Complex.conj_eq_iff_im.mp
  unfold saddleCurvatureAlong
  simp only [map_sub, map_mul, map_add, map_inv₀, map_pow, map_div₀,
    map_ofNat, conj_ofReal]
  rw [quantitativeSaddleBranch_ofReal_conj hx hs]

theorem saddleMomentLogMain_ofReal_im
    {x : ℝ} (hx : 0 < x) (hs : (x : ℂ) ∈ leanSaddleSector) :
    (saddleMomentLogMain (x : ℂ)).im = 0 := by
  let K := saddleCurvatureAlong (x : ℂ)
  have hKpos : 0 < K.re := by
    change 0 < (saddleCurvatureAlong (x : ℂ)).re
    rw [saddleCurvatureAlong_eq hs]
    exact quantitativeSaddleBranch_curvature_re_pos hs
  have hKim : K.im = 0 := by
    simpa only [K] using saddleCurvatureAlong_ofReal_im hx hs
  have hK : K = (K.re : ℂ) := by
    apply Complex.ext
    · simp
    · simpa using hKim
  have hbasepos : 0 < 2 * Real.pi / K.re := by positivity
  have hleading : (saddleLeadingLog (x : ℂ)).im = 0 :=
    saddleLeadingLog_ofReal_im hx hs
  unfold saddleMomentLogMain
  change (saddleLeadingLog (x : ℂ) +
      (1 / 2 : ℂ) * log ((2 * Real.pi : ℂ) / K) + 1 / (2 * K)).im = 0
  have hbase : (2 * Real.pi : ℂ) / K =
      ((2 * Real.pi / K.re : ℝ) : ℂ) := by
    rw [hK]
    push_cast
    rfl
  rw [hbase, ← Complex.ofReal_log hbasepos.le, hK]
  simp [hleading]

theorem complexXiNaturalTwoShiftLog_ofReal_im
    {x : ℝ} (hx : 0 < x) (hM : (x : ℂ) ∈ leanXiCoefficientSector) :
    (complexXiNaturalTwoShiftLog (x : ℂ)).im = 0 := by
  let N : ℂ := coefficientMellinParameter (x : ℂ)
  let c : ℂ := coefficientCancellationCorrection N
  have hN : N ∈ leanSaddleSector :=
    leanTwoShiftAdmissible_base (leanCoefficientSector_admissible hM.2)
  have hNre : 0 < N.re := leanSaddleSector_re_pos hN
  have hNreal : N = (N.re : ℂ) := by
    unfold N coefficientMellinParameter
    apply Complex.ext <;> simp
  have hNcastSector : (N.re : ℂ) ∈ leanSaddleSector := by
    rwa [← hNreal]
  have hcim : c.im = 0 := by
    apply Complex.conj_eq_iff_im.mp
    have hNconj : conj N = N := by rw [hNreal, conj_ofReal]
    have hLconj : conj (quantitativeSaddleBranch N) =
        quantitativeSaddleBranch N := by
      rw [hNreal]
      exact quantitativeSaddleBranch_ofReal_conj hNre hNcastSector
    unfold c coefficientCancellationCorrection coefficientMomentMultiplier
    simp only [map_sub, map_div₀, map_pow, map_mul, map_add, map_one, map_ofNat]
    rw [hNconj, hLconj]
  have hcpos : 0 < c.re := by
    simpa only [c, N] using coefficientCancellationCorrection_re_pos hM
  have hc : c = (c.re : ℂ) := by
    apply Complex.ext
    · simp
    · simpa using hcim
  unfold complexXiNaturalTwoShiftLog
  change (log 16 + log (N + 2) + log (N + 1) + log c).im = 0
  have hlog16 : log (16 : ℂ) = (Real.log 16 : ℂ) :=
    (Complex.ofReal_log (by norm_num : (0 : ℝ) ≤ 16)).symm
  have hlog16im : (log (16 : ℂ)).im = 0 := by
    have h : (log (16 : ℂ)).im = ((Real.log 16 : ℂ)).im :=
      congrArg Complex.im hlog16
    rw [Complex.ofReal_im] at h
    exact h
  have hN2 : (N.re : ℂ) + 2 = ((N.re + 2 : ℝ) : ℂ) := by
    push_cast
    rfl
  have hN1 : (N.re : ℂ) + 1 = ((N.re + 1 : ℝ) : ℂ) := by
    push_cast
    rfl
  rw [hNreal, hc, hlog16, hN2,
    ← Complex.ofReal_log (by linarith : 0 ≤ N.re + 2), hN1,
    ← Complex.ofReal_log (by linarith : 0 ≤ N.re + 1),
    ← Complex.ofReal_log hcpos.le]
  simp only [add_im, Complex.ofReal_im, zero_add]

theorem complexXiNaturalAuxiliaryLogMain_ofReal_im
    {x : ℝ} (hx : 0 < x) (hM : (x : ℂ) ∈ leanXiCoefficientSector) :
    (complexXiNaturalAuxiliaryLogMain (x : ℂ)).im = 0 := by
  let N : ℂ := coefficientMellinParameter (x : ℂ)
  have hN : N ∈ leanSaddleSector :=
    leanTwoShiftAdmissible_base (leanCoefficientSector_admissible hM.2)
  have hNx : N = ((2 * x - 2 : ℝ) : ℂ) := by
    unfold N coefficientMellinParameter
    push_cast
    ring
  have hNxpos : 0 < 2 * x - 2 := by
    have hNre := leanSaddleSector_re_pos hN
    rw [hNx] at hNre
    simpa using hNre
  unfold complexXiNaturalAuxiliaryLogMain
  rw [show coefficientMellinParameter (x : ℂ) = N by rfl, hNx]
  have hlog2 : log (2 : ℂ) = (Real.log 2 : ℂ) :=
    (Complex.ofReal_log (by norm_num : (0 : ℝ) ≤ 2)).symm
  have hlog2im : (log (2 : ℂ)).im = 0 := by
    have h : (log (2 : ℂ)).im = ((Real.log 2 : ℂ)).im :=
      congrArg Complex.im hlog2
    rw [Complex.ofReal_im] at h
    exact h
  have hlinear : (-(2 * (x : ℂ) + 2) * log 2).im = 0 := by
    rw [mul_im, hlog2im]
    simp
  rw [add_im, add_im, hlinear,
    saddleMomentLogMain_ofReal_im hNxpos (by simpa [hNx] using hN),
    complexXiNaturalTwoShiftLog_ofReal_im hx hM]
  norm_num

theorem complexXiNaturalAuxiliaryMain_ofReal_im
    {x : ℝ} (hx : 0 < x) (hM : (x : ℂ) ∈ leanXiCoefficientSector) :
    (complexXiNaturalAuxiliaryMain (x : ℂ)).im = 0 := by
  have hlogim := complexXiNaturalAuxiliaryLogMain_ofReal_im hx hM
  have hlogreal : complexXiNaturalAuxiliaryLogMain (x : ℂ) =
      ((complexXiNaturalAuxiliaryLogMain (x : ℂ)).re : ℂ) := by
    apply Complex.ext
    · simp
    · simpa using hlogim
  have hexp := exp_complexXiNaturalAuxiliaryLogMain hM
  rw [← hexp, hlogreal]
  exact Complex.exp_ofReal_im _

theorem complexXiNaturalAuxiliaryMain_ofReal_re_pos
    {x : ℝ} (hx : 0 < x) (hM : (x : ℂ) ∈ leanXiCoefficientSector) :
    0 < (complexXiNaturalAuxiliaryMain (x : ℂ)).re := by
  have hlogim := complexXiNaturalAuxiliaryLogMain_ofReal_im hx hM
  have hlogreal : complexXiNaturalAuxiliaryLogMain (x : ℂ) =
      ((complexXiNaturalAuxiliaryLogMain (x : ℂ)).re : ℂ) := by
    apply Complex.ext
    · simp
    · simpa using hlogim
  have hexp := exp_complexXiNaturalAuxiliaryLogMain hM
  rw [← hexp, hlogreal, Complex.exp_ofReal_re]
  exact Real.exp_pos _

theorem one_add_complexXiNaturalAuxiliaryRelativeError_nat_eq_ofReal
    {m : ℕ} (hm : 0 < m) (hM : (m : ℂ) ∈ leanXiCoefficientSector) :
    1 + complexXiNaturalAuxiliaryRelativeError (m : ℂ) =
      ((riemannXiAuxiliaryMomentReal m /
        (complexXiNaturalAuxiliaryMain (m : ℂ)).re : ℝ) : ℂ) := by
  let A := complexXiNaturalAuxiliaryMain (m : ℂ)
  let E := complexXiNaturalAuxiliaryRelativeError (m : ℂ)
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  have hMreal : ((m : ℝ) : ℂ) ∈ leanXiCoefficientSector := by
    rwa [Complex.ofReal_natCast]
  have hAne : A ≠ 0 := by
    simpa only [A] using complexXiNaturalAuxiliaryMain_ne_zero hM
  have hAim : A.im = 0 := by
    simpa only [A, Complex.ofReal_natCast] using
      complexXiNaturalAuxiliaryMain_ofReal_im hmR hMreal
  have hAreal : A = (A.re : ℂ) := by
    apply Complex.ext
    · simp
    · simpa using hAim
  have hfactor := complexXiAuxiliaryMoment_natural_factorization hM
  rw [← complexXiNaturalAuxiliaryRelativeError_eq_momentError hM] at hfactor
  have hquot : 1 + E = complexXiAuxiliaryMoment (m : ℂ) / A := by
    apply (eq_div_iff hAne).2
    rw [hfactor]
    simp only [A, E]
    ring
  rw [hquot, complexXiAuxiliaryMoment_nat_eq_ofReal hm, hAreal,
    ← Complex.ofReal_div]

theorem one_add_complexXiNaturalAuxiliaryRelativeError_nat_re_pos
    {m : ℕ} (hm : 0 < m) (hM : (m : ℂ) ∈ leanXiCoefficientSector) :
    0 < (1 + complexXiNaturalAuxiliaryRelativeError (m : ℂ)).re := by
  rw [one_add_complexXiNaturalAuxiliaryRelativeError_nat_eq_ofReal hm hM]
  simp only [Complex.ofReal_re]
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  have hMreal : ((m : ℝ) : ℂ) ∈ leanXiCoefficientSector := by
    rwa [Complex.ofReal_natCast]
  have hmainpos : 0 < (complexXiNaturalAuxiliaryMain (m : ℂ)).re := by
    simpa only [Complex.ofReal_natCast] using
      complexXiNaturalAuxiliaryMain_ofReal_re_pos hmR hMreal
  exact div_pos (riemannXiAuxiliaryMomentReal_pos m)
    hmainpos

theorem complexXiNaturalAuxiliaryLogError_nat_im
    {m : ℕ} (hm : 0 < m) (hM : (m : ℂ) ∈ leanXiCoefficientSector) :
    (complexXiNaturalAuxiliaryLogError (m : ℂ)).im = 0 := by
  let q : ℝ := riemannXiAuxiliaryMomentReal m /
    (complexXiNaturalAuxiliaryMain (m : ℂ)).re
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  have hMreal : ((m : ℝ) : ℂ) ∈ leanXiCoefficientSector := by
    rwa [Complex.ofReal_natCast]
  have hmainpos : 0 < (complexXiNaturalAuxiliaryMain (m : ℂ)).re := by
    simpa only [Complex.ofReal_natCast] using
      complexXiNaturalAuxiliaryMain_ofReal_re_pos hmR hMreal
  have hq : 0 < q := div_pos (riemannXiAuxiliaryMomentReal_pos m)
    hmainpos
  unfold complexXiNaturalAuxiliaryLogError
  rw [one_add_complexXiNaturalAuxiliaryRelativeError_nat_eq_ofReal hm hM]
  change (log (q : ℂ)).im = 0
  rw [← Complex.ofReal_log hq.le]
  simp

theorem complexXiNaturalAuxiliaryLog_nat_im
    {m : ℕ} (hm : 0 < m) (hM : (m : ℂ) ∈ leanXiCoefficientSector) :
    (complexXiNaturalAuxiliaryLog (m : ℂ)).im = 0 := by
  unfold complexXiNaturalAuxiliaryLog
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  have hMreal : ((m : ℝ) : ℂ) ∈ leanXiCoefficientSector := by
    rwa [Complex.ofReal_natCast]
  have hmainim : (complexXiNaturalAuxiliaryLogMain (m : ℂ)).im = 0 := by
    simpa only [Complex.ofReal_natCast] using
      complexXiNaturalAuxiliaryLogMain_ofReal_im hmR hMreal
  rw [add_im,
    hmainim,
    complexXiNaturalAuxiliaryLogError_nat_im hm hM]
  norm_num

/-- At every positive integer in the fixed coefficient sector, the analytic
logarithm is exactly the principal logarithm of the discrete auxiliary
moment.  No equality modulo `2 pi i` remains. -/
theorem complexXiNaturalAuxiliaryLog_nat_eq_discrete
    {m : ℕ} (hm : 0 < m) (hM : (m : ℂ) ∈ leanXiCoefficientSector) :
    complexXiNaturalAuxiliaryLog (m : ℂ) =
      complexXiDiscreteAuxiliaryLog m := by
  let z := complexXiNaturalAuxiliaryLog (m : ℂ)
  let a := riemannXiAuxiliaryMomentReal m
  have hzim : z.im = 0 := by
    simpa only [z] using complexXiNaturalAuxiliaryLog_nat_im hm hM
  have hzreal : z = (z.re : ℂ) := by
    apply Complex.ext
    · simp
    · simpa using hzim
  have hexp := exp_complexXiNaturalAuxiliaryLog hM
  rw [complexXiAuxiliaryMoment_nat_eq_ofReal hm] at hexp
  have hexpReal : Real.exp z.re = a := by
    have h := congrArg Complex.re hexp
    rw [show complexXiNaturalAuxiliaryLog (m : ℂ) = z by rfl,
      hzreal, Complex.exp_ofReal_re, Complex.ofReal_re] at h
    simpa only [a] using h
  have hzre : z.re = Real.log a := by
    apply Real.exp_injective
    rw [hexpReal, Real.exp_log]
    simpa only [a] using riemannXiAuxiliaryMomentReal_pos m
  calc
    complexXiNaturalAuxiliaryLog (m : ℂ) = z := rfl
    _ = (z.re : ℂ) := hzreal
    _ = (Real.log a : ℂ) := by rw [hzre]
    _ = complexXiDiscreteAuxiliaryLog m := by
      simpa only [a] using ofReal_log_riemannXiAuxiliaryMomentReal hm

/-- Second difference of the branch-fixed analytic auxiliary logarithm,
sampled at positive integers. -/
def complexXiNaturalAuxiliarySecondDiff (m : ℕ) : ℂ :=
  complexXiNaturalAuxiliaryLog (m + 2 : ℕ) -
    2 * complexXiNaturalAuxiliaryLog (m + 1 : ℕ) +
      complexXiNaturalAuxiliaryLog (m : ℂ)

theorem complexXiNaturalAuxiliarySecondDiff_eq_discrete
    {m : ℕ} (hm : 0 < m)
    (h0 : (m : ℂ) ∈ leanXiCoefficientSector)
    (h1 : ((m + 1 : ℕ) : ℂ) ∈ leanXiCoefficientSector)
    (h2 : ((m + 2 : ℕ) : ℂ) ∈ leanXiCoefficientSector) :
    complexXiNaturalAuxiliarySecondDiff m =
      complexXiAuxiliarySecondDiff m := by
  unfold complexXiNaturalAuxiliarySecondDiff complexXiAuxiliarySecondDiff
  rw [complexXiNaturalAuxiliaryLog_nat_eq_discrete (by omega) h2,
    complexXiNaturalAuxiliaryLog_nat_eq_discrete (by omega) h1,
    complexXiNaturalAuxiliaryLog_nat_eq_discrete hm h0]

/-- The four finite-difference coordinates used by the interval certificate
can be computed from the single holomorphic logarithm, provided the six
integer samples lie in the fixed sector. -/
theorem ofReal_exactXiAuxiliarySecondDiff_forwardDiffs_natural
    {n : ℕ} (hn : 0 < n)
    (hsector : ∀ j : ℕ, j ≤ 5 →
      ((n + j : ℕ) : ℂ) ∈ leanXiCoefficientSector) :
    ((natForwardDiff0 (exactXiAuxiliarySecondDiff n) : ℝ) : ℂ) =
        complexNatForwardDiff0
          (fun k => complexXiNaturalAuxiliarySecondDiff (n + k)) ∧
    ((natForwardDiff1 (exactXiAuxiliarySecondDiff n) : ℝ) : ℂ) =
        complexNatForwardDiff1
          (fun k => complexXiNaturalAuxiliarySecondDiff (n + k)) ∧
    ((natForwardDiff2 (exactXiAuxiliarySecondDiff n) : ℝ) : ℂ) =
        complexNatForwardDiff2
          (fun k => complexXiNaturalAuxiliarySecondDiff (n + k)) ∧
    ((natForwardDiff3 (exactXiAuxiliarySecondDiff n) : ℝ) : ℂ) =
        complexNatForwardDiff3
          (fun k => complexXiNaturalAuxiliarySecondDiff (n + k)) := by
  have hbridge := ofReal_exactXiAuxiliarySecondDiff_forwardDiffs hn
  have hsample (k : ℕ) (hk : k ≤ 3) :
      complexXiNaturalAuxiliarySecondDiff (n + k) =
        complexXiAuxiliarySecondDiff (n + k) := by
    apply complexXiNaturalAuxiliarySecondDiff_eq_discrete (by omega)
    · simpa [Nat.add_assoc] using hsector k (by omega)
    · simpa [Nat.add_assoc] using hsector (k + 1) (by omega)
    · simpa [Nat.add_assoc] using hsector (k + 2) (by omega)
  have hs0 : complexXiNaturalAuxiliarySecondDiff n =
      complexXiAuxiliarySecondDiff n := by
    simpa using hsample 0 (by omega)
  have hs1 : complexXiNaturalAuxiliarySecondDiff (n + 1) =
      complexXiAuxiliarySecondDiff (n + 1) := hsample 1 (by omega)
  have hs2 : complexXiNaturalAuxiliarySecondDiff (n + 2) =
      complexXiAuxiliarySecondDiff (n + 2) := hsample 2 (by omega)
  have hs3 : complexXiNaturalAuxiliarySecondDiff (n + 3) =
      complexXiAuxiliarySecondDiff (n + 3) := hsample 3 (by omega)
  constructor
  · simpa [complexNatForwardDiff0, hs0] using hbridge.1
  constructor
  · simpa [complexNatForwardDiff1, hs0, hs1] using hbridge.2.1
  constructor
  · simpa [complexNatForwardDiff2, hs0, hs1, hs2] using hbridge.2.2.1
  · simpa [complexNatForwardDiff3, hs0, hs1, hs2, hs3] using hbridge.2.2.2

end

end Zeta23.Research.JensenWedge
