import Zeta23.Research.JensenWedge.Terminating3F2CriticalRadius

namespace Zeta23.Research.JensenWedge
noncomputable section

structure CriticalRadiusCoefficientBounds
    (A B C D y : ℝ) (d : ℕ) (n S : ℝ) : Prop where
  center_lower : ∀ m : ℕ, m + 2 ≤ d →
    n / 8 ≤ recurrenceP2 A B C D y d m
  cubic_bound : |recurrenceP3 A C D y| ≤ 2
  linear_bound : ∀ m : ℕ, m + 2 ≤ d →
    |recurrenceP1 A B C D y d m| ≤ 96 * (n * S + n * d)
  constant_bound : ∀ m : ℕ, m + 2 ≤ d →
    |recurrenceP0 A C D y d m| ≤ 48 * n ^ 2 * d

private theorem mul_three_le_of_le_components
    {a b c A B C : ℝ} (ha : a ≤ A) (hb : b ≤ B) (hc : c ≤ C) :
    a + b + c ≤ A + B + C := by linarith

 theorem CriticalRadiusCoefficientBounds.contraction_threeQuarters
    {A B C D y n S : ℝ} {d : ℕ}
    (H : CriticalRadiusCoefficientBounds A B C D y d n S)
    (hn : 0 < n) (hS : 0 < S)
    (hdegree : (d : ℝ) ≤ S)
    (hscale_sq : n * d ≤ S ^ 2)
    (hsmall : 128 * (4096 * S) ≤ n) :
    ∀ m : ℕ, m + 2 ≤ d →
      |recurrenceP3 A C D y| * (4096 * S) ^ 3 +
          |recurrenceP1 A B C D y d m| * (4096 * S) +
          |recurrenceP0 A C D y d m| ≤
        (3 / 4 : ℝ) * recurrenceP2 A B C D y d m *
          (4096 * S) ^ 2 := by
  intro m hm
  let R : ℝ := 4096 * S
  have hR : 0 < R := by dsimp [R]; positivity
  have hd : (0 : ℝ) ≤ d := Nat.cast_nonneg d
  have hcenter := H.center_lower m hm
  have hP2 : 0 < recurrenceP2 A B C D y d m := by nlinarith
  have h3 : |recurrenceP3 A C D y| * R ^ 3 ≤
      (1 / 8 : ℝ) * recurrenceP2 A B C D y d m * R ^ 2 := by
    have hleft := mul_le_mul_of_nonneg_right H.cubic_bound (pow_nonneg hR.le 3)
    have hsmall' : 128 * R ≤ n := by simpa [R] using hsmall
    have hright : n / 64 * R ^ 2 ≤
        (1 / 8 : ℝ) * recurrenceP2 A B C D y d m * R ^ 2 := by
      have := mul_le_mul_of_nonneg_right hcenter (pow_nonneg hR.le 2)
      nlinarith
    calc
      |recurrenceP3 A C D y| * R ^ 3 ≤ 2 * R ^ 3 := hleft
      _ ≤ n / 64 * R ^ 2 := by nlinarith [sq_nonneg R]
      _ ≤ _ := hright
  have h1 : |recurrenceP1 A B C D y d m| * R ≤
      (1 / 2 : ℝ) * recurrenceP2 A B C D y d m * R ^ 2 := by
    have hleft := mul_le_mul_of_nonneg_right (H.linear_bound m hm) hR.le
    have hdegterm : n * (d : ℝ) ≤ n * S :=
      mul_le_mul_of_nonneg_left hdegree hn.le
    have hbudget : 96 * (n * S + n * (d : ℝ)) * R ≤
        n / 16 * R ^ 2 := by
      dsimp [R]
      nlinarith [mul_pos hn hS]
    have hright : n / 16 * R ^ 2 ≤
        (1 / 2 : ℝ) * recurrenceP2 A B C D y d m * R ^ 2 := by
      have := mul_le_mul_of_nonneg_right hcenter (pow_nonneg hR.le 2)
      nlinarith
    exact hleft.trans (hbudget.trans hright)
  have h0 : |recurrenceP0 A C D y d m| ≤
      (1 / 8 : ℝ) * recurrenceP2 A B C D y d m * R ^ 2 := by
    have hleft := H.constant_bound m hm
    have hscale_mul := mul_le_mul_of_nonneg_left hscale_sq hn.le
    have hbudget : 48 * n ^ 2 * (d : ℝ) ≤ n / 64 * R ^ 2 := by
      dsimp [R]
      nlinarith
    have hright : n / 64 * R ^ 2 ≤
        (1 / 8 : ℝ) * recurrenceP2 A B C D y d m * R ^ 2 := by
      have := mul_le_mul_of_nonneg_right hcenter (pow_nonneg hR.le 2)
      nlinarith
    exact hleft.trans (hbudget.trans hright)
  dsimp [R] at h3 h1 h0 ⊢
  have := mul_three_le_of_le_components h3 h1 h0
  nlinarith [mul_pos hP2 (sq_pos_of_pos (by positivity : 0 < 4096 * S))]

noncomputable def terminating3F2CriticalRadiusCertificate_of_coefficientBounds
    {d : ℕ} {A B C D y n S : ℝ}
    (hp : (terminating3F2Polynomial d A B C D (D / (A * C))).eval y ≠ 0)
    (hcritical : (terminating3F2Polynomial d A B C D
      (D / (A * C))).derivative.eval y = 0)
    (hA : 0 < A) (hB : 0 < B) (hC : 0 < C) (hD : 0 < D)
    (H : CriticalRadiusCoefficientBounds A B C D y d n S)
    (hn : 0 < n) (hS : 0 < S)
    (hdegree : (d : ℝ) ≤ S)
    (hscale_sq : n * d ≤ S ^ 2)
    (hsmall : 128 * (4096 * S) ≤ n) :
    FourTermCriticalRadiusCertificate
      (polynomialDerivativeRatio
        (terminating3F2Polynomial d A B C D (D / (A * C))) y)
      d (4096 * S) (3 / 4) :=
  terminating3F2CriticalRadiusCertificate hp hcritical hA.ne' hC.ne'
    (fun k _ => by positivity) (fun k _ => by positivity)
    (by positivity) (by norm_num) (by norm_num)
    (fun m hm => by nlinarith [H.center_lower m hm])
    (H.contraction_threeQuarters hn hS hdegree hscale_sq hsmall)

theorem terminating3F2_critical_radius_of_coefficientBounds
    {d : ℕ} {A B C D y n S : ℝ}
    (hp : (terminating3F2Polynomial d A B C D (D / (A * C))).eval y ≠ 0)
    (hcritical : (terminating3F2Polynomial d A B C D
      (D / (A * C))).derivative.eval y = 0)
    (hA : 0 < A) (hB : 0 < B) (hC : 0 < C) (hD : 0 < D)
    (H : CriticalRadiusCoefficientBounds A B C D y d n S)
    (hn : 0 < n) (hS : 0 < S)
    (hdegree : (d : ℝ) ≤ S)
    (hscale_sq : n * d ≤ S ^ 2)
    (hsmall : 128 * (4096 * S) ≤ n) :
    ∀ k ≤ d,
      |polynomialDerivativeRatio
        (terminating3F2Polynomial d A B C D (D / (A * C))) y k| ≤
        (4096 * S) ^ k :=
  (terminating3F2CriticalRadiusCertificate_of_coefficientBounds hp hcritical
    hA hB hC hD H hn hS hdegree hscale_sq hsmall).derivative_radius

structure CriticalRadiusParameterGeometry
    (A B C D y : ℝ) (d : ℕ) (n S : ℝ) : Prop where
  n_pos : 0 < n
  scale_pos : 0 < S
  A_lower : 30 * n ≤ A
  B_lower : n ≤ B
  B_upper : B ≤ 11 / 4 * n
  C_lower : 7 / 4 * n ≤ C
  C_upper : C ≤ 9 / 4 * n
  D_lower : n ≤ D
  D_upper : D ≤ 3 / 2 * n
  localized : |y - B| ≤ 32 * S
  degree_le_scale : (d : ℝ) ≤ S
  scale_small : 524288 * S ≤ n

theorem CriticalRadiusParameterGeometry.basic_bounds
    {A B C D y n S : ℝ} {d : ℕ}
    (G : CriticalRadiusParameterGeometry A B C D y d n S) :
    0 < A ∧ 0 < B ∧ 0 < C ∧ 0 < D ∧
      0 < y ∧ y ≤ 3 * n ∧ (d : ℝ) ≤ n ∧ 0 < C - D := by
  have hn := G.n_pos
  have hA := G.A_lower
  have hB0 := G.B_lower
  have hB1 := G.B_upper
  have hC0 := G.C_lower
  have hD0 := G.D_lower
  have hD1 := G.D_upper
  have hsmall := G.scale_small
  have hloc := (abs_le.mp G.localized)
  have hSnonneg := G.scale_pos.le
  have hSsmall : 32 * S ≤ n / 16384 := by nlinarith
  have hnS : S ≤ n := by nlinarith
  have hdnonneg : (0 : ℝ) ≤ d := Nat.cast_nonneg d
  constructor
  · nlinarith
  constructor
  · nlinarith
  constructor
  · nlinarith
  constructor
  · nlinarith
  constructor
  · nlinarith
  constructor
  · nlinarith
  constructor
  · exact G.degree_le_scale.trans hnS
  · nlinarith

theorem CriticalRadiusParameterGeometry.cubic_bound
    {A B C D y n S : ℝ} {d : ℕ}
    (G : CriticalRadiusParameterGeometry A B C D y d n S) :
    |recurrenceP3 A C D y| ≤ 2 := by
  obtain ⟨hA, _, hC, hD, hy, hyupper, _, _⟩ := G.basic_bounds
  have hAC : 0 < A * C := mul_pos hA hC
  have hDy : 0 ≤ D * y := mul_nonneg hD.le hy.le
  have hDyAC : D * y ≤ A * C := by
    have hleft : D * y ≤ (3 / 2 * n) * (3 * n) := by
      have hn := G.n_pos
      have hDupper := G.D_upper
      gcongr
    have hright : (3 / 2 * n) * (3 * n) ≤ A * C := by
      have hn := G.n_pos
      have hAlower := G.A_lower
      have hClower := G.C_lower
      have hprod : (30 * n) * (7 / 4 * n) ≤ A * C := by
        gcongr
      nlinarith
    exact hleft.trans hright
  rw [recurrenceP3_closed hA.ne' hC.ne']
  rw [abs_le]
  constructor
  · have hnonneg : 0 ≤ (A * C - D * y) / (A * C) :=
      div_nonneg (sub_nonneg.mpr hDyAC) hAC.le
    linarith
  · have hle_one : (A * C - D * y) / (A * C) ≤ 1 := by
      apply (div_le_iff₀ hAC).2
      nlinarith
    linarith

theorem CriticalRadiusParameterGeometry.constant_bound
    {A B C D y n S : ℝ} {d : ℕ}
    (G : CriticalRadiusParameterGeometry A B C D y d n S) :
    ∀ m : ℕ, m + 2 ≤ d →
      |recurrenceP0 A C D y d m| ≤ 48 * n ^ 2 * d := by
  intro m hm
  obtain ⟨hA, _, hC, hD, hy, hyupper, hdle, _⟩ := G.basic_bounds
  have hn := G.n_pos
  have hd0 : (0 : ℝ) ≤ d := Nat.cast_nonneg d
  have hm0 : (0 : ℝ) ≤ m := Nat.cast_nonneg m
  have hmd : (m : ℝ) ≤ d := by exact_mod_cast (Nat.le_trans (Nat.le_add_right m 2) hm)
  have hdm : 0 ≤ (d : ℝ) - m := sub_nonneg.mpr hmd
  have hdmupper : (d : ℝ) - m ≤ d := by nlinarith
  have hAlower := G.A_lower
  have hClower := G.C_lower
  have hAm : A + (m : ℝ) ≤ 2 * A := by nlinarith
  have hCm : C + (m : ℝ) ≤ 2 * C := by nlinarith
  have hDupper := G.D_upper
  have hAC : 0 < A * C := mul_pos hA hC
  have hnum0 : 0 ≤ D * y * (A + m) * (C + m) * (d - m) := by positivity
  have hnum : D * y * (A + m) * (C + m) * (d - m) ≤
      (3 / 2 * n) * (3 * n) * (2 * A) * (2 * C) * d := by
    gcongr
  rw [recurrenceP0_closed hA.ne' hC.ne']
  rw [abs_of_nonneg (div_nonneg hnum0 hAC.le)]
  apply (div_le_iff₀ hAC).2
  calc
    D * y * (A + ↑m) * (C + ↑m) * (↑d - ↑m) ≤
        (3 / 2 * n) * (3 * n) * (2 * A) * (2 * C) * d := hnum
    _ ≤ (48 * n ^ 2 * d) * (A * C) := by
      have hfac : 0 ≤ n ^ 2 * (d : ℝ) * (A * C) := by positivity
      nlinarith

theorem CriticalRadiusParameterGeometry.center_lower
    {A B C D y n S : ℝ} {d : ℕ}
    (G : CriticalRadiusParameterGeometry A B C D y d n S) :
    ∀ m : ℕ, m + 2 ≤ d →
      n / 8 ≤ recurrenceP2 A B C D y d m := by
  intro m hm
  obtain ⟨hA, _, hC, hD, hy, hyupper, hdle, hCD⟩ := G.basic_bounds
  have hn := G.n_pos
  have hS := G.scale_pos
  have hd0 : (0 : ℝ) ≤ d := Nat.cast_nonneg d
  have hm0 : (0 : ℝ) ≤ m := Nat.cast_nonneg m
  have hm2 : (m : ℝ) + 2 ≤ d := by exact_mod_cast hm
  have hmd : (m : ℝ) ≤ d := by nlinarith
  have hratio0 : 0 ≤ y / A := div_nonneg hy.le hA.le
  have hratio : y / A ≤ 1 / 10 := by
    apply (div_le_iff₀ hA).2
    have hAlower := G.A_lower
    nlinarith
  have ha : 9 / 10 ≤ recurrenceA A y := by
    simp only [recurrenceA]
    linarith
  have hcoef : -(d : ℝ) ≤ (d : ℝ) - 1 - 2 * (m + 1) := by nlinarith
  have hcoefratio : -(d : ℝ) / 10 ≤
      ((d : ℝ) - 1 - 2 * (m + 1)) * (y / A) := by
    have hleft : -(d : ℝ) * (1 / 10) ≤ -(d : ℝ) * (y / A) :=
      mul_le_mul_of_nonpos_left hratio (by linarith)
    have hright : -(d : ℝ) * (y / A) ≤
        ((d : ℝ) - 1 - 2 * (m + 1)) * (y / A) :=
      mul_le_mul_of_nonneg_right hcoef hratio0
    nlinarith
  have hcoefratio' : -(d : ℝ) / 10 ≤
      ((d : ℝ) - 1 - 2 * (m + 1)) * y / A := by
    simpa only [div_eq_mul_inv, mul_assoc] using hcoefratio
  have hBdiff : -(32 * S) ≤ B - y := by
    have hloc := (abs_le.mp G.localized).2
    linarith
  have hb : -(33 * S) ≤ recurrenceB A B y d (m + 1) := by
    simp only [recurrenceB]
    have hdS := G.degree_le_scale
    nlinarith
  have hDm : n ≤ D + m := by
    have hDlower := G.D_lower
    nlinarith
  have hcenterProduct : 9 / 10 * n ≤ (D + m) * recurrenceA A y := by
    have hnonneg : 0 ≤ (D + m - n) * (recurrenceA A y - 9 / 10) := by
      positivity
    nlinarith
  have hepsilon : 0 ≤ recurrenceEpsilon C D := by
    simp only [recurrenceEpsilon]
    exact div_nonneg hCD.le hC.le
  have hfactor : 0 ≤ A - (d : ℝ) + 3 + 3 * m := by
    have hAlower := G.A_lower
    nlinarith
  have hlast : 0 ≤ recurrenceEpsilon C D * (y / A) *
      (A - (d : ℝ) + 3 + 3 * m) := by positivity
  have hlast' : 0 ≤ recurrenceEpsilon C D * y / A *
      (A - (d : ℝ) + 3 + 3 * m) := by
    simpa only [div_eq_mul_inv, mul_assoc] using hlast
  simp only [recurrenceP2]
  have hsmall := G.scale_small
  nlinarith

set_option maxHeartbeats 800000 in
theorem CriticalRadiusParameterGeometry.linear_bound
    {A B C D y n S : ℝ} {d : ℕ}
    (G : CriticalRadiusParameterGeometry A B C D y d n S) :
    ∀ m : ℕ, m + 2 ≤ d →
      |recurrenceP1 A B C D y d m| ≤ 96 * (n * S + n * d) := by
  intro m hm
  obtain ⟨hA, _, hC, hD, hy, hyupper, hdle, hCD⟩ := G.basic_bounds
  have hn := G.n_pos
  have hS := G.scale_pos
  have hd0 : (0 : ℝ) ≤ d := Nat.cast_nonneg d
  have hm0 : (0 : ℝ) ≤ m := Nat.cast_nonneg m
  have hm2 : (m : ℝ) + 2 ≤ d := by exact_mod_cast hm
  have hmd : (m : ℝ) ≤ d := by nlinarith
  have hm1d : (m : ℝ) + 1 ≤ d := by nlinarith
  have hratio0 : 0 ≤ y / A := div_nonneg hy.le hA.le
  have hratio : y / A ≤ 1 / 10 := by
    apply (div_le_iff₀ hA).2
    have hAlower := G.A_lower
    nlinarith
  have hratioAbs : |y / A| ≤ 1 / 10 := by
    rw [abs_of_nonneg hratio0]
    exact hratio
  have hCterm0 : 0 ≤ recurrenceC A y d (m + 1) := by
    simp only [recurrenceC]
    positivity
  have hm1ratio : (m + 1 : ℝ) / A ≤ 1 := by
    apply (div_le_iff₀ hA).2
    have hAlower := G.A_lower
    nlinarith
  have hCterm : |recurrenceC A y d (m + 1)| ≤ 6 * n * d := by
    rw [abs_of_nonneg hCterm0]
    simp only [recurrenceC]
    have hdiff0 : 0 ≤ (d : ℝ) - (m + 1) := by nlinarith
    have hdiff : (d : ℝ) - (m + 1) ≤ d := by nlinarith
    have hone0 : 0 ≤ 1 + (m + 1 : ℝ) / A := by positivity
    have hone : 1 + (m + 1 : ℝ) / A ≤ 2 := by linarith
    calc
      ((d : ℝ) - (m + 1)) * (1 + (m + 1 : ℝ) / A) * y ≤
          d * 2 * (3 * n) := by gcongr
      _ = 6 * n * d := by ring
  have hcoefLower : -(d : ℝ) ≤ (d : ℝ) - 1 - 2 * m := by nlinarith
  have hcoefUpper : (d : ℝ) - 1 - 2 * m ≤ d := by nlinarith
  have hcoefAbs : |(d : ℝ) - 1 - 2 * m| ≤ d := (abs_le).2 ⟨hcoefLower, hcoefUpper⟩
  have hcoefratioAbs : |((d : ℝ) - 1 - 2 * m) * y / A| ≤ d / 10 := by
    have hassoc : ((d : ℝ) - 1 - 2 * m) * y / A =
        ((d : ℝ) - 1 - 2 * m) * (y / A) := by ring
    rw [hassoc, abs_mul]
    have := mul_le_mul hcoefAbs hratioAbs (abs_nonneg _) hd0
    nlinarith
  have hb : |recurrenceB A B y d m| ≤ 32 * S + 2 * d := by
    simp only [recurrenceB]
    have hloc := abs_le.mp G.localized
    rw [abs_le]
    constructor
    · have hterm := (abs_le.mp hcoefratioAbs).1
      nlinarith
    · have hterm := (abs_le.mp hcoefratioAbs).2
      nlinarith
  have hDm0 : 0 ≤ D + (m : ℝ) := by positivity
  have hDm : D + (m : ℝ) ≤ 2 * n := by
    have hDupper := G.D_upper
    have hsmall := G.scale_small
    have hmdS := hmd.trans G.degree_le_scale
    nlinarith
  have hBterm : |(D + m) * recurrenceB A B y d m| ≤
      64 * n * S + 4 * n * d := by
    rw [abs_mul, abs_of_nonneg hDm0]
    have hmul := mul_le_mul hDm hb (abs_nonneg _) (by positivity : 0 ≤ 2 * n)
    nlinarith
  have hepsilon0 : 0 ≤ recurrenceEpsilon C D := by
    simp only [recurrenceEpsilon]
    exact div_nonneg hCD.le hC.le
  have hepsilon1 : recurrenceEpsilon C D ≤ 1 := by
    simp only [recurrenceEpsilon]
    apply (div_le_iff₀ hC).2
    nlinarith
  let q : ℝ := 2 * m + 1 - d
  let r : ℝ := -(d : ℝ) * (2 * m + 1) + 3 * m ^ 2 + 3 * m + 1
  have hq : |q| ≤ d := by
    apply (abs_le).2
    dsimp [q]
    constructor <;> nlinarith
  have hd2nat : 2 ≤ d := by omega
  have hd2 : (2 : ℝ) ≤ d := by exact_mod_cast hd2nat
  have hdmul : (d : ℝ) * m ≤ d ^ 2 := by
    have h := mul_le_mul_of_nonneg_left hmd hd0
    simpa [pow_two] using h
  have hmSq : (m : ℝ) ^ 2 ≤ d ^ 2 := by
    have h := mul_le_mul hmd hmd hm0 hd0
    simpa [pow_two] using h
  have hr : |r| ≤ 8 * d ^ 2 := by
    apply (abs_le).2
    dsimp [r]
    constructor <;> nlinarith [sq_nonneg ((d : ℝ) - 1)]
  have hyq : |y * q| ≤ 3 * n * d := by
    rw [abs_mul, abs_of_pos hy]
    exact mul_le_mul hyupper hq (abs_nonneg _) (by positivity)
  have hrr : |(y / A) * r| ≤ (4 / 5 : ℝ) * d ^ 2 := by
    rw [abs_mul]
    have := mul_le_mul hratioAbs hr (abs_nonneg _) (by norm_num : (0 : ℝ) ≤ 1 / 10)
    nlinarith
  have hbetaIdentity : (y / A) * recurrenceBeta A d m = y * q + (y / A) * r := by
    dsimp [q, r]
    simp only [recurrenceBeta]
    field_simp [hA.ne']
    ring
  have hbetaScaled : |(y / A) * recurrenceBeta A d m| ≤ 4 * n * d := by
    rw [hbetaIdentity]
    calc
      |y * q + y / A * r| ≤ |y * q| + |(y / A) * r| := abs_add_le _ _
      _ ≤ 3 * n * d + (4 / 5 : ℝ) * d ^ 2 := add_le_add hyq hrr
      _ ≤ 4 * n * d := by nlinarith
  have hBetaTerm : |recurrenceEpsilon C D * y / A * recurrenceBeta A d m| ≤
      4 * n * d := by
    have hassoc : recurrenceEpsilon C D * y / A * recurrenceBeta A d m =
        recurrenceEpsilon C D * ((y / A) * recurrenceBeta A d m) := by ring
    rw [hassoc, abs_mul, abs_of_nonneg hepsilon0]
    have := mul_le_mul hepsilon1 hbetaScaled (abs_nonneg _) (by norm_num : (0 : ℝ) ≤ 1)
    nlinarith
  simp only [recurrenceP1]
  calc
    |recurrenceC A y (↑d) (↑m + 1) + (D + ↑m) * recurrenceB A B y (↑d) (↑m) +
        recurrenceEpsilon C D * y / A * recurrenceBeta A (↑d) (↑m)| ≤
        |recurrenceC A y d (m + 1)| +
          |(D + m) * recurrenceB A B y d m| +
          |recurrenceEpsilon C D * y / A * recurrenceBeta A d m| := by
            linarith [abs_add_le (recurrenceC A y d (m + 1) +
              (D + m) * recurrenceB A B y d m)
              (recurrenceEpsilon C D * y / A * recurrenceBeta A d m),
              abs_add_le (recurrenceC A y d (m + 1))
                ((D + m) * recurrenceB A B y d m)]
    _ ≤ 6 * n * d + (64 * n * S + 4 * n * d) + 4 * n * d := by
      gcongr
    _ ≤ 96 * (n * S + n * d) := by
      nlinarith [mul_pos hn hS, mul_nonneg hn.le hd0]

theorem CriticalRadiusParameterGeometry.coefficientBounds
    {A B C D y n S : ℝ} {d : ℕ}
    (G : CriticalRadiusParameterGeometry A B C D y d n S) :
    CriticalRadiusCoefficientBounds A B C D y d n S where
  center_lower := G.center_lower
  cubic_bound := G.cubic_bound
  linear_bound := G.linear_bound
  constant_bound := G.constant_bound

noncomputable def terminating3F2CriticalRadiusCertificate_of_geometry
    {d : ℕ} {A B C D y n S : ℝ}
    (hp : (terminating3F2Polynomial d A B C D (D / (A * C))).eval y ≠ 0)
    (hcritical : (terminating3F2Polynomial d A B C D
      (D / (A * C))).derivative.eval y = 0)
    (G : CriticalRadiusParameterGeometry A B C D y d n S)
    (hscale_sq : n * d ≤ S ^ 2) :
    FourTermCriticalRadiusCertificate
      (polynomialDerivativeRatio
        (terminating3F2Polynomial d A B C D (D / (A * C))) y)
      d (4096 * S) (3 / 4) := by
  obtain ⟨hA, hB, hC, hD, _, _, _, _⟩ := G.basic_bounds
  apply terminating3F2CriticalRadiusCertificate_of_coefficientBounds
    hp hcritical hA hB hC hD G.coefficientBounds G.n_pos G.scale_pos
    G.degree_le_scale hscale_sq
  calc
    128 * (4096 * S) = 524288 * S := by ring
    _ ≤ n := G.scale_small

theorem terminating3F2_critical_radius_of_geometry
    {d : ℕ} {A B C D y n S : ℝ}
    (hp : (terminating3F2Polynomial d A B C D (D / (A * C))).eval y ≠ 0)
    (hcritical : (terminating3F2Polynomial d A B C D
      (D / (A * C))).derivative.eval y = 0)
    (G : CriticalRadiusParameterGeometry A B C D y d n S)
    (hscale_sq : n * d ≤ S ^ 2) :
    ∀ k ≤ d,
      |polynomialDerivativeRatio
        (terminating3F2Polynomial d A B C D (D / (A * C))) y k| ≤
        (4096 * S) ^ k :=
  (terminating3F2CriticalRadiusCertificate_of_geometry hp hcritical G
    hscale_sq).derivative_radius
end
end Zeta23.Research.JensenWedge
