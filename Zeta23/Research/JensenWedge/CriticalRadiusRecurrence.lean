import Zeta23.Research.JensenWedge.DominantMaximum

/-!
# Complete finite maximum argument for the critical-point radius

This module closes the finite bridge between a genuine four-term recurrence
and the derivative-radius bound used by the multiplier argument.  It builds
the maximum over `0,...,d` inside Lean, handles the terminal `T_(d+1)=0`
case, and reduces the conclusion to one explicit coefficient contraction.

The later xi specialization is responsible for proving that its recurrence
coefficients satisfy the contraction inequality. No recurrence, root, or
analytic estimate is postulated here.
-/

namespace Zeta23.Research.JensenWedge

open Finset

noncomputable section

/-- Absolute derivative jet normalized by the proposed radius. -/
def normalizedDerivativeJet (T : ℕ → ℝ) (R : ℝ) (k : ℕ) : ℝ :=
  |T k| / R ^ k

theorem normalizedDerivativeJet_nonneg
    (T : ℕ → ℝ) {R : ℝ} (hR : 0 < R) (k : ℕ) :
    0 ≤ normalizedDerivativeJet T R k :=
  div_nonneg (abs_nonneg _) (pow_nonneg hR.le _)

/-- A contractive bound at every index at least two controls the complete
finite derivative jet.  Unlike the older abstract maximum lemma, this
theorem constructs and bounds the actual finite maximum. -/
theorem normalizedDerivativeJet_le_one_of_contractive
    {T : ℕ → ℝ} {d : ℕ} {R q : ℝ}
    (hR : 0 < R) (hq : q < 1)
    (hzero : normalizedDerivativeJet T R 0 ≤ 1)
    (hone : normalizedDerivativeJet T R 1 ≤ 1)
    (hrec : ∀ M, 0 ≤ M →
      (∀ j, j ≤ d → normalizedDerivativeJet T R j ≤ M) →
      ∀ k, 2 ≤ k → k ≤ d → normalizedDerivativeJet T R k ≤ q * M) :
    ∀ k, k ≤ d → normalizedDerivativeJet T R k ≤ 1 := by
  let s := range (d + 1)
  have hs : s.Nonempty := ⟨0, mem_range.mpr (Nat.zero_lt_succ d)⟩
  let M := s.sup' hs (normalizedDerivativeJet T R)
  have hleM : ∀ j, j ≤ d → normalizedDerivativeJet T R j ≤ M := by
    intro j hj
    exact Finset.le_sup' (normalizedDerivativeJet T R)
      (mem_range.mpr (by omega : j < d + 1))
  obtain ⟨k, hkMem, hMk⟩ := Finset.exists_mem_eq_sup' hs
    (normalizedDerivativeJet T R)
  have hk : k ≤ d := by
    exact Nat.le_of_lt_succ (mem_range.mp hkMem)
  have hMnonneg : 0 ≤ M := by
    exact (normalizedDerivativeJet_nonneg T hR k).trans_eq hMk.symm
  have hMle : M ≤ 1 := by
    apply dominantMaximum_le_one hq
    · exact ⟨k, hk, hMk.symm⟩
    · exact hzero
    · exact hone
    · intro j hj2 hjd
      exact hrec M hMnonneg hleM j hj2 hjd
  intro j hj
  exact (hleM j hj).trans hMle

theorem abs_le_radius_pow_of_normalizedDerivativeJet_le_one
    {T : ℕ → ℝ} {R : ℝ} (hR : 0 < R) {k : ℕ}
    (h : normalizedDerivativeJet T R k ≤ 1) :
    |T k| ≤ R ^ k := by
  unfold normalizedDerivativeJet at h
  rw [div_le_iff₀ (pow_pos hR k)] at h
  simpa using h

/-- Exact coefficient data sufficient for the four-term recurrence to be a
strict contraction after normalization by `R`.  The displayed contraction
is the denominator-free version of the three neighbor budgets in the paper.
-/
structure FourTermCriticalRadiusCertificate
    (T : ℕ → ℝ) (d : ℕ) (R q : ℝ) where
  P3 : ℕ → ℝ
  P2 : ℕ → ℝ
  P1 : ℕ → ℝ
  P0 : ℕ → ℝ
  radius_pos : 0 < R
  contraction_nonneg : 0 ≤ q
  contraction_lt_one : q < 1
  zero_jet : |T 0| ≤ 1
  one_jet : |T 1| ≤ R
  terminal : T (d + 1) = 0
  center_pos : ∀ m, m + 2 ≤ d → 0 < P2 m
  recurrence : ∀ m, m + 2 ≤ d →
    P3 m * T (m + 3) + P2 m * T (m + 2) +
      P1 m * T (m + 1) + P0 m * T m = 0
  coefficient_contraction : ∀ m, m + 2 ≤ d →
    |P3 m| * R ^ 3 + |P1 m| * R + |P0 m| ≤
      q * P2 m * R ^ 2

private theorem normalized_bound_to_abs_bound
    {T : ℕ → ℝ} {R M : ℝ} (hR : 0 < R) {k : ℕ}
    (h : normalizedDerivativeJet T R k ≤ M) :
    |T k| ≤ M * R ^ k := by
  unfold normalizedDerivativeJet at h
  rw [div_le_iff₀ (pow_pos hR k)] at h
  exact h

theorem FourTermCriticalRadiusCertificate.contractive_step
    {T : ℕ → ℝ} {d : ℕ} {R q M : ℝ}
    (C : FourTermCriticalRadiusCertificate T d R q)
    (hM : 0 ≤ M)
    (hbound : ∀ j, j ≤ d → normalizedDerivativeJet T R j ≤ M)
    {k : ℕ} (hk2 : 2 ≤ k) (hkd : k ≤ d) :
    normalizedDerivativeJet T R k ≤ q * M := by
  let m := k - 2
  have hmk : m + 2 = k := by omega
  have hmRange : m + 2 ≤ d := by omega
  have hT0 : |T m| ≤ M * R ^ m :=
    normalized_bound_to_abs_bound C.radius_pos (hbound m (by omega))
  have hT1 : |T (m + 1)| ≤ M * R ^ (m + 1) :=
    normalized_bound_to_abs_bound C.radius_pos (hbound (m + 1) (by omega))
  have hT3 : |T (m + 3)| ≤ M * R ^ (m + 3) := by
    by_cases hm3 : m + 3 ≤ d
    · exact normalized_bound_to_abs_bound C.radius_pos
        (hbound (m + 3) hm3)
    · have hm3eq : m + 3 = d + 1 := by omega
      rw [hm3eq, C.terminal]
      simpa using mul_nonneg hM (pow_nonneg C.radius_pos.le (d + 1))
  have hcenter :
      C.P2 m * |T (m + 2)| ≤
        |C.P3 m| * |T (m + 3)| +
          |C.P1 m| * |T (m + 1)| + |C.P0 m| * |T m| := by
    have hrec := C.recurrence m hmRange
    have heq : C.P2 m * T (m + 2) =
        -(C.P3 m * T (m + 3) +
          C.P1 m * T (m + 1) + C.P0 m * T m) := by
      linarith
    calc
      C.P2 m * |T (m + 2)| = |C.P2 m * T (m + 2)| := by
        rw [abs_mul, abs_of_pos (C.center_pos m hmRange)]
      _ = |C.P3 m * T (m + 3) +
          C.P1 m * T (m + 1) + C.P0 m * T m| := by rw [heq, abs_neg]
      _ ≤ |C.P3 m * T (m + 3)| +
          |C.P1 m * T (m + 1)| + |C.P0 m * T m| := by
        exact (abs_add_le _ _).trans (add_le_add_left (abs_add_le _ _) _)
      _ = |C.P3 m| * |T (m + 3)| +
          |C.P1 m| * |T (m + 1)| + |C.P0 m| * |T m| := by
        rw [abs_mul, abs_mul, abs_mul]
  have hneighbors :
      |C.P3 m| * |T (m + 3)| +
          |C.P1 m| * |T (m + 1)| + |C.P0 m| * |T m| ≤
        M * R ^ m *
          (|C.P3 m| * R ^ 3 + |C.P1 m| * R + |C.P0 m|) := by
    calc
      |C.P3 m| * |T (m + 3)| +
          |C.P1 m| * |T (m + 1)| + |C.P0 m| * |T m| ≤
          |C.P3 m| * (M * R ^ (m + 3)) +
            |C.P1 m| * (M * R ^ (m + 1)) +
              |C.P0 m| * (M * R ^ m) := by
        gcongr
      _ = M * R ^ m *
          (|C.P3 m| * R ^ 3 + |C.P1 m| * R + |C.P0 m|) := by
        rw [show m + 3 = m + 3 by rfl, pow_add,
          show m + 1 = m + 1 by rfl, pow_add]
        ring
  have hcontract := C.coefficient_contraction m hmRange
  have hscale : 0 ≤ M * R ^ m :=
    mul_nonneg hM (pow_nonneg C.radius_pos.le _)
  have htotal :
      C.P2 m * |T (m + 2)| ≤
        M * R ^ m * (q * C.P2 m * R ^ 2) :=
    hcenter.trans (hneighbors.trans (mul_le_mul_of_nonneg_left hcontract hscale))
  have hcancel : |T (m + 2)| ≤ q * M * R ^ (m + 2) := by
    have hp2 := C.center_pos m hmRange
    have hmul : C.P2 m * |T (m + 2)| ≤
        C.P2 m * (q * M * R ^ (m + 2)) := by
      calc
      C.P2 m * |T (m + 2)| ≤
          M * R ^ m * (q * C.P2 m * R ^ 2) := htotal
      _ = C.P2 m * (q * M * R ^ (m + 2)) := by
        rw [show m + 2 = m + 2 by rfl, pow_add]
        ring
    nlinarith
  unfold normalizedDerivativeJet
  rw [← hmk]
  rw [div_le_iff₀ (pow_pos C.radius_pos (m + 2))]
  exact hcancel

/-- Complete critical-radius conclusion from the exact four-term recurrence
certificate. -/
theorem FourTermCriticalRadiusCertificate.derivative_radius
    {T : ℕ → ℝ} {d : ℕ} {R q : ℝ}
    (C : FourTermCriticalRadiusCertificate T d R q) :
    ∀ k, k ≤ d → |T k| ≤ R ^ k := by
  have hzero : normalizedDerivativeJet T R 0 ≤ 1 := by
    simpa [normalizedDerivativeJet] using C.zero_jet
  have hone : normalizedDerivativeJet T R 1 ≤ 1 := by
    unfold normalizedDerivativeJet
    rw [pow_one, div_le_iff₀ C.radius_pos]
    simpa using C.one_jet
  have hnormalized := normalizedDerivativeJet_le_one_of_contractive
    C.radius_pos C.contraction_lt_one hzero hone
    (fun M hM hbound k hk2 hkd => C.contractive_step hM hbound hk2 hkd)
  intro k hk
  exact abs_le_radius_pow_of_normalizedDerivativeJet_le_one C.radius_pos
    (hnormalized k hk)

end

end Zeta23.Research.JensenWedge
