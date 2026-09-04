import Mathlib

/-!
# Geometric tail for sixth-order multiplier stability

The analytic stability proof reduces to the geometric series beginning at
order six.  This module checks its exact finite value and strict `1/32` cap.
-/

namespace Zeta23.Research.JensenWedge

/-- Sum of `n` consecutive powers of `1/2`, beginning with `(1/2)^6`. -/
def sixthOrderTail : ℕ → ℚ
  | 0 => 0
  | n + 1 => sixthOrderTail n + (1 / 2 : ℚ) ^ (n + 6)

theorem sixthOrderTail_eq (n : ℕ) :
    sixthOrderTail n = (1 / 32 : ℚ) * (1 - (1 / 2 : ℚ) ^ n) := by
  induction n with
  | zero => norm_num [sixthOrderTail]
  | succ n ih =>
      rw [sixthOrderTail, ih, pow_succ]
      ring

theorem sixthOrderTail_lt (n : ℕ) :
    sixthOrderTail n < (1 / 32 : ℚ) := by
  rw [sixthOrderTail_eq]
  have hpow : 0 < (1 / 2 : ℚ) ^ n := pow_pos (by norm_num) _
  nlinarith

end Zeta23.Research.JensenWedge
