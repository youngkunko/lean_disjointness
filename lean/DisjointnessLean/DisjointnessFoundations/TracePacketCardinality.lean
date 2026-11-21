import DisjointnessFoundations.FiniteTraceEncoding
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

namespace DisjointnessFoundations.ShortMessage

open Description
noncomputable section
open Classical

theorem message_bits (w capacity : ℕ) :
    Fintype.card (TraceCode w capacity) ≤ 2^((2*w+1)*capacity+2) := by
  have header (n : ℕ) : n+1 ≤ 2^n := by
    induction n with
    | zero => decide
    | succ n ih => rw [pow_succ]; omega
  calc
    _ = (capacity+1) * ((2:ℕ)^(2*w*capacity) * 3) := by
      simp [TraceCode, Cell, Fintype.card_pi, ←pow_add, ←pow_mul, two_mul]
    _ ≤ (2:ℕ)^capacity * (2^(2*w*capacity) * 2^2) :=
      Nat.mul_le_mul (header _) (Nat.mul_le_mul_left _ (by decide))
    _ = _ := by rw [←pow_add, ←pow_add]; congr 1; ring

end
end DisjointnessFoundations.ShortMessage
