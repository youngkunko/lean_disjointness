import DisjointnessFoundations.EpochPopulation
import Mathlib.Tactic.GCongr

namespace DisjointnessFoundations.Parameters

open Statement HardDistribution Finset

theorem size_succ (ℓ g : ℕ) : problemSize (ℓ+1) g = problemSize ℓ g + g^(2*(ℓ+1)) := by
  simp [problemSize, Fin.sum_univ_castSucc, epochSize]

theorem size_lower {ℓ g : ℕ} (hl : 0 < ℓ) : g^(2*ℓ) ≤ problemSize ℓ g := by
  cases ℓ with
  | zero => omega
  | succ ℓ => rw [size_succ]; omega

theorem size_upper (ℓ : ℕ) {g : ℕ} (hg : 2 ≤ g) : problemSize ℓ g ≤ 2*g^(2*ℓ) := by
  induction ℓ with
  | zero => simp [problemSize]
  | succ ℓ ih =>
    have h : 2 ≤ g^2 := by nlinarith
    have hb := Nat.mul_le_mul_left (g^(2*ℓ)) h
    rw [size_succ, show 2 * (ℓ+1) = 2*ℓ+2 by omega, pow_add]
    nlinarith only [ih,hb]

theorem earlier_size {ℓ g : ℕ} (hg : 2 ≤ g) (i : Fin ℓ) :
    problemSize i.val g * g^2 ≤ 2 * epochSize g i := by
  have h := Nat.mul_le_mul_right (g^2) (size_upper i.val hg)
  simpa [epochSize, show 2 * (i.val+1) = 2*i.val+2 by omega, pow_add, mul_assoc] using h

theorem ell_le_size {ℓ g : ℕ} (hg : 0 < g) : ℓ ≤ problemSize ℓ g := by
  unfold problemSize
  calc ℓ = ∑ _i : Fin ℓ, 1 := by simp
       _ ≤ _ := Finset.sum_le_sum (fun i _ => pow_pos hg _)

end DisjointnessFoundations.Parameters
