import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Tactic

namespace DisjointnessFoundations.ExtraQueries

noncomputable section

theorem index_room (exponent : ℕ) (lo : ℝ) (hlo : 0 < lo) :
    ∃ words : ℕ, ∀ N M w : ℕ, 0 < N → M ≤ N^exponent →
      lo*Real.logb 2 N ≤ w → M ≤ 2^(words*w) := by
  refine ⟨⌈(exponent : ℝ)/lo⌉₊, ?_⟩
  intro N M w hN hM hw
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  have hlog : 0 ≤ Real.logb 2 (N : ℝ) := Real.logb_nonneg (by norm_num) (by exact_mod_cast hN)
  have hceil : (exponent : ℝ) / lo ≤ (↑⌈(exponent : ℝ)/lo⌉₊ : ℝ) := Nat.le_ceil _
  have hcoeff := (div_le_iff₀ hlo).mp hceil
  have hbound : (exponent : ℝ) * Real.logb 2 N ≤ (↑⌈(exponent : ℝ)/lo⌉₊ : ℝ) * w := by
    calc
      _ ≤ ((↑⌈(exponent : ℝ)/lo⌉₊ : ℝ) * lo) * Real.logb 2 N :=
        mul_le_mul_of_nonneg_right hcoeff hlog
      _ = (↑⌈(exponent : ℝ)/lo⌉₊ : ℝ) * (lo * Real.logb 2 N) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hw (by positivity)
  apply hM.trans
  have hout := Real.rpow_le_rpow_of_exponent_le (show (1 : ℝ) ≤ 2 by norm_num) hbound
  rw [mul_comm (exponent : ℝ),Real.rpow_mul (by norm_num : (0:ℝ) ≤ 2),
    Real.rpow_logb (by norm_num : (0:ℝ) < 2) (by norm_num : (2:ℝ) ≠ 1) hNr,
    Real.rpow_natCast, ← Nat.cast_mul, Real.rpow_natCast] at hout
  exact_mod_cast hout

end
end DisjointnessFoundations.ExtraQueries
