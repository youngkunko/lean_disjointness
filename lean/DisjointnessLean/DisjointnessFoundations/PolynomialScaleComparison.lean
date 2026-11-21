import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Tactic.NormNum

namespace DisjointnessFoundations.ApplicationSizes

open Real
noncomputable section

theorem log_range {M N : ℕ} (m : 2≤M) (lo : M≤N) (hi : N≤M^3) :
    logb 2 M ≤ logb 2 N ∧ logb 2 N ≤ 3*logb 2 M := by
  have mpos : 0 < (M:ℝ) := by exact_mod_cast (by omega : 0 < M)
  have order : (M:ℝ) ≤ N := by exact_mod_cast lo
  have cube : (N:ℝ) ≤ (M:ℝ)^3 := by exact_mod_cast hi
  refine ⟨logb_le_logb_of_le (by norm_num) mpos order, ?_⟩
  have h := logb_le_logb_of_le (b:=2) (by norm_num) (mpos.trans_le order) cube
  simpa [logb_pow] using h

end
end DisjointnessFoundations.ApplicationSizes
