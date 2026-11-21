import DisjointnessFoundations.ProbeMachineInterface
import Mathlib.Analysis.SpecialFunctions.Log.Base

namespace DisjointnessFoundations.Tradeoff

open Filter Real
noncomputable section

def ratio (N w : ℕ) (u : ℝ) : ℝ := logb 2 N / logb 2 (u*w)

theorem log_tends : Tendsto (fun N : ℕ => logb 2 (N:ℝ)) atTop atTop :=
  (tendsto_logb_atTop (by norm_num : (1:ℝ) < 2)).comp tendsto_natCast_atTop_atTop

end
end DisjointnessFoundations.Tradeoff
