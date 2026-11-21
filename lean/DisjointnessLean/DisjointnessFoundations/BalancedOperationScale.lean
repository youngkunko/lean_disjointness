import Mathlib.Analysis.SpecialFunctions.Log.Base

namespace DisjointnessFoundations.FixedFamilySizes

noncomputable section

def logRatio (n : ℕ) : ℝ := Real.logb 2 n / Real.logb 2 (Real.logb 2 n)

end
end DisjointnessFoundations.FixedFamilySizes
