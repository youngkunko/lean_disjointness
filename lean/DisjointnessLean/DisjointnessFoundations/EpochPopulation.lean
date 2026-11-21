import Mathlib.Analysis.SpecialFunctions.Log.Base
import DisjointnessFoundations.ProbeMachineInterface
import DisjointnessFoundations.EpochSizesAndAverages

namespace DisjointnessFoundations.Statement

open HardDistribution
open scoped BigOperators

def problemSize (ℓ g : ℕ) : ℕ := ∑ i : Fin ℓ, epochSize g i

end DisjointnessFoundations.Statement
