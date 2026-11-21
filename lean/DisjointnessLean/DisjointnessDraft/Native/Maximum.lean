import DisjointnessDraft.Native.Main
import DisjointnessDraft.Maximum

namespace DisjointnessDraft.Native
open DisjointnessFoundations CellProbe MeasureTheory Real Filter
open scoped ENNReal

/-- The minimax corollary obtained from the sparse-Disjointness communication proof. -/
theorem maximum (lo hi : ℝ) (lp : 0<lo) (lu : lo≤hi) :
    ∃ c : ℝ, 0<c ∧ ∀ᶠ n : ℕ in atTop, ∀ w tu : ℕ, 1≤tu →
    lo*logb 2 n≤w → (w:ℝ)≤hi*logb 2 n →
    ∀ (Ω C : Type) [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
      (D : Machine n w C) (R : RandomTape Ω C) (tq : ℝ),
      1≤tq → MeasurableRuns D R → ZeroError D R answer → WorstUpdate D R (tu:ℝ≥0∞) → QueryBound μ D R tq →
      c*(FixedFamilySizes.logRatio n)^2≤max (tu:ℝ) tq := DisjointnessDraft.maximum_of main lo hi lp lu

end DisjointnessDraft.Native
