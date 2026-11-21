import DisjointnessFoundations.ProbeMachineInterface
import Mathlib.MeasureTheory.Measure.Typeclasses.Probability
import DisjointnessFoundations.LogarithmicTradeoff

/-! Multiphase Disjointness with n arbitrary indexed subsets of an n-point universe.
An independent tape supplies the randomness. Each fixed history must terminate
with the correct bit on every tape; its query cost is an expectation. -/
namespace DisjointnessDraft
open DisjointnessFoundations DisjointnessFoundations.CellProbe MeasureTheory
open scoped ENNReal
noncomputable section
open Classical

abbrev Family (n : ℕ) := Fin n → Finset (Fin n)

def answer {n : ℕ} (f : Family n) (xs : List (Fin n)) (q : Fin n) : Bool :=
  decide (∀ x ∈ xs, x ∉ f q)

def ZeroError {w : ℕ} {F E Q C Ω : Type} (D : DataStructure w F E Q C)
    (R : RandomTape Ω C) (spec : F → List E → Q → Bool) : Prop :=
  ∀ a f xs q, (finalRun D R a f xs q).map Prod.fst = some (spec f xs q)

def QueryBound {w : ℕ} {F E Q C Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω)
    (D : DataStructure w F E Q C) (R : RandomTape Ω C) (tq : ℝ) : Prop :=
  ∀ f xs q, (∫⁻ a, cost (finalRun D R a f xs q) ∂μ) ≤ ENNReal.ofReal tq

theorem error_of_zero {w : ℕ} {F E Q C Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω)
    {D : DataStructure w F E Q C} {R : RandomTape Ω C} {spec : F → List E → Q → Bool}
    (h : ZeroError D R spec) (δ : ℝ≥0∞) : PointwiseError μ D R spec δ := by
  intro f xs q
  simp [h _ f xs q]

abbrev Machine (n w : ℕ) (C : Type) :=
  DataStructure w (Family n) (Fin n) (Fin n) C

def MainBound : Prop :=
  ∀ lo hi : ℝ, 0<lo → lo≤hi → ∃ c : ℝ, 0<c ∧ ∀ᶠ n : ℕ in Filter.atTop,
    ∀ w tu : ℕ, 1≤tu → lo*Real.logb 2 n≤w → (w:ℝ)≤hi*Real.logb 2 n →
    ∀ (Ω C : Type) [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
      (D : Machine n w C) (R : RandomTape Ω C) (tq : ℝ),
      1≤tq → MeasurableRuns D R → ZeroError D R answer →
      WorstUpdate D R (tu:ℝ≥0∞) → QueryBound μ D R tq →
      c*(Tradeoff.ratio n w tu)^2≤tq

end
end DisjointnessDraft
