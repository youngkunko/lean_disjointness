import DisjointnessDraft.Native.Main
import DisjointnessFoundations.AppendSelectorReduction

/-! Strict insertion histories. Only observations and time guarantees on
histories with fresh keys are needed. The cutoff makes off-promise executions
total without changing any charged hard trial. -/
namespace DisjointnessDraft.Fresh
open DisjointnessFoundations CellProbe MeasureTheory Real Filter
open scoped ENNReal
noncomputable section
open Classical

variable {n w : ℕ} {Ω C : Type} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
variable (D : Machine n w C) (R : RandomTape Ω C)

structure OnFresh (tu : ℕ) (tq : ℝ) : Prop where
  pays : ∀ a f xs, xs.Nodup → SingleSelector.Pays D R tu a f xs
  right : ∀ a f xs q, xs.Nodup → (finalRun D R a f xs q).map Prod.fst = some (DisjointnessDraft.answer f xs q)
  measurable : ∀ f xs q, xs.Nodup → Measurable (fun a => cost (finalRun D R a f xs q))
  query : ∀ f xs q, xs.Nodup → (∫⁻ a, cost (finalRun D R a f xs q) ∂μ)≤ENNReal.ofReal tq

theorem lower (lo hi : ℝ) (lp : 0<lo) (lu : lo≤hi) :
    ∃ c : ℝ, 0<c ∧ ∀ᶠ n : ℕ in atTop, ∀ w tu : ℕ, 0<w → 0<tu → lo*logb 2 n≤w → (w:ℝ)≤hi*logb 2 n →
    ∀ (Ω C : Type) [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
      (D : Machine n w C) (R : RandomTape Ω C) (tq : ℝ), 1≤tq → OnFresh μ D R tu tq →
      c*(Tradeoff.ratio n w tu)^2≤tq := by
  obtain ⟨c,cp,H⟩ := Native.main_on_fresh lo hi lp lu
  refine ⟨c,cp,?_⟩
  filter_upwards [H] with n low
  intro w tu wp up wl wh Ω C _ μ _ D R tq qp cls
  let B := UpdateCutoff.machine D tu
  have same (a : Ω) (f : Family n) (xs : List (Fin n)) (q : Fin n) (nd : xs.Nodup) :
      finalRun B R a f xs q=finalRun D R a f xs q := by
    unfold finalRun
    rw [show prefixRun B R a f xs=prefixRun D R a f xs from
      SingleSelector.agrees D R tu a f xs (cls.pays a f xs nd)]
    rfl
  apply low w tu up wl wh Ω C μ B R tq qp _ _ (UpdateCutoff.worst D R tu) _
  · intro f xs q nd
    simpa only [same _ _ _ _ nd] using cls.measurable f xs q nd
  · intro a f xs q nd; rw [same _ _ _ _ nd]; exact cls.right a f xs q nd
  · intro f xs q nd
    simpa only [same _ _ _ _ nd] using cls.query f xs q nd

end
end DisjointnessDraft.Fresh
