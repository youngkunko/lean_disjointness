import DisjointnessFoundations.FiniteBernoulliLaw
import Mathlib.Probability.ProbabilityMassFunction.Constructions
import Mathlib.MeasureTheory.Measure.Real

namespace DisjointnessFoundations.ProtocolInformation

open FiniteSampling MeasureTheory
open scoped BigOperators ENNReal
noncomputable section
open Classical

variable {n : ℕ}

def bitWeight (r : SamplingRate) (b : Fin n → Bool) : ℝ :=
  ∏ i, if b i then r.p else 1-r.p

theorem bitWeight_nonneg (r : SamplingRate) (b : Fin n → Bool) : 0 ≤ bitWeight r b :=
  weight_nonneg r b

theorem bitMean_eq (r : SamplingRate) (n : ℕ) (f : List Bool → ℝ) :
    bitMean r.p n f = ∑ b : Fin n → Bool, bitWeight r b * f (List.ofFn b) := rfl

def pmf {B : Type} [Fintype B] (m : InputLaw B) : PMF B :=
  PMF.ofFintype (fun b => ENNReal.ofReal (m.weight b)) (by
    rw [← ENNReal.ofReal_sum_of_nonneg (fun b _ => m.nonneg b), m.total, ENNReal.ofReal_one])

theorem pmf_real {B : Type} [Fintype B] [MeasurableSpace B] [MeasurableSingletonClass B]
    (m : InputLaw B) (S : Set B) :
    (pmf m).toMeasure.real S = ∑ x, if x ∈ S then m.weight x else 0 := by
  rw [measureReal_def, PMF.toMeasure_apply_fintype]
  have fin : ∀ x ∈ (Finset.univ : Finset B), S.indicator (pmf m) x ≠ ∞ := by
    intro x _
    by_cases h : x ∈ S <;> simp [Set.indicator_apply, h, pmf]
  rw [ENNReal.toReal_sum fin]
  apply Finset.sum_congr rfl
  intro x _
  by_cases h : x ∈ S <;> simp [Set.indicator_apply, h, pmf, m.nonneg x]

end
end DisjointnessFoundations.ProtocolInformation
