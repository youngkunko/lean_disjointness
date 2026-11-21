import DisjointnessFoundations.FiniteMaskMeasures
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.MeasureTheory.Integral.Lebesgue.Countable

namespace DisjointnessFoundations.VerifierLaw

open MeasureTheory FiniteSampling ProtocolInformation
open scoped ENNReal BigOperators
noncomputable section
open Classical

theorem prod_event {X C : Type} [Fintype X] [MeasurableSpace X] [MeasurableSingletonClass X]
    [MeasurableSpace C] (μ : Measure X) (ν : Measure C) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (E : Set (X × C)) (hE : MeasurableSet E) :
    (μ.prod ν).real E = ∑ x, μ.real {x} * ν.real (Prod.mk x ⁻¹' E) := by
  rw [measureReal_def, Measure.prod_apply hE, lintegral_fintype, ENNReal.toReal_sum]
  · simp only [measureReal_def, ENNReal.toReal_mul, mul_comm]
  · intro x _
    exact ENNReal.mul_ne_top (measure_ne_top _ _) (measure_ne_top _ _)

def maskWeights (r : SamplingRate) (n : ℕ) : InputLaw (Fin n → Bool) where
  weight := bitWeight r
  nonneg := bitWeight_nonneg r
  total := totalWeights r.p n

def masks (r : SamplingRate) (n : ℕ) : Measure (Fin n → Bool) :=
  (pmf (maskWeights r n)).toMeasure

instance (r : SamplingRate) (n : ℕ) : IsProbabilityMeasure (masks r n) := by
  unfold masks
  infer_instance

theorem mask_atom (r : SamplingRate) {n : ℕ} (mask : Fin n → Bool) :
    (masks r n).real {mask} = bitWeight r mask := by
  unfold masks
  rw [pmf_real]
  simp [maskWeights]

end
end DisjointnessFoundations.VerifierLaw
