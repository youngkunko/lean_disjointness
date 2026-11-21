import DisjointnessFoundations.UniformProductLaws

namespace DisjointnessFoundations.ActualAcceptance
open HardIndependence MeasureTheory
open scoped ENNReal
noncomputable section
open Classical

theorem real_unif_atom {X : Type} [Fintype X] [MeasurableSpace X] [MeasurableSingletonClass X]
    (x : X) : (unif X).real {x} = (Fintype.card X : ℝ)⁻¹ := by
  simp [measureReal_def, one_atom, ENNReal.toReal_inv]

end
end DisjointnessFoundations.ActualAcceptance
