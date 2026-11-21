import DisjointnessFoundations.UniformProductLaws

namespace DisjointnessFoundations.ProtocolCorrelation
open MeasureTheory ProbabilityTheory
open scoped ProbabilityTheory BigOperators
noncomputable section
open Classical

theorem lift_independence {Ω T A B : Type*} [MeasurableSpace Ω] [MeasurableSpace T]
    [MeasurableSpace A] [MeasurableSpace B] (μ : Measure Ω) (ν : Measure T)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] {X : Ω → A} {Y : Ω → B}
    (hX : Measurable X) (hY : Measurable Y) (ind : IndepFun X Y μ) :
    IndepFun (X ∘ Prod.fst) (Y ∘ Prod.fst) (μ.prod ν) := by
  rw [indepFun_iff_map_prod_eq_prod_map_map (hX.comp measurable_fst).aemeasurable
      (hY.comp measurable_fst).aemeasurable]
  change (μ.prod ν).map ((prod X Y) ∘ Prod.fst) =
    ((μ.prod ν).map (X ∘ Prod.fst)).prod ((μ.prod ν).map (Y ∘ Prod.fst))
  simp only [← Measure.map_map (hX.prodMk hY) measurable_fst,
    ← Measure.map_map hX measurable_fst, ← Measure.map_map hY measurable_fst,
    Measure.map_fst_prod, measure_univ, one_smul]
  exact (indepFun_iff_map_prod_eq_prod_map_map hX.aemeasurable hY.aemeasurable).mp ind

end
end DisjointnessFoundations.ProtocolCorrelation
