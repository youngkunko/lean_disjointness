import DisjointnessFoundations.FiniteInformationIdentities

open MeasureTheory ProbabilityTheory
open scoped ProbabilityTheory BigOperators

namespace DisjointnessFoundations.Correlation

open Information

variable {Ω : Type*} [MeasurableSpace Ω]
variable {A B C D E : Type*} [Fintype A] [Fintype B] [Fintype C] [Fintype D] [Fintype E]
  [MeasurableSpace A] [MeasurableSpace B] [MeasurableSpace C] [MeasurableSpace D]
  [MeasurableSpace E] [MeasurableSingletonClass A] [MeasurableSingletonClass B]
  [MeasurableSingletonClass C] [MeasurableSingletonClass D] [MeasurableSingletonClass E]

theorem advice_budget (μ : Measure Ω) [IsProbabilityMeasure μ] {family : Ω → A}
    {data : Ω → B} {advice : Ω → C} (hF : Measurable family) (hD : Measurable data)
    (hA : Measurable advice) (ind : IndepFun family data μ)
    (target : C × B → D) (message : C × B → E) :
    I[family : target ∘ prod advice data | message ∘ prod advice data ; μ] ≤ H[advice ; μ] := by
  have hT := (measurable_of_finite target).comp (hA.prodMk hD)
  have hM := (measurable_of_finite message).comp (hA.prodMk hD)
  have h₁ := message_chain μ hF hT hM
  have h₂ := information_of_function_le μ hF (hA.prodMk hD) (prod target message)
  have h₃ := message_chain μ hF hA hD
  rw [ind.mutualInfo_eq_zero hF hD, zero_add] at h₃
  exact (show I[family : target ∘ prod advice data | message ∘ prod advice data ; μ] ≤
      I[family : prod advice data ; μ] by
        change I[family : prod (target ∘ prod advice data) (message ∘ prod advice data) ; μ] ≤
          I[family : prod advice data ; μ] at h₂
        linarith [mutualInfo_nonneg hF hM μ]).trans
    (h₃ ▸ conditional_information_le_entropy μ hF hA hD)

theorem project_conditioned (μ : Measure Ω) [IsProbabilityMeasure μ]
    {X : Ω → A} {Y : Ω → B} {Z : Ω → C}
    (hX : Measurable X) (hY : Measurable Y) (hZ : Measurable Z) (f : A → D) (g : B → E) :
    I[f ∘ X : g ∘ Y | Z ; μ] ≤ I[X : Y | Z ; μ] := by
  rw [condMutualInfo_eq_sum' hZ, condMutualInfo_eq_sum' hZ]
  apply Finset.sum_le_sum
  intro z _
  refine mul_le_mul_of_nonneg_left ?_ (measureReal_nonneg)
  have hfx := (measurable_of_finite f).comp hX
  have hgy := (measurable_of_finite g).comp hY
  exact (information_of_function_le _ hfx hY g).trans (by
    rw [mutualInfo_comm hfx hY, mutualInfo_comm hX hY]
    exact information_of_function_le _ hY hX f)

end DisjointnessFoundations.Correlation
