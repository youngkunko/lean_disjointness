import PFR.ForMathlib.Entropy.Basic
import PFR.Mathlib.Probability.Independence.Basic

open MeasureTheory ProbabilityTheory
open scoped BigOperators ProbabilityTheory

namespace DisjointnessFoundations.Information

variable {Ω : Type*} [MeasurableSpace Ω]
variable {A B C : Type*} [Fintype A] [Fintype B] [Fintype C]
  [MeasurableSpace A] [MeasurableSpace B] [MeasurableSpace C]
  [MeasurableSingletonClass A] [MeasurableSingletonClass B] [MeasurableSingletonClass C]

theorem information_le_entropy (μ : Measure Ω) [IsZeroOrProbabilityMeasure μ]
    {X : Ω → A} {Y : Ω → B} (hX : Measurable X) (hY : Measurable Y) :
    I[X : Y ; μ] ≤ H[Y ; μ] := by
  rw [mutualInfo_eq_entropy_sub_condEntropy' hX hY]
  exact sub_le_self _ (condEntropy_nonneg _ _ _)

theorem information_of_function_le (μ : Measure Ω) [IsZeroOrProbabilityMeasure μ]
    {X : Ω → A} {Y : Ω → B} (hX : Measurable X) (hY : Measurable Y) (f : B → C) :
    I[X : f ∘ Y ; μ] ≤ I[X : Y ; μ] := by
  rw [mutualInfo_eq_entropy_sub_condEntropy hX ((measurable_of_finite f).comp hY),
      mutualInfo_eq_entropy_sub_condEntropy hX hY]
  exact sub_le_sub_left (condEntropy_comp_ge μ hY hX f) _

theorem message_chain (μ : Measure Ω) [IsZeroOrProbabilityMeasure μ]
    {X : Ω → A} {Y : Ω → B} {Z : Ω → C} (hX : Measurable X) (hY : Measurable Y)
    (hZ : Measurable Z) :
    I[X : prod Y Z ; μ] = I[X : Z ; μ] + I[X : Y | Z ; μ] := by
  rw [mutualInfo_eq_entropy_sub_condEntropy hX (hY.prodMk hZ),
    mutualInfo_eq_entropy_sub_condEntropy hX hZ, condMutualInfo_eq' hX hY hZ]
  ring

theorem conditional_information_le_entropy (μ : Measure Ω) [IsZeroOrProbabilityMeasure μ]
    {X : Ω → A} {Y : Ω → B} {Z : Ω → C} (hX : Measurable X) (hY : Measurable Y)
    (hZ : Measurable Z) : I[X : Y | Z ; μ] ≤ H[Y ; μ] := by
  rw [condMutualInfo_comm hX hY, condMutualInfo_eq' hY hX hZ]
  exact (sub_le_self _ (condEntropy_nonneg _ _ _)).trans (condEntropy_le_entropy μ hY hZ)

theorem entropy_of_bits (μ : Measure Ω) (Y : Ω → B) (bits : ℕ)
    (hcard : Fintype.card B ≤ 2 ^ bits) : H[Y ; μ] ≤ bits * Real.log 2 := by
  by_cases h : Fintype.card B = 0
  · simpa [h] using (entropy_le_log_card Y μ).trans
      (show Real.log (Fintype.card B : ℝ) ≤ bits * Real.log 2 by
        rw [h]; simp; positivity)
  · refine (entropy_le_log_card Y μ).trans ?_
    rw [←Real.log_pow]
    exact Real.log_le_log (by exact_mod_cast Nat.pos_of_ne_zero h) (by exact_mod_cast hcard)

end DisjointnessFoundations.Information
