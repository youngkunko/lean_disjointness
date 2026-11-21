import DisjointnessFoundations.FiniteInformationIdentities
import DisjointnessFoundations.FiniteRelativeEntropy

open MeasureTheory ProbabilityTheory
open scoped ProbabilityTheory BigOperators

namespace DisjointnessFoundations.EntropyBridge
open FiniteSampling InformationLoss
noncomputable section

variable {Ω A L : Type*} [MeasurableSpace Ω]
  [Fintype A] [MeasurableSpace A] [MeasurableSingletonClass A]
  [Fintype L] [MeasurableSpace L] [MeasurableSingletonClass L]

def law (μ : Measure Ω) [IsProbabilityMeasure μ] (X : Ω → A) (hX : Measurable X) :
    InputLaw A where
  weight a := μ.real (X ⁻¹' {a})
  nonneg _ := measureReal_nonneg
  total := by
    rw [sum_measureReal_preimage_singleton Finset.univ (fun a _ => hX (.singleton a))]
    simp

omit [MeasurableSpace A] [MeasurableSingletonClass A] in
def shannon (p : InputLaw A) := ∑ a, Real.negMulLog (p.weight a)

theorem entropy_law (μ : Measure Ω) [IsProbabilityMeasure μ] (X : Ω → A) (hX : Measurable X) :
    H[X ; μ] = shannon (law μ X hX) := by
  rw [entropy_eq_sum, tsum_fintype]
  simp only [shannon, law, map_measureReal_apply hX (.singleton _)]

omit [Fintype L] [MeasurableSpace L] [MeasurableSingletonClass L] in
def posterior (μ : Measure Ω) [IsProbabilityMeasure μ] (X : Ω → A) (hX : Measurable X)
    (Y : Ω → L) (l : L) : InputLaw A :=
  if h : μ (Y ⁻¹' {l}) = 0 then law μ X hX else
    letI := cond_isProbabilityMeasure h
    law μ[|Y ← l] X hX

theorem posterior_weight (μ : Measure Ω) [IsProbabilityMeasure μ] (X : Ω → A)
    (hX : Measurable X) (Y : Ω → L) (hY : Measurable Y) (l : L) (a : A) :
    (law μ Y hY).weight l * (posterior μ X hX Y l).weight a =
      μ.real ((Y ⁻¹' {l}) ∩ (X ⁻¹' {a})) := by
  by_cases h : μ (Y ⁻¹' {l}) = 0
  · have h' := measure_mono_null (μ := μ) (Set.inter_subset_left : (Y ⁻¹' {l}) ∩ (X ⁻¹' {a}) ⊆ Y ⁻¹' {l}) h
    simp [law, measureReal_def, h, h']
  · have hn : μ.real (Y ⁻¹' {l}) ≠ 0 := by
      exact fun hz => h ((measureReal_eq_zero_iff (measure_ne_top _ _)).mp hz)
    simp only [posterior, dif_neg h, law, cond_real_apply (hY (.singleton l))]
    rw [mul_inv_cancel_left₀ hn]

theorem posterior_marginal (μ : Measure Ω) [IsProbabilityMeasure μ] (X : Ω → A)
    (hX : Measurable X) (Y : Ω → L) (hY : Measurable Y) (a : A) :
    (marginal (law μ Y hY) (posterior μ X hX Y)).weight a = (law μ X hX).weight a := by
  simp only [marginal, posterior_weight]
  change _ = μ.real (X ⁻¹' {a})
  have sums := sum_measureReal_preimage_singleton (μ := μ.restrict (X ⁻¹' {a})) Finset.univ
      (fun l _ => hY (.singleton l))
  simpa only [measureReal_restrict_apply (hY (.singleton _)), Finset.coe_univ, Set.preimage_univ,
    measureReal_restrict_apply MeasurableSet.univ, Set.univ_inter] using sums

omit [Fintype L] [MeasurableSpace L] [MeasurableSingletonClass L] in
theorem posterior_ac (μ : Measure Ω) [IsProbabilityMeasure μ] (X : Ω → A)
    (hX : Measurable X) (Y : Ω → L) (l : L) (a : A) (ha : (law μ X hX).weight a = 0) :
    (posterior μ X hX Y l).weight a = 0 := by
  unfold posterior
  split_ifs
  · exact ha
  · exact (measureReal_eq_zero_iff (measure_ne_top _ _)).mpr
      (cond_absolutelyContinuous ((measureReal_eq_zero_iff (measure_ne_top _ _)).mp ha))

omit [MeasurableSpace A] [MeasurableSpace L] [MeasurableSingletonClass A] [MeasurableSingletonClass L] in
theorem information_entropy_gap (w : InputLaw L) (q : L → InputLaw A)
    (ac : ∀ l a, (marginal w q).weight a = 0 → (q l).weight a = 0) :
    jointInformation w q (marginal w q) =
      shannon (marginal w q) - ∑ l, w.weight l * shannon (q l) := by
  let p := marginal w q
  have term (l : L) (a : A) :
      (q l).weight a * Real.log ((q l).weight a / p.weight a) =
        - Real.negMulLog ((q l).weight a) - (q l).weight a * Real.log (p.weight a) := by
    by_cases h : (q l).weight a = 0
    · simp [h, Real.negMulLog]
    · rw [Real.log_div h (fun h' => h (ac l a h'))]
      simp only [Real.negMulLog]
      ring
  change jointInformation w q p = _
  unfold jointInformation kl shannon
  change (∑ l, w.weight l * ∑ a, (q l).weight a * Real.log ((q l).weight a / p.weight a)) =
    (∑ a, Real.negMulLog (p.weight a)) - ∑ l, w.weight l * ∑ a, Real.negMulLog ((q l).weight a)
  simp_rw [term, Finset.mul_sum]
  rw [Finset.sum_comm]
  nth_rw 2 [Finset.sum_comm]
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro a _
  simp_rw [mul_sub, mul_neg, ← mul_assoc, Finset.sum_sub_distrib, Finset.sum_neg_distrib]
  rw [← Finset.sum_mul]
  change -(∑ l, w.weight l * Real.negMulLog ((q l).weight a)) - p.weight a * Real.log (p.weight a) = _
  rw [Real.negMulLog]
  ring

theorem conditional_entropy_law (μ : Measure Ω) [IsProbabilityMeasure μ] (X : Ω → A)
    (hX : Measurable X) (Y : Ω → L) (hY : Measurable Y) :
    H[X | Y ; μ] = ∑ l, (law μ Y hY).weight l * shannon (posterior μ X hX Y l) := by
  rw [condEntropy_eq_sum_fintype X Y μ hY]
  apply Finset.sum_congr rfl
  intro l _
  by_cases h : μ (Y ⁻¹' {l}) = 0
  · simp [law, measureReal_def, h]
  · letI := cond_isProbabilityMeasure h
    rw [posterior, dif_neg h, ← entropy_law]
    rfl

private theorem eq_of_weight {U : Type*} [Fintype U] (p q : InputLaw U)
    (same : p.weight = q.weight) : p = q := by
  cases p
  cases q
  cases same
  rfl

private theorem marginal_eq (μ : Measure Ω) [IsProbabilityMeasure μ] (X : Ω → A)
    (hX : Measurable X) (Y : Ω → L) (hY : Measurable Y) :
    marginal (law μ Y hY) (posterior μ X hX Y) = law μ X hX := by
  exact eq_of_weight _ _ (funext (posterior_marginal μ X hX Y hY))

theorem information_bits (μ : Measure Ω) [IsProbabilityMeasure μ] (X : Ω → A)
    (hX : Measurable X) (Y : Ω → L) (hY : Measurable Y) :
    mutualInformationBits (law μ Y hY) (posterior μ X hX Y) = I[X : Y ; μ] / Real.log 2 := by
  unfold mutualInformationBits
  rw [information_entropy_gap _ _ (fun l a h => posterior_ac μ X hX Y l a (by
      rwa [marginal_eq] at h)), marginal_eq, ← entropy_law, ← conditional_entropy_law μ X hX Y hY,
    mutualInfo_eq_entropy_sub_condEntropy hX hY]

theorem expected_posterior_kl (μ : Measure Ω) [IsProbabilityMeasure μ] (X : Ω → A)
    (hX : Measurable X) (Y : Ω → L) (hY : Measurable Y) :
    ∑ l, (law μ Y hY).weight l * klBits (posterior μ X hX Y l).weight (law μ X hX).weight =
      I[X : Y ; μ] / Real.log 2 := by
  rw [← information_bits μ X hX Y hY]
  simp_rw [mutualInformationBits, marginal_eq, jointInformation, klBits, Finset.sum_div,
    mul_div_assoc]

theorem joint_product_kl (μ : Measure Ω) [IsProbabilityMeasure μ] (X : Ω → A)
    (hX : Measurable X) (Y : Ω → L) (hY : Measurable Y) :
    klBits (law μ (prod Y X) (hY.prodMk hX)).weight
      (fun p : L × A => (law μ Y hY).weight p.1 * (law μ X hX).weight p.2) =
      I[X : Y ; μ] / Real.log 2 := by
  rw [← expected_posterior_kl μ X hX Y hY]
  simp_rw [klBits, ← mul_div_assoc]
  rw [← Finset.sum_div]
  unfold kl
  simp_rw [Fintype.sum_prod_type, Finset.mul_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro l _
  apply Finset.sum_congr rfl
  intro a _
  have heq : (law μ (prod Y X) (hY.prodMk hX)).weight (l,a) =
      (law μ Y hY).weight l * (posterior μ X hX Y l).weight a := by
    rw [posterior_weight]
    have pre : (prod Y X) ⁻¹' {(l,a)} = (Y ⁻¹' {l}) ∩ (X ⁻¹' {a}) := by
      ext ω
      simp
    change μ.real ((prod Y X) ⁻¹' {(l,a)}) = _
    rw [pre]
  rw [heq]
  by_cases h : (law μ Y hY).weight l = 0
  · simp [h]
  · rw [mul_div_mul_left _ _ h, mul_assoc]

end
end DisjointnessFoundations.EntropyBridge
