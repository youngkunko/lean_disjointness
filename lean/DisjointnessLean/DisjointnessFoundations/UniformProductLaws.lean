import DisjointnessFoundations.EpochSizesAndAverages
import DisjointnessFoundations.FiniteInformationIdentities
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.Probability.UniformOn

namespace DisjointnessFoundations.HardIndependence
open HardDistribution MeasureTheory ProbabilityTheory Set
open scoped BigOperators ProbabilityTheory ENNReal
noncomputable section
open Classical

variable {A B : Type*} [Fintype A] [Fintype B] [MeasurableSpace A] [MeasurableSpace B]
  [MeasurableSingletonClass A] [MeasurableSingletonClass B]

abbrev unif (A : Type*) [MeasurableSpace A] : Measure A := uniformOn univ

instance unif_probability (A : Type*) [Finite A] [Nonempty A] [MeasurableSpace A]
    [MeasurableSingletonClass A] : IsProbabilityMeasure (unif A) :=
  uniformOn_isProbabilityMeasure (Set.toFinite _) Set.univ_nonempty

theorem one_atom (x : A) : (unif A) {x} = (Fintype.card A : ℝ≥0∞)⁻¹ := by
  rw [unif, uniformOn_univ, Measure.count_singleton, one_div]

omit [Fintype B] in
theorem uniform_equiv (e : A ≃ B) : (unif A).map e = unif B := by
  letI := Fintype.ofEquiv A e
  apply Measure.ext_of_singleton
  intro b
  have pre : e ⁻¹' {b} = {e.symm b} := by ext a; simp [Equiv.eq_symm_apply]
  rw [Measure.map_apply (measurable_of_finite e) (.singleton _), pre, one_atom, one_atom,
    Fintype.card_congr e]

theorem uniform_prod : unif (A × B) = (unif A).prod (unif B) := by
  apply Measure.ext_of_singleton
  rintro ⟨a,b⟩
  rw [← Set.singleton_prod_singleton, Measure.prod_prod, Set.singleton_prod_singleton,
    one_atom, one_atom, one_atom, Fintype.card_prod, Nat.cast_mul, ENNReal.mul_inv] <;> simp

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {β : ι → Type*}
  [∀ i, Fintype (β i)] [∀ i, Nonempty (β i)] [∀ i, MeasurableSpace (β i)]
  [∀ i, MeasurableSingletonClass (β i)]

omit [∀ i, Nonempty (β i)] in
theorem uniform_pi : unif (∀ i, β i) = Measure.pi (fun i => unif (β i)) := by
  apply Measure.ext_of_singleton
  intro x
  have sing : ({x} : Set (∀ i, β i)) = univ.pi (fun i => {x i}) := by
    ext y
    simp [funext_iff]
  rw [one_atom, sing, Measure.pi_pi, Fintype.card_pi]
  push_cast
  simp only [one_atom]
  apply ENNReal.prod_inv_distrib
  intro i _ j _ _
  exact Or.inr (ENNReal.natCast_ne_top _)

theorem eval_uniform (i : ι) : (unif (∀ i, β i)).map (fun s => s i) = unif (β i) := by
  apply Measure.ext_of_singleton
  intro x
  rw [Measure.map_apply (measurable_pi_apply i) (.singleton _), uniform_pi]
  change (Measure.pi (fun i => unif (β i))) (Function.eval i ⁻¹' {x}) = _
  rw [← univ_pi_update_univ, Measure.pi_pi, Finset.prod_eq_single i]
  · simp
  · intro j _ hji
    simp [Function.update_of_ne hji]
  · simp

theorem independent_rows : iIndepFun (fun i (s : ∀ j, β j) => s i) (unif (∀ i, β i)) := by
  rw [iIndepFun_iff_map_fun_eq_pi_map (fun i => (measurable_pi_apply i).aemeasurable)]
  simp_rw [eval_uniform]
  simpa using (uniform_pi (β := β))

end
end DisjointnessFoundations.HardIndependence
