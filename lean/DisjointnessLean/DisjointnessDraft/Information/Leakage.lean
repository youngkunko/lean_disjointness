import DisjointnessDraft.Information.Charges

namespace DisjointnessDraft.Information
open MeasureTheory ProbabilityTheory DisjointnessFoundations.HardIndependence DisjointnessFoundations.EntropyBridge
open scoped ProbabilityTheory BigOperators ENNReal
noncomputable section
open Classical

variable {m N s : ℕ} {W O R U P A : Type*}
  [Fintype W] [MeasurableSpace W] [MeasurableSingletonClass W] [Nonempty W]
  [Fintype O] [MeasurableSpace O] [MeasurableSingletonClass O]
  [Fintype R] [MeasurableSpace R] [MeasurableSingletonClass R]
  [adviceFinite : Fintype U] [adviceMeasurable : MeasurableSpace U] [singleAdvice : MeasurableSingletonClass U]
  [Fintype P] [packetMeasurable : MeasurableSpace P] [singlePacket : MeasurableSingletonClass P]
  [Fintype A] [responseMeasurable : MeasurableSpace A] [singleResponse : MeasurableSingletonClass A] [nonemptyLayer : Nonempty (Layer N s)]

/-- Even a prediction chosen from the whole family, outside updates, and
private randomness succeeds with probability exactly one uniform atom. -/
theorem blind_guess (o : Measure O) (r : Measure R) [IsProbabilityMeasure o] [IsProbabilityMeasure r]
    (f : Family m W → O × R → Layer N s) :
    (experiment m N s W o r).real {v | v.2.1=f v.1 v.2.2} = (Fintype.card (Layer N s):ℝ)⁻¹ := by
  -- Keep the original theorem signature for existing clients.
  let _compat_1 := nonemptyLayer
  unfold experiment
  rw [measureReal_def,Measure.prod_apply (Set.toFinite _).measurableSet]
  have inner (F : Family m W) :
      ((unif (Layer N s)).prod (o.prod r)) ((fun v => (F,v)) ⁻¹' {v | v.2.1=f v.1 v.2.2}) =
        (Fintype.card (Layer N s):ℝ≥0∞)⁻¹ := by
    rw [Measure.prod_apply_symm (Set.toFinite _).measurableSet]
    change ∫⁻ y, (unif (Layer N s)) {f F y} ∂(o.prod r) = _
    simp [one_atom]
  simp_rw [inner]
  simp

def guessAtom {L : Type*} [Fintype L] [Nonempty L] (p : L → ℝ) : L :=
  Classical.choose (Finset.exists_max_image Finset.univ p Finset.univ_nonempty)

theorem guess_max {L : Type*} [Fintype L] [Nonempty L] (p : L → ℝ) (x : L) : p x≤p (guessAtom p) :=
  (Classical.choose_spec (Finset.exists_max_image Finset.univ p Finset.univ_nonempty)).2 x (Finset.mem_univ x)

/-- The accepted joint mass of the best guess in every transcript has a
single packet-alphabet bound; no cost is charged for the verification bit. -/
theorem packet_guess (G : Game m N s W O R U P A) (o : Measure O) (r : Measure R)
    [IsProbabilityMeasure o] [IsProbabilityMeasure r] (q : Fin m) (g : View m W O P A→Layer N s) :
    (∑ z, (experiment m N s W o r).real ((G.label q ⁻¹' {(z,true)}) ∩
      ((fun v : World m N s W O R => v.2.1) ⁻¹' {g z}))) ≤ Fintype.card P/(Fintype.card (Layer N s):ℝ) := by
  -- Keep the original theorem signature for existing clients.
  let _compat_1 := adviceFinite
  let _compat_2 := adviceMeasurable
  let _compat_3 := singleAdvice
  let _compat_4 := packetMeasurable
  let _compat_5 := singlePacket
  let _compat_6 := responseMeasurable
  let _compat_7 := singleResponse
  let μ := experiment m N s W o r
  let C := fun z => (G.label q ⁻¹' {(z,true)}) ∩ ((fun v : World m N s W O R => v.2.1) ⁻¹' {g z})
  let predict := fun ψ (F : Family m W) (y : O×R) => g (((y.1,ψ),G.reply F y.1 ψ),rowPrefix q.val F)
  let E := fun ψ => {v : World m N s W O R | v.2.1=predict ψ v.1 v.2.2}
  have dis : Pairwise (fun z t => Disjoint (C z) (C t)) := by
    intro z t ne
    apply Set.disjoint_left.mpr
    intro v v₁ v₂
    exact ne (congrArg Prod.fst ((show G.label q v=(z,true) from v₁.1).symm.trans (show G.label q v=(t,true) from v₂.1)))
  have sub : (⋃z,C z) ⊆ ⋃ψ,E ψ := by
    intro v hv
    obtain ⟨z,hz⟩ := Set.mem_iUnion.mp hv
    apply Set.mem_iUnion.mpr
    refine ⟨G.psi v,?_⟩
    have view := congrArg Prod.fst (show G.label q v=(z,true) from hz.1)
    change G.observed q v=z at view
    exact (show v.2.1=g z from hz.2).trans (congrArg g view.symm)
  calc _ = μ.real (⋃z,C z) := (measureReal_iUnion_fintype dis (fun _ => (Set.toFinite _).measurableSet)).symm
       _ ≤ μ.real (⋃ψ,E ψ) := measureReal_mono sub
       _ ≤ ∑ψ, μ.real (E ψ) := measureReal_iUnion_fintype_le E
       _ = _ := by
         have atom (ψ : P) : μ.real (E ψ)=(Fintype.card (Layer N s):ℝ)⁻¹ := blind_guess o r (predict ψ)
         simp [atom,div_eq_mul_inv]

/-- The same guessing bound expressed with the actual per-label posterior. -/
theorem posterior_guess (G : Game m N s W O R U P A) (o : Measure O) (r : Measure R)
    [IsProbabilityMeasure o] [IsProbabilityMeasure r] (q : Fin m) :
    let μ := experiment m N s W o r
    let x := fun v : World m N s W O R => v.2.1
    let px := fun z => posterior μ x (measurable_of_finite x) (G.label q) (z,true)
    ∑ z, (law μ (G.label q) (measurable_of_finite _)).weight (z,true) * (px z).weight (guessAtom (px z).weight)
      ≤ Fintype.card P/(Fintype.card (Layer N s):ℝ) := by
  dsimp only
  simp_rw [posterior_weight]
  exact packet_guess G o r q _

end
end DisjointnessDraft.Information
