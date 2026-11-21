import DisjointnessDraft.Information.Leakage
import DisjointnessDraft.Information.Smoothing

namespace DisjointnessDraft.Information
open Finset Real MeasureTheory ProbabilityTheory DisjointnessFoundations.HardIndependence DisjointnessFoundations.EntropyBridge DisjointnessFoundations.InformationLoss
open scoped ProbabilityTheory BigOperators
noncomputable section
open Classical

theorem true_part {Z : Type*} [Fintype Z] (f : Z×Bool→ℝ) (nonneg : ∀v,0≤f v) :
    (∑z,f (z,true))≤∑v,f v := by
  rw [Fintype.sum_prod_type]
  exact sum_le_sum (fun z _ => single_le_sum (fun b _ => nonneg (z,b)) (mem_univ true))

variable {m N s : ℕ} {W O R U P A : Type*}
  [Fintype W] [MeasurableSpace W] [MeasurableSingletonClass W] [Nonempty W]
  [Fintype O] [MeasurableSpace O] [MeasurableSingletonClass O]
  [Fintype R] [MeasurableSpace R] [MeasurableSingletonClass R]
  [Fintype U] [MeasurableSpace U] [MeasurableSingletonClass U]
  [Fintype P] [MeasurableSpace P] [MeasurableSingletonClass P]
  [Fintype A] [MeasurableSpace A] [MeasurableSingletonClass A] [Nonempty (Layer N s)]

namespace Game
variable (G : Game m N s W O R U P A) (o : Measure O) (r : Measure R) [IsProbabilityMeasure o] [IsProbabilityMeasure r]
abbrev Key (m : ℕ) (W O P A : Type*) := Fin m × View m W O P A
def event (v : Key m W O P A) := G.label v.1 ⁻¹' {(v.2,true)}
def mass (v : Key m W O P A) := (experiment m N s W o r).real (G.event v)
def qcost (v : Key m W O P A) :=
  kl (posterior (experiment m N s W o r) (G.row v.1) (measurable_of_finite _) (G.label v.1) (v.2,true)).weight
    (flat (Layer N s)).weight
def corr (v : Key m W O P A) :=
  I[G.row v.1 : (fun w => w.2.1) ; (experiment m N s W o r)[|G.event v]]
def atomCost (v : Key m W O P A) :=
  let μ := experiment m N s W o r
  let x := fun w : World m N s W O R => w.2.1
  let p := posterior μ x (measurable_of_finite x) (G.label v.1) (v.2,true)
  p.weight (guessAtom p.weight)*Fintype.card (Layer N s)

theorem mass_sum (pos : 0<m) : ∑ v,G.mass o r v=m*acceptance G o r := by
  -- Retain the existing section parameters for this theorem interface.
  have _apiInstances := ((inferInstance : Fintype U), (inferInstance : MeasurableSpace U), (inferInstance : MeasurableSpace P), (inferInstance : MeasurableSpace A))
  have _apiSingletonU := (inferInstance : MeasurableSingletonClass U)
  have _apiSingletonP := (inferInstance : MeasurableSingletonClass P)
  have _apiSingletonA := (inferInstance : MeasurableSingletonClass A)
  let μ := experiment m N s W o r
  rw [acceptance,mul_div_cancel₀ _ (by exact_mod_cast pos.ne' : (m:ℝ)≠0),Fintype.sum_prod_type]
  apply sum_congr rfl; intro q _
  let S := fun z : View m W O P A => G.event (q,z)
  have dis : Pairwise (fun u v => Disjoint (S u) (S v)) := by
    intro u v ne; apply Set.disjoint_left.mpr; intro w h k
    exact ne (congrArg Prod.fst ((show G.label q w=(u,true) from h).symm.trans k))
  have eq : (⋃z,S z)=G.accepted q ⁻¹' {true} := by
    ext w; constructor
    · intro h; obtain ⟨z,hz⟩ := Set.mem_iUnion.mp h
      exact congrArg Prod.snd (show G.label q w=(z,true) from hz)
    · intro h; exact Set.mem_iUnion.mpr ⟨G.observed q w,Prod.ext rfl h⟩
  exact (measureReal_iUnion_fintype (μ:=μ) dis (fun _ => (Set.toFinite _).measurableSet)).symm.trans (congrArg μ.real eq)

theorem qcost_nonnegative (v : Key m W O P A) : 0≤G.qcost o r v := by
  -- Retain the existing section parameters for this theorem interface.
  have _apiInstances := ((inferInstance : Fintype U), (inferInstance : MeasurableSpace U), (inferInstance : Fintype P), (inferInstance : MeasurableSpace P), (inferInstance : Fintype A), (inferInstance : MeasurableSpace A))
  have _apiSingletonU := (inferInstance : MeasurableSingletonClass U)
  have _apiSingletonP := (inferInstance : MeasurableSingletonClass P)
  have _apiSingletonA := (inferInstance : MeasurableSingletonClass A)
  apply kl_nonneg
  intro a h
  have c : (0:ℝ)<Fintype.card (Layer N s) := by exact_mod_cast Fintype.card_pos
  exact False.elim ((inv_pos.mpr c).ne' h)

theorem qcost_sum (balanced : (unif W).map G.block=unif (Layer N s))
    (ub ab : ℕ) (hu : Fintype.card U≤2^ub) (ha : Fintype.card A≤2^ab) :
    ∑v, G.mass o r v*G.qcost o r v ≤ (ub+m*ab : ℕ)*log 2 := by
  let μ := experiment m N s W o r
  rw [Fintype.sum_prod_type]
  apply le_trans _ (query_charge G o r ub ab hu ha)
  apply sum_le_sum; intro q _
  let z := G.label q
  let y := G.row q
  let nr := law μ z (measurable_of_finite _)
  let post := posterior μ y (measurable_of_finite y) z
  let F := flat (Layer N s)
  have reflaw : (law μ y (measurable_of_finite y)).weight=F.weight := by
    funext a
    change μ.real (y ⁻¹' {a})=(Fintype.card (Layer N s):ℝ)⁻¹
    rw [←map_measureReal_apply (measurable_of_finite y) (.singleton a),row_uniform G o r q balanced,
      measureReal_def,one_atom]; simp
  have h := expected_posterior_kl μ y (measurable_of_finite _) z (measurable_of_finite _)
  rw [reflaw] at h
  simp only [klBits,←mul_div_assoc,←sum_div] at h
  have full : (∑ t,nr.weight t*kl (post t).weight F.weight) = I[y:z;μ] :=
    (div_left_inj' (log_pos (by norm_num : (1:ℝ)<2)).ne').mp h
  apply (true_part (fun t => nr.weight t*kl (post t).weight F.weight) _).trans_eq full
  intro t
  apply mul_nonneg (nr.nonneg t)
  apply kl_nonneg
  intro a e
  have pos : (0:ℝ)<(Fintype.card (Layer N s):ℝ) := by exact_mod_cast Fintype.card_pos
  exact False.elim ((inv_pos.mpr pos).ne' e)

theorem corr_sum (ub : ℕ) (hu : Fintype.card U≤2^ub) :
    ∑v,G.mass o r v*G.corr o r v≤ub*log 2 := by
  let μ := experiment m N s W o r
  rw [Fintype.sum_prod_type]
  apply le_trans _ (correlation_charge G o r ub hu)
  apply sum_le_sum; intro q _
  rw [condMutualInfo_eq_sum' (measurable_of_finite (G.label q))]
  let x := fun v : World m N s W O R => v.2.1
  exact true_part (fun t : View m W O P A × Bool => μ.real (G.label q ⁻¹' {t})*I[G.row q:x;μ[|G.label q ← t]]) (fun t => mul_nonneg measureReal_nonneg (mutualInfo_nonneg (measurable_of_finite (G.row q)) (measurable_of_finite x) _))

theorem atom_sum : ∑v,G.mass o r v*G.atomCost o r v≤m*(Fintype.card P:ℝ) := by
  let μ := experiment m N s W o r
  rw [Fintype.sum_prod_type]
  calc _ ≤ ∑_q : Fin m,(Fintype.card P:ℝ) := by
         apply sum_le_sum; intro q _
         have h := posterior_guess G o r q
         dsimp only at h
         have cp : (0:ℝ)<Fintype.card (Layer N s) := by exact_mod_cast Fintype.card_pos
         have bound := (le_div_iff₀ cp).mp h
         unfold atomCost; simp only [←mul_assoc,←sum_mul]
         exact bound
       _ = _ := by simp

end Game
end
end DisjointnessDraft.Information
