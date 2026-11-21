import DisjointnessDraft.Information.DirectSum
import DisjointnessFoundations.IndependentSideInformation

namespace DisjointnessDraft.Information
open MeasureTheory ProbabilityTheory DisjointnessFoundations.HardIndependence
open scoped ProbabilityTheory BigOperators
noncomputable section
open Classical

variable {m N s : ℕ} {W O R U P A : Type*}
  [Fintype W] [MeasurableSpace W] [MeasurableSingletonClass W] [Nonempty W]
  [Fintype O] [MeasurableSpace O] [MeasurableSingletonClass O]
  [Fintype R] [MeasurableSpace R] [MeasurableSingletonClass R]
  [Fintype U] [MeasurableSpace U] [MeasurableSingletonClass U]
  [Fintype P] [MeasurableSpace P] [MeasurableSingletonClass P]
  [Fintype A] [MeasurableSpace A] [MeasurableSingletonClass A] [Nonempty (Layer N s)]

instance experiment_probability (o : Measure O) (r : Measure R) [IsProbabilityMeasure o] [IsProbabilityMeasure r] :
    IsProbabilityMeasure (experiment m N s W o r) := by unfold experiment; infer_instance

theorem row_uniform {m N s : ℕ} {W O R U P A : Type*}
    [Fintype W] [MeasurableSpace W] [MeasurableSingletonClass W] [Nonempty W]
    [Fintype O] [MeasurableSpace O] [MeasurableSingletonClass O]
    [Fintype R] [MeasurableSpace R] [MeasurableSingletonClass R]
    [Fintype U] [MeasurableSpace U] [MeasurableSingletonClass U]
    [Fintype P] [MeasurableSpace P] [MeasurableSingletonClass P]
    [Fintype A] [MeasurableSpace A] [MeasurableSingletonClass A] [Nonempty (Layer N s)]
    (G : Game m N s W O R U P A) (o : Measure O) (r : Measure R)
    [IsProbabilityMeasure o] [IsProbabilityMeasure r] (q : Fin m)
    (balanced : (unif W).map G.block = unif (Layer N s)) :
    (experiment m N s W o r).map (G.row q)=unif (Layer N s) := by
  change (experiment m N s W o r).map (G.block ∘ (fun f : Family m W => f q) ∘ Prod.fst) = _
  rw [←Measure.map_map (measurable_of_finite _) (measurable_of_finite _),
    ←Measure.map_map (measurable_of_finite _) (measurable_of_finite _)]
  simp [experiment,eval_uniform,balanced]

theorem fresh_prefix (q : Fin m) :
    IndepFun (fun f : Family m W => f q) (rowPrefix q.val) (unif (Family m W)) := by
  let seen : Finset (Fin m) := Finset.univ.filter (fun j => j.val<q.val)
  have no : q∉seen := by simp [seen]
  have ind := (independent_rows (β:=fun _ : Fin m => W)).indepFun_finset ({q} : Finset (Fin m)) seen
    (by simpa) (fun _ => measurable_of_finite _)
  let expand := fun (p : seen → W) (j : Fin m) => if h : j∈seen then some (p ⟨j,h⟩) else none
  have h := ind.comp (measurable_pi_apply (⟨q,by simp⟩ : ({q} : Finset (Fin m)))) (measurable_of_finite expand)
  convert h using 1
  funext f j
  simp [Function.comp_def,expand,rowPrefix,seen]

/-- Total query-side Shannon deficit across all indices, in natural units. -/
theorem query_charge (G : Game m N s W O R U P A) (o : Measure O) (r : Measure R)
    [IsProbabilityMeasure o] [IsProbabilityMeasure r] (ub ab : ℕ)
    (hu : Fintype.card U≤2^ub) (ha : Fintype.card A≤2^ab) :
    ∑q : Fin m, I[G.row q : G.label q ; experiment m N s W o r] ≤
      (ub+m*ab : ℕ)*Real.log 2 := by
  let μ := experiment m N s W o r
  let F : World m N s W O R → Family m W := Prod.fst
  let data : World m N s W O R → Layer N s × (O×R) := Prod.snd
  letI : FiniteRange F := ⟨Set.toFinite _⟩
  letI : FiniteRange data := ⟨Set.toFinite _⟩
  let msgs := prod G.advice G.answers
  let big := prod msgs data
  let c := fun _ : World m N s W O R => ()
  have ind : IndepFun F data μ := indepFun_fst_snd
  have budget : I[F : big ; μ] ≤ (ub+m*ab : ℕ)*Real.log 2 := by
    rw [show big=prod msgs data from rfl,DisjointnessFoundations.Information.message_chain μ (measurable_of_finite F) (measurable_of_finite msgs) (measurable_of_finite data),
      ind.mutualInfo_eq_zero (measurable_of_finite F) (measurable_of_finite data),zero_add]
    apply (DisjointnessFoundations.Information.conditional_information_le_entropy μ (measurable_of_finite F) (measurable_of_finite msgs) (measurable_of_finite data)).trans
    apply DisjointnessFoundations.Information.entropy_of_bits
    simp only [Fintype.card_prod,Fintype.card_fun,Fintype.card_fin,pow_add]
    rw [mul_comm m ab,pow_mul]
    exact Nat.mul_le_mul hu (Nat.pow_le_pow_left ha _)
  have reduce (q : Fin m) : I[G.row q : G.label q ; μ] ≤
      I[(fun ω => F ω q) : big | history F c q.val ; μ] := by
    let whole := fun ω => F ω q
    letI : FiniteRange whole := ⟨Set.toFinite _⟩
    let hist := history F c q.val
    letI : FiniteRange hist := ⟨Set.toFinite _⟩
    have ind' := DisjointnessFoundations.ProtocolCorrelation.lift_independence (unif (Family m W))
      ((unif (Layer N s)).prod (o.prod r)) (measurable_of_finite _) (measurable_of_finite _) (fresh_prefix (W:=W) q)
    have hi : IndepFun whole hist μ := ind'.comp measurable_id (measurable_of_finite (fun p => ((),p)))
    let decoder := fun p : ((U×(Fin m→A))×(Layer N s×(O×R))) × (Unit×(Fin m→Option W)) =>
      let ψ := G.packet p.1.1.1 p.1.2.2.2
      ((((p.1.2.2.1,ψ),p.1.1.2),p.2.2),G.verify ψ (p.1.1.2 q) p.1.1.1)
    have d := DisjointnessFoundations.Information.information_of_function_le μ (measurable_of_finite whole)
      (measurable_of_finite (prod big hist)) decoder
    change I[whole : G.label q ; μ] ≤ I[whole : prod big hist ; μ] at d
    have proj := DisjointnessFoundations.Information.information_of_function_le μ (measurable_of_finite (G.label q))
      (measurable_of_finite whole) G.block
    rw [mutualInfo_comm (measurable_of_finite (G.label q)) (measurable_of_finite (G.block ∘ whole)),
      mutualInfo_comm (measurable_of_finite (G.label q)) (measurable_of_finite whole)] at proj
    apply proj.trans (d.trans_eq _)
    rw [DisjointnessFoundations.Information.message_chain μ (measurable_of_finite whole) (measurable_of_finite big) (measurable_of_finite hist),
      hi.mutualInfo_eq_zero (measurable_of_finite whole) (measurable_of_finite hist),zero_add]
  apply (Finset.sum_le_sum (s:=Finset.univ) (fun q _ => reduce q)).trans
  rw [direct_sum μ F big c]
  have inject := DisjointnessFoundations.Information.information_of_function_le μ (measurable_of_finite F) (measurable_of_finite big) (fun x => (x,()))
  change I[F : prod big c ; μ]≤I[F : big ; μ] at inject
  rw [DisjointnessFoundations.Information.message_chain μ (measurable_of_finite F) (measurable_of_finite big) (measurable_of_finite c)] at inject
  have zero : I[F : c ; μ]=0 := mutualInfo_const (measurable_of_finite F) ()
  rw [zero,zero_add] at inject
  exact inject.trans budget

/-- Total residual target correlation across indices, revealing the exact
transcript vector and the deterministic verification flag in each summand. -/
theorem correlation_charge (G : Game m N s W O R U P A) (o : Measure O) (r : Measure R)
    [IsProbabilityMeasure o] [IsProbabilityMeasure r] (ub : ℕ) (hu : Fintype.card U≤2^ub) :
    ∑q : Fin m, I[G.row q : (fun v => v.2.1) | G.label q ; experiment m N s W o r] ≤
      ub*Real.log 2 := by
  let μ := experiment m N s W o r
  let F : World m N s W O R → Family m W := Prod.fst
  let data : World m N s W O R → Layer N s × (O×R) := Prod.snd
  let target := fun v : World m N s W O R => (v.2.1,G.advice v)
  have reduce (q : Fin m) : I[G.row q : (fun v => v.2.1) | G.label q ; μ] ≤
      I[(fun v => F v q) : target | history F G.public q.val ; μ] := by
    let whole := fun ω => F ω q
    have h := DisjointnessFoundations.Correlation.project_conditioned μ (measurable_of_finite whole)
      (measurable_of_finite target) (measurable_of_finite (G.label q)) G.block Prod.fst
    apply h.trans
    exact reveal_test μ whole target (G.observed q) (G.accepted q)
      (fun p => G.verify p.2.1.1.2 (p.2.1.2 q) p.1.2) rfl
  apply (Finset.sum_le_sum (s:=Finset.univ) (fun q _ => reduce q)).trans
  rw [direct_sum μ F target G.public,condMutualInfo_comm (measurable_of_finite F) (measurable_of_finite target)]
  have rev := reveal_test μ target F G.phi G.answers (fun p => G.reply p.1 p.2.1 p.2.2) rfl
  apply rev.trans
  rw [condMutualInfo_comm (measurable_of_finite target) (measurable_of_finite F)]
  have ind : IndepFun F data μ := indepFun_fst_snd
  have h := DisjointnessFoundations.Correlation.advice_budget μ (measurable_of_finite F) (measurable_of_finite data)
    (measurable_of_finite G.advice) ind (fun p => (p.2.1,p.1)) (fun p => (p.2.2.1,G.packet p.1 p.2.2.2))
  exact h.trans (DisjointnessFoundations.Information.entropy_of_bits μ G.advice ub hu)

end
end DisjointnessDraft.Information
