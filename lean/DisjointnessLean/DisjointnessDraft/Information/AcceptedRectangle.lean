import DisjointnessDraft.Information.Intermediate
import DisjointnessDraft.Information.ProductRectangle

/-! Conditioning on one verified view and one likely query-side event. -/
namespace DisjointnessDraft.Information.Game
open Finset Real MeasureTheory ProbabilityTheory DisjointnessFoundations.HardIndependence DisjointnessFoundations.EntropyBridge
open scoped BigOperators ProbabilityTheory
open Classical
noncomputable section
set_option maxHeartbeats 1000000
variable {m N s : ℕ} {W O R U P A : Type*}
  [Fintype W] [MeasurableSpace W] [singleRows : MeasurableSingletonClass W] [nonemptyRows : Nonempty W]
  [sideFinite : Fintype O] [MeasurableSpace O] [singleSide : MeasurableSingletonClass O]
  [randomFinite : Fintype R] [MeasurableSpace R] [singleRandom : MeasurableSingletonClass R]
  [adviceFinite : Fintype U] [adviceMeasurable : MeasurableSpace U] [singleAdvice : MeasurableSingletonClass U]
  [packetFinite : Fintype P] [packetMeasurable : MeasurableSpace P] [singlePacket : MeasurableSingletonClass P]
  [responseFinite : Fintype A] [responseMeasurable : MeasurableSpace A] [singleResponse : MeasurableSingletonClass A] [nonemptyLayer : Nonempty (Layer N s)]
variable (G : Game m N s W O R U P A) (o : Measure O) (r : Measure R)
  [IsProbabilityMeasure o] [IsProbabilityMeasure r]

abbrev fiber (v : Key m W O P A) := (experiment m N s W o r)[|G.event v]
abbrev selected (v : Key m W O P A) (E : Finset (Layer N s)) := (G.fiber o r v)[|G.row v.1 ⁻¹' (E:Set _)]
abbrev updateRow (w : World m N s W O R) := w.2.1

/-- The witness uses one actual positive-probability view and one
query-side event inside it. The powers of two encode the two min-entropy
bounds with ε=1/40; correlation uses base-two units. -/
structure NearWitness where
  view : Key m W O P A
  positive : 0<G.mass o r view
  rows : Finset (Layer N s)
  likely : 3/4≤(G.fiber o r view).real (G.row view.1 ⁻¹' (rows:Set _))
  queryCap : ∀x,(G.selected o r view rows).real (G.row view.1 ⁻¹' {x})*Fintype.card (Layer N s) ≤ (2:ℝ)^((s:ℝ)/80)
  updateCap : ∀x,(G.selected o r view rows).real (updateRow ⁻¹' {x})*Fintype.card (Layer N s) ≤ (2:ℝ)^((s:ℝ)/80)
  correlation : I[G.row view.1:updateRow; G.selected o r view rows]/log 2≤(m:ℝ)^(-1/5:ℝ)
  monochromatic : ∀ᵐ w ∂G.selected o r view rows,Disjoint (G.row view.1 w).val (updateRow w).val

/-- The scalar comparisons isolate where the manuscript uses sufficiently
large n. Neither existence nor properties of the accepted witness are
assumptions. -/
theorem accepted_near_rectangle (hm : 0<m) (hr : 0<acceptance G o r) (sound : G.Sound)
    (bal : (unif W).map G.block=unif (Layer N s)) (ub ab : ℕ)
    (hu : Fintype.card U≤2^ub) (ha : Fintype.card A≤2^ab)
    (budget : ((ub+m*ab : ℕ):ℝ)/(m*acceptance G o r)≤(m:ℝ)^(1/5:ℝ))
    (short : (ub:ℝ)/m≤(m:ℝ)^(-2/5:ℝ))
    (packet : (Fintype.card P:ℝ)≤(2:ℝ)^((s:ℝ)/160))
    (big : 1<(3/4:ℝ)*(2:ℝ)^((s:ℝ)/80))
    (smoothFits : 4*(4*(m:ℝ)^(1/5:ℝ)*log 2+1)≤log ((3/4:ℝ)*(2:ℝ)^((s:ℝ)/80)))
    (packetFits : 4*(2:ℝ)^((s:ℝ)/160)/acceptance G o r≤(3/4:ℝ)*(2:ℝ)^((s:ℝ)/80))
    (corrFits : (4/3:ℝ)*4*(m:ℝ)^(-2/5:ℝ)/acceptance G o r≤(m:ℝ)^(-1/5:ℝ)) :
    Nonempty (G.NearWitness o r) := by
  let μ := experiment m N s W o r
  let w := G.acceptedLaw o r hm hr
  let t := (m:ℝ)^(1/5:ℝ)
  let c := (m:ℝ)^(-2/5:ℝ)/acceptance G o r
  let k := (3/4:ℝ)*(2:ℝ)^((s:ℝ)/80)
  have lp := log_pos (by norm_num : (1:ℝ)<2)
  have mp : (0:ℝ)<m := by exact_mod_cast hm
  have tp : 0<t := rpow_pos_of_pos mp _
  have cp : 0<c := div_pos (rpow_pos_of_pos mp _) hr
  have norm := w.total
  have qa := (G.query_mean o r hm hr bal ub ab hu ha).trans budget
  have ca := G.accepted_correlation o r hm hr ub hu short
  have xa := (G.atom_mean o r hm hr).trans (div_le_div_of_nonneg_right packet hr.le)
  have nn (v) : 0≤G.atomCost o r v := mul_nonneg ((G.updatePosterior o r v).nonneg _) (Nat.cast_nonneg _)
  have pb : 4*(∑v,w.weight v*G.atomCost o r v)≤k := (mul_le_mul_of_nonneg_left xa (by norm_num : (0:ℝ)≤4)).trans (by simpa only [mul_div_assoc] using packetFits)
  obtain ⟨v,vp,qs,cs,xs⟩ := select_three w.weight (fun v => G.qcost o r v/log 2)
    (fun v => G.corr o r v/log 2) (G.atomCost o r) w.nonneg
    (fun v => div_nonneg (G.qcost_nonnegative o r v) lp.le)
    (fun v => div_nonneg (mutualInfo_nonneg (measurable_of_finite _) (measurable_of_finite _) _) lp.le)
    nn (T:=1) (F:=4*t) (G:=4*c) (H:=k) (by norm_num) (by positivity) (by positivity)
    (by dsimp [k]; positivity) (le_of_eq norm.symm)
    (by simpa only [one_mul] using mul_le_mul_of_nonneg_left qa (by norm_num : (0:ℝ)≤4))
    (by simpa only [one_mul] using mul_le_mul_of_nonneg_left ca (by norm_num : (0:ℝ)≤4))
    (by simpa only [one_mul] using pb)
  have mass : 0<G.mass o r v := (div_pos_iff_of_pos_right (mul_pos mp hr)).mp vp
  have nz : μ (G.event v)≠0 := fun z => mass.ne' (by change μ.real (G.event v)=0; simp [measureReal_def,z])
  have nlab : μ (G.label v.1 ⁻¹' {(v.2,true)})≠0 := nz
  let ν := G.fiber o r v
  letI : IsProbabilityMeasure ν := cond_isProbabilityMeasure nz
  let a := G.row v.1
  let x := (updateRow (m:=m) (N:=N) (s:=s) (W:=W) (O:=O) (R:=R))
  have qbound := (div_le_iff₀ lp).mp qs
  have qlaw : G.qcost o r v=DisjointnessFoundations.InformationLoss.kl (law ν a (measurable_of_finite a)).weight (flat (Layer N s)).weight := by
    change DisjointnessFoundations.InformationLoss.kl (posterior μ a _ (G.label v.1) (v.2,true)).weight _=_
    simp only [posterior,dif_neg nlab]; rfl
  rw [qlaw] at qbound
  have qh : 4*(DisjointnessFoundations.InformationLoss.kl (law ν a (measurable_of_finite a)).weight (flat (Layer N s)).weight+1)≤log k := by
    linarith only [qbound,smoothFits]
  have xh (y) : ν.real (x ⁻¹' {y})*Fintype.card (Layer N s)≤k := by
    have raw := (mul_le_mul_of_nonneg_right (guess_max (G.updatePosterior o r v).weight y) (Nat.cast_nonneg (Fintype.card (Layer N s)))).trans xs
    change (posterior μ x _ (G.label v.1) (v.2,true)).weight y* _ ≤k at raw
    simpa only [posterior,dif_neg nlab,law] using raw
  obtain ⟨E,prob,qcap,xcap,ic⟩ := near_rectangle ν a x k big qh xh
  let S := a ⁻¹' (E:Set (Layer N s))
  letI : FiniteRange x := ⟨Set.toFinite _⟩
  have corrnn : 0≤I[a:x;ν[|S]] := mutualInfo_nonneg (measurable_of_finite a) (measurable_of_finite x) (ν[|S])
  have im := mul_le_mul_of_nonneg_right prob corrnn
  have cc := (div_le_iff₀ lp).mp cs
  change I[a:x;ν]≤4*c*log 2 at cc
  have icap : I[a:x;ν[|S]]/log 2≤(m:ℝ)^(-1/5:ℝ) := by
    apply (div_le_iff₀ lp).mpr
    have cf : (4/3:ℝ)*4*c≤(m:ℝ)^(-1/5:ℝ) := by simpa only [c,mul_div_assoc] using corrFits
    linarith only [im,ic,cc,mul_le_mul_of_nonneg_right cf lp.le]
  have cap : (4/3)*k = (2:ℝ)^((s:ℝ)/80) := by dsimp [k]; ring
  have ds : ∀ᵐ w ∂ν,Disjoint (a w).val (x w).val := by
    filter_upwards [ae_cond_mem (μ:=μ) (s:=G.event v) (Set.toFinite _).measurableSet] with z hz
    exact sound v.1 z (congrArg Prod.snd (show G.label v.1 z=(v.2,true) from hz))
  exact ⟨⟨v,mass,E,prob,fun y => (qcap y).trans_eq cap,fun y => (xcap y).trans_eq cap,
    icap,cond_absolutelyContinuous.ae_le ds⟩⟩

def intersections (N s : ℕ) : Finset (Layer N s × Layer N s) :=
  univ.filter fun t => ¬Disjoint t.1.val t.2.val

/-- The two positive restrictions retain a probability measure. -/
theorem NearWitness.probability (z : G.NearWitness o r) : IsProbabilityMeasure (G.selected o r z.view z.rows) := by
  -- Keep the original theorem signature for existing clients.
  let _compat_1 := singleRows
  let _compat_2 := nonemptyRows
  let _compat_3 := sideFinite
  let _compat_4 := singleSide
  let _compat_5 := randomFinite
  let _compat_6 := singleRandom
  let _compat_7 := adviceFinite
  let _compat_8 := adviceMeasurable
  let _compat_9 := singleAdvice
  let _compat_10 := packetFinite
  let _compat_11 := packetMeasurable
  let _compat_12 := singlePacket
  let _compat_13 := responseFinite
  let _compat_14 := responseMeasurable
  let _compat_15 := singleResponse
  let _compat_16 := nonemptyLayer
  have vp : (experiment m N s W o r) (G.event z.view)≠0 :=
    fun h => z.positive.ne' (by simp [mass,measureReal_def,h])
  letI : IsProbabilityMeasure (G.fiber o r z.view) := cond_isProbabilityMeasure vp
  exact cond_isProbabilityMeasure_of_real (ne_of_gt (by linarith only [z.likely]))

/-- Corollary rect. The product uses exactly the two marginals conditional
on the witness; it puts at most n^(-1/10) probability on intersections. -/
theorem NearWitness.rectangle (hm : 0<m) (z : G.NearWitness o r) :
    let ν := G.selected o r z.view z.rows
    let a := G.row z.view.1
    let x := (updateRow (m:=m) (N:=N) (s:=s) (W:=W) (O:=O) (R:=R))
    letI : IsProbabilityMeasure ν := z.probability G o r
    (∀y,ν.real (a ⁻¹' {y})*Fintype.card (Layer N s)≤(2:ℝ)^((s:ℝ)/80)) ∧
    (∀y,ν.real (x ⁻¹' {y})*Fintype.card (Layer N s)≤(2:ℝ)^((s:ℝ)/80)) ∧
    ∑y∈intersections N s,(pairLaw (law ν a (measurable_of_finite _)) (law ν x (measurable_of_finite _))).weight y≤(m:ℝ)^(-1/10:ℝ) := by
  intro ν a x
  letI : IsProbabilityMeasure ν := z.probability G o r
  have cn : (0:ℝ)<Fintype.card (Layer N s) := by exact_mod_cast Fintype.card_pos
  have bad : ν ((prod a x) ⁻¹' ((intersections N s:Set (Layer N s × Layer N s))))=0 := by
    apply measure_mono_null _ (ae_iff.mp z.monochromatic)
    intro w hw; simpa [intersections,prod] using hw
  have mono : ν.real ((prod a x) ⁻¹' ((intersections N s:Set (Layer N s × Layer N s))))≤0 := by
    simp [measureReal_def,bad]
  have h := (product_rectangle ν a x (intersections N s) ((2:ℝ)^((s:ℝ)/80)/Fintype.card (Layer N s))
    0 ((m:ℝ)^(-1/5:ℝ)) (fun y => (le_div_iff₀ cn).mpr (z.queryCap y)) (fun y => (le_div_iff₀ cn).mpr (z.updateCap y)) mono z.correlation).2.2
  have mp : (0:ℝ)<m := by exact_mod_cast hm
  have lg : log 2/2≤1 := by linarith [log_le_sub_one_of_pos (by norm_num : (0:ℝ)<2)]
  have small := Real.sqrt_le_sqrt (mul_le_of_le_one_left (rpow_pos_of_pos mp (-1/5:ℝ)).le lg)
  have sq : sqrt ((m:ℝ)^(-1/5:ℝ))=(m:ℝ)^(-1/10:ℝ) := by
    rw [Real.sqrt_eq_rpow,←Real.rpow_mul mp.le]; norm_num
  exact ⟨z.queryCap,z.updateCap,(le_trans (by simpa only [zero_add] using h) (small.trans_eq sq))⟩

end
end DisjointnessDraft.Information.Game
