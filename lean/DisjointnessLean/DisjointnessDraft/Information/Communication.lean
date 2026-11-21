import DisjointnessDraft.Information.Fibers
import DisjointnessDraft.Information.Rectangle

namespace DisjointnessDraft.Information
open Finset Real MeasureTheory ProbabilityTheory DisjointnessFoundations.EntropyBridge DisjointnessFoundations.HardIndependence
open scoped ProbabilityTheory BigOperators
noncomputable section
open Classical

/-- Simultaneous weighted Markov selection on exactly the same accepted fiber. -/
theorem select_three {I : Type*} [Fintype I] (w f g h : I→ℝ) (wf : ∀i,0≤w i)
    (ff : ∀i,0≤f i) (gf : ∀i,0≤g i) (hf : ∀i,0≤h i)
    {T F G H : ℝ} (tp : 0<T) (fp : 0<F) (gp : 0<G) (hp : 0<H)
    (total : T≤∑i,w i)
    (b₁ : 4*(∑i,w i*f i)≤T*F) (b₂ : 4*(∑i,w i*g i)≤T*G) (b₃ : 4*(∑i,w i*h i)≤T*H) :
    ∃ i,0<w i ∧ f i≤F ∧ g i≤G ∧ h i≤H := by
  have a : (∑i,w i*f i)/F≤T/4 := (div_le_iff₀ fp).mpr (by linarith only [b₁])
  have b : (∑i,w i*g i)/G≤T/4 := (div_le_iff₀ gp).mpr (by linarith only [b₂])
  have c : (∑i,w i*h i)/H≤T/4 := (div_le_iff₀ hp).mpr (by linarith only [b₃])
  by_contra no
  have point (i : I) : w i ≤ w i*(f i/F+g i/G+h i/H) := by
    rcases (wf i).eq_or_lt with eq|ip
    · simp [←eq]
    apply le_mul_of_one_le_right ip.le
    by_contra! bad
    apply no; refine ⟨i,ip,?_,?_,?_⟩
    · apply (div_le_one fp).mp
      linarith [div_nonneg (gf i) gp.le,div_nonneg (hf i) hp.le]
    · apply (div_le_one gp).mp
      linarith [div_nonneg (ff i) fp.le,div_nonneg (hf i) hp.le]
    · apply (div_le_one hp).mp
      linarith [div_nonneg (ff i) fp.le,div_nonneg (gf i) gp.le]
  have all := sum_le_sum (s:=univ) (fun i _ => point i)
  simp_rw [mul_add,←mul_div_assoc,sum_add_distrib,←sum_div] at all
  linarith only [a,b,c,total,all,tp]

variable {m N s : ℕ} {W O R U P A : Type*}
  [Fintype W] [MeasurableSpace W] [MeasurableSingletonClass W] [Nonempty W]
  [Fintype O] [MeasurableSpace O] [MeasurableSingletonClass O]
  [Fintype R] [MeasurableSpace R] [MeasurableSingletonClass R]
  [Fintype U] [MeasurableSpace U] [MeasurableSingletonClass U]
  [Fintype P] [MeasurableSpace P] [MeasurableSingletonClass P]
  [Fintype A] [MeasurableSpace A] [MeasurableSingletonClass A] [Nonempty (Layer N s)]

/-- Native Step 2 communication bound. The only structural hypotheses about the
algorithm are its deterministic message functions and the correctness of its
accepted answers. All Shannon, min-entropy and correlation bounds are proved
for the experiment inside the theorem. Logarithms in the budgets are natural. -/
theorem communication_bound (G : Game m N s W O R U P A) (o : Measure O) (r : Measure R)
    [IsProbabilityMeasure o] [IsProbabilityMeasure r] (sound : G.Sound)
    (balanced : (unif W).map G.block=unif (Layer N s))
    (hm : 0<m) (hs : 200≤s) (hN : 0<N) (multiple : s^2∣N)
    (ub ab : ℕ) (hU : Fintype.card U≤2^ub) (hA : Fintype.card A≤2^ab)
    (r₀ Q C : ℝ) (pr : 0<r₀) (pq : 0<Q) (pc : 0<C)
    (hQ : 4*((ub+m*ab : ℕ)*log 2)≤(m*r₀)*Q)
    (hC : 4*(ub*log 2)≤(m*r₀)*C)
    (hP : 4*(Fintype.card P:ℝ)≤r₀*(Corruption.capFactor s/2))
    (large : 1<Corruption.capFactor s/2)
    (smoothBudget : 4*(Q+1)≤log (Corruption.capFactor s/2))
    (rare : C<((s:ℝ)^2/(100*N))^2/2) :
    acceptance G o r<r₀ := by
  by_contra! many
  let μ := experiment m N s W o r
  let K := Corruption.capFactor s/2
  change 1<K at large
  change 4*(Fintype.card P:ℝ)≤r₀*K at hP
  change 4*(Q+1)≤log K at smoothBudget
  let x := fun w : World m N s W O R => w.2.1
  have mp : (0:ℝ)<m := by exact_mod_cast hm
  have positive (v : Game.Key m W O P A) : 0≤G.atomCost o r v := by
    unfold Game.atomCost; exact mul_nonneg ((posterior _ _ _ _ _).nonneg _) (Nat.cast_nonneg _)
  obtain ⟨v,mass,qa,ca,ua⟩ := select_three (G.mass o r) (G.qcost o r) (G.corr o r) (G.atomCost o r)
    (fun _ => measureReal_nonneg) (G.qcost_nonnegative o r)
    (fun v => mutualInfo_nonneg (measurable_of_finite (G.row v.1)) (measurable_of_finite x) _) positive
    (T:=m*r₀) (F:=Q) (G:=C) (H:=K) (mul_pos mp pr) pq pc (by linarith only [large])
    (by rw [G.mass_sum o r hm]; exact mul_le_mul_of_nonneg_left many mp.le)
    (le_trans (mul_le_mul_of_nonneg_left (G.qcost_sum o r balanced ub ab hU hA) (by norm_num)) hQ)
    (le_trans (mul_le_mul_of_nonneg_left (G.corr_sum o r ub hU) (by norm_num)) hC)
    (by have e := G.atom_sum o r; nlinarith only [e,mul_le_mul_of_nonneg_left hP mp.le])
  let ν := μ[|G.event v]
  have nz : μ (G.event v)≠0 := fun hz => (ne_of_gt mass) (by change μ.real (G.event v)=0; simp [measureReal_def,hz])
  letI : IsProbabilityMeasure ν := cond_isProbabilityMeasure nz
  let a := G.row v.1
  have fq : 4*(DisjointnessFoundations.InformationLoss.kl (law ν a (measurable_of_finite a)).weight (flat (Layer N s)).weight+1)≤log K := by
    have hn : μ (G.label v.1 ⁻¹' {(v.2,true)})≠0 := nz
    change DisjointnessFoundations.InformationLoss.kl (posterior μ a (measurable_of_finite a) (G.label v.1) (v.2,true)).weight _≤Q at qa
    simp only [posterior,dif_neg hn] at qa
    change DisjointnessFoundations.InformationLoss.kl (law ν a (measurable_of_finite a)).weight (flat (Layer N s)).weight≤Q at qa
    linarith only [qa,smoothBudget]
  have fx (t) : ν.real (x ⁻¹' {t})*Fintype.card (Layer N s)≤K := by
    let p := posterior μ x (measurable_of_finite x) (G.label v.1) (v.2,true)
    have mx := mul_le_mul_of_nonneg_right (guess_max p.weight t) (Nat.cast_nonneg (Fintype.card (Layer N s)))
    have bound : p.weight t*Fintype.card (Layer N s)≤K := mx.trans ua
    have hn : μ (G.label v.1 ⁻¹' {(v.2,true)})≠0 := nz
    simpa only [p,posterior,dif_neg hn,law] using bound
  obtain ⟨E,prob,capA,capX,info⟩ := near_rectangle ν a x K large fq fx
  let S := a ⁻¹' (E:Set (Layer N s))
  have pos : 0<ν.real S := by linarith only [prob]
  letI : IsProbabilityMeasure (ν[|S]) := cond_isProbabilityMeasure_of_real pos.ne'
  have dis : ∀ᵐ w ∂ν, Disjoint (a w).val (x w).val := by
    filter_upwards [ae_cond_mem (μ:=μ) (s:=G.event v) (Set.toFinite _).measurableSet] with w hw
    exact sound v.1 w (congrArg Prod.snd (show G.label v.1 w=(v.2,true) from hw))
  have step := rectangle_cost (ν[|S]) a x hs hN multiple
    (cond_absolutelyContinuous.ae_le dis)
    (fun t => (capA t).trans (by dsimp [K]; linarith [Corruption.cap_pos s]))
    (fun t => (capX t).trans (by dsimp [K]; linarith [Corruption.cap_pos s]))
  have ni : 0≤I[a:x;ν[|S]] := mutualInfo_nonneg (measurable_of_finite a) (measurable_of_finite x) _
  have lb := mul_le_mul_of_nonneg_right prob ni
  change I[a:x;ν]≤C at ca
  nlinarith only [lb,step,info,ca,rare,sq_nonneg ((s:ℝ)^2/(100*N))]

end
end DisjointnessDraft.Information
