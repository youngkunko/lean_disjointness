import DisjointnessDraft.Information.Smoothing
import DisjointnessDraft.Information.DirectSum

namespace DisjointnessDraft.Information
open Finset Real MeasureTheory ProbabilityTheory DisjointnessFoundations.FiniteSampling DisjointnessFoundations.EntropyBridge
open scoped ProbabilityTheory BigOperators
noncomputable section
open Classical

/-- Conditioning on a positive event determined by the query side costs at
most its inverse probability in correlation. Mutual information is in nats. -/
theorem one_side {Ω L : Type*} [Fintype Ω] [MeasurableSpace Ω] [MeasurableSingletonClass Ω]
  [Fintype L] [Nonempty L] [MeasurableSpace L] [MeasurableSingletonClass L]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (a x : Ω→L) (E : Finset L) :
    μ.real (a ⁻¹' (E:Set L))*I[a : x ; μ[|a ⁻¹' (E:Set L)]] ≤ I[a : x ; μ] := by
  let flag := fun v => decide (a v∈E)
  have ev : flag ⁻¹' {true}=a ⁻¹' (E:Set L) := by ext v; simp [flag]
  have pos := condMutualInfo_eq_sum' (Z:=flag) (X:=a) (Y:=x) (μ:=μ) (measurable_of_finite flag)
  have term := Finset.single_le_sum (s:=univ) (f:=fun b : Bool => μ.real (flag ⁻¹' {b})*I[a:x;μ[|flag ← b]])
    (fun b _ => mul_nonneg measureReal_nonneg (mutualInfo_nonneg (measurable_of_finite a) (measurable_of_finite x) _)) (mem_univ true)
  rw [←pos] at term
  dsimp only at term
  rw [ev,condMutualInfo_comm (measurable_of_finite a) (measurable_of_finite x)] at term
  have dp := DisjointnessFoundations.Information.information_of_function_le μ (measurable_of_finite x) (measurable_of_finite a)
    (fun y => (y,decide (y∈E)))
  change I[x:prod a flag;μ]≤I[x:a;μ] at dp
  rw [DisjointnessFoundations.Information.message_chain μ (measurable_of_finite x) (measurable_of_finite a) (measurable_of_finite flag),
    mutualInfo_comm (measurable_of_finite x) (measurable_of_finite a)] at dp
  linarith [mutualInfo_nonneg (measurable_of_finite x) (measurable_of_finite flag) μ]

variable {Ω L : Type*} [Fintype Ω] [MeasurableSpace Ω] [MeasurableSingletonClass Ω]
  [Fintype L] [Nonempty L] [MeasurableSpace L] [MeasurableSingletonClass L]

/-- A high-probability one-sided smoothing event yields two capped marginals
and retains weak correlation on the same joint conditional measure. -/
theorem near_rectangle (μ : Measure Ω) [IsProbabilityMeasure μ] (a x : Ω→L) (K : ℝ) (one : 1<K)
    (query : 4*(DisjointnessFoundations.InformationLoss.kl (law μ a (measurable_of_finite a)).weight (flat L).weight+1)≤log K)
    (update : ∀y,μ.real (x ⁻¹' {y})*(Fintype.card L:ℝ)≤K) :
    ∃E : Finset L, let S := a ⁻¹' (E:Set L)
      3/4≤μ.real S ∧ (∀y,μ[|S].real (a ⁻¹' {y})*Fintype.card L≤(4/3)*K) ∧
      (∀y,μ[|S].real (x ⁻¹' {y})*Fintype.card L≤(4/3)*K) ∧
      μ.real S*I[a:x;μ[|S]]≤I[a:x;μ] := by
  obtain ⟨E,mass,cap⟩ := smooth (law μ a (measurable_of_finite a)) one query
  let S := a ⁻¹' (E:Set L)
  have hm : 3/4≤μ.real S := by
    change 3/4≤∑y∈E,μ.real (a ⁻¹' {y}) at mass
    rwa [sum_measureReal_preimage_singleton E (fun y _ => (Set.toFinite _).measurableSet)] at mass
  have pos : 0<μ.real S := by linarith only [hm]
  have divide (T : Set Ω) (cap : μ.real (S∩T)*Fintype.card L≤K) : μ[|S].real T*Fintype.card L≤(4/3)*K := by
    rw [cond_real_apply (Set.toFinite _).measurableSet,mul_assoc,←div_eq_inv_mul,div_le_iff₀ pos]
    have h := mul_le_mul_of_nonneg_left hm (by linarith : 0≤4/3*K)
    linarith only [h,cap]
  refine ⟨E,hm,?_,?_,one_side μ a x E⟩
  · intro y
    apply divide
    by_cases mem : y∈E
    · exact (mul_le_mul_of_nonneg_right (measureReal_mono Set.inter_subset_right) (Nat.cast_nonneg _)).trans (cap y mem)
    · have empty : S∩a ⁻¹' {y}=∅ := Set.eq_empty_of_forall_not_mem (fun v hv => mem ((show a v=y from hv.2) ▸ hv.1))
      rw [empty]; simp; linarith
  · intro y
    exact divide _ ((mul_le_mul_of_nonneg_right (measureReal_mono Set.inter_subset_right) (Nat.cast_nonneg _)).trans (update y))

variable {N s : ℕ}
def pairLaw (a b : InputLaw L) : InputLaw (L×L) where
  weight t := a.weight t.1*b.weight t.2
  nonneg _ := mul_nonneg (a.nonneg _) (b.nonneg _)
  total := by rw [Fintype.sum_prod_type]; simp_rw [←mul_sum,b.total,mul_one]; exact a.total

/-- Pinsker for the disjoint-support experiment, followed by the sparse-set
product theorem. This bounds the correlation of the original joint law below. -/
theorem rectangle_cost (μ : Measure Ω) [IsProbabilityMeasure μ] (a x : Ω→Layer N s)
    (hs : 200≤s) (hp : 0<N) (div : s^2∣N)
    (sound : ∀ᵐ v ∂μ, Disjoint (a v).val (x v).val)
    (ac : ∀y,μ.real (a ⁻¹' {y})*Fintype.card (Layer N s)≤Corruption.capFactor s)
    (xc : ∀y,μ.real (x ⁻¹' {y})*Fintype.card (Layer N s)≤Corruption.capFactor s) :
    2*((s:ℝ)^2/(100*N))^2 ≤ I[a:x;μ] := by
  let j := law μ (prod a x) (measurable_of_finite _)
  let pa := law μ a (measurable_of_finite a)
  let px := law μ x (measurable_of_finite x)
  let pr := pairLaw pa px
  let hit := fun t : Layer N s × Layer N s => if Disjoint t.1.val t.2.val then (0:ℝ) else 1
  have mono (t) : j.weight t ≤ pa.weight t.1 ∧ j.weight t≤px.weight t.2 :=
    ⟨measureReal_mono (fun v h => congrArg Prod.fst (show (a v,x v)=t from h)),
     measureReal_mono (fun v h => congrArg Prod.snd (show (a v,x v)=t from h))⟩
  have abscont (t) (h : pr.weight t=0) : j.weight t=0 := by
    rcases mul_eq_zero.mp h with z|z
    · exact le_antisymm ((mono t).1.trans_eq z) (j.nonneg _)
    · exact le_antisymm ((mono t).2.trans_eq z) (j.nonneg _)
  have bare : (∑t, j.weight t*hit t)=0 := by
    apply sum_eq_zero
    intro t _
    by_cases miss : Disjoint t.1.val t.2.val
    · simp [hit,miss]
    · have nu : μ ((prod a x) ⁻¹' {t})=0 := by
        apply measure_mono_null _ (ae_iff.mp sound)
        intro v hv hv'
        have e : (a v,x v)=t := hv
        apply miss
        simpa only [←e] using hv'
      simp [j,law,measureReal_def,nu]
  have prodlow := product_lower hs hp div pa px ac xc
  have eq : (∑t,pr.weight t*hit t)=∑u,pa.weight u*(∑v : Layer N s,if Disjoint u.val v.val then 0 else px.weight v) := by
    rw [Fintype.sum_prod_type]; apply sum_congr rfl; intro u _; rw [mul_sum]
    apply sum_congr rfl; intro v _
    by_cases h : Disjoint u.val v.val <;> simp [pr,pairLaw,hit,h]
  have trans := DisjointnessFoundations.ProductTransfer.expectation_transfer j pr hit 1 (fun t => by dsimp [hit]; split_ifs <;> norm_num) (fun t => by dsimp [hit]; split_ifs <;> norm_num)
  rw [bare,zero_add,one_mul,eq] at trans
  have pin := DisjointnessFoundations.ProductTransfer.pinsker_sq j pr abscont
  have bridge := joint_product_kl μ x (measurable_of_finite x) a (measurable_of_finite a)
  rw [mutualInfo_comm (measurable_of_finite x) (measurable_of_finite a)] at bridge
  unfold DisjointnessFoundations.InformationLoss.klBits at bridge
  have corr : DisjointnessFoundations.InformationLoss.kl j.weight pr.weight=I[a:x;μ] :=
    (div_left_inj' (log_pos (by norm_num : (1:ℝ)<2)).ne').mp bridge
  rw [corr] at pin
  have sq := pow_le_pow_left₀ (by positivity : 0≤(s:ℝ)^2/(100*N)) (prodlow.trans trans) 2
  linarith only [pin,sq]

end
end DisjointnessDraft.Information
