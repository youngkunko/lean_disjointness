import DisjointnessDraft.Information.Communication
import DisjointnessDraft.Information.GeneralSmoothing

/-! The posterior is the actual law of the random query index and observed
transcript after verification. Entropy deficiencies are expressed as equivalent
bounds on normalized atom probabilities, with information measured in bits. -/
namespace DisjointnessDraft.Information
open Finset Real MeasureTheory ProbabilityTheory DisjointnessFoundations.FiniteSampling DisjointnessFoundations.HardIndependence
open DisjointnessFoundations.EntropyBridge DisjointnessFoundations.InformationLoss
open scoped BigOperators ProbabilityTheory
open Classical
set_option maxHeartbeats 2000000
noncomputable section

private theorem quarter {T : Type*} [Fintype T] (p : InputLaw T) (f : T→ℝ)
    (nn : ∀v,0≤f v) {t : ℝ} (tp : 0<t) (bound : (∑v,p.weight v*f v)≤t)
    (ok : T→Prop) (inc : ∀v,f v≤4*t → ok v) :
    3/4≤∑v with ok v,p.weight v := by
  let S := univ.filter ok
  have mul : (∑v∈Sᶜ,p.weight v)*(4*t)≤∑v∈Sᶜ,p.weight v*f v := by
    rw [sum_mul]; apply sum_le_sum
    intro v hv
    have h : ¬ok v := by simpa [S] using hv
    exact mul_le_mul_of_nonneg_left (le_of_lt (lt_of_not_ge (fun z => h (inc v z)))) (p.nonneg v)
  have all := sum_le_sum_of_subset_of_nonneg (f:=fun v=>p.weight v*f v) (subset_univ Sᶜ)
    (fun v _ _ => mul_nonneg (p.nonneg _) (nn _))
  have bad : (∑v∈Sᶜ,p.weight v)≤1/4 := by
    apply (mul_le_mul_right tp).mp
    linarith only [mul,all,bound]
  have eq := (sum_add_sum_compl S p.weight).trans p.total
  change 3/4≤∑v∈S,p.weight v
  linarith only [bad,eq]

variable {m N s : ℕ} {W O R U P A : Type*}
  [Fintype W] [MeasurableSpace W] [MeasurableSingletonClass W] [Nonempty W]
  [Fintype O] [MeasurableSpace O] [MeasurableSingletonClass O]
  [Fintype R] [MeasurableSpace R] [MeasurableSingletonClass R]
  [Fintype U] [MeasurableSpace U] [MeasurableSingletonClass U]
  [Fintype P] [MeasurableSpace P] [MeasurableSingletonClass P]
  [Fintype A] [MeasurableSpace A] [MeasurableSingletonClass A] [Nonempty (Layer N s)]
namespace Game
variable (G : Game m N s W O R U P A) (o : Measure O) (r : Measure R)
  [IsProbabilityMeasure o] [IsProbabilityMeasure r]

def acceptedLaw (hm : 0<m) (hr : 0<acceptance G o r) : InputLaw (Key m W O P A) where
  weight v := G.mass o r v/(m*acceptance G o r)
  nonneg _ := div_nonneg measureReal_nonneg (by positivity)
  total := by rw [←sum_div,G.mass_sum o r hm,div_self (by positivity)]

def queryPosterior (v : Key m W O P A) :=
  posterior (experiment m N s W o r) (G.row v.1) (measurable_of_finite _) (G.label v.1) (v.2,true)

def updatePosterior (v : Key m W O P A) :=
  posterior (experiment m N s W o r) (fun w => w.2.1) (measurable_of_finite _) (G.label v.1) (v.2,true)

theorem accepted_mean (hm : 0<m) (hr : 0<acceptance G o r) (f : Key m W O P A→ℝ) :
    (∑v,(G.acceptedLaw o r hm hr).weight v*f v)=(∑v,G.mass o r v*f v)/(m*acceptance G o r) := by
  simp only [acceptedLaw,div_mul_eq_mul_div,←sum_div]

theorem query_mean (hm : 0<m) (hr : 0<acceptance G o r)
    (bal : (unif W).map G.block=unif (Layer N s)) (ub ab : ℕ)
    (hu : Fintype.card U≤2^ub) (ha : Fintype.card A≤2^ab) :
    (∑v,(G.acceptedLaw o r hm hr).weight v*(G.qcost o r v/log 2)) ≤
      (ub+m*ab : ℕ)/(m*acceptance G o r) := by
  simp only [←mul_div_assoc,←sum_div,G.accepted_mean o r hm hr]
  have norm : (0:ℝ)<m*acceptance G o r := by positivity
  have lp := log_pos (by norm_num : (1:ℝ)<2)
  rw [div_right_comm]
  apply div_le_div_of_nonneg_right _ norm.le
  exact (div_le_iff₀ lp).mpr (G.qcost_sum o r bal ub ab hu ha)

theorem atom_mean (hm : 0<m) (hr : 0<acceptance G o r) :
    (∑v,(G.acceptedLaw o r hm hr).weight v*G.atomCost o r v) ≤ Fintype.card P/acceptance G o r := by
  rw [G.accepted_mean]
  apply (div_le_iff₀ (by positivity)).mpr
  calc _ ≤ (m:ℝ)*Fintype.card P := G.atom_sum o r
       _ = _ := by field_simp; ring

theorem corr_mean (hm : 0<m) (hr : 0<acceptance G o r) (ub : ℕ) (hu : Fintype.card U≤2^ub) :
    (∑v,(G.acceptedLaw o r hm hr).weight v*(G.corr o r v/log 2)) ≤ (ub:ℝ)/(m*acceptance G o r) := by
  simp only [←mul_div_assoc,←sum_div,G.accepted_mean o r hm hr]
  rw [div_right_comm]
  apply div_le_div_of_nonneg_right _ (by positivity)
  exact (div_le_iff₀ (log_pos (by norm_num : (1:ℝ)<2))).mpr (G.corr_sum o r ub hu)

def eventProbability {T : Type*} [Fintype T] (p : InputLaw T) (ok : T→Prop) : ℝ :=
  ∑v with ok v,p.weight v

def SmoothQuery {L : Type*} [Fintype L] (p : InputLaw L) (b : ℝ) : Prop :=
  ∃E : Finset L, ∃h : 0<∑x∈E,p.weight x, 3/4≤∑x∈E,p.weight x ∧
    ∀x,(restrict p E h).weight x * Fintype.card L ≤ (2:ℝ)^b

def CappedUpdate {L : Type*} [Fintype L] (p : InputLaw L) (cap : ℝ) : Prop :=
  ∀x,p.weight x*Fintype.card L≤cap

private theorem row_smoothing {L : Type*} [Fintype L] [Nonempty L] (p : InputLaw L)
    (t : ℝ) (one : 1≤t) (ok : klBits p.weight (flat L).weight≤4*t) : SmoothQuery p (32*t) := by
  obtain ⟨E,h,prob,cap⟩ := smoothing p (4*t) 4 (by linarith only [one]) (by norm_num) ok
  exact ⟨E,h,by linarith only [prob],fun x => (cap x).trans_eq (by congr 1; ring)⟩

/-- Proposition S-entropy. A quarter-tail event gives exactly the stated
three-quarters smoothing mass and 32 n^(1/5) bits of entropy loss. -/
theorem query_entropy (hm : 0<m) (hr : 0<acceptance G o r)
    (bal : (unif W).map G.block=unif (Layer N s)) (ub ab : ℕ)
    (hu : Fintype.card U≤2^ub) (ha : Fintype.card A≤2^ab)
    (budget : ((ub+m*ab : ℕ):ℝ)/(m*acceptance G o r)≤(m:ℝ)^(1/5:ℝ)) :
    3/4≤eventProbability (G.acceptedLaw o r hm hr)
      (fun v => SmoothQuery (G.queryPosterior o r v) (32*(m:ℝ)^(1/5:ℝ))) := by
  let t := (m:ℝ)^(1/5:ℝ)
  have mp : (1:ℝ)≤m := by exact_mod_cast hm
  have one : 1≤t := one_le_rpow mp (by norm_num)
  exact quarter (G.acceptedLaw o r hm hr) (fun v => G.qcost o r v/log 2)
    (fun v => div_nonneg (G.qcost_nonnegative o r v) (log_pos (by norm_num : (1:ℝ)<2)).le) (by linarith only [one] : 0<t)
    ((G.query_mean o r hm hr bal ub ab hu ha).trans budget)
    (fun v => SmoothQuery (G.queryPosterior o r v) (32*t))
    (fun v ok => row_smoothing (G.queryPosterior o r v) t one ok)

/-- Proposition X-leak. The factor 4/ρ gives the additional two bits and
the cost of conditioning on acceptance. -/
theorem update_entropy (hm : 0<m) (hr : 0<acceptance G o r) (b : ℝ)
    (packet : (Fintype.card P:ℝ)≤(2:ℝ)^b) :
    3/4≤eventProbability (G.acceptedLaw o r hm hr)
      (fun v => CappedUpdate (G.updatePosterior o r v) (4*(2:ℝ)^b/acceptance G o r)) := by
  let bound := (2:ℝ)^b/acceptance G o r
  have nn (v) : 0≤G.atomCost o r v :=
    mul_nonneg ((G.updatePosterior o r v).nonneg _) (Nat.cast_nonneg _)
  have pos : 0<bound := div_pos (rpow_pos_of_pos (by norm_num) _) hr
  exact quarter (G.acceptedLaw o r hm hr) (G.atomCost o r) nn pos
    ((G.atom_mean o r hm hr).trans (div_le_div_of_nonneg_right packet hr.le))
    (fun v => CappedUpdate (G.updatePosterior o r v) (4*(2:ℝ)^b/acceptance G o r))
    (fun v ok x => (mul_le_mul_of_nonneg_right (guess_max (G.updatePosterior o r v).weight x)
      (Nat.cast_nonneg (Fintype.card (Layer N s)))).trans (by simpa only [bound,mul_div_assoc] using ok))

/-- Proposition key. Correlation is in bits and the expectation is taken
under the normalized law of verified transcripts. -/
theorem accepted_correlation (hm : 0<m) (hr : 0<acceptance G o r) (ub : ℕ)
    (hu : Fintype.card U≤2^ub) (short : (ub:ℝ)/m≤(m:ℝ)^(-2/5:ℝ)) :
    (∑v,(G.acceptedLaw o r hm hr).weight v*(G.corr o r v/log 2))≤(m:ℝ)^(-2/5:ℝ)/acceptance G o r := by
  apply (G.corr_mean o r hm hr ub hu).trans
  simpa only [div_div] using div_le_div_of_nonneg_right short hr.le

end Game
end
end DisjointnessDraft.Information
