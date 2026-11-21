import DisjointnessDraft.Information.Intermediate
import DisjointnessDraft.Information.AverageMinEntropy

/-! Reading the posterior atom inequalities as the manuscript's logarithmic
min-entropy statements, including the price of conditioning on acceptance. -/
namespace DisjointnessDraft.Information.Game
open Finset Real DisjointnessFoundations.FiniteSampling MinEntropy
open scoped BigOperators
noncomputable section
open Classical
variable {L : Type*} [Fintype L] [Nonempty L]

def minEntropy (p : InputLaw L) := bits (best p.weight)

private theorem max_pos (p : InputLaw L) : 0<best p.weight := by
  by_contra! small
  have h (x) : p.weight x=0 := le_antisymm ((guess_max p.weight x).trans small) (p.nonneg x)
  have eq := p.total
  simp [h] at eq

theorem min_entropy_of_cap (p : InputLaw L) (b : ℝ) (bound : CappedUpdate p ((2:ℝ)^b)) :
    logb 2 (Fintype.card L)-b≤minEntropy p := by
  have mp := max_pos p
  have cp : (0:ℝ)<Fintype.card L := by exact_mod_cast Fintype.card_pos
  have le := log_le_log (mul_pos mp cp) (bound (guessAtom p.weight))
  rw [log_mul mp.ne' cp.ne',log_rpow (by norm_num : (0:ℝ)<2)] at le
  unfold minEntropy bits logb
  apply (le_div_iff₀ (log_pos (by norm_num : (1:ℝ)<2))).mpr
  rw [sub_mul,div_mul_cancel₀ _ (log_pos (by norm_num : (1:ℝ)<2)).ne']
  linarith only [le]

theorem update_min_entropy (p : InputLaw L) (b ρ : ℝ) (hr : 0<ρ)
    (bound : CappedUpdate p (4*(2:ℝ)^b/ρ)) :
    logb 2 (Fintype.card L)-b-logb 2 (1/ρ)-2≤minEntropy p := by
  have eq : (2:ℝ)^(b+logb 2 (1/ρ)+2)=4*(2:ℝ)^b/ρ := by
    rw [rpow_add (by norm_num : (0:ℝ)<2),rpow_add (by norm_num : (0:ℝ)<2),rpow_logb (by norm_num) (by norm_num) (by positivity)]
    norm_num; ring
  have e := min_entropy_of_cap p (b+logb 2 (1/ρ)+2) (by rwa [eq])
  linarith only [e]

theorem SmoothQuery.min_entropy {p : InputLaw L} {b : ℝ} (h : SmoothQuery p b) :
    ∃ E : Finset L, ∃pos : 0<∑x∈E,p.weight x, 3/4≤∑x∈E,p.weight x ∧
    logb 2 (Fintype.card L)-b≤minEntropy (restrict p E pos) := by
  obtain ⟨E,pos,prob,cap⟩ := h
  exact ⟨E,pos,prob,min_entropy_of_cap _ _ cap⟩

theorem eventProbability_mono {T : Type*} [Fintype T] (p : InputLaw T) {a b : T→Prop}
    (inc : ∀v,a v→b v) : eventProbability p a≤eventProbability p b :=
  sum_le_sum_of_subset_of_nonneg (fun _ hx => mem_filter.mpr ⟨mem_univ _,inc _ (mem_filter.mp hx).2⟩)
    (fun v _ _ => p.nonneg v)

variable {m N s : ℕ} {W O R U P A : Type*}
  [Fintype W] [MeasurableSpace W] [MeasurableSingletonClass W] [Nonempty W]
  [Fintype O] [MeasurableSpace O] [MeasurableSingletonClass O]
  [Fintype R] [MeasurableSpace R] [MeasurableSingletonClass R]
  [Fintype U] [MeasurableSpace U] [MeasurableSingletonClass U]
  [Fintype P] [MeasurableSpace P] [MeasurableSingletonClass P]
  [Fintype A] [MeasurableSpace A] [MeasurableSingletonClass A] [Nonempty (Layer N s)]
open MeasureTheory DisjointnessFoundations.HardIndependence
variable (G : Game m N s W O R U P A) (o : Measure O) (r : Measure R)
  [IsProbabilityMeasure o] [IsProbabilityMeasure r]

theorem query_entropy_bits (hm : 0<m) (hr : 0<acceptance G o r)
    (bal : (unif W).map G.block=unif (Layer N s)) (ub ab : ℕ)
    (hu : Fintype.card U≤2^ub) (ha : Fintype.card A≤2^ab)
    (budget : ((ub+m*ab : ℕ):ℝ)/(m*acceptance G o r)≤(m:ℝ)^(1/5:ℝ)) :
    3/4≤eventProbability (G.acceptedLaw o r hm hr) (fun v =>
      let p := G.queryPosterior o r v
      ∃E : Finset (Layer N s), ∃h : 0<∑x∈E,p.weight x, 3/4≤∑x∈E,p.weight x ∧
        logb 2 (Fintype.card (Layer N s))-32*(m:ℝ)^(1/5:ℝ)≤minEntropy (restrict p E h)) := by
  exact (G.query_entropy o r hm hr bal ub ab hu ha budget).trans
    (eventProbability_mono _ fun _ h => h.min_entropy)

theorem update_entropy_bits (hm : 0<m) (hr : 0<acceptance G o r)
    (packet : (Fintype.card P:ℝ)≤(2:ℝ)^((s:ℝ)/160)) :
    3/4≤eventProbability (G.acceptedLaw o r hm hr) (fun v =>
      logb 2 (Fintype.card (Layer N s))-(s:ℝ)/160-logb 2 (1/acceptance G o r)-2
      ≤ minEntropy (G.updatePosterior o r v)) := by
  exact (G.update_entropy o r hm hr _ packet).trans
    (eventProbability_mono _ fun _ h => update_min_entropy _ _ _ hr h)
end
end DisjointnessDraft.Information.Game
