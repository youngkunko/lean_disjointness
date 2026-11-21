import DisjointnessDraft.Native.Distribution
import DisjointnessDraft.Native.Physical
import DisjointnessFoundations.AdaptiveTraceComparison
import Mathlib.MeasureTheory.Integral.Average

namespace DisjointnessDraft.Native
open DisjointnessFoundations CellProbe ProtocolRun HardDistribution VerifiedEpoch Simulation MeasureTheory
open scoped ENNReal BigOperators
noncomputable section
open Classical

variable {ℓ g n w : ℕ} {C Ω : Type}
abbrev Draw (n ℓ g : ℕ) := Fin n × ((Fin n → Whole ℓ g) × Whole ℓ g)

def outcome (fit : occupied ℓ g≤n) (D : Machine n w C) (R : RandomTape Ω C)
    (a : Ω) (z : Draw n ℓ g) :=
  finalRun D R a (rows fit z.2.1) (updates fit z.2.2) z.1

def reads (fit : occupied ℓ g≤n) (D : Machine n w C) (R : RandomTape Ω C) (a : Ω) (z : Draw n ℓ g) :=
  ((outcome fit D R a z).getD (false,0)).2

theorem result (fit : occupied ℓ g≤n) (D : Machine n w C) (R : RandomTape Ω C)
    (hz : FreshCorrect D R) (a : Ω) (z : Draw n ℓ g) :
    outcome fit D R a z = some (answer (rows fit z.2.1) (updates fit z.2.2) z.1,reads fit D R a z) := by
  have eq := hz a (rows fit z.2.1) (updates fit z.2.2) z.1 (updates_nodup fit z.2.2)
  change (outcome fit D R a z).map Prod.fst = _ at eq
  unfold reads
  cases e : outcome fit D R a z with
  | none => simp [e] at eq
  | some v => rcases v with ⟨b,k⟩; rw [e] at eq; exact congrArg (fun b => some (b,k)) (Option.some.inj eq)

def trace (fit : occupied ℓ g≤n) (D : Machine n w C) (R : RandomTape Ω C) (a : Ω) (z : Draw n ℓ g) (fuel : ℕ) :=
  run D.queryStep (afterPrefix D R a (rows fit z.2.1) (updates fit z.2.2)) fuel (D.startQuery (R.query a) z.1)

theorem exact_trace (fit : occupied ℓ g≤n) (D : Machine n w C) (R : RandomTape Ω C) {tu : ℕ}
    (hu : WorstUpdate D R (tu:ℝ≥0∞)) (hz : FreshCorrect D R) (a : Ω) (z : Draw n ℓ g) :
    let t := trace fit D R a z (reads fit D R a z)
    t.answer = some (answer (rows fit z.2.1) (updates fit z.2.2) z.1) ∧ t.probes.length = reads fit D R a z := by
  obtain ⟨c,hc⟩ := prefix_ok D R hu a (rows fit z.2.1) (updates fit z.2.2)
  have hr := result fit D R hz a z
  simp only [outcome,finalRun,hc,Option.bind_some] at hr
  obtain ⟨fuel,hr⟩ := Execution.finish_witness _ hr
  change (trace fit D R a z fuel).answer.map (fun b => (b,(trace fit D R a z fuel).probes.length)) = _ at hr
  obtain ⟨b,done,hp⟩ := Option.map_eq_some_iff.mp hr
  obtain ⟨out,len⟩ := Prod.mk.inj hp
  have stable := run_stable D.queryStep _ fuel _ b done _ len.le
  change trace fit D R a z (reads fit D R a z)=trace fit D R a z fuel at stable
  dsimp only
  rw [stable]
  exact ⟨out ▸ done,len⟩

theorem fix_tape [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (hl : 0<ℓ) (hg : 0<g) (hn : 0<n) (fit : occupied ℓ g≤n) (D : Machine n w C) (R : RandomTape Ω C)
    {tq : ℝ} (qp : 0≤tq) (hm : FreshMeasurable D R) (hz : FreshCorrect D R) (hq : FreshQuery μ D R tq) :
    ∃ a : Ω,mean (fun z : Draw n ℓ g => (reads fit D R a z : ℝ))≤tq := by
  letI (i : Fin ℓ) : Nonempty (Block ℓ g i) := layer_nonempty hl hg i
  letI : NeZero n := ⟨hn.ne'⟩
  let X := Draw n ℓ g
  let work (z : X) (a : Ω) := cost (outcome fit D R a z)
  have meas (z : X) : Measurable (work z) := hm _ _ _ (updates_nodup fit z.2.2)
  have cheap (z : X) : (∫⁻ a,work z a ∂μ)≤ENNReal.ofReal tq := hq _ _ _ (updates_nodup fit z.2.2)
  have meas_sum : Measurable (fun a : Ω => ∑ z : X,work z a) := Finset.measurable_sum _ (fun i _ => meas i)
  obtain ⟨a,ha⟩ := exists_le_lintegral (μ:=μ) meas_sum.aemeasurable
  rw [lintegral_finset_sum _ (fun z _ => meas z)] at ha
  have up := ha.trans (Finset.sum_le_sum (fun (z : X) _ => cheap z))
  simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul] at up
  have exactCost (z : X) : work z a=(reads fit D R a z : ℝ≥0∞) := by simp [work,result fit D R hz a z,cost]
  simp_rw [exactCost] at up
  have real := ENNReal.toReal_mono (ENNReal.mul_ne_top (ENNReal.natCast_ne_top _) ENNReal.ofReal_ne_top) up
  rw [ENNReal.toReal_sum (fun _ _ => ENNReal.natCast_ne_top _),ENNReal.toReal_mul,ENNReal.toReal_natCast,ENNReal.toReal_ofReal qp] at real
  simp only [ENNReal.toReal_natCast] at real
  refine ⟨a,(div_le_iff₀ (by exact_mod_cast (Fintype.card_pos : 0<Fintype.card X) : (0:ℝ)<Fintype.card X)).mpr ?_⟩
  simpa [mul_comm] using real

end
end DisjointnessDraft.Native
