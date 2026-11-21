import DisjointnessDraft.Information.AcceptedRectangle
import DisjointnessDraft.Information.IntermediateSizes
import DisjointnessDraft.Information.FiberEntropy

/-! The intermediate Step 2 conclusions on the same protocol under the
draft's actual bit lengths, epoch range, and acceptance threshold. -/
namespace DisjointnessDraft.Information.Game
open Real Filter MeasureTheory DisjointnessFoundations.HardIndependence
open scoped Topology BigOperators
noncomputable section
open Classical
set_option maxHeartbeats 800000
variable {W O R U P A : Type*}
  [Fintype W] [MeasurableSpace W] [MeasurableSingletonClass W] [Nonempty W]
  [Fintype O] [MeasurableSpace O] [MeasurableSingletonClass O]
  [Fintype R] [MeasurableSpace R] [MeasurableSingletonClass R]
  [Fintype U] [MeasurableSpace U] [MeasurableSingletonClass U]
  [Fintype P] [MeasurableSpace P] [MeasurableSingletonClass P]
  [Fintype A] [MeasurableSpace A] [MeasurableSingletonClass A]

/-- Propositions on both marginals and the correlation, followed by the
monochromatic near-rectangle. Its product-law corollary is
`NearWitness.rectangle`. The same positive acceptance law appears throughout. -/
theorem fiber_conclusions (hi : ℝ) : ∀ᶠ n : ℕ in atTop, ∀ ℓ s g w ub ab : ℕ, ∀ tq : ℝ,
    ∀ [Nonempty (Layer (ℓ*s^2) s)] (G : Game n (ℓ*s^2) s W O R U P A)
      (o : Measure O) (r : Measure R) [IsProbabilityMeasure o] [IsProbabilityMeasure r],
    G.Sound → (unif W).map G.block=unif (Layer (ℓ*s^2) s) →
    0<ℓ → (ℓ:ℝ)≤logb 2 n → n≤s^3 → s^2≤n → g^95≤n →
    1≤tq → tq≤(logb 2 n)^2 → (w:ℝ)≤hi*logb 2 n →
    (ub:ℝ)≤5*g*s → (ab:ℝ)≤17*tq*w →
    Fintype.card U≤2^ub → Fintype.card A≤2^ab → (Fintype.card P:ℝ)≤(2:ℝ)^((s:ℝ)/160) →
    (n:ℝ)^(-1/6:ℝ)≤acceptance G o r →
    ∃ hn : 0<n, ∃ hr : 0<acceptance G o r,
      (3/4≤eventProbability (G.acceptedLaw o r hn hr) (fun v => SmoothQuery (G.queryPosterior o r v) (32*(n:ℝ)^(1/5:ℝ)))) ∧
      (3/4≤eventProbability (G.acceptedLaw o r hn hr) (fun v => CappedUpdate (G.updatePosterior o r v) (4*(2:ℝ)^((s:ℝ)/160)/acceptance G o r))) ∧
      (∑v,(G.acceptedLaw o r hn hr).weight v*(G.corr o r v/log 2))≤(n:ℝ)^(-2/5:ℝ)/acceptance G o r ∧
      Nonempty (G.NearWitness o r) := by
  filter_upwards [eventually_ge_atTop 1,eventual_intermediate hi] with n np seq
  intro ℓ s g w ub ab tq inst G o r io ir sound bal lp depth low high growth tq1 tqu wh hu ha aU aA aP rho
  have pos : (0:ℝ)<n := by exact_mod_cast np
  have hr := (rpow_pos_of_pos pos _).trans_le rho
  have b := seq ℓ s g w ub ab tq (acceptance G o r) lp depth low high growth tq1 tqu wh hu ha rho
  exact ⟨np,hr,G.query_entropy o r np hr bal ub ab aU aA b.query,
    G.update_entropy o r np hr _ aP,G.accepted_correlation o r np hr ub aU b.common,
    G.accepted_near_rectangle o r np hr sound bal ub ab aU aA b.query b.common aP b.large b.smooth b.packet b.correlation⟩

end
end DisjointnessDraft.Information.Game
