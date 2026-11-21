import DisjointnessDraft.Native.Bridge

/-! Counts of distinct cells read in the complete, untruncated correct query.
The finite-fuel simulation is charged to these actual epoch counts. -/
namespace DisjointnessDraft.Native
open DisjointnessFoundations HardDistribution Simulation VerifiedEpoch PhysicalProtocol CellProbe
open scoped ENNReal BigOperators
noncomputable section
open Classical

theorem prefix_log {A W S : Type} (step : S → QueryStep A W S) (m : A→W) {k K : ℕ} (small : k≤K) (s : S) :
    (run step m k s).probes <+: (run step m K s).probes := by
  induction k generalizing s K with
  | zero => cases K <;> cases e : step s <;> simp [run,e]
  | succ k ih =>
    cases K with
    | zero => omega
    | succ K =>
      cases e : step s with
      | done b => simp [run,e]
      | read addr next =>
        simpa only [run,e,Transcript.prepend,List.cons_prefix_cons,true_and] using ih (Nat.le_of_succ_le_succ small) (next (m addr))

variable {n ℓ g w tu : ℕ} {C Ω : Type} (fit : occupied ℓ g≤n) (D : Machine n w C) (R : RandomTape Ω C) (a : Ω)
def fullTau (i : Fin ℓ) := mean (fun z : Draw n ℓ g => (hits fit D R a z i (reads fit D R a z):ℝ))

theorem tau_le_full (hu : WorstUpdate D R (tu:ℝ≥0∞)) (hz : FreshCorrect D R) (i : Fin ℓ) (fuel : ℕ) :
    tau fit D R a fuel i≤fullTau fit D R a i := by
  apply mean_mono
  intro z
  have h := exact_trace fit D R hu hz a z
  dsimp only at h
  by_cases k : reads fit D R a z ≤ fuel
  · have eq : trace fit D R a z fuel=trace fit D R a z (reads fit D R a z) :=
      run_stable _ _ _ _ _ h.1 _ (h.2.le.trans k)
    simp [hits,eq]
  · have pref : (trace fit D R a z fuel).probes <+: (trace fit D R a z (reads fit D R a z)).probes := prefix_log _ _ (le_of_not_ge k) _
    have sub : touched (trace fit D R a z fuel).probes ⊆ touched (trace fit D R a z (reads fit D R a z)).probes := by
      intro x hx; obtain ⟨v,hv⟩ := (mem_touched _ _).mp hx
      exact (mem_touched _ _).mpr ⟨v,pref.sublist.subset hv⟩
    exact_mod_cast Finset.card_le_card (Finset.inter_subset_inter (Finset.Subset.refl _) sub :
      lastCells fit D R a z i ∩ _ ⊆ _)

theorem full_budget (hu : WorstUpdate D R (tu:ℝ≥0∞)) (hz : FreshCorrect D R) {tq : ℝ}
    (cost : mean (fun z : Draw n ℓ g => (reads fit D R a z:ℝ))≤tq) : ∑ i,fullTau fit D R a i≤tq := by
  unfold fullTau; rw [←mean_sum]
  apply le_trans _ cost
  apply mean_mono; intro z
  have k := distinct_budget fit D R a hu z (reads fit D R a z)
  rw [(exact_trace fit D R hu hz a z).2] at k
  exact_mod_cast k

theorem intersection_expectation (hl : 0<ℓ) (hg : 0<g) (q : Fin n) (x : Whole ℓ g) (i : Fin ℓ) :
    mean (fun F : Fin n → Whole ℓ g => ((F q i).val∩(x i).val).card) = 1/(ℓ:ℝ) := by
  letI (j : Fin ℓ) : Nonempty (Block ℓ g j) := layer_nonempty hl hg j
  rw [mean_eval (β:=fun _ : Fin n => Whole ℓ g) q (fun r => (((r i).val∩(x i).val).card:ℝ)),
    mean_eval (β:=Block ℓ g) i (fun r => ((r.val∩(x i).val).card:ℝ)),fixed_intersection,block_ratio hl hg i]

end
end DisjointnessDraft.Native
