import DisjointnessDraft.Applications.UnitTarget
import DisjointnessDraft.Applications.UnitSizes

/-! Exact and threshold queries in unweighted planar graphs, with every
source insertion implemented by one ordinary edge insertion. All large
target sizes are covered by explicitly attached unit pendant leaves. -/
namespace DisjointnessDraft.Applications.UnitTarget
open UnitEncoding PlanarEncoding PlanarPadding WeightedWalk Transfer.Compiler ShortTransfer Filter Real MeasureTheory Classical
noncomputable section
variable {n pad : ℕ} (hn : 0<n)
def exactPlan (pad : ℕ) := plan hn pad none (PlanarTarget.readSize n)
def testPlan (pad : ℕ) := plan hn pad false (!·)
private theorem nohit (f : Family n) (xs : List (Fin n)) (q : Fin n) :
    decide (¬∃x∈xs,x∈f q)=answer f xs q := by apply decide_eq_decide.mpr; simp

theorem size_valid : Valid (exactPlan hn pad) (initLegal (init hn pad) legal) (initSpec (init hn pad) exactSpec) := by
  refine ⟨fun f xs q nd h pre => valid_path hn _ _ f xs q nd h pre,?_⟩
  intro f xs q _
  change PlanarTarget.readSize n (PlanarTarget.minimum (graph (initial hn f++before (exactPlan hn pad) xs)) (terminals hn q))=_
  rw [show graph (initial hn f++before (exactPlan hn pad) xs)=present hn f xs from final_graph ..,←nohit]
  have m := distance (pad:=pad) hn f xs q
  let D := PlanarTarget.normal n
  have pp : 1≤D := by dsimp [D,PlanarTarget.normal,PlanarCore.H,dim]; push_cast; nlinarith [sq_nonneg (n:ℤ)]
  let d : ℤ := D-(if ∃x∈xs,x∈f q then 1 else 0)
  have nn : 0≤d := by dsimp [d]; split_ifs <;> omega
  have out := PlanarTarget.exact_value (present hn f xs) (terminals hn q) d nn m.1 m.2
  unfold PlanarTarget.readSize; rw [out]; apply decide_eq_decide.mpr; rw [Option.some.injEq]
  by_cases h : ∃x∈xs,x∈f q
  · have e : d=D-1 := by simp [d,h]
    rw [e]; simp only [h,not_true_eq_false,iff_false]; change (D-1).toNat≠D.toNat; omega
  · simp [d,D,h]

theorem test_valid : Valid (testPlan hn pad) (initLegal (init hn pad) legal)
    (initSpec (init hn pad) (thresholdSpec (PlanarTarget.normal n-1))) := by
  refine ⟨fun f xs q nd h pre => valid_path hn _ _ f xs q nd h pre,?_⟩
  intro f xs q _
  change (!decide (∃ k : ℤ,k≤PlanarTarget.normal n-1 ∧ Path (sym (graph (initial hn f++before (testPlan hn pad) xs))) (terminals hn q).1 k (terminals hn q).2))=_
  rw [show graph (initial hn f++before (testPlan hn pad) xs)=present hn f xs from final_graph ..,←nohit]
  have m := distance (pad:=pad) hn f xs q
  let d : ℤ := PlanarTarget.normal n-(if ∃x∈xs,x∈f q then 1 else 0)
  have out := PlanarTarget.threshold_value (present hn f xs) (terminals hn q) d (PlanarTarget.normal n-1) m.1 m.2
  rw [←decide_not]; apply decide_eq_decide.mpr; rw [out]
  by_cases hit : ∃x∈xs,x∈f q <;> simp [d,hit]

def padding (N : ℕ) (hz : 0<unitSize N) := N-Fintype.card (U (unitSize N) hz)

theorem lower (lo hi : ℝ) (lp : 0<lo) (lh : lo≤hi) :
    ∃ c : ℝ,0<c ∧ ∀ᶠ N : ℕ in atTop,
      ∃ hz : 0<unitSize N, let T := V (unitSize N) (padding N hz) hz
      Fintype.card T=N ∧ Bound lo hi c N false (legal (T:=T)) exactSpec ∧
      Bound lo hi c N false (legal (T:=T)) (thresholdSpec (PlanarTarget.normal (unitSize N)-1)) := by
  obtain ⟨c,cp,large⟩ := Transfer.Compiler.lower lo hi lp lh 1 1 24 (by norm_num)
  obtain ⟨k,B⟩ := eventually_atTop.mp large
  refine ⟨c,cp,?_⟩
  filter_upwards [UnitEncoding.geometry k] with N g
  let n := unitSize N
  obtain ⟨kn,n16,fit,nN,dist⟩ := g
  have hz : 0<n := by change 16≤n at n16; omega
  let pad := padding N hz
  have card : Fintype.card (U n hz)≤N := (mesh_size n16 hz).trans fit
  have full : Fintype.card (V n pad hz)=N := by
    change Fintype.card (U n hz ⊕ Fin pad)=N
    rw [Fintype.card_sum,Fintype.card_fin]; exact Nat.add_sub_of_le card
  refine ⟨hz,full,?_,?_⟩
  all_goals
    intro w tu tq tu1 tq1 wl wh Ω _ μ _ D H
    have nn : (0:ℝ)<N := by exact_mod_cast hz.trans_le nN
    have logs := logb_le_logb_of_le (b:=2) (by norm_num) nn (by exact_mod_cast dist : (N:ℝ)≤(n:ℝ)^24)
    rw [logb_pow] at logs
  · exact B n kn N w tu nN (by simpa using logs) tu1 wl wh _ _ _ _ Ω μ (exactPlan hz pad)
      (initialized D (init hz pad)) _ _ false tq tq1 (init_guarantees μ D _ H)
      (size_valid hz) (by simp [exactPlan,plan]) (by simp [exactPlan,plan]) (by simp [exactPlan,plan])
  · exact B n kn N w tu nN (by simpa using logs) tu1 wl wh _ _ _ _ Ω μ (testPlan hz pad)
      (initialized D (init hz pad)) _ _ false tq tq1 (init_guarantees μ D _ H)
      (test_valid hz) (by simp [testPlan,plan]) (by simp [testPlan,plan]) (by simp [testPlan,plan])

end
end DisjointnessDraft.Applications.UnitTarget
