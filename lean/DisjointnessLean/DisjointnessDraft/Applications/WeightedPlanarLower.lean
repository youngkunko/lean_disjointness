import DisjointnessDraft.Applications.PlanarTarget

/-! Exact weighted planar distance, and its fixed-threshold decision version,
on every sufficiently large number of vertices. Preprocessing begins empty;
the planar drawing and the positive weight bound hold at every legal prefix. -/
namespace DisjointnessDraft.Applications.PlanarTarget
open PlanarEncoding PlanarPadding PlanarCore WeightedWalk CoreSize Transfer.Compiler ShortTransfer MeasureTheory Filter Real Classical
noncomputable section
def normal (n : ℕ) : ℤ := 2*H (dim n)
def readSize (n : ℕ) (ans : Option ℕ) := decide (ans=some (normal n).toNat)
def exactPlan (n pad : ℕ) := plan n pad none (readSize n)
def testPlan (n pad : ℕ) := plan n pad false (!·)

private theorem positive (n : ℕ) : 1≤normal n := by dsimp [normal,H,dim]; push_cast; nlinarith [sq_nonneg (n:ℤ)]
private theorem nohit (f : Family n) (xs : List (Fin n)) (q : Fin n) :
    decide (¬∃x∈xs,x∈f q)=answer f xs q := by apply decide_eq_decide.mpr; simp

theorem exact_valid : Valid (exactPlan n pad) (initLegal (init n pad) (legal (limit n)))
    (initSpec (init n pad) exactSpec) := by
  refine ⟨fun f xs q nd h pre => path_valid _ _ f xs q nd h pre,?_⟩
  intro f xs q _
  change readSize n (minimum (graph (initial f++before (exactPlan n pad) xs)) (query q))=_
  rw [show graph (initial f++before (exactPlan n pad) xs)=input f xs from final_edges ..,←nohit]
  have m := encoded_distance (pad:=pad) f xs q
  have pp := positive n
  let d : ℤ := normal n-(if ∃x∈xs,x∈f q then 1 else 0)
  have nnd : 0≤d := by dsimp [d]; split_ifs <;> omega
  have out := exact_value (input f xs) (query q) d nnd m.1 m.2
  unfold readSize; rw [out]
  apply decide_eq_decide.mpr
  rw [Option.some.injEq]
  by_cases h : ∃x∈xs,x∈f q
  · have e : d=normal n-1 := by simp [d,h]
    rw [e]; simp only [h,not_true_eq_false,iff_false]; omega
  · simp [d,h]

theorem threshold_valid : Valid (testPlan n pad) (initLegal (init n pad) (legal (limit n)))
    (initSpec (init n pad) (thresholdSpec (normal n-1))) := by
  refine ⟨fun f xs q nd h pre => path_valid _ _ f xs q nd h pre,?_⟩
  intro f xs q _
  change (!decide (∃ k : ℤ,k≤normal n-1 ∧ Path (sym (graph (initial f++before (testPlan n pad) xs))) (query q).1 k (query q).2))=_
  rw [show graph (initial f++before (testPlan n pad) xs)=input f xs from final_edges ..,←nohit]
  have m := encoded_distance (pad:=pad) f xs q
  let d : ℤ := normal n-(if ∃x∈xs,x∈f q then 1 else 0)
  have out := threshold_value (input f xs) (query q) d (normal n-1) m.1 m.2
  rw [←decide_not]; apply decide_eq_decide.mpr; rw [out]
  by_cases hit : ∃x∈xs,x∈f q <;> simp [d,hit]

def vertexCount (n : ℕ) := 8*(dim n)^2+4*(dim n)
def padding (N : ℕ) := N-vertexCount (ShortTransfer.stringSize N)
theorem vertex_count (n pad : ℕ) : Fintype.card (W n pad)=vertexCount n+pad := by
  change Fintype.card ((Bool × Menu (dim n)) ⊕ Fin pad)=_; simp only [Fintype.card_sum,Fintype.card_fin,paired_size,vertexCount]

theorem lower (lo hi : ℝ) (lp : 0<lo) (lh : lo≤hi) :
    ∃c : ℝ,0<c ∧ ∀ᶠ N : ℕ in atTop,
      let n := ShortTransfer.stringSize N
      let pad := padding N
      Fintype.card (W n pad)=N ∧
      Bound lo hi c N false (legal (T:=W n pad) (limit n)) exactSpec ∧
      Bound lo hi c N false (legal (T:=W n pad) (limit n)) (thresholdSpec (normal n-1)) := by
  obtain ⟨c,cp,event⟩ := ShortTransfer.eventual lo hi lp lh
  obtain ⟨k,b⟩ := eventually_atTop.mp event
  refine ⟨c,cp,?_⟩
  filter_upwards [ShortTransfer.string_geometry (max k 32)] with N geom
  obtain ⟨kn,_,fit,low,high⟩ := geom
  let n := ShortTransfer.stringSize N
  let pad := padding N
  have nn : 32≤n := (le_max_right ..).trans kn
  have cap : vertexCount n≤N := by
    change 9*(n*n)≤N at fit
    dsimp [vertexCount,dim]; nlinarith [Nat.mul_le_mul_left n nn]
  have card : Fintype.card (W n pad)=N := by rw [vertex_count]; exact Nat.add_sub_of_le cap
  refine ⟨card,?_,?_⟩
  · intro w tu tq tu1 tq1 wl wh Ω _ μ _ D H
    have cert := b n ((le_max_left ..).trans kn) N low high (exactPlan n pad) false exact_valid
      (by simp [exactPlan,plan]) (by simp [exactPlan,plan]) (by simp [exactPlan,plan])
    exact cert w tu tq tu1 tq1 wl wh Ω μ (initialized D (init n pad)) (init_guarantees μ D _ H)
  · intro w tu tq tu1 tq1 wl wh Ω _ μ _ D H
    have cert := b n ((le_max_left ..).trans kn) N low high (testPlan n pad) false threshold_valid
      (by simp [testPlan,plan]) (by simp [testPlan,plan]) (by simp [testPlan,plan])
    exact cert w tu tq tu1 tq1 wl wh Ω μ (initialized D (init n pad)) (init_guarantees μ D _ H)
end
end DisjointnessDraft.Applications.PlanarTarget
