import DisjointnessDraft.Applications.GirthTarget

/-! On every positive-weight graph, minimizing nonempty closed walks gives
the same directed girth as minimizing cycles whose vertices are all distinct. -/
namespace DisjointnessDraft.Applications.GirthCycles
open GirthTarget WeightedWalk Classical
noncomputable section
variable {V : Type} {E : V → ℤ → V → Prop}

inductive Route (E : V → ℤ → V → Prop) : V → ℤ → V → List V → Prop
  | start (u : V) : Route E u 0 u [u]
  | step {a b c k t vs} : Route E a k b vs → E b t c → Route E a (k+t) c (c::vs)

/-- The closing edge returns to the initial vertex. Its predecessor route
lists every vertex exactly once, including its two endpoints. -/
def Simple (E : V → ℤ → V → Prop) (d : ℤ) :=
  ∃ a b k t vs, Route E a k b vs ∧ vs.Nodup ∧ E b t a ∧ d=k+t

private theorem listed {a b k} (p : Path E a k b) : ∃ vs,Route E a k b vs := by
  induction p with | nil => exact ⟨_,.start _⟩ | snoc _ e ih => obtain ⟨_,pre⟩ := ih; exact ⟨_,pre.step e⟩

private theorem forgotten {a b k vs} (r : Route E a k b vs) : Path E a k b := by
  induction r with | start => exact .nil _ | step _ e ih => exact ih.snoc e

private theorem suffix {a b k vs} (r : Route E a k b vs) (pos : ∀u d v,E u d v → 0<d)
    (x : V) (inside : x∈vs) : ∃ t ls,Route E x t b ls ∧ ls <+: vs ∧ t≤k := by
  induction r with
  | start =>
    obtain rfl := List.mem_singleton.mp inside; exact ⟨0,[_],.start _,List.prefix_refl _,le_rfl⟩
  | @step b c k t vs rr edge ih =>
    rcases List.mem_cons.mp inside with rfl|pre
    · exact ⟨0,[_],.start _,⟨vs,rfl⟩,by have := (forgotten rr).nonneg (fun u k v e => (pos u k v e).le); have := pos _ _ _ edge; omega⟩
    · obtain ⟨d,ls,path,⟨rest,eq⟩,bound⟩ := ih pre
      exact ⟨d+t,c::ls,path.step edge,⟨rest,congrArg (c::·) eq⟩,by omega⟩

private theorem repeat_or_simple {a b k vs} (r : Route E a k b vs) (pos : ∀u d v,E u d v → 0<d) :
    vs.Nodup ∨ ∃ t,t≤k ∧ Simple E t := by
  induction r with
  | start => exact Or.inl (by simp)
  | @step b c k t vs pre edge ih =>
    rcases ih with nd|⟨d,le,found⟩
    · by_cases m : c∈vs
      · obtain ⟨cost,ls,path,sub,le⟩ := suffix pre pos c m
        exact Or.inr ⟨cost+t,by omega,c,b,cost,t,ls,path,nd.sublist sub.sublist,edge,rfl⟩
      · exact Or.inl (List.nodup_cons.mpr ⟨m,nd⟩)
    · exact Or.inr ⟨d,by have := pos _ _ _ edge; omega,found⟩

theorem closed_of_simple (pos : ∀u d v,E u d v → 0<d) {d} (h : Simple E d) : Cycle E d := by
  obtain ⟨a,b,k,t,vs,path,_,ed,rfl⟩ := h
  have nn := (forgotten path).nonneg (fun u k v e => (pos u k v e).le)
  exact ⟨add_pos_of_nonneg_of_pos nn (pos _ _ _ ed),a,(forgotten path).snoc ed⟩

theorem extract (pos : ∀u d v,E u d v → 0<d) {d} (walk : Cycle E d) : ∃ t,t≤d ∧ Simple E t := by
  obtain ⟨positive,u,p⟩ := walk
  cases p with
  | nil => omega
  | @snoc b _ k t pre ed =>
    obtain ⟨vs,r⟩ := listed pre
    rcases repeat_or_simple r pos with nd|⟨c,le,cy⟩
    · exact ⟨k+t,le_rfl,u,b,k,t,vs,r,nd,ed,rfl⟩
    · exact ⟨c,by have := pos _ _ _ ed; omega,cy⟩

theorem threshold (pos : ∀u d v,E u d v → 0<d) (D : ℤ) :
    (∃k,k≤D ∧ Cycle E k) ↔ ∃k,k≤D ∧ Simple E k := by
  constructor
  · rintro ⟨k,le,p⟩; obtain ⟨j,jk,s⟩ := extract pos p; exact ⟨j,jk.trans le,s⟩
  · rintro ⟨k,le,p⟩; exact ⟨k,le,closed_of_simple pos p⟩

theorem minimum (pos : ∀u d v,E u d v → 0<d) (k : ℤ) :
    (Cycle E k ∧ ∀d,Cycle E d → k≤d) ↔ Simple E k ∧ ∀d,Simple E d → k≤d := by
  constructor
  · rintro ⟨p,lo⟩; obtain ⟨j,le,s⟩ := extract pos p
    exact ⟨le_antisymm le (lo j (closed_of_simple pos s)) ▸ s,fun d simple => lo d (closed_of_simple pos simple)⟩
  · rintro ⟨s,lo⟩; refine ⟨closed_of_simple pos s,?_⟩
    intro d p; obtain ⟨j,le,cycle⟩ := extract pos p; exact (lo j cycle).trans le

def bySimpleCycles (h : Hist V) : Option ℕ :=
  if yes : ∃k : ℕ,Simple (graph h) k then some (Nat.find yes) else none

theorem reported_girth (h : Hist V) (pos : ∀u k v,graph h u k v → 0<k) :
    exactSpec () h ()=bySimpleCycles h := by
  unfold exactSpec bySimpleCycles
  by_cases hc : ∃k : ℕ,Cycle (graph h) k
  · have present := Nat.find_spec hc
    have least (d : ℤ) (w : Cycle (graph h) d) : (Nat.find hc:ℤ)≤d := by
      have same := Int.toNat_of_nonneg w.1.le
      have w' : Cycle (graph h) (d.toNat:ℤ) := same.symm ▸ w
      have small := Nat.find_min' hc w'; omega
    have m := (minimum pos (Nat.find hc)).mp ⟨present,least⟩
    have hs : ∃k : ℕ,Simple (graph h) k := ⟨_,m.1⟩
    rw [dif_pos hc,dif_pos hs,Option.some.injEq]
    refine le_antisymm ?_ (Nat.find_min' hs m.1)
    exact_mod_cast m.2 _ (Nat.find_spec hs)
  · have hs : ¬∃k : ℕ,Simple (graph h) k := fun ⟨k,w⟩ => hc ⟨k,closed_of_simple pos w⟩
    rw [dif_neg hc,dif_neg hs]

theorem reported_threshold (h : Hist V) (pos : ∀u k v,graph h u k v → 0<k) (D : ℤ) :
    testSpec D () h ()=decide (∃k,k≤D ∧ Simple (graph h) k) :=
  decide_eq_decide.mpr (threshold pos D)

end
end DisjointnessDraft.Applications.GirthCycles
