import DisjointnessDraft.Applications.MatchGraph

/-! The matching reduction consists of a static graph with the dummy row,
one connector per inserted element, then the two fresh query edges. -/
namespace DisjointnessDraft.Applications.MatchUpdates
open OriginalGrid DirectedCore PlanarCore PlanarMatching CoreSize PlanarEncoding MatchGraph
open WeightedMatching FinitePlanarDistance Classical
noncomputable section
variable {n pad : ℕ}

def localCost (p : ℤ) (a b : Vertex) : ℤ := match a with
  | .corner _ => localWeight p a b
  | .inside _ _ _ => localWeight p b a
def cost (p : ℤ) : T → T → ℤ
  | .left a,.left b | .right a,.right b => localCost p a b
  | .left a,.right _ => match a with | .corner (r,_) => link p r | _ => 0
  | _,_ => 0

theorem unique_weight {p M A a k b} (e : Physical p M A a k b) : k=cost p a b := by
  have both {M u t v} (st : OriginalGrid.Step p M u t v) :
      t=localCost p u v ∧ t=localCost p v u := by
    cases st with
    | cell r c _ _ _ _ st => cases st <;> simp [embed,localCost,localWeight]
  cases e with
  | l h => exact h.elim (fun s => (both s).1) (fun s => (both s).2)
  | r h => exact h.elim (fun s => (both s).1) (fun s => (both s).2)
  | cross j on => rfl

def pairWeight (z : Pair n pad) : ℤ := match z with
  | (some u,.inl (some v)) => if u=v then limit n else limit n-cost (dim n) (PlanarMatching.place u) (PlanarMatching.place v)
  | _ => limit n

def original (f : Family n) : Pair n pad → Prop
  | (some u,.inl (some v)) => u=v ∨ ∃k,mapped (table f) (enabled ([] : List (Fin n))) u k v
  | _ => False
def connector (x : Fin n) : Pair n pad := (some (false,.right x.castSucc),.inl (some (true,.right x.castSucc)))
def entry (q : Fin n) : Pair n pad := (none,.inl (some (src q)))
def exitEdge (q : Fin n) : Pair n pad := (some (dst q),.inl none)

private theorem physical_change {f : Family n} {xs : List (Fin n)} {u v : T} {k : ℤ} :
    Physical (dim n) (table f) (enabled xs) u k v ↔ Physical (dim n) (table f) (enabled ([] : List (Fin n))) u k v ∨
      ∃x∈xs,u=.left (side (dim n) (pos x)) ∧ v=.right (side (dim n) (pos x)) ∧ k=link (dim n) (pos x) := by
  constructor
  · intro e
    cases e with
    | l h => exact Or.inl (.l h)
    | r h => exact Or.inl (.r h)
    | cross j on =>
      rcases on with rfl|⟨x,h,rfl⟩
      · exact Or.inl (.cross _ (Or.inl rfl))
      · exact Or.inr ⟨x,h,rfl,rfl,rfl⟩
  · rintro (e|⟨x,h,rfl,rfl,rfl⟩)
    · cases e with
      | l h => exact .l h
      | r h => exact .r h
      | cross j on => exact .cross _ (Or.inl (by simpa [enabled] using on))
    · exact .cross _ (Or.inr ⟨x,h,rfl⟩)

private theorem change_arcs {f : Family n} {xs : List (Fin n)} {u v : Core n} {k : ℤ} :
    mapped (table f) (enabled xs) u k v ↔ mapped (table f) (enabled ([] : List (Fin n))) u k v ∨
      ∃x∈xs,u=(false,.right x.castSucc) ∧ v=(true,.right x.castSucc) ∧ k=link (dim n) (pos x) := by
  constructor
  · rintro ⟨edge,rankh⟩
    rcases physical_change.mp edge with h|⟨x,h,eu,ev,rfl⟩
    · exact Or.inl ⟨h,rankh⟩
    · exact Or.inr ⟨x,h,PlanarMatching.inj (eu.trans rfl),PlanarMatching.inj (ev.trans rfl),rfl⟩
  · rintro (⟨e,rankh⟩|⟨x,h,rfl,rfl,rfl⟩)
    · exact ⟨physical_change.mpr (Or.inl e),rankh⟩
    · refine ⟨Physical.cross _ (Or.inr ⟨x,h,rfl⟩),?_⟩
      dsimp [PlanarMatching.place,UnitCore.layer,vertex,pos,rank,level,dim]
      have := x.isLt; omega

private theorem onArc {f : Family n} {xs : List (Fin n)} {u v : Core n} {k : ℤ}
    (e : mapped (table f) (enabled xs) u k v) :
    u≠v ∧ k=cost (dim n) (PlanarMatching.place u) (PlanarMatching.place v) := by
  refine ⟨?_,unique_weight e.1⟩
  rintro rfl
  exact (lt_irrefl _ e.2)

theorem components (f : Family n) (xs : List (Fin n)) (q : Fin n) (z : Pair n pad) (k : ℤ) :
    graph f xs q z.1 k z.2 ↔
      (original f z ∨ (∃ x∈xs,z=connector x) ∨ z=entry q ∨ z=exitEdge q) ∧ k=pairWeight z := by
  rcases z with ⟨a,b⟩; cases b with
  | inr i => cases a <;> simp [graph,BipartiteOptimum.padded,original,connector,entry,exitEdge]
  | inl b =>
    cases a <;> cases b
    case none.none => simp [graph,BipartiteOptimum.padded,allowed,original,connector,entry,exitEdge]
    case none.some v =>
      simp [graph,BipartiteOptimum.padded,allowed,original,connector,entry,exitEdge,pairWeight,sub_eq_zero,eq_comm]
      omega
    case some.none u =>
      simp [graph,BipartiteOptimum.padded,allowed,original,connector,entry,exitEdge,pairWeight,sub_eq_zero,eq_comm]
      omega
    case some.some u v =>
      change ((u=v ∧ limit n-k=0) ∨ mapped (table f) (enabled xs) u (limit n-k) v) ↔ _
      simp only [original,connector,entry,exitEdge,Prod.mk.injEq,Option.some.injEq,Sum.inl.injEq,
        reduceCtorEq,and_false,false_and,or_false,pairWeight]
      by_cases eq : u=v
      · subst v
        simp only [true_or,if_pos rfl,true_and,sub_eq_zero]
        constructor
        · rintro (e|e)
          · exact e.symm
          · exact False.elim ((onArc e).1 rfl)
        · exact fun h => Or.inl h.symm
      · simp only [eq,false_and,false_or,if_false]
        constructor
        · intro e
          obtain ⟨_,ew⟩ := onArc e
          refine ⟨?_,by omega⟩
          rcases change_arcs.mp e with eo|⟨x,h,eu,ev,_⟩
          · exact Or.inl ⟨_,eo⟩
          · exact Or.inr ⟨x,h,eu,ev⟩
        · rintro ⟨present,ew⟩
          rcases present with ⟨t,h⟩|⟨x,h,rfl,rfl⟩
          · have w := (onArc h).2
            rw [show limit n-k=t by omega]
            exact change_arcs.mpr (Or.inl h)
          · apply change_arcs.mpr (Or.inr ⟨x,h,rfl,rfl,?_⟩)
            dsimp [cost,PlanarMatching.place,UnitCore.layer,vertex] at ew
            change k=limit n-link (dim n) (pos x) at ew
            omega

theorem weight_bound (f : Family n) (xs : List (Fin n)) (q : Fin n) {a : L n} {b : R n pad} {k : ℤ}
    (e : graph f xs q a k b) : 0<k ∧ k≤limit n := by
  have p2 : 2≤dim n := by have := q.isLt; dsimp [dim]; omega
  have pos : 0<limit n := by dsimp [limit,H,dim]; push_cast; positivity
  cases b with
  | inr => contradiction
  | inl b =>
    cases a <;> cases b
    case none.none => contradiction
    case none.some | some.none => obtain ⟨_,eq⟩ := e; omega
    case some.some u v =>
      rcases e with ⟨_,eq⟩|ar
      · omega
      · have ww := directed_sub ar
        have h : 0<limit n-k ∧ limit n-k≤8*(dim n:ℤ)*(dim n+1) :=
          ww.elim (weight_bounds p2 (rows xs)) (weight_bounds p2 (rows xs))
        dsimp [limit,H] at *
        constructor <;> nlinarith

theorem connector_inj : Function.Injective (@connector n pad) := by
  intro u v eq; simpa [connector] using eq

theorem missing (f : Family n) (x : Fin n) : ¬original (pad:=pad) f (connector x) := by
  rintro (no|⟨k,e⟩)
  · cases no
  · have h : Physical (dim n) (table f) (enabled ([] : List (Fin n))) (.left (side (dim n) (pos x))) k
          (.right (side (dim n) (pos x))) := e.1
    cases h with
    | cross j on => simp [enabled,dim,pos] at on; have := x.isLt; omega

end
end DisjointnessDraft.Applications.MatchUpdates
