import DisjointnessDraft.Applications.BipartiteOptimum
import DisjointnessDraft.Applications.SplitArcs
import DisjointnessDraft.Applications.OuterDrawing

/-! The complete, weighted bipartite graph on the actual hard input, its
planar embedding, and the exact matching optimum at the queried column. -/
namespace DisjointnessDraft.Applications.MatchGraph
open OriginalGrid DirectedCore PlanarCore PlanarMatching CoreSize PlanarEncoding
open SplitArcs OuterDrawing PlanarPadding Classical
noncomputable section
variable {n pad : ℕ}
abbrev Core (n : ℕ) := V (dim n)
abbrev L (n : ℕ) := Option (Core n)
abbrev R (n pad : ℕ) := Option (Core n) ⊕ Fin pad
abbrev Pair (n pad : ℕ) := L n × R n pad
def limit (n : ℕ) : ℤ := 2*H (dim n)+1
def src (q : Fin n) : Core n := (false,.top q.castSucc)
def dst (q : Fin n) : Core n := (true,.top (Fin.rev q.castSucc))
def graph (f : Family n) (xs : List (Fin n)) (q : Fin n) :=
  BipartiteOptimum.padded (pad:=pad) (mapped (table f) (enabled xs)) (src q) (dst q) (limit n)
def value (n : ℕ) : ℤ := (8*(dim n:ℤ)^2+4*(dim n:ℤ))*limit n+1

theorem optimum (f : Family n) (xs : List (Fin n)) (q : Fin n) :
    BipartiteOptimum.maximum (graph (pad:=pad) f xs q)=value n+(if ∃ x∈xs,x∈f q then 1 else 0) := by
  have size : 2≤dim n := by have := q.isLt; dsimp [dim]; omega
  have blank : table f (dim n) (pos q.castSucc)=false := by
    simp only [table,decide_eq_false_iff_not]
    rintro ⟨x,i,e,_,_⟩; have := x.isLt; dsimp [pos,dim] at e; omega
  have hit : (∃j,enabled xs j ∧ table f j (pos q.castSucc)=true) ↔ ∃ x∈xs,x∈f q := by
    constructor
    · rintro ⟨j,yes,mem⟩
      obtain ⟨x,i,r,c,m⟩ := of_decide_eq_true mem
      have ii : i=q := pos_inj (show pos i=pos q from c)
      rcases yes with rfl|⟨y,hy,ey⟩
      · rw [blank] at mem; contradiction
      · obtain rfl := pos_inj (r.trans ey.symm); exact ⟨x,hy,ii▸m⟩
    · rintro ⟨x,h,m⟩; exact ⟨pos x,Or.inr ⟨x,h,rfl⟩,decide_eq_true ⟨x,q,rfl,rfl,m⟩⟩
  obtain ⟨attain,bound⟩ := PlanarMatching.maximum (dim n) q.castSucc (table f) (enabled xs) size
    (rows xs) (Or.inl rfl) blank
  apply BipartiteOptimum.transfer
  · simpa only [value,limit,hit] using attain
  · simpa only [value,limit,hit] using bound

def chart : L n ⊕ R n pad → Host (SplitCore.Chart (dim n)) pad
  | .inl none => .source
  | .inl (some u) => .old (tag true u)
  | .inr (.inl none) => .sink
  | .inr (.inl (some u)) => .old (tag false u)
  | .inr (.inr i) => .isolate i

theorem tag_eq {u v : V p} {a b : Bool} : tag a u=tag b v ↔ u=v ∧ a=b := by
  obtain ⟨i,u⟩ := u; obtain ⟨j,v⟩ := v
  cases i <;> cases j <;> cases a <;> cases b <;> simp [tag]

theorem chart_inj : Function.Injective (@chart n pad) := by
  have forms (v : L n ⊕ R n pad) :
      v=.inl none ∨ (∃u,v=.inl (some u)) ∨ v=.inr (.inl none) ∨
        (∃u,v=.inr (.inl (some u))) ∨ ∃i,v=.inr (.inr i) := by
    rcases v with _|(_|_)
    case inl a => cases a <;> simp
    case inr.inl a => cases a <;> simp
    case inr.inr => simp
  intro a b eq
  rcases forms a with rfl|⟨u,rfl⟩|rfl|⟨u,rfl⟩|⟨u,rfl⟩ <;>
    rcases forms b with rfl|⟨v,rfl⟩|rfl|⟨v,rfl⟩|⟨v,rfl⟩ <;> simp_all [chart,tag_eq]

def plain {A B : Type} (F : A → ℤ → B → Prop) : A ⊕ B → A ⊕ B → Prop
  | .inl a,.inr b => ∃k,F a k b
  | _,_ => False

theorem planar (f : Family n) (xs : List (Fin n)) (q : Fin n) :
    Nonempty (Drawing (plain (graph (pad:=pad) f xs q))) := by
  let a := tag false (src q)
  let b := tag true (dst q)
  have ne : a≠b := by simp [a,b,tag,src,dst]
  let d := OuterDrawing.drawing (pad:=pad) (SplitCore.drawing (dim n)) SplitCore.high a b ne
    (top_y false false q.castSucc) (top_y true true (Fin.rev q.castSucc))
  apply Nonempty.intro (OuterDrawing.pull d chart chart_inj ?_)
  intro u v edge
  rcases u with u|u <;> rcases v with v|v <;> try contradiction
  obtain ⟨k,e⟩ := edge
  cases v with
  | inr v => contradiction
  | inl v =>
    cases u <;> cases v
    case none.none => contradiction
    case none.some v =>
      obtain ⟨rfl,_⟩ := e
      exact .left
    case some.none u =>
      obtain ⟨rfl,_⟩ := e
      exact .right
    case some.some u v =>
      rcases e with ⟨rfl,_⟩|arc
      · exact .base (diagonal u)
      · exact .base (drawing_edges (rows xs) arc)

end
end DisjointnessDraft.Applications.MatchGraph
