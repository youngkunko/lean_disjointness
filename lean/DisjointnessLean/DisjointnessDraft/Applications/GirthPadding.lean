import DisjointnessDraft.Applications.GirthOrient

/-! Directed leaves have no outgoing arcs. They preserve core distances, the
single update per inserted element, and an outer-face return drawing. -/
namespace DisjointnessDraft.Applications.GirthPadding
open GirthOrient GirthTarget GirthDrawing PlanarPadding WeightedWalk Classical
noncomputable section
variable {V : Type} (s : Storage n V) (root : V)
def power : V ⊕ Fin pad → ℚ | .inl a => s.rank a | .inr _ => s.rank root+1
def pair (a : V×V) : (V⊕Fin pad)×(V⊕Fin pad) := (.inl a.1,.inl a.2)
theorem pair_inj : Function.Injective (@pair V pad) := by rintro ⟨a,b⟩ ⟨x,y⟩ e; simpa [pair] using e

def lift (pad : ℕ) : Storage n (V ⊕ Fin pad) where
  stored f xs := extend (s.stored f xs) root
  potential a b := match a,b with | .inl x,.inl y => s.potential x y | .inl x,.inr _ => x=root | _,_ => False
  strength a b := match a,b with | .inl x,.inl y => s.strength x y | _,_ => 1
  rank := power s root
  put x := pair (s.put x)
  src x := .inl (s.src x)
  dst x := .inl (s.dst x)
  inside := by rintro f xs (u|u) k (v|v) h; exact s.inside _ _ _ _ _ h; exact h.1; contradiction; contradiction
  asymmetric := by rintro (u|u) (v|v) h <;> first | exact s.asymmetric _ _ h | contradiction | exact id
  canonical := by rintro f xs (u|u) k (v|v) h; exact s.canonical _ _ _ _ _ h; exact h.2; contradiction; contradiction
  activity := by
    rintro f xs (u|u) k (v|v)
    · have ids (x : Fin n) : ((u,v)=s.put x) ↔ u=(s.put x).1 ∧ v=(s.put x).2 := Prod.ext_iff
      simpa [extend,pair,ids] using s.activity f xs u k v
    all_goals simp [extend,pair]
  fresh := fun f x => s.fresh f x
  injective := pair_inj.comp s.injective
  inserted := s.inserted
  forward := s.forward
  order := s.order

private theorem to_core {f : Family n} {xs : List (Fin n)} {a b : V} {k : ℤ}
    (p : Path (oriented (lift s root pad) f xs) (.inl a) k (.inl b)) : Path (oriented s f xs) a k b := by
  have project {v : V ⊕ Fin pad} {k} (walk : Path (oriented (lift s root pad) f xs) (.inl a) k v) :
      ∀ b,v=.inl b → Path (oriented s f xs) a k b := by
    induction walk with
    | nil => intro b eq; cases eq; exact .nil _
    | @snoc u v _ _ _ edge ih =>
      intro b eq; subst v
      cases u with
      | inl u => exact (ih u rfl).snoc edge
      | inr u =>
        rcases edge with ⟨op|⟨rfl,rfl⟩,hi⟩
        · contradiction
        · change s.rank b+1<s.rank b at hi; linarith
  exact project p b rfl

structure Geometry (s : Storage n V) (root : V) (B D : ℤ) where
  diagram : ∀f xs,Drawing (plain (s.stored f xs))
  leftmost : ∀ f xs v,((diagram f xs).point root).1≤((diagram f xs).point v).1
  above : ∀f xs v,0≤((diagram f xs).point v).2
  top : ∀f xs q,((diagram f xs).point (s.src q)).2=0 ∧ ((diagram f xs).point (s.dst q)).2=0
  distinct : ∀q,s.src q≠s.dst q
  weights : ∀f xs u k v,s.stored f xs u k v → 0<k ∧ k≤B
  positive : 1≤B
  distance : ∀f xs q,let d := D-(if ∃x∈xs,x∈f q then (1:ℤ) else 0)
    Path (oriented s f xs) (s.src q) d (s.dst q) ∧ ∀k,Path (oriented s f xs) (s.src q) k (s.dst q) → d≤k

theorem certificate [Fintype V] {B D : ℤ} (g : Geometry s root B D) (pad : ℕ) :
    Certificate (core (lift s root pad)) B D := by
  let l := lift s root pad
  have bounds (f : Family n) (xs : List (Fin n)) (u : V⊕Fin pad) (k : ℤ) (v : V⊕Fin pad)
      (ed : l.stored f xs u k v) : 0<k ∧ k≤B := by
    cases u with
    | inl u => cases v with
               | inl v => exact g.weights f xs u k v ed
               | inr v => exact ed.2▸⟨by decide,g.positive⟩
    | inr u => cases v <;> contradiction
  have orientedBound {f xs u k v} (ed : oriented l f xs u k v) : 0<k ∧ k≤B :=
    ed.1.elim (bounds _ _ _ _ _) (bounds _ _ _ _ _)
  constructor
  · rintro f xs q u k v (ed|⟨_,rfl,_⟩)
    · exact orientedBound ed
    · exact ⟨by decide,g.positive⟩
  · intro f xs q
    obtain ⟨d,up,old⟩ := pad_left (pad:=pad) (s.stored f xs) (g.diagram f xs) root (g.leftmost f xs) (g.above f xs)
    have base {u v : V⊕Fin pad} (e : plain (oriented l f xs) u v) :
        plain (l.stored f xs) u v ∨ plain (l.stored f xs) v u := by
      obtain ⟨k,uv|vu,_⟩ := e; exact Or.inl ⟨k,uv⟩; exact Or.inr ⟨k,vu⟩
    have diagram := with_return d up (fun _ _ e => base e)
      (fun _ ⟨_,_,r⟩ => lt_irrefl _ r) (.inl (s.src q)) (.inl (s.dst q))
      (by rw [old]; exact (g.top f xs q).1) (by rw [old]; exact (g.top f xs q).2) (fun e => g.distinct _ (Sum.inl.inj e))
    apply diagram.some.mono
    rintro u v ⟨k,h|⟨rfl,rfl,rfl⟩⟩
    · exact Or.inl ⟨k,h⟩
    · exact Or.inr ⟨rfl,rfl⟩
  · intro f xs q
    obtain ⟨reach,low⟩ := g.distance f xs q
    let d := D-(if ∃x∈xs,x∈f q then (1:ℤ) else 0)
    have incl {a b k} (p : Path (oriented s f xs) a k b) : Path (oriented l f xs) (.inl a) k (.inl b) := by
      induction p with | nil => exact .nil _ | snoc _ e ih => exact ih.snoc e
    have gg := rank_girth l.rank (E:=oriented l f xs) (fun _ _ _ e => e.2)
      (fun _ _ _ e => (orientedBound e).1.le) (incl reach) (fun k p => low k (to_core s root p))
    simpa [d,sub_add_eq_add_sub] using gg

end
end DisjointnessDraft.Applications.GirthPadding
