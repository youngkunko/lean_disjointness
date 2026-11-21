import DisjointnessDraft.Applications.GirthTarget

/-! Orient an incremental undirected edge menu by a strict potential.
A positive-weight pendant extension and its query remain literal edges. -/
namespace DisjointnessDraft.Applications.GirthOrient
open GirthTarget PlanarPadding WeightedWalk Classical
noncomputable section
variable {V : Type}

structure Storage (n : ℕ) (V : Type) where
  stored : Family n → List (Fin n) → V → ℤ → V → Prop
  potential : V → V → Prop
  strength : V → V → ℤ
  rank : V → ℚ
  put : Fin n → V×V
  src : Fin n → V
  dst : Fin n → V
  inside : ∀ f xs u k v,stored f xs u k v → potential u v
  asymmetric : ∀u v,potential u v → ¬potential v u
  canonical : ∀ f xs u k v,stored f xs u k v → k=strength u v
  activity : ∀ f xs u k v,stored f xs u k v ↔ stored f [] u k v ∨
    ∃x∈xs,(u,v)=put x ∧ k=strength u v
  fresh : ∀ f x,¬plain (stored f []) (put x).1 (put x).2
  injective : Function.Injective put
  inserted : ∀ x,potential (put x).1 (put x).2
  forward : ∀x,rank (put x).1<rank (put x).2
  order : ∀q, rank (src q)≤rank (dst q)

variable (s : Storage n V)
def oriented (f : Family n) (xs : List (Fin n)) (u : V) (w : ℤ) (v : V) :=
  sym (s.stored f xs) u w v ∧ s.rank u<s.rank v
def weight (u v : V) := if s.potential u v then s.strength u v else s.strength v u

def core : Core n V where
  network := oriented s
  weight := weight s
  put := s.put
  src := s.src
  dst := s.dst
  canonical := by
    rintro f xs u k v ⟨h|h,_⟩
    · simpa [weight,s.inside _ _ _ _ _ h] using s.canonical _ _ _ _ _ h
    · simpa [weight,s.asymmetric _ _ (s.inside _ _ _ _ _ h)] using s.canonical _ _ _ _ _ h
  activity := by
    intro f xs u k v
    constructor
    · rintro ⟨h|h,dir⟩
      · rcases (s.activity ..).mp h with old|⟨x,mem,p,eq⟩
        · exact Or.inl ⟨Or.inl old,dir⟩
        · exact Or.inr ⟨x,mem,p,by simpa [weight,s.inside _ _ _ _ _ h] using eq⟩
      · rcases (s.activity ..).mp h with old|⟨x,mem,p,eq⟩
        · exact Or.inl ⟨Or.inr old,dir⟩
        · have rev := s.forward x; rw [←p] at rev; exact (not_lt_of_ge dir.le rev).elim
    · rintro (⟨old|old,dir⟩|⟨x,mem,p,eq⟩)
      · exact ⟨Or.inl ((s.activity ..).mpr (Or.inl old)),dir⟩
      · exact ⟨Or.inr ((s.activity ..).mpr (Or.inl old)),dir⟩
      · have i := s.inserted x; have d := s.forward x; rw [←p] at i d
        exact ⟨Or.inl ((s.activity ..).mpr (Or.inr ⟨x,mem,p,by simpa [weight,i] using eq⟩)),d⟩
  fresh := by
    rintro f x ⟨k,h,dir⟩
    exact h.elim (fun e => s.fresh f x ⟨k,e⟩) (fun e => s.asymmetric _ _ (s.inserted x) (s.inside _ _ _ _ _ e))
  injective := s.injective
  selector := by rintro f xs q ⟨_,_,dir⟩; exact not_lt_of_ge (s.order q) dir

theorem rank_girth [Fintype V] {E : V→ℤ→V→Prop} (r : V→ℚ) (increase : ∀u k v,E u k v → r u<r v)
    (nn : ∀u k v,E u k v → 0≤k) {src dst d} (reach : Path E src d dst)
    (min : ∀k,Path E src k dst → d≤k) :
    Cycle (addBack E src dst) (d+1) ∧ ∀k,Cycle (addBack E src dst) k → d+1≤k := by
  -- A rational ranking can be replaced by its rank in the finite vertex menu.
  classical
  have mono [Fintype V] : ∃ R : V→ℤ,∀a b,r a<r b → R a<R b := by
    let below (v : V) := Finset.univ.filter (fun a => r a<r v)
    refine ⟨fun v => (below v).card,?_⟩
    intro a b ab
    apply Int.ofNat_lt.mpr; apply Finset.card_lt_card
    apply Finset.ssubset_iff_subset_ne.mpr
    refine ⟨fun x hx => by simp only [below,Finset.mem_filter,Finset.mem_univ,true_and] at hx ⊢; exact hx.trans ab,?_⟩
    intro eq
    have m : a ∈ below b := by simp [below,ab]
    rw [←eq] at m; simp [below] at m
  obtain ⟨R,hm⟩ := mono
  obtain ⟨got,pos,low⟩ := WeightedWalk.girth R (fun u k v e => hm _ _ (increase u k v e)) nn reach min
  exact ⟨⟨pos,_,got⟩,fun k ⟨pos,_,p⟩ => low _ k pos p⟩

theorem no_flip {E : V→V→Prop} (d : Drawing E) (u v : V) (uv : E u v) : ¬E v u := by
  intro vu
  have flip : Planarity.interpolate (d.point u) (d.point v) (1/2)=Planarity.interpolate (d.point v) (d.point u) (1/2) := by
    apply Prod.ext <;> dsimp [Planarity.interpolate] <;> ring
  have eq := (d.apart uv vu _ _ (by norm_num) (by norm_num) (by norm_num) (by norm_num) flip).1
  subst v
  apply d.miss uv u (1/2) (by norm_num) (by norm_num)
  apply Prod.ext <;> dsimp [Planarity.interpolate] <;> ring

end
end DisjointnessDraft.Applications.GirthOrient
