import DisjointnessDraft.Applications.PlanarPadding

/-! The last row is a permanent empty dummy. Source memberships populate
the first n rows and columns. Every data insertion adds exactly its literal
positive-weight crossing edge and leaves all other grid edges untouched. -/
namespace DisjointnessDraft.Applications.PlanarEncoding
open CoreSize OriginalGrid PlanarCore FinitePlanarDistance PlanarPadding WeightedWalk Classical
noncomputable section

def dim (n : ℕ) := n+1
abbrev W (n pad : ℕ) := FinitePlanarDistance.V (dim n) ⊕ Fin pad
def root (n : ℕ) : FinitePlanarDistance.V (dim n) := start ⟨0,Nat.succ_pos n⟩
def table (f : Family n) (r c : ℤ) :=
  decide (∃ (x i : Fin n),pos x=r ∧ pos i=c ∧ x∈f i)
def enabled (xs : List (Fin n)) (r : ℤ) := r=(dim n:ℕ) ∨ ∃ x∈xs,pos x=r
def input (f : Family n) (xs : List (Fin n)) : W n pad → ℤ → W n pad → Prop :=
  extend (wire (p:=dim n) (table f) (enabled xs)) (root n)
def point (n : ℕ) (u : W n pad) := extendPoint (fun v => Planarity.draw (dim n) (PlanarMatching.place v)) (root n) u
def ends (x : Fin n) : W n pad × W n pad :=
  (.inl (false,.right x.castSucc),.inl (true,.right x.castSucc))
def query (q : Fin n) : W n pad × W n pad :=
  (.inl (start q.castSucc),.inl (finishLine q.castSucc))
def weight (a b : W n pad) : ℤ :=
  match a,b with
  | .inl u,.inl v => wireWeight (dim n) (PlanarMatching.place u) (PlanarMatching.place v)
  | _,_ => 1
theorem pos_inj {n : ℕ} : Function.Injective (@pos n) := by intro a b h; apply Fin.ext; dsimp [pos] at h; omega
theorem rows (xs : List (Fin n)) (j : ℤ) (h : enabled xs j) : 1≤j ∧ j≤(dim n:ℕ) := by
  rcases h with rfl|⟨x,_,rfl⟩ <;> dsimp [pos,dim] <;> push_cast <;> omega

theorem actual_weight {f : Family n} {xs : List (Fin n)} {u v : W n pad} {d}
    (e : input f xs u d v) : d=weight u v := by
  cases u <;> cases v <;> try contradiction
  · exact weight_eq e
  · exact e.2

theorem bound {f : Family n} {xs : List (Fin n)} {u v : W n pad} {d} (hn : 1≤n)
    (e : input f xs u d v) : 0<d ∧ d≤8*(dim n:ℤ)*(dim n+1) := by
  cases u <;> cases v <;> try contradiction
  · exact weight_bounds (by dsimp [dim]; omega) (rows xs) e
  · have eq : d=1 := e.2
    subst d; constructor
    · norm_num
    · dsimp [dim]; push_cast; nlinarith [sq_nonneg (n:ℤ)]

theorem root_y (n : ℕ) : (Planarity.draw (dim n) (PlanarMatching.place (root n))).2=0 := by simp [root,start,PlanarMatching.place,UnitCore.layer,vertex,Planarity.draw,Planarity.point,Planarity.coord]
theorem planar (f : Family n) (xs : List (Fin n)) : Nonempty (Drawing (plain (input (pad:=pad) f xs))) := by
  let E := wire (p:=dim n) (table f) (enabled xs)
  let D : Drawing (plain E) := {
    point := fun u => Planarity.draw (dim n) (PlanarMatching.place u)
    injective := fun a b eq => PlanarMatching.inj (Planarity.core_vertices (displayed a) (displayed b) eq)
    miss := fun ⟨_,h⟩ z t t0 t1 => Planarity.core_misses_vertices (drawn h) (displayed z) t t0 t1
    apart := fun ⟨_,h⟩ ⟨_,e⟩ t s t0 t1 s0 s1 eq =>
      let same := Planarity.core_segments (drawn h) (drawn e) t s t0 t1 s0 s1 eq
      ⟨PlanarMatching.inj same.1,PlanarMatching.inj same.2⟩ }
  exact drawing E (root n) D upper_half (root_y _)

private theorem cross_eq {n} (x : Fin n) (a b : FinitePlanarDistance.V (dim n)) :
    PlanarMatching.place a=.left (side (dim n) (pos x)) ∧ PlanarMatching.place b=.right (side (dim n) (pos x)) ↔
      a=(false,.right x.castSucc) ∧ b=(true,.right x.castSucc) := by
  have l : PlanarMatching.place (false,Menu.right x.castSucc)=.left (side (dim n) (pos x)) := rfl
  have r : PlanarMatching.place (true,Menu.right x.castSucc)=.right (side (dim n) (pos x)) := rfl
  rw [←l,←r,PlanarMatching.inj.eq_iff,PlanarMatching.inj.eq_iff]
theorem connector (f : Family n) (xs : List (Fin n)) (a b : W n pad) (k : ℤ) :
    input f xs a k b ↔ input f [] a k b ∨ ∃ x∈xs,(a,b)=ends x ∧ k=weight a b := by
  have core {a b : T} : Wire (dim n) (table f) (enabled xs) a k b ↔
      Wire (dim n) (table f) (enabled ([] : List (Fin n))) a k b ∨
      ∃ x∈xs,a=.left (side (dim n) (pos x)) ∧ b=.right (side (dim n) (pos x)) ∧ k=PlanarCore.link (dim n) (pos x) := by
    constructor
    · intro e
      cases e with
      | l h => exact Or.inl (.l h)
      | r h => exact Or.inl (.r h)
      | link j h =>
        rcases h with rfl|⟨x,h,rfl⟩
        · exact Or.inl (.link _ (Or.inl rfl))
        · exact Or.inr ⟨x,h,rfl,rfl,rfl⟩
    · rintro (e|⟨x,h,rfl,rfl,rfl⟩)
      · cases e with
        | l h => exact .l h
        | r h => exact .r h
        | link j h => exact .link j (Or.inl (by simpa [enabled] using h))
      · exact .link _ (Or.inr ⟨x,h,rfl⟩)
  rcases a with a|a <;> rcases b with b|b
  case inl.inr | inr.inl | inr.inr => simp [input,PlanarPadding.extend,ends,Prod.mk.injEq]
  change Wire _ _ _ _ k _ ↔ _
  rw [core]
  apply or_congr_right
  constructor
  · rintro ⟨x,h,l,r,rfl⟩
    obtain ⟨rfl,rfl⟩ := (cross_eq x a b).mp ⟨l,r⟩
    exact ⟨x,h,rfl,rfl⟩
  · rintro ⟨x,h,pair,rfl⟩
    obtain ⟨rfl,rfl⟩ : a=(false,.right x.castSucc) ∧ b=(true,.right x.castSucc) := by simpa [ends] using pair
    exact ⟨x,h,rfl,rfl,rfl⟩

theorem missing (f : Family n) (x : Fin n) : ¬plain (input (pad:=pad) f []) (ends x).1 (ends x).2 := by
  rintro ⟨k,h⟩
  have e : Wire (dim n) (table f) (enabled ([] : List (Fin n))) (.left (side (dim n) (pos x))) k (.right (side (dim n) (pos x))) := h
  cases e with
  | link j on =>
    simp [enabled,dim,pos] at on
    have := x.isLt; omega

theorem ends_injective : Function.Injective (@ends n pad) := by
  intro x y h
  have e := congrArg Prod.fst h
  simp [ends] at e
  exact e

theorem encoded_distance (f : Family n) (xs : List (Fin n)) (q : Fin n) :
    let d : ℤ := 2*H (dim n) - (if ∃x∈xs,x∈f q then 1 else 0)
    let terminals := query (pad:=pad) q
    Path (sym (input f xs)) terminals.1 d terminals.2 ∧
      ∀ k,Path (sym (input f xs)) terminals.1 k terminals.2 → d≤k := by
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
  have core := FinitePlanarDistance.distance (dim n) q.castSucc (table f) (enabled xs) size (rows xs) (Or.inl rfl) blank
  simp only [hit] at core
  exact ⟨upper_path (root n) core.1,fun k w => by obtain ⟨d,le,h⟩ := lower_path w; exact (core.2 d h).trans le⟩

end
end DisjointnessDraft.Applications.PlanarEncoding
