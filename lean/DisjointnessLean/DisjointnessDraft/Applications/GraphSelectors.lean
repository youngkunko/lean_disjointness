import DisjointnessDraft.Applications.GraphCosts

namespace DisjointnessDraft.Applications.GraphCosts
open Graphs Reachability Components GraphHistories GraphVariants
noncomputable section
open Classical
variable {n p : ℕ}

def extraEdge (k : Kind) (q : Fin n) (a b : Core n) : Prop := match k with
  | .source => sourceEdge (Sum.inl q : Fin n ⊕ Fin n) a b
  | .back => returnEdge (Sum.inl q : Fin n ⊕ Fin n) a b
  | .triangle => a=.row (.inl q) ∧ b=.target

def underlying (F : Family n) (xs : List (Fin n)) (q : Fin n) (k : Kind) (a b : Core n) :=
  base (extRows F) (·∈xs) a b ∨ extraEdge k q a b

abbrev G (F : Family n) (xs : List (Fin n)) (q : Fin n) (k : Kind) (a b : Vertex n p) :=
  Raw (edges F xs++[select k q]) a b

theorem down (F : Family n) (xs : List (Fin n)) (q : Fin n) (k : Kind) {a b : Vertex n p}
    (h : G F xs q k a b) : underlying F xs q k (strip a) (strip b) := by
  rcases List.mem_append.mp h with h|h
  · exact Or.inl (projects F xs h)
  · have e := List.mem_singleton.mp h
    cases k <;> obtain ⟨rfl,rfl⟩ := Prod.mk.inj e <;> exact Or.inr ⟨rfl,rfl⟩

theorem up (F : Family n) (xs : List (Fin n)) (q : Fin n) (k : Kind) {a b : Core n}
    (h : underlying F xs q k a b) : G F xs q k (.inl a : Vertex n p) (.inl b) := by
  rcases h with h|h
  · exact List.mem_append_left _ ((edge_exact F xs (.inl a) (.inl b)).mpr h)
  · apply List.mem_append_right
    cases k <;> obtain ⟨rfl,rfl⟩ := h <;> simp [select,row,target]

def explicit_hit (F : Family n) (xs : List (Fin n)) (q : Fin n) : Prop := Hit (extRows F) (·∈xs) (.inl q)

theorem decode_hit (F : Family n) (xs : List (Fin n)) (q : Fin n) (P : Prop) [Decidable P] (h : P ↔ explicit_hit F xs q) :
    (!decide P) = answer F xs q := by
  by_cases x : P
  · obtain ⟨j,m,t⟩ := h.mp x
    have no : ¬∀ z∈xs,z∉F q := fun all => all j t m
    simp [x,answer,no]
  · have no : ∀ z∈xs,z∉F q := fun z t m => x (h.mpr ⟨z,m,t⟩)
    simp [x,answer,no]
    exact no

theorem select_reaches (F : Family n) (xs : List (Fin n)) (q : Fin n) :
    reach (G (p:=p) F xs q .source) (.inl .source) (target n p) ↔ explicit_hit F xs q := by
  have equiv := selected_class (extRows F) (·∈xs) (.inl q) .target
  constructor
  · rintro ⟨k,path⟩
    exact equiv.mp ⟨k,walk_map strip (fun _ _ => down F xs q .source) path⟩
  · intro yes; obtain ⟨k,path⟩ := equiv.mpr yes
    exact ⟨k,walk_map Sum.inl (fun _ _ => up F xs q .source) path⟩

theorem selected_cycle (F : Family n) (xs : List (Fin n)) (q : Fin n) :
    cycle (G (p:=p) F xs q .back) ↔ explicit_hit F xs q := by
  have equiv := cycle_iff (extRows F) (·∈xs) (.inl q)
  constructor
  · rintro ⟨v,k,path⟩; exact equiv.mp ⟨_,k,walk_map strip (fun _ _ => down F xs q .back) path⟩
  · intro hit; obtain ⟨v,k,path⟩ := equiv.mpr hit
    exact ⟨_,k,walk_map Sum.inl (fun _ _ => up F xs q .back) path⟩

theorem selected_mutual (F : Family n) (xs : List (Fin n)) (q : Fin n) :
    (component (G (p:=p) F xs q .back)).r (row q) (target n p) ↔ explicit_hit F xs q := by
  have cv := pair_iff (extRows F) (·∈xs) (.inl q)
  constructor
  · rintro ⟨⟨j,pr⟩,⟨k,rp⟩⟩
    exact cv.mp ⟨⟨j,walk_map strip (fun _ _ => down F xs q .back) pr⟩,⟨k,walk_map strip (fun _ _ => down F xs q .back) rp⟩⟩
  · intro yes; obtain ⟨⟨j,pr⟩,⟨k,rp⟩⟩ := cv.mpr yes
    exact ⟨⟨j,walk_map Sum.inl (fun _ _ => up F xs q .back) pr⟩,⟨k,walk_map Sum.inl (fun _ _ => up F xs q .back) rp⟩⟩

theorem selected_distinct (F : Family n) (xs : List (Fin n)) (q : Fin n) :
    (∃ a b, a≠b ∧ (component (G (p:=p) F xs q .back)).r a b) ↔ explicit_hit F xs q := by
  constructor
  · rintro ⟨a,b,ne,⟨k,path⟩,⟨l,rev⟩⟩
    apply (selected_cycle (p:=p) F xs q).mp
    have nz : 0<k := by by_contra! z; have := Nat.eq_zero_of_le_zero z; subst k; cases path; exact ne rfl
    have sum := walk_join path rev
    exact ⟨a,k+l-1,by simpa [show k+l-1+1=k+l by omega] using sum⟩
  · intro y
    exact ⟨row q,target n p,by simp [row,target],(selected_mutual F xs q).mpr y⟩

def triangle (E : W→W→Prop) := ∃ a b c,sym E a b ∧ sym E b c ∧ sym E c a

theorem selected_triangle (F : Family n) (xs : List (Fin n)) (q : Fin n) :
    triangle (G (p:=p) F xs q .triangle) ↔ explicit_hit F xs q := by
  have equiv := triangle_iff (extRows F) (·∈xs) (.inl q)
  have project {a b : Vertex n p} (h : sym (G F xs q .triangle) a b) :
      triEdge (extRows F) (·∈xs) (.inl q) (strip a) (strip b) := by
    rcases h with h|h
    · rcases down F xs q .triangle h with e|s
      · exact Or.inl (Or.inl e)
      · exact Or.inr (Or.inl s)
    · rcases down F xs q .triangle h with e|s
      · exact Or.inl (Or.inr e)
      · exact Or.inr (Or.inr ⟨s.2,s.1⟩)
  have lift {a b : Core n} (h : triEdge (extRows F) (·∈xs) (.inl q) a b) :
      sym (G (p:=p) F xs q .triangle) (.inl a) (.inl b) := by
    rcases h with (h|h)|h|h
    · exact Or.inl (up F xs q .triangle (Or.inl h))
    · exact Or.inr (up F xs q .triangle (Or.inl h))
    · exact Or.inl (up F xs q .triangle (Or.inr h))
    · exact Or.inr (up F xs q .triangle (Or.inr ⟨h.2,h.1⟩))
  constructor
  · rintro ⟨a,b,c,m,e,z⟩; exact equiv.mp ⟨_,_,_,project m,project e,project z⟩
  · intro yes; obtain ⟨a,b,c,m,e,z⟩ := equiv.mpr yes; exact ⟨_,_,_,lift m,lift e,lift z⟩

def bitDecode : List Bool → Bool | [b] => !b | _ => false

def fixedReach (n p : ℕ) : Entry n p Unit Bool :=
  ⟨.source,fun _ => (),bitDecode,fun es _ => decide (reach (Raw es) (.inl .source) (target n p)),
    fun f xs q => decode_hit f xs q _ (select_reaches f xs q)⟩

def cycleDetection (n p : ℕ) : Entry n p Unit Bool :=
  ⟨.back,fun _ => (),bitDecode,fun es _ => decide (cycle (Raw es)),fun f xs q => decode_hit f xs q _ (selected_cycle f xs q)⟩

def pairScc (n p : ℕ) : Entry n p (Vertex n p × Vertex n p) Bool :=
  ⟨.back,fun q => (row q,target n p),bitDecode,fun es q => decide ((component (Raw es)).r q.1 q.2),
    fun f xs q => decode_hit f xs q _ (selected_mutual f xs q)⟩

def sccCount (n p : ℕ) : Entry n p Unit ℕ :=
  ⟨.back,fun _ => (),fun z => !decide (z.head!<Fintype.card (Vertex n p)),fun es _ => Nat.card (Quotient (component (Raw es))),
    fun f xs q => by
      simp only [List.head!_cons]; exact decode_hit f xs q _ ((component_count _).trans (selected_distinct (p:=p) f xs q))⟩

def maxComp {W : Type} [Fintype W] (E : W→W→Prop) : ℕ := Finset.univ.sup (fun a => (Finset.univ.filter ((component E).r a)).card)

theorem maxComp_test {W : Type} [Fintype W] (E : W→W→Prop) :
    2≤maxComp E ↔ ∃ a,2≤(Finset.univ.filter ((component E).r a)).card := by simp [maxComp,←Nat.lt_iff_add_one_le,Finset.lt_sup_iff]

def largestScc (n p : ℕ) : Entry n p Unit ℕ :=
  ⟨.back,fun _ => (),fun z => !decide (2≤z.head!),fun es _ => maxComp (Raw es),
    fun f xs q => by
      simp only [List.head!_cons]; exact decode_hit f xs q _ ((maxComp_test _).trans ((largest_test _).trans (selected_distinct (p:=p) f xs q)))⟩

def triangles (n p : ℕ) : Entry n p Unit Bool :=
  ⟨.triangle,fun _ => (),bitDecode,fun es _ => decide (triangle (Raw es)),fun f xs q => decode_hit f xs q _ (selected_triangle f xs q)⟩

end
end DisjointnessDraft.Applications.GraphCosts
