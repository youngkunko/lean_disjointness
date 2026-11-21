import DisjointnessDraft.Applications.WeightedMatching

/-! The diameter selector works for any connected undirected core of small
diameter. Permanent fallback edges of weight 3L keep both selectors connected.
Inserting the two length-L shortcuts makes the extremal pair unique. -/
namespace DisjointnessDraft.Applications.Diameter
open WeightedWalk
noncomputable section
variable {V : Type}

abbrev Node (V : Type) := V ⊕ Bool
def tip (a b : V) : Bool → V | false => a | true => b
inductive Edge (E : V → ℤ → V → Prop) (fallback : Bool → V → Prop) (a b : V) (L : ℤ) : Node V → ℤ → Node V → Prop
  | base {u k v} (e : E u k v) : Edge E fallback a b L (.inl u) k (.inl v)
  | old (side u) (has : fallback side u) : Edge E fallback a b L (.inr side) (3*L) (.inl u)
  | oldRev (side u) (has : fallback side u) : Edge E fallback a b L (.inl u) (3*L) (.inr side)
  | short (side) : Edge E fallback a b L (.inr side) L (.inl (tip a b side))
  | shortRev (side) : Edge E fallback a b L (.inl (tip a b side)) L (.inr side)

theorem lift {E : V→ℤ→V→Prop} {fallback a b L u k v} (p : Path E u k v) :
    Path (Edge E fallback a b L) (.inl u) k (.inl v) := by
  induction p with | nil => exact .nil _ | snoc _ e ih => exact ih.snoc (.base e)
theorem one {W : Type} {E : W→ℤ→W→Prop} {u d v} (e : E u d v) : Path E u d v := by simpa using (Path.nil u).snoc e
theorem path_bound {W : Type} {E : W→ℤ→W→Prop} {u d v} (P : W→ℤ)
    (ok : ∀ i k j,E i k j → P j-P i≤k) (p : Path E u d v) : P v-P u≤d := by
  induction p with
  | nil => simp
  | snoc _ edge ih => have h := ok _ _ _ edge; omega

def HasDiameter {W : Type} (E : W→ℤ→W→Prop) (D : ℤ) :=
  (∃ i j,Path E i D j ∧ ∀ k,Path E i k j → D≤k) ∧ ∀ i j,∃ k,k≤D ∧ Path E i k j

/-- Exact maximum of all pairwise shortest-path distances, including in the
presence of every fallback edge. -/
theorem selector_pair [Fintype V] (E : V→ℤ→V→Prop) (fallback : Bool→V→Prop) (a b : V) (L d : ℤ)
    (pos : ∀ u k v,E u k v → 0≤k) (short : ∀u v,∃k,k<L ∧ Path E u k v)
    (forward : Path E a d b) (backward : Path E b d a) (best : ∀ k,Path E a k b → d≤k) :
    (Path (Edge E fallback a b L) (.inr false) (2*L+d) (.inr true) ∧
    ∀ k,Path (Edge E fallback a b L) (.inr false) k (.inr true) → 2*L+d≤k) ∧
    ∀ u v,∃ k,k≤2*L+d ∧ Path (Edge E fallback a b L) u k v := by
  classical
  have dz := forward.nonneg pos
  obtain ⟨k,kl,ab⟩ := short a b
  have dl := (best k ab).trans_lt kl
  have lp : 0<L := by omega
  obtain ⟨P,pa,pb,law⟩ := WeightedMatching.dual E forward best pos
  have small (x : V) : -L<P x ∧ P x<L := by
    obtain ⟨j,jl,xs⟩ := short x a
    obtain ⟨k,kl,sx⟩ := short a x
    have lo := path_bound P law xs; have hi := path_bound P law sx; omega
  let F : Node V→ℤ := fun v => match v with | .inl x => P x | .inr false => -L | .inr true => d+L
  have bound (u : Node V) (k : ℤ) (v : Node V) (e : Edge E fallback a b L u k v) : F v-F u≤k := by
    cases e with
    | base e => exact law _ _ _ e
    | old s x _ => have := small x; cases s <;> dsimp [F] <;> omega
    | oldRev s x _ => have := small x; cases s <;> dsimp [F] <;> omega
    | short s => cases s <;> dsimp [F,tip] <;> omega
    | shortRev s => cases s <;> dsimp [F,tip] <;> omega
  have across (s t : Bool) (w : Path E (tip a b s) d (tip a b t)) :
      Path (Edge E fallback a b L) (.inr s) (2*L+d) (.inr t) := by
    simpa only [show (L+d)+L=2*L+d by omega] using ((one (Edge.short (E:=E) (fallback:=fallback) (a:=a) (b:=b) (L:=L) s)).append (lift w)).snoc (Edge.shortRev t)
  refine ⟨⟨across false true forward,?_⟩,?_⟩
  · intro k walk; have z := path_bound F bound walk; change (d+L)- -L≤k at z; omega
  · rintro (u|s) (v|t)
    · obtain ⟨k,le,z⟩ := short u v; exact ⟨k,by omega,lift z⟩
    · obtain ⟨k,le,z⟩ := short u (tip a b t); exact ⟨k+L,by omega,(lift z).snoc (.shortRev t)⟩
    · obtain ⟨k,le,z⟩ := short (tip a b s) v; exact ⟨L+k,by omega,(one (Edge.short (E:=E) (fallback:=fallback) (a:=a) (b:=b) (L:=L) s)).append (lift z)⟩
    · by_cases eq : s=t
      · subst t; exact ⟨0,by omega,.nil _⟩
      · cases s <;> cases t <;> try contradiction
        · exact ⟨_,le_rfl,across false true forward⟩
        · exact ⟨_,le_rfl,across true false backward⟩

theorem selector [Fintype V] (E : V→ℤ→V→Prop) (fallback : Bool→V→Prop) (a b : V) (L d : ℤ)
    (pos : ∀ u k v,E u k v → 0≤k) (short : ∀u v,∃k,k<L ∧ Path E u k v)
    (forward : Path E a d b) (backward : Path E b d a) (best : ∀ k,Path E a k b → d≤k) :
    HasDiameter (Edge E fallback a b L) (2*L+d) := by
  obtain ⟨pair,all⟩ := selector_pair E fallback a b L d pos short forward backward best
  exact ⟨⟨_,_,pair⟩,all⟩

end
end DisjointnessDraft.Applications.Diameter
