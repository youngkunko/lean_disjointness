import DisjointnessDraft.Applications.FiniteDiameter

/-! Exact diameter of the manuscript's two complete fans. Each long fallback
edge ends at its own unit-length terminal leaf. Further pendant leaves can be
attached at arbitrary core vertices without changing the two selected extremes. -/
namespace DisjointnessDraft.Applications.OriginalDiameter
open WeightedWalk FinitePlanarDistance PlanarCore CoreSize
open Classical
noncomputable section
variable {V J : Type}

def leafGraph (E : V→ℤ→V→Prop) (root : J→V) : V ⊕ J → ℤ → V ⊕ J → Prop
  | .inl u,k,.inl v => E u k v
  | .inl u,k,.inr j => u=root j ∧ k=1
  | .inr j,k,.inl v => v=root j ∧ k=1
  | .inr _,_,.inr _ => False

def project (root : J→V) : V ⊕ J → V := Sum.elim id root

theorem project_path {E : V→ℤ→V→Prop} {root : J→V} {u v k}
    (p : Path (leafGraph E root) u k v) : ∃ d,d≤k ∧ Path E (project root u) d (project root v) := by
  induction p with
  | nil => exact ⟨0,le_rfl,.nil _⟩
  | @snoc a b d t old e ih =>
    obtain ⟨k,le,w⟩ := ih
    cases a <;> cases b
    · exact ⟨k+t,by omega,w.snoc e⟩
    · obtain ⟨rfl,rfl⟩ := e; exact ⟨k,by omega,w⟩
    · obtain ⟨rfl,rfl⟩ := e; exact ⟨k,by omega,w⟩
    · contradiction

theorem lift {E : V→ℤ→V→Prop} (root : J→V) {u v k} (p : Path E u k v) :
    Path (leafGraph E root) (.inl u) k (.inl v) := by
  induction p with | nil => exact .nil _ | snoc _ e ih => exact ih.snoc e

theorem routes {E : V→ℤ→V→Prop} (root : J→V) {L : ℤ}
    (cheap : ∀u v,∃k,k<L-2 ∧ Path E u k v) (a b : V⊕J) :
    ∃k,k<L ∧ Path (leafGraph E root) a k b := by
  have hop (j : J) : leafGraph E root (.inl (root j)) 1 (.inr j) := ⟨rfl,rfl⟩
  have back (j : J) : leafGraph E root (.inr j) 1 (.inl (root j)) := ⟨rfl,rfl⟩
  obtain ⟨k,le,w⟩ := cheap (project root a) (project root b)
  cases a with
  | inl u =>
    cases b with
    | inl v => exact ⟨k,by omega,lift root w⟩
    | inr j => exact ⟨k+1,by omega,(lift root w).snoc (hop j)⟩
  | inr i =>
    cases b with
    | inl v => exact ⟨1+k,by omega,(Diameter.one (back i)).append (lift root w)⟩
    | inr j => exact ⟨1+k+1,by omega,((Diameter.one (back i)).append (lift root w)).snoc (hop j)⟩

abbrev Leaf (p pad : ℕ) := (Bool × Fin p) ⊕ Fin pad

def parent {p pad : ℕ} (extra : Fin pad → FinitePlanarDistance.V p) :
    Leaf p pad → FinitePlanarDistance.V p
  | .inl (false,i) => start i
  | .inl (true,i) => finishLine i
  | .inr i => extra i

def fallback {p pad : ℕ} (side : Bool) : FinitePlanarDistance.V p ⊕ Leaf p pad → Prop
  | .inr (.inl (s,_)) => side=s
  | _ => False

/-- The two selector edges recover exactly 2L+D minus the query bit on the
original fan graph, with any number of pendant padding vertices. -/
theorem diameter {p pad : ℕ} (hp : 2≤p) (q : Fin p) (M : ℤ→ℤ→Bool) (A : ℤ→Prop)
    (rows : ∀j,A j→1≤j ∧ j≤(p:ℤ)) (dummy : A p) (blank : M p (pos q)=false) (extra : Fin pad→FinitePlanarDistance.V p) :
    let E := leafGraph (edge (p:=p) M A) (parent extra)
    Diameter.HasDiameter (Diameter.Edge E fallback (.inl (start q)) (.inl (finishLine q)) (FiniteDiameter.L p))
      (2*FiniteDiameter.L p+ (2*H (p:ℤ)-(if ∃j,A j ∧ M j (pos q)=true then 1 else 0))) := by
  intro E
  obtain ⟨w,best⟩ := FinitePlanarDistance.distance p q M A hp rows dummy blank
  refine Diameter.selector E _ _ _ _ _ ?_ ?_ (lift _ w) (lift _ (FiniteDiameter.reversed (fun _ _ _ e => e.symm) w)) ?_
  · rintro (u|i) k (v|j) e
    · rcases e with e|e <;> exact (weight_bounds hp rows e).1.le
    · obtain ⟨_,rfl⟩ := e; decide
    · obtain ⟨_,rfl⟩ := e; decide
    · contradiction
  · apply routes
    intro u v; obtain ⟨k,lt,w⟩ := DiameterRoutes.cheap_paths hp M A dummy u v
    exact ⟨k,by dsimp [FiniteDiameter.L]; omega,FiniteDiameter.expand hp rows u v w⟩
  · intro k path
    obtain ⟨d,small,z⟩ := project_path path
    exact (best d z).trans small

theorem size (p pad : ℕ) : Fintype.card (Diameter.Node (FinitePlanarDistance.V p ⊕ Leaf p pad)) = 8*p^2+6*p+2+pad := by
  change Fintype.card (((Bool×Menu p)⊕((Bool×Fin p)⊕Fin pad))⊕Bool)=_
  simp only [Fintype.card_sum,Fintype.card_prod,Fintype.card_bool,Fintype.card_fin]
  have r := paired_size p
  simp only [Fintype.card_prod,Fintype.card_bool] at r
  omega
end
end DisjointnessDraft.Applications.OriginalDiameter
