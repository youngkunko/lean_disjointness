import DisjointnessDraft.Applications.FinitePlanarDistance
import DisjointnessDraft.Applications.DiameterRoutes

namespace DisjointnessDraft.Applications.FiniteDiameter
open WeightedWalk CoreSize OriginalGrid PlanarCore UnitCore Subdivision DiameterRoutes
open FinitePlanarDistance Classical
noncomputable section

theorem reversed {V : Type} {E : V→ℤ→V→Prop} (symm : ∀ i t j,E i t j → E j t i) {u d v} (w : Path E u d v) : Path E v d u := by
  induction w with
  | nil => exact .nil _
  | snoc _ e ih => simpa only [add_comm] using (Diameter.one (symm _ _ _ e)).append ih

theorem strand_finite {p : ℕ} {M : ℤ→ℤ→Bool} (s : Strand p M) :
    ∃ u v : V p,PlanarMatching.place u=src s ∧ PlanarMatching.place v=dst s := by
  cases s with
  | cell side e =>
    cases e with
    | cell r c r1 rp c1 cp edge =>
      obtain ⟨i,ei⟩ := local_vertices r1 rp c1 cp _
      obtain ⟨j,ej⟩ := local_vertices r1 rp c1 cp _
      exact ⟨(side,i),(side,j),congrArg (layer side) ei,congrArg (layer side) ej⟩
  | bridge j j1 jp =>
    let i : Fin p := ⟨(j-1).toNat,by omega⟩
    have e : pos i=j := by dsimp [pos,i]; rw [Int.toNat_of_nonneg (by omega)]; omega
    exact ⟨(false,.right i),(true,.right i),by simp [src,PlanarMatching.place,layer,side,vertex,e],
      by simp [dst,PlanarMatching.place,layer,side,vertex,e]⟩

theorem expand {p : ℕ} {M A} (hp : 2≤p) (rows : ∀j,A j→1≤j ∧ j≤(p:ℤ)) (u v : V p)
    {d} (walk : PlanarCore.Walk p M A (PlanarMatching.place u) d (PlanarMatching.place v)) :
    Path (edge M A) u d v := by
  have hp' : (2:ℤ)≤p := by exact_mod_cast hp
  obtain ⟨k,rfl,w⟩ := UnitCore.physical hp' rows walk
  let G := UnitCore.graph (p:ℤ) M A hp'
  have arc {u v : V p} (s : Strand p M) (en : G.enabled s) (a : PlanarMatching.place u=src s) (b : PlanarMatching.place v=dst s) :
      wire M A u (G.len s:ℤ) v := by
    have size : (G.len s:ℤ)=weight s := Int.toNat_of_nonneg (UnitCore.positive hp' s).le
    rw [size]; unfold wire; rw [a,b]
    cases s with
    | cell layer ed => cases layer <;> first | exact Wire.l ed | exact Wire.r ed
    | bridge j _ _ => exact Wire.link j en
  have go {t k'} (w : Subdivision.Walk G (PlanarMatching.place u) k' t) :
      ∀ v' : V p,PlanarMatching.place v'=t → Path (edge M A) u (k':ℤ) v' := by
    induction w with
    | nil => intro v' eq; obtain rfl := PlanarMatching.inj eq; exact .nil _
    | forward s _ en ih =>
      intro v' eq; obtain ⟨a,b,x,y⟩ := strand_finite s
      obtain rfl := PlanarMatching.inj (eq.trans y.symm)
      simpa only [Nat.cast_add] using (ih a x).snoc (Or.inl (arc s en x y))
    | backward s _ en ih =>
      intro v' eq; obtain ⟨a,b,x,y⟩ := strand_finite s
      obtain rfl := PlanarMatching.inj (eq.trans x.symm)
      simpa only [Nat.cast_add] using (ih b y).snoc (Or.inr (arc s en x y))
  exact go w v rfl

def L (p : ℕ) : ℤ := 64*(p:ℤ)^3

/-- The exact planar diameter once the two length-L edges have been inserted.
The permanent fallback edges may attach to one or more core vertices. -/
theorem diameter {p : ℕ} (hp : 2≤p) (q : Fin p) (M : ℤ→ℤ→Bool) (A : ℤ→Prop)
    (rows : ∀j,A j→1≤j ∧ j≤(p:ℤ)) (dummy : A p) (blank : M p (pos q)=false) (fallback : Bool→V p→Prop) :
    let d := 2*H (p:ℤ)-(if ∃ j,A j ∧ M j (pos q)=true then 1 else 0)
    Diameter.HasDiameter (Diameter.Edge (edge M A) fallback (start q) (finishLine q) (L p)) (2*L p+d) := by
  intro d
  obtain ⟨path,least⟩ := FinitePlanarDistance.distance p q M A hp rows dummy blank
  apply Diameter.selector _ _ _ _ _ _ _ _ path (reversed (fun _ _ _ e => e.symm) path) least
  · intro u k v e; rcases e with h|h <;> exact (weight_bounds hp rows h).1.le
  · intro u v; obtain ⟨k,short,z⟩ := cheap_paths hp M A dummy u v
    exact ⟨k,by dsimp [L]; omega,expand hp rows u v z⟩

end
end DisjointnessDraft.Applications.FiniteDiameter
