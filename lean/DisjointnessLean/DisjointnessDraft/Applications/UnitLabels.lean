import DisjointnessDraft.Applications.UnitSizes

/-! Literal names for all strands that can have strictly interior vertices.
The remaining three local edge types have weight one. -/
namespace DisjointnessDraft.Applications.UnitLabels
open UnitEncoding FinitePlanarDistance OriginalGrid CoreSize Classical
noncomputable section
inductive Kind where | vertical | middle | horizontal deriving DecidableEq, Fintype
abbrev Label (p : ℕ) := (Bool × Fin p × Fin p × Kind) ⊕ Fin p

private theorem bounds {p : ℕ} (i : Fin p) : 1≤pos i ∧ pos i≤p := by have := i.isLt; dsimp [pos]; omega
def coordinate (r c : Fin p) (u : Local) : Menu p :=
  (CoreSize.local_vertices (bounds r).1 (bounds r).2 (bounds c).1 (bounds c).2 u).choose
theorem at_coordinate (r c : Fin p) (u : Local) : vertex (coordinate r c u)=embed (pos r) (pos c) u := by
  unfold coordinate; exact (CoreSize.local_vertices (bounds r).1 (bounds r).2 (bounds c).1 (bounds c).2 u).choose_spec

def endpoint : Kind → Local × Local
  | .vertical => (.a,.inside .v)
  | .middle => (.b,.inside .w)
  | .horizontal => (.c,.inside .w)
def ends : Label p → V p × V p
  | .inl (s,r,c,k) => ((s,coordinate r c (endpoint k).1),(s,coordinate r c (endpoint k).2))
  | .inr j => ((false,.right j),(true,.right j))
def meters : Label p → ℕ
  | .inl (_,_,c,.vertical) => 2*c.val+1
  | .inl (_,_,_,.middle) => 2
  | .inl (_,_,_,.horizontal) => 2*p-2
  | .inr j => 4*p*(p+1)+2*(p+1)*(p-(j.val+1))
def watts (p : ℕ) (c : Fin p) : Kind → ℤ
  | .vertical => 2*pos c-1 | .middle => 2 | .horizontal => 2*(p:ℤ)-2

private theorem poss {p : ℕ} {v : ℤ} (lo : 1≤v) (hi : v≤p) : ∃ i : Fin p,pos i=v := by
  have eq : ((v-1).toNat:ℤ)=v-1 := Int.toNat_of_nonneg (by omega)
  exact ⟨⟨(v-1).toNat,by omega⟩,by dsimp [pos]; omega⟩
private theorem local_step (r c : Fin p) (k : Kind) (M : ℤ → ℤ → Bool) : Step (p:ℤ) M
    (embed (pos r) (pos c) (endpoint k).1) (watts p c k) (embed (pos r) (pos c) (endpoint k).2) := by
  apply Step.cell (pos r) (pos c) (bounds r).1 (bounds r).2 (bounds c).1 (bounds c).2
  cases k <;> constructor

theorem occupied (hp : 2≤p) (l : Label p) : potential p (ends l).1 (meters l:ℤ) (ends l).2 := by
  rcases l with ⟨s,r,c,k⟩|j
  · have m : (meters (Sum.inl (s,r,c,k)):ℤ)=watts p c k := by
      cases k <;> simp [meters,watts,pos,Nat.cast_sub (show 2≤2*p by omega)]
      all_goals ring
    unfold potential wire
    rw [m]
    cases s <;> dsimp [PlanarMatching.place,ends,UnitCore.layer] <;> rw [at_coordinate,at_coordinate]
    · exact .l (local_step r c k _)
    · exact .r (local_step r c k _)
  · have m : (meters (Sum.inr j):ℤ)=PlanarCore.link p (pos j) := by
      have le : j.val+1≤p := j.isLt
      simp [meters,PlanarCore.link,PlanarCore.H,pos,Nat.cast_sub le]
    rw [m]; exact Wire.link (pos j) (bounds j)

def strand (hp : 2≤p) (l : Label p) : Id p := ⟨ends l,⟨_,occupied hp l⟩⟩
theorem strand_length (hp : 2≤p) (l : Label p) : length (strand hp l)=meters l := by
  have a := weight_eq (has_weight (strand hp l) hp).1
  have b := weight_eq (occupied hp l)
  exact_mod_cast (a.trans b.symm)

def locations (l : Label p) := (PlanarMatching.place (ends l).1,PlanarMatching.place (ends l).2)
private theorem layer_inj (a b : Bool) (u v : Vertex) :
    UnitCore.layer a u=UnitCore.layer b v ↔ a=b ∧ u=v := by cases a <;> cases b <;> simp [UnitCore.layer]

theorem ends_injective (p : ℕ) : Function.Injective (@ends p) := by
  intro a b pair
  have e : locations a=locations b := congrArg (fun z : V p × V p => (PlanarMatching.place z.1,PlanarMatching.place z.2)) pair
  rcases a with ⟨s,r,c,k⟩|j <;> rcases b with ⟨s',r',c',k'⟩|j'
  · cases k <;> cases k' <;> simp only [locations,ends,PlanarMatching.place,at_coordinate,endpoint,embed,Prod.mk.injEq,
        layer_inj,Vertex.corner.injEq,Vertex.inside.injEq,PlanarEncoding.pos_inj.eq_iff,reduceCtorEq,and_false,false_and] at e ⊢ <;>
      simp_all [and_assoc,Sum.inl.injEq,Prod.mk.injEq] <;> obtain ⟨_,_,step,_,_,rfl⟩ := e <;> omega
  · simp only [locations,ends,PlanarMatching.place,at_coordinate,Prod.mk.injEq,layer_inj] at e
    obtain ⟨⟨rfl,_⟩,bad,_⟩ := e; contradiction
  · simp only [locations,ends,PlanarMatching.place,at_coordinate,Prod.mk.injEq,layer_inj] at e
    obtain ⟨⟨rfl,_⟩,bad,_⟩ := e; contradiction
  · simpa [ends] using congrArg Prod.fst pair

theorem strand_injective (hp : 2≤p) : Function.Injective (strand hp) :=
  fun _ _ h => ends_injective p (congrArg Subtype.val h)

theorem classify {p : ℕ} (_hp : 2≤p) {a b : PlanarCore.T} {w : ℤ}
    (ed : Wire p (fun _ _ => true) (allRows p) a w b) (long : 1<w) :
    ∃ l : Label p,locations l=(a,b) := by
  have one (s : Bool) {M u v k} (e : Step (p:ℤ) M u k v) (long : 1<k) :
      ∃ l : Label p,locations l=(UnitCore.layer s u,UnitCore.layer s v) := by
    cases e with
    | cell r c r1 rp c1 cp ed =>
      obtain ⟨i,ri⟩ := poss r1 rp; obtain ⟨j,cj⟩ := poss c1 cp
      cases ed with
      | av => exact ⟨.inl (s,i,j,.vertical),by simp [locations,ends,PlanarMatching.place,at_coordinate,endpoint,ri,cj]⟩
      | bw => exact ⟨.inl (s,i,j,.middle),by simp [locations,ends,PlanarMatching.place,at_coordinate,endpoint,ri,cj]⟩
      | cw => exact ⟨.inl (s,i,j,.horizontal),by simp [locations,ends,PlanarMatching.place,at_coordinate,endpoint,ri,cj]⟩
      | bv | vx | xw => omega
  cases ed with
  | l e => exact one false e long
  | r e => exact one true e long
  | link j h => obtain ⟨i,eq⟩ := poss h.1 h.2
                exact ⟨.inr i,by simp [locations,ends,PlanarMatching.place,vertex,UnitCore.layer,PlanarCore.side,eq]⟩

end
end DisjointnessDraft.Applications.UnitLabels
