import DisjointnessDraft.Applications.CoreSize
import DisjointnessDraft.Applications.UnitCore
import DisjointnessDraft.Applications.Diameter

namespace DisjointnessDraft.Applications.DiameterRoutes
open CoreSize OriginalGrid PlanarCore
noncomputable section

theorem range {p : ℕ} (x : Fin p) : 1≤pos x ∧ pos x≤(p:ℤ) := by have := x.isLt; dsimp [pos]; omega

theorem from_top (p : ℕ) (hp : 2≤p) (M : ℤ→ℤ→Bool) (c : Fin p) (r : ℤ) (r1 : 1≤r) (rp : r≤p) :
    ∃ k,k≤4*((p:ℤ)+1)^2 ∧ OriginalGrid.Walk p M (top (pos c)) k (side p r) := by
  have hh : (2:ℤ)≤p := by exact_mod_cast hp
  have h := range c
  let d := 2*(p:ℤ)*(p-pos c+1)+2*pos c*r-Grid.bit (M r (pos c))
  refine ⟨d,?_,(grid_distance p (pos c) r M hh h.1 h.2 r1 rp).1⟩
  have P := mul_le_mul_of_nonneg_left (show (p:ℤ)-pos c+1≤p by omega) (show 0≤2*(p:ℤ) by positivity)
  have Q := mul_le_mul h.2 rp (by omega : 0≤r) (by positivity : 0≤(p:ℤ))
  have z : 0≤Grid.bit (M r (pos c)) := by unfold Grid.bit; split <;> decide
  dsimp [d]; nlinarith only [P,Q,z,hh]

theorem cell_to_corner {p : ℕ} (M : ℤ→ℤ→Bool) (i j : Fin p) (part : Part) :
    ∃ k,k≤2 ∧ OriginalGrid.Walk p M (vertex (.site i j part)) k (vertex (.site i j .corner)) := by
  have I := range i; have J := range j
  have make {src dst : Local} {t : ℤ} (e : OriginalGrid.Edge p (pos j) (M (pos i) (pos j)) src t dst) :
      OriginalGrid.Step p M (embed (pos i) (pos j) src) t (embed (pos i) (pos j) dst) :=
    .cell _ _ I.1 I.2 J.1 J.2 e
  cases part with
  | corner => exact ⟨0,by decide,.nil _⟩
  | v => exact ⟨1,by decide,one (Or.inr (make .bv))⟩
  | w => exact ⟨2,by decide,one (Or.inr (make .bw))⟩
  | x => exact ⟨2,by decide,(one (Or.inr (make .vx))).append (one (Or.inr (make .bv)))⟩

theorem to_corner_right (p : ℕ) (hp : 2≤p) (M : ℤ→ℤ→Bool) (v : Menu p) :
    ∃ k,k≤8*((p:ℤ)+1)^2+2 ∧ OriginalGrid.Walk p M (vertex v) k (side p p) := by
  have hh : (2:ℤ)≤p := by exact_mod_cast hp
  cases v with
  | top c =>
    obtain ⟨k,h,w⟩ := from_top p hp M c p (by omega) le_rfl
    exact ⟨k,by nlinarith [sq_nonneg ((p:ℤ)+1)],w⟩
  | right i =>
    let c := i
    obtain ⟨k,h,w⟩ := from_top p hp M c (pos i) (range i).1 (range i).2
    obtain ⟨t,l,z⟩ := from_top p hp M c p (by omega) le_rfl
    exact ⟨_,by linarith only [h,l],w.reverse.append z⟩
  | site i j part =>
    obtain ⟨k,h,w⟩ := cell_to_corner M i j part
    obtain ⟨t,l,z⟩ := from_top p hp M j p (by omega) le_rfl
    have row : ((i.val+1:ℕ):ℤ)=pos i := by simp [pos]
    have path := expand_walk (Grid.down p (pos j) M (range j).1 (range j).2 (i.val+1) (by rw [row]; exact (range i).2))
    rw [row] at path
    have b := mul_le_mul (range j).2 (range i).2 (by have := (range i).1; omega : 0≤pos i) (by positivity : 0≤(p:ℤ))
    exact ⟨_,by nlinarith only [h,l,b,hh],(w.append path.reverse).append z⟩

theorem concat {p M A a b c k l} (u : PlanarCore.Walk p M A a k b) (v : PlanarCore.Walk p M A b l c) :
    PlanarCore.Walk p M A a (k+l) c := by
  induction v with
  | nil => simpa using u
  | left _ z ih => simpa only [add_assoc] using ih.left z
  | right _ z ih => simpa only [add_assoc] using ih.right z
  | cross _ on ih => simpa only [add_assoc] using ih.cross on
  | back _ on ih => simpa only [add_assoc] using ih.back on

theorem reverse_walk {p M A a b k} (w : PlanarCore.Walk p M A a k b) : PlanarCore.Walk p M A b k a := by
  induction w with
  | nil => exact .nil _
  | left _ z ih => simpa only [zero_add,add_zero,add_comm] using concat ((PlanarCore.Walk.nil _).left z.reverse) ih
  | right _ z ih => simpa only [zero_add,add_zero,add_comm] using concat ((PlanarCore.Walk.nil _).right z.reverse) ih
  | cross _ on ih => simpa only [zero_add,add_zero,add_comm] using concat ((PlanarCore.Walk.nil _).back on) ih
  | back _ on ih => simpa only [zero_add,add_zero,add_comm] using concat ((PlanarCore.Walk.nil _).cross on) ih

abbrev place {p : ℕ} (v : Bool × Menu p) := UnitCore.layer v.1 (vertex v.2)

theorem to_hub {p : ℕ} (hp : 2≤p) (M : ℤ→ℤ→Bool) (A : ℤ→Prop) (dummy : A p) (v : Bool × Menu p) :
    ∃ k,k≤12*((p:ℤ)+1)^2+2 ∧ PlanarCore.Walk p M A (place v) k (.left (side p p)) := by
  obtain ⟨s,v⟩ := v
  cases s with
  | false =>
    obtain ⟨k,b,w⟩ := to_corner_right p hp M v
    exact ⟨k,by nlinarith only [b,sq_nonneg ((p:ℤ)+1)],by simpa using (PlanarCore.Walk.nil _).left w⟩
  | true =>
    obtain ⟨k,b,w⟩ := to_corner_right p hp Zmat v
    have z : PlanarCore.Walk p M A (place (true,v)) k (.right (side p p)) := by simpa using (PlanarCore.Walk.nil _).right w
    exact ⟨_,by dsimp [link,H]; nlinarith only [b,Nat.cast_nonneg (α:=ℤ) p],z.back dummy⟩

theorem cheap_paths {p : ℕ} (hp : 2≤p) (M : ℤ→ℤ→Bool) (A : ℤ→Prop) (dummy : A p) (u v : Bool × Menu p) :
    ∃ k,k<64*(p:ℤ)^3-4 ∧ PlanarCore.Walk p M A (place u) k (place v) := by
  obtain ⟨k,b,w⟩ := to_hub hp M A dummy u
  obtain ⟨l,c,z⟩ := to_hub hp M A dummy v
  have h : (2:ℤ)≤p := by exact_mod_cast hp
  have x := mul_nonneg (show (0:ℤ)≤p-2 by omega) (sq_nonneg (p:ℤ))
  have y := mul_nonneg (show (0:ℤ)≤p-2 by omega) (show (0:ℤ)≤p by omega)
  exact ⟨_,by nlinarith only [h,x,y,b,c],concat w (reverse_walk z)⟩

end
end DisjointnessDraft.Applications.DiameterRoutes
