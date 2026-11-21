import DisjointnessDraft.Applications.UnitCore
import DisjointnessDraft.Applications.WeightedWalk

/-! The directed core and its one-edge girth selector. The row-plus-column
rank orients every physical grid edge and every connector; on the empty
right grid its dangling leaf edges point outwards. -/
namespace DisjointnessDraft.Applications.DirectedCore
open Grid OriginalGrid PlanarCore WeightedWalk Classical
noncomputable section
def level (right : Bool) : OriginalGrid.Vertex → ℤ
  | .corner (r,c) => 4*(r+c)
  | .inside r c .v => 4*(r+c)-2
  | .inside r c .w => 4*(r+c)+2
  | .inside r c .x => if right then 4*(r+c)-3 else 4*(r+c)

def rank (p : ℤ) : T → ℤ | .left v => level false v | .right v => 32*p+100-level true v
inductive Physical (p : ℤ) (M : ℤ → ℤ → Bool) (A : ℤ → Prop) : T → ℤ → T → Prop
  | l {u t v} (edge : OriginalGrid.Step p M u t v ∨ OriginalGrid.Step p M v t u) : Physical p M A (.left u) t (.left v)
  | r {u t v} (edge : OriginalGrid.Step p Zmat u t v ∨ OriginalGrid.Step p Zmat v t u) : Physical p M A (.right u) t (.right v)
  | cross (j) (on : A j) : Physical p M A (.left (side p j)) (link p j) (.right (side p j))
def arc (p : ℤ) (M : ℤ → ℤ → Bool) (A : ℤ → Prop) (u : T) (w : ℤ) (v : T) :=
  Physical p M A u w v ∧ rank p u<rank p v

private theorem single {p M A u v w} (edge : Physical p M A u w v) (up : rank p u<rank p v) : Path (arc p M A) u w v := by
  simpa using (Path.nil u).snoc (show arc p M A u w v from ⟨edge,up⟩)

macro "node_order" : tactic => `(tactic| (dsimp [rank,level,embed]; omega))

private theorem left_step {p M A u w v} (step : Grid.Step p M u w v) :
    Path (arc p M A) (.left (.corner u)) w (.left (.corner v)) := by
  cases step with
  | vert r c r1 rp c1 cp =>
    let e := @OriginalGrid.Step.cell p M r c r1 rp c1 cp
    have a := single (A:=A) (.l (Or.inl (e .av))) (by node_order)
    have b := a.append (single (.l (Or.inr (e .bv))) (by node_order))
    (convert b using 1; dsimp [embed]; ring)
  | hor r c r1 rp c1 cp =>
    let e := @OriginalGrid.Step.cell p M r c r1 rp c1 cp
    have a := single (A:=A) (.l (Or.inl (e .bw))) (by node_order)
    have b := a.append (single (.l (Or.inr (e .cw))) (by node_order))
    (convert b using 1; dsimp [embed]; ring)
  | diag r c r1 rp c1 cp =>
    let e := @OriginalGrid.Step.cell p M r c r1 rp c1 cp
    have a := single (A:=A) (.l (Or.inl (e .av))) (by node_order)
    cases m : M r c with
    | false =>
      have b := ((a.append (single (.l (Or.inr (e .bv))) (by node_order))).append
        (single (.l (Or.inl (e .bw))) (by node_order))).append (single (.l (Or.inr (e .cw))) (by node_order))
      (convert b using 1; dsimp [embed,bit]; ring)
    | true =>
      have b := ((a.append (single (.l (Or.inl (e .vx))) (by node_order))).append
        (single (.l (Or.inl (e (.xw m)))) (by node_order))).append (single (.l (Or.inr (e .cw))) (by node_order))
      (convert b using 1; dsimp [embed,bit]; ring)

private theorem right_step {p M A u w v} (step : Grid.Step p Zmat u w v) :
    Path (arc p M A) (.right (.corner v)) w (.right (.corner u)) := by
  cases step with
  | vert r c r1 rp c1 cp =>
    let e := @OriginalGrid.Step.cell p Zmat r c r1 rp c1 cp
    have a := single (A:=A) (M:=M) (.r (Or.inl (e .bv))) (by node_order)
    have b := a.append (single (.r (Or.inr (e .av))) (by node_order))
    (convert b using 1; dsimp [embed]; ring)
  | hor r c r1 rp c1 cp =>
    let e := @OriginalGrid.Step.cell p Zmat r c r1 rp c1 cp
    have a := single (A:=A) (M:=M) (.r (Or.inl (e .cw))) (by node_order)
    have b := a.append (single (.r (Or.inr (e .bw))) (by node_order))
    (convert b using 1; dsimp [embed]; ring)
  | diag r c r1 rp c1 cp =>
    let e := @OriginalGrid.Step.cell p Zmat r c r1 rp c1 cp
    have a := single (A:=A) (M:=M) (.r (Or.inl (e .cw))) (by node_order)
    have b := ((a.append (single (.r (Or.inr (e .bw))) (by node_order))).append
      (single (.r (Or.inl (e .bv))) (by node_order))).append (single (.r (Or.inr (e .av))) (by node_order))
    (convert b using 1; dsimp [embed,bit,Zmat]; ring)

private theorem down (p q : ℤ) (M : ℤ → ℤ → Bool) (q1 : 1≤q) (qp : q≤p) (h : ℕ) (hr : (h:ℤ)≤p) :
    Path (Grid.Step p M) (0,q) (2*q*h) ((h:ℤ),q) := by
  induction h with
  | zero => simpa using Path.nil (E:=Grid.Step p M) (0,q)
  | succ h ih =>
    have e := Grid.Step.vert (M:=M) ((h:ℤ)+1) q (by omega) hr q1 qp
    simp only [add_sub_cancel_right] at e
    (convert (ih (by omega)).snoc e using 1; push_cast; ring)

private theorem rightward {p j c : ℤ} (M : ℤ → ℤ → Bool) (j1 : 1≤j) (jp : j≤p) (c1 : 1≤c)
    (h : ℕ) (u : GridPoint) (d : ℤ) (start : Path (Grid.Step p M) u d (j,c)) (fit : c+h≤p+1) :
    Path (Grid.Step p M) u (d+2*p*h) (j,c+h) := by
  induction h with
  | zero => simpa using start
  | succ h ih =>
    have e := Grid.Step.hor (M:=M) j (c+h) j1 jp (by omega) (by omega)
    convert (ih (by omega)).snoc e using 1 <;> push_cast <;> ring

private theorem canonical (p q j : ℤ) (M : ℤ → ℤ → Bool) (q1 : 1≤q) (qp : q≤p) (j1 : 1≤j) (jp : j≤p) :
    Path (Grid.Step p M) (0,q) (2*p*(p-q+1)+2*q*j-bit (M j q)) (j,p+1) := by
  have a : ((j-1).toNat:ℤ)=j-1 := Int.toNat_of_nonneg (by omega)
  have b : ((p-q).toNat:ℤ)=p-q := Int.toNat_of_nonneg (by omega)
  have w := down p q M q1 qp (j-1).toNat (by omega)
  rw [a] at w
  have s := w.snoc (Grid.Step.diag (M:=M) j q j1 jp q1 qp)
  have last := rightward M j1 jp (by omega : 1≤q+1) (p-q).toNat _ _ s (by omega)
  rw [b] at last
  convert last using 1 <;> ring_nf

private theorem left_walk {p M A u d v} (w : Path (Grid.Step p M) u d v) :
    Path (arc p M A) (.left (.corner u)) d (.left (.corner v)) := by
  induction w with | nil => exact .nil _ | snoc _ e ih => exact ih.append (left_step e)
private theorem right_walk {p M A u d v} (w : Path (Grid.Step p Zmat) u d v) :
    Path (arc p M A) (.right (.corner v)) d (.right (.corner u)) := by
  induction w with | nil => exact .nil _ | snoc _ e ih => simpa only [add_comm] using (right_step e).append ih

theorem forget {p M A u d v} (w : Path (arc p M A) u d v) : PlanarCore.Walk p M A u d v := by
  induction w with
  | nil => exact .nil _
  | snoc _ e ih =>
    cases e.1 with
    | l ed => exact ih.left (OriginalGrid.one ed)
    | r ed => exact ih.right (OriginalGrid.one ed)
    | cross j on => exact ih.cross on

theorem directed_distance (p q : ℤ) (M : ℤ → ℤ → Bool) (A : ℤ → Prop) (p2 : 2≤p)
    (q1 : 1≤q) (qp : q≤p) (range : ∀ j,A j → 1≤j ∧ j≤p) (dummy : A p) (empty : M p q=false) :
    let d := 2*H p-(if ∃ j,A j ∧ M j q=true then (1:ℤ) else 0)
    Path (arc p M A) (.left (top q)) d (.right (top (p-q+1))) ∧
    ∀ k,Path (arc p M A) (.left (top q)) k (.right (top (p-q+1))) → d≤k := by
  intro d
  have picked : ∃ j,A j ∧ Grid.bit (M j q)=(if ∃ i,A i ∧ M i q=true then (1:ℤ) else 0) := by
    by_cases h : ∃ i,A i ∧ M i q=true
    · obtain ⟨j,a,b⟩ := h
      exact ⟨j,a,by simp [Grid.bit,b,show ∃ i,A i ∧ M i q=true from ⟨j,a,b⟩]⟩
    · exact ⟨p,dummy,by simp [h,Grid.bit,empty]⟩
  obtain ⟨j,aj,eq⟩ := picked
  obtain ⟨j1,jp⟩ := range j aj
  have l := left_walk (A:=A) (canonical p q j M q1 qp j1 jp)
  have r := right_walk (A:=A) (M:=M) (canonical p (p-q+1) j Zmat (by omega) (by omega) j1 jp)
  have c := single (p:=p) (M:=M) (.cross j aj) (by dsimp [rank,side,level]; omega)
  refine ⟨?_,fun k w => (PlanarCore.distance p q M A p2 q1 qp range dummy empty).2 k (forget w)⟩
  have got := (l.append c).append r
  have id : (2*p*(p-q+1)+2*q*j-bit (M j q))+link p j+(2*p*(p-(p-q+1)+1)+2*(p-q+1)*j-bit (Zmat j (p-q+1)))=d := by
    dsimp [d]; rw [←eq]; dsimp [link,H,bit,Zmat]; ring
  rw [id] at got; exact got

theorem girth (p q : ℤ) (M : ℤ → ℤ → Bool) (A : ℤ → Prop) (p2 : 2≤p)
    (q1 : 1≤q) (qp : q≤p) (range : ∀ j,A j → 1≤j ∧ j≤p) (dummy : A p) (empty : M p q=false) :
    let d := 2*H p-(if ∃ j,A j ∧ M j q=true then (1:ℤ) else 0)
    let src := T.left (top q)
    let back := addBack (arc p M A) src (.right (top (p-q+1)))
    Path back src (d+1) src ∧ 0<d+1 ∧ ∀ a k,0<k → Path back a k a → d+1≤k := by
  obtain ⟨w,min⟩ := directed_distance p q M A p2 q1 qp range dummy empty
  apply WeightedWalk.girth (rank p) (fun _ _ _ e => e.2) _ w min
  intro u k v e
  have st {B a t b} (h : OriginalGrid.Step p B a t b) : 0≤t := by
    cases h with | cell _ _ r1 rp c1 cp e => cases e <;> omega
  cases e.1 with
  | l ed => exact ed.elim st st
  | r ed => exact ed.elim st st
  | cross j on =>
    have h := (range j on).2
    have z := mul_nonneg (show 0≤2*(p+1) by omega) (show 0≤p-j by omega)
    have zz : 0≤4*p*(p+1) := by positivity
    dsimp [link,H]; omega

end
end DisjointnessDraft.Applications.DirectedCore
