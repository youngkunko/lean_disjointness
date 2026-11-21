import DisjointnessDraft.Applications.OriginalGrid
import Mathlib.Tactic.Positivity

/-! The undirected two-grid core. A walk is a concatenation of walks in a
literal grid and present connector edges in either direction. This permits
repeated connectors and arbitrarily many changes of direction. -/
namespace DisjointnessDraft.Applications.PlanarCore
open OriginalGrid Classical
abbrev Zmat := fun (_ _ : ℤ) => false
def H (p : ℤ) := 4*p*(p+1)
def link (p j : ℤ) := H p+2*(p+1)*(p-j)
def top (q : ℤ) : Vertex := .corner (0,q)
def side (p j : ℤ) : Vertex := .corner (j,p+1)
inductive T where | left (u : Vertex) | right (u : Vertex)
inductive Walk (p : ℤ) (M : ℤ → ℤ → Bool) (A : ℤ → Prop) : T → ℤ → T → Prop
  | nil (u) : Walk p M A u 0 u
  | left {s u v d t} : Walk p M A s d (.left u) → OriginalGrid.Walk p M u t v → Walk p M A s (d+t) (.left v)
  | right {s u v d t} : Walk p M A s d (.right u) → OriginalGrid.Walk p Zmat u t v → Walk p M A s (d+t) (.right v)
  | cross {s j d} : Walk p M A s d (.left (side p j)) → A j → Walk p M A s (d+link p j) (.right (side p j))
  | back {s j d} : Walk p M A s d (.right (side p j)) → A j → Walk p M A s (d+link p j) (.left (side p j))

private theorem length_nonneg {p M a d b} (p2 : 2≤p) (w : OriginalGrid.Walk p M a d b) : 0≤d := by
  have step {u v t} (e : OriginalGrid.Step p M u t v) : 0≤t := by
    cases e with
    | cell r c r1 rp c1 cp e => cases e <;> omega
  induction w with
  | nil => rfl
  | snoc _ e ih => rcases e with e|e <;> exact add_nonneg ih (step e)

private def Summary (p q : ℤ) (M : ℤ → ℤ → Bool) (A : ℤ → Prop) (d : ℤ) : T → Prop
  | .left u => OriginalGrid.Walk p M (top q) d u ∨ 2*H p≤d
  | .right u => (∃ j,A j ∧ ∃ e f, OriginalGrid.Walk p M (top q) e (side p j) ∧
      OriginalGrid.Walk p Zmat (side p j) f u ∧ d=e+link p j+f) ∨ 3*H p≤d

private theorem classify {p q M A u d} (p2 : 2≤p) (bounds : ∀ j,A j → j≤p)
    (w : Walk p M A (.left (top q)) d u) : Summary p q M A d u := by
  have link_big j (a : A j) : H p≤link p j := by
    have := bounds j a
    have h := mul_nonneg (show 0≤2*(p+1) by omega) (show 0≤p-j by omega)
    dsimp [link]; omega
  induction w with
  | nil => exact Or.inl (.nil _)
  | left _ path ih =>
    rcases ih with w|big
    · exact Or.inl (w.append path)
    · exact Or.inr (by have := length_nonneg p2 path; omega)
  | right _ path ih =>
    rcases ih with ⟨j,a,e,f,wl,wr,rfl⟩|big
    · exact Or.inl ⟨j,a,e,_,wl,wr.append path,by ring⟩
    · exact Or.inr (by have := length_nonneg p2 path; omega)
  | cross _ a ih =>
    rcases ih with w|big
    · exact Or.inl ⟨_,a,_,0,w,.nil _,by ring⟩
    · exact Or.inr (by have := link_big _ a; omega)
  | back _ a ih =>
    have zeroH : 0≤H p := by dsimp [H]; positivity
    rcases ih with ⟨j,b,e,f,wl,wr,rfl⟩|big
    · exact Or.inr (by have := length_nonneg p2 wl; have := length_nonneg p2 wr
                       have := link_big _ a; have := link_big _ b; omega)
    · exact Or.inr (by have := link_big _ a; omega)

theorem distance (p q : ℤ) (M : ℤ → ℤ → Bool) (A : ℤ → Prop) (p2 : 2≤p)
    (q1 : 1≤q) (qp : q≤p) (range : ∀ j,A j → 1≤j ∧ j≤p) (dummy : A p) (empty : M p q=false) :
    let hit := if ∃ j,A j ∧ M j q=true then (1:ℤ) else 0
    let d := 2*H p-hit
    Walk p M A (.left (top q)) d (.right (top (p-q+1))) ∧
      ∀ t, Walk p M A (.left (top q)) t (.right (top (p-q+1))) → d≤t := by
  classical
  intro hit d
  have q'1 : 1≤p-q+1 := by omega
  have q'p : p-q+1≤p := by omega
  have bit_le j (a : A j) : Grid.bit (M j q)≤hit := by
    dsimp [hit,Grid.bit]
    split_ifs <;> aesop
  have picked : ∃ j,A j ∧ Grid.bit (M j q)=hit := by
    by_cases h : ∃ j,A j ∧ M j q=true
    · obtain ⟨j,a,b⟩ := h; exact ⟨j,a,by simp [Grid.bit,b,hit,show ∃ j,A j ∧ M j q=true from ⟨j,a,b⟩]⟩
    · exact ⟨p,dummy,by simp [Grid.bit,hit,h,empty]⟩
  have formula j : (2*p*(p-q+1)+2*q*j-Grid.bit (M j q))+link p j+
      (2*p*(p-(p-q+1)+1)+2*(p-q+1)*j-Grid.bit (Zmat j (p-q+1)))=2*H p-Grid.bit (M j q) := by
    dsimp [link,H,Zmat,Grid.bit]; ring
  refine ⟨?_,?_⟩
  · obtain ⟨j,a,eq⟩ := picked
    have l := (OriginalGrid.grid_distance p q j M p2 q1 qp (range j a).1 (range j a).2).1
    have r := (OriginalGrid.grid_distance p (p-q+1) j Zmat p2 q'1 q'p (range j a).1 (range j a).2).1
    have pth := (((Walk.nil (.left (top q))).left l).cross a).right r.reverse
    simp only [zero_add] at pth
    rw [formula j,eq] at pth
    exact pth
  · intro t w
    rcases classify p2 (fun j a => (range j a).2) w with ⟨j,a,e,f,wl,wr,rfl⟩|huge
    · have L := (OriginalGrid.grid_distance p q j M p2 q1 qp (range j a).1 (range j a).2).2 e wl
      have R := (OriginalGrid.grid_distance p (p-q+1) j Zmat p2 q'1 q'p (range j a).1 (range j a).2).2 f wr.reverse
      dsimp only [d]
      linarith only [L,R,formula j,bit_le j a]
    · have zeroH : 0≤H p := by dsimp [H]; positivity
      have zeroHit : 0≤hit := by dsimp [hit]; split <;> decide
      dsimp [d]; omega
end DisjointnessDraft.Applications.PlanarCore
