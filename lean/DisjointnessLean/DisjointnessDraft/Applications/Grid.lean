import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-! Shortest paths in the compressed planar grid. Each cell contributes a
vertical, horizontal and diagonal edge. The potential bounds walks in both
directions, including walks that revisit cells. -/
namespace DisjointnessDraft.Applications.Grid
open Classical
set_option maxHeartbeats 6000000
def bit (p : Bool) : ℤ := if p then 1 else 0
private theorem bitBounds (p : Bool) : 0≤bit p ∧ bit p≤1 := by cases p <;> decide
abbrev GridPoint := ℤ × ℤ

def eta (q j : ℤ) (β : ℤ) (r c : ℤ) : ℤ :=
  if r<j then (if c<q then 1 else if q<c then -1 else 0) else if q<c then -β else 0

def potential (p q j β : ℤ) (v : GridPoint) :=
  2*q*j+2*p*(v.2-q)-2*min v.2 q*max (j-v.1) 0+eta q j β v.1 v.2

inductive Step (p : ℤ) (M : ℤ → ℤ → Bool) : GridPoint → ℤ → GridPoint → Prop
  | vert (r c) (r1 : 1≤r) (rp : r≤p) (c1 : 1≤c) (cp : c≤p) : Step p M (r-1,c) (2*c) (r,c)
  | hor (r c) (r1 : 1≤r) (rp : r≤p) (c1 : 1≤c) (cp : c≤p) : Step p M (r,c) (2*p) (r,c+1)
  | diag (r c) (r1 : 1≤r) (rp : r≤p) (c1 : 1≤c) (cp : c≤p) : Step p M (r-1,c) (2*c+2*p-bit (M r c)) (r,c+1)

inductive Walk (p : ℤ) (M : ℤ → ℤ → Bool) : GridPoint → ℤ → GridPoint → Prop
  | nil (u) : Walk p M u 0 u
  | snoc {u z v d t} : Walk p M u d z → (Step p M z t v ∨ Step p M v t z) → Walk p M u (d+t) v

private theorem v_diff {p q j r c β : ℤ} (qr : 1≤q) (cr : 1≤c) (br : 0≤β) (b1 : β≤1) :
    let V := potential p q j β (r,c)-potential p q j β (r-1,c)
    0≤V ∧ V≤2*c := by
  simp only [potential,eta,min_def,max_def,Prod.fst,Prod.snd]
  split_ifs
  all_goals try omega
  all_goals try (have e : r=j := by omega
                 subst r)
  all_goals try (have e : c=q := by omega
                 subst c)
  all_goals constructor <;> ring_nf <;> omega

private theorem h_diff {p q j r c β : ℤ} (jr : j≤p) (rr : 1≤r) (pr : 2≤p) (br : 0≤β) (b1 : β≤1) :
    let H := potential p q j β (r,c+1)-potential p q j β (r,c)
    0≤H ∧ H≤2*p := by
  simp only [potential,eta,min_def,max_def,Prod.fst,Prod.snd]
  split_ifs
  all_goals try omega
  all_goals try (have e : c=q := by omega
                 subst c)
  all_goals try (have e : c+1=q := by omega
                 subst q)
  all_goals constructor <;> ring_nf <;> omega

private theorem diagonal {p q j r c : ℤ} (M : ℤ → ℤ → Bool) (qr : 1≤q) (jr : j≤p) (rr : 1≤r)
    (cr : 1≤c) (pr : 2≤p) :
    let β := bit (M j q)
    let D := potential p q j β (r,c+1)-potential p q j β (r-1,c)
    0≤D ∧ D≤2*c+2*p-bit (M r c) := by
  intro β D
  have b0 := (bitBounds (M j q)).1
  have b1 := (bitBounds (M j q)).2
  have h1 := (bitBounds (M r c)).2
  have v := v_diff (p:=p) (j:=j) (r:=r) qr cr b0 b1
  have h := h_diff (q:=q) (c:=c) jr rr pr b0 b1
  refine ⟨by dsimp [D,β]; linarith only [h.1,v.1],?_⟩
  by_cases rj : r=j <;> by_cases cq : c=q
  all_goals try subst r
  all_goals try subst c
  all_goals simp only [D,β,potential,eta,min_def,max_def,Prod.fst,Prod.snd]
  all_goals split_ifs
  all_goals try omega
  all_goals try (have e : c+1=q := by omega
                 subst q)
  all_goals (ring_nf; omega)

theorem lipschitz {p q j u v t} (M : ℤ → ℤ → Bool) (p2 : 2≤p) (q1 : 1≤q) (jp : j≤p) (e : Step p M u t v) :
    let F := potential p q j (bit (M j q))
    F v-F u≤t ∧ F u-F v≤t := by
  intro F
  have ⟨b0,b1⟩ := bitBounds (M j q)
  cases e with
  | vert r c r1 rp c1 cp => have h := v_diff (p:=p) (j:=j) (r:=r) q1 c1 b0 b1; dsimp [F]; exact ⟨h.2,by linarith only [h.1,c1]⟩
  | hor r c r1 rp c1 cp => have h := h_diff (q:=q) (c:=c) jp r1 p2 b0 b1; dsimp [F]; exact ⟨h.2,by linarith only [h.1,p2]⟩
  | diag r c r1 rp c1 cp => have h := diagonal M q1 jp r1 c1 p2; dsimp [F]; exact ⟨h.2,by linarith only [h.1,c1,p2,(bitBounds (M r c)).2]⟩

theorem walk_bound {p q j u v d} (M : ℤ → ℤ → Bool) (p2 : 2≤p) (q1 : 1≤q) (jp : j≤p) (w : Walk p M u d v) :
    let F := potential p q j (bit (M j q))
    F v - F u ≤ d := by
  induction w with
  | nil => simp
  | snoc _ e ih =>
    rcases e with e|e <;> have h := lipschitz M p2 q1 jp e <;> dsimp only at * <;> linarith only [ih,h.1,h.2]

theorem down (p q : ℤ) (M : ℤ → ℤ → Bool) (q1 : 1≤q) (qp : q≤p) (h : ℕ) (hr : (h:ℤ)≤p) :
    Walk p M (0,q) (2*q*h) ((h:ℤ),q) := by
  induction h with
  | zero => simpa using Walk.nil (p:=p) (M:=M) (0,q)
  | succ h ih =>
    have e := Step.vert (M:=M) ((h:ℤ)+1) q (by omega) hr q1 qp
    simp only [add_sub_cancel_right] at e
    (convert (ih (by omega)).snoc (Or.inl e) using 1; push_cast; ring)

private theorem right {p j c : ℤ} (M : ℤ → ℤ → Bool) (j1 : 1≤j) (jp : j≤p) (c1 : 1≤c)
    (h : ℕ) (u : GridPoint) (d : ℤ) (start : Walk p M u d (j,c)) (fit : c+h≤p+1) :
    Walk p M u (d+2*p*h) (j,c+h) := by
  induction h with
  | zero => simpa using start
  | succ h ih =>
    have e := Step.hor (M:=M) j (c+h) j1 jp (by omega) (by omega)
    convert (ih (by omega)).snoc (Or.inl e) using 1 <;> push_cast <;> ring

theorem grid_distance (p q j : ℤ) (M : ℤ → ℤ → Bool) (p2 : 2≤p) (q1 : 1≤q) (qp : q≤p) (j1 : 1≤j) (jp : j≤p) :
    let d := 2*p*(p-q+1)+2*q*j-bit (M j q)
    Walk p M (0,q) d (j,p+1) ∧ ∀ e,Walk p M (0,q) e (j,p+1) → d≤e := by
  intro d
  have a : ((j-1).toNat:ℤ)=j-1 := Int.toNat_of_nonneg (by omega)
  have b : ((p-q).toNat:ℤ)=p-q := Int.toNat_of_nonneg (by omega)
  have w := down p q M q1 qp (j-1).toNat (by omega)
  rw [a] at w
  have s := w.snoc (Or.inl (Step.diag (M:=M) j q j1 jp q1 qp))
  have last := right M j1 jp (by omega : 1≤q+1) (p-q).toNat _ _ s (by omega)
  rw [b] at last
  refine ⟨?_,?_⟩
  · convert last using 1 <;> dsimp [d] <;> ring_nf
  · intro e path
    have h := walk_bound (q:=q) (j:=j) M p2 q1 jp path
    dsimp [potential,eta] at h
    rw [min_eq_right (by omega : q≤p+1),min_self,max_eq_left (by omega : 0≤j-0)] at h
    simp [show ¬j<j by omega,show q<p+1 by omega,show (0:ℤ)<j by omega] at h
    dsimp [d]; linarith

/-- The two grids plus a single connector cancel every term dependent on the
chosen element, except its incidence bit. Three connectors are always too long. -/
theorem connector (p q j β : ℤ) (p2 : 2≤p) :
    let H := 4*p*(p+1)
    (2*p*(p-q+1)+2*q*j-β)+(H+2*(p+1)*(p-j))+(2*p*q+2*(p-q+1)*j)=2*H-β ∧ 2*H<3*H := by
  dsimp only; exact ⟨by ring,by nlinarith⟩

end DisjointnessDraft.Applications.Grid
