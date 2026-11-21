import DisjointnessDraft.Applications.PlanarCore
import DisjointnessDraft.Applications.Subdivision

/-! Exact unit-weight specialization of the two-grid core. Each disabled
connector keeps its entire unit path except the first edge, so an insertion
enables exactly that edge. -/
namespace DisjointnessDraft.Applications.UnitCore
open OriginalGrid PlanarCore Subdivision Classical
noncomputable section
def matrix (M : ℤ → ℤ → Bool) : Bool → ℤ → ℤ → Bool | false => M | true => Zmat
def layer : Bool → Vertex → T | false => .left | true => .right
inductive Strand (p : ℤ) (M : ℤ → ℤ → Bool) where
  | cell (s : Bool) {u v t} (e : Step p (matrix M s) u t v)
  | bridge (j : ℤ) (j1 : 1≤j) (jp : j≤p)
def src {p M} : Strand p M → T | .cell s (u:=u) _ => layer s u | .bridge j _ _ => .left (side p j)
def dst {p M} : Strand p M → T | .cell s (v:=v) _ => layer s v | .bridge j _ _ => .right (side p j)
def weight {p M} : Strand p M → ℤ | .cell _ (t:=t) _ => t | .bridge j _ _ => link p j
def live {p M} (A : ℤ → Prop) : Strand p M → Prop | .cell _ _ => True | .bridge j _ _ => A j
private theorem step_positive {p M u t v} (p2 : 2≤p) (e : Step p M u t v) : 0<t := by
  cases e with | cell _ _ r1 rp c1 cp e => cases e <;> omega
theorem positive {p M} (p2 : 2≤p) (e : Strand p M) : 0<weight e := by
  cases e with
  | cell s e => exact step_positive p2 e
  | bridge j j1 jp =>
    have h : 0≤2*(p+1)*(p-j) := mul_nonneg (by omega) (by omega)
    have b : 0<4*p*(p+1) := by positivity
    dsimp [weight,link,H]; omega
def graph (p : ℤ) (M : ℤ → ℤ → Bool) (A : ℤ → Prop) (p2 : 2≤p) : Subdivision.Graph T (Strand p M) where
  src := src
  dst := dst
  len e := (weight e).toNat
  positive e := by have := positive p2 e; omega
  enabled := live A

private theorem extend_grid {p M A s u v d a k} (p2 : 2≤p)
    (walk : OriginalGrid.Walk p (matrix M s) u d v)
    (prior : Subdivision.Walk (graph p M A p2) a k (layer s u)) :
    ∃ e : ℕ, (e:ℤ)=d ∧ Subdivision.Walk (graph p M A p2) a (k+e) (layer s v) := by
  induction walk with
  | nil => exact ⟨0,rfl,by simpa using prior⟩
  | @snoc y z d t _ edge ih =>
    obtain ⟨e,eq,pr⟩ := ih
    rcases edge with f|f
    · have h := pr.forward (Strand.cell (M:=M) s f) (show live A (Strand.cell (M:=M) s f) from trivial)
      refine ⟨e+t.toNat,?_,?_⟩
      · rw [Nat.cast_add,eq,Int.toNat_of_nonneg (step_positive p2 f).le]
      · simpa only [graph,weight,Nat.add_assoc] using h
    · have h := pr.backward (Strand.cell (M:=M) s f) (show live A (Strand.cell (M:=M) s f) from trivial)
      refine ⟨e+t.toNat,?_,?_⟩
      · rw [Nat.cast_add,eq,Int.toNat_of_nonneg (step_positive p2 f).le]
      · simpa only [graph,weight,Nat.add_assoc] using h

theorem physical {p M A s v d} (p2 : 2≤p) (range : ∀ j,A j → 1≤j ∧ j≤p)
    (w : PlanarCore.Walk p M A s d v) :
    ∃ e : ℕ,(e:ℤ)=d ∧ Subdivision.Walk (graph p M A p2) s e v := by
  induction w with
  | nil => exact ⟨0,rfl,.nil _⟩
  | left _ w ih =>
    obtain ⟨k,rfl,prior⟩ := ih
    obtain ⟨e,rfl,h⟩ := extend_grid (s:=false) p2 w prior
    exact ⟨k+e,Nat.cast_add _ _,h⟩
  | right _ w ih =>
    obtain ⟨k,rfl,prior⟩ := ih
    obtain ⟨e,rfl,h⟩ := extend_grid (s:=true) p2 w prior
    exact ⟨k+e,Nat.cast_add _ _,h⟩
  | @cross j d _ on ih =>
    obtain ⟨k,rfl,prior⟩ := ih
    let e : Strand p M := .bridge j (range j on).1 (range j on).2
    have h : 0<link p j := positive p2 e
    exact ⟨k+(link p j).toNat,by rw [Nat.cast_add,Int.toNat_of_nonneg h.le],prior.forward e on⟩
  | @back j d _ on ih =>
    obtain ⟨k,rfl,prior⟩ := ih
    let e : Strand p M := .bridge j (range j on).1 (range j on).2
    have h : 0<link p j := positive p2 e
    exact ⟨k+(link p j).toNat,by rw [Nat.cast_add,Int.toNat_of_nonneg h.le],prior.backward e on⟩

theorem weighted {p M A s v d} (p2 : 2≤p) (w : Subdivision.Walk (graph p M A p2) s d v) :
    PlanarCore.Walk p M A s (d:ℤ) v := by
  induction w with
  | nil => exact .nil _
  | forward e _ on ih =>
    rw [Nat.cast_add,show (((graph p M A p2).len e:ℕ):ℤ)=weight e from Int.toNat_of_nonneg (positive p2 e).le]
    cases e with
    | cell s e => cases s
                  · exact ih.left (OriginalGrid.one (Or.inl e))
                  · exact ih.right (OriginalGrid.one (Or.inl e))
    | bridge j j1 jp => exact ih.cross on
  | backward e _ on ih =>
    rw [Nat.cast_add,show (((graph p M A p2).len e:ℕ):ℤ)=weight e from Int.toNat_of_nonneg (positive p2 e).le]
    cases e with
    | cell s e => cases s
                  · exact ih.left (OriginalGrid.one (Or.inr e))
                  · exact ih.right (OriginalGrid.one (Or.inr e))
    | bridge j j1 jp => exact ih.back on

theorem distance (p q : ℤ) (M : ℤ → ℤ → Bool) (A : ℤ → Prop) (p2 : 2≤p)
    (q1 : 1≤q) (qp : q≤p) (range : ∀ j,A j → 1≤j ∧ j≤p) (dummy : A p) (empty : M p q=false) :
    let D := 2*H p-(if ∃ j,A j ∧ M j q=true then (1:ℤ) else 0)
    let g := graph p M A p2
    ∃ d : ℕ,(d:ℤ)=D ∧ UnitWalk g (.core (.left (top q))) d (.core (.right (top (p-q+1)))) ∧
      ∀ t,UnitWalk g (.core (.left (top q))) t (.core (.right (top (p-q+1)))) → d≤t := by
  intro D g
  obtain ⟨w,least⟩ := PlanarCore.distance p q M A p2 q1 qp range dummy empty
  obtain ⟨e,eq,r⟩ := physical p2 range w
  refine ⟨e,eq,Subdivision.distance g r (fun t path => ?_)⟩
  have small := least _ (weighted p2 path)
  rw [←eq] at small
  exact_mod_cast small

end
end DisjointnessDraft.Applications.UnitCore
