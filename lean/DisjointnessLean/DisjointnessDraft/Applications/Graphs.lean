import Mathlib.Data.Finset.Card
import Mathlib.Tactic.DeriveFintype

/-! The layered graph gadgets in the graph-problems corollary. The relations
below are literal edge sets; walks and their lengths are unbounded inductive
objects. All inserted edges are independent of the data structure's answers. -/
namespace DisjointnessDraft.Applications.Graphs
open Classical
noncomputable section
variable {Q U : Type}

inductive V (Q U : Type) where
  | row (q : Q) | col (x : U) | target | source
  deriving DecidableEq, Fintype

def Hit (S : Q → U → Prop) (X : U → Prop) (q : Q) := ∃ x, S q x ∧ X x

def base (S : Q → U → Prop) (X : U → Prop) : V Q U → V Q U → Prop
  | .row q,.col x => S q x
  | .col x,.target => X x
  | _,_ => False

def sourceEdge (q : Q) (a b : V Q U) := a=.source ∧ b=.row q
def returnEdge (q : Q) (a b : V Q U) := a=.target ∧ b=.row q

inductive Walk {V : Type} (G : V → V → Prop) : V → ℕ → V → Prop
  | nil (a) : Walk G a 0 a
  | cons {a b c k} : G a b → Walk G b k c → Walk G a (k+1) c

theorem Walk.mono {V : Type} {G H : V → V → Prop} (inc : ∀ a b,G a b → H a b) {a b : V} {d}
    (p : Walk G a d b) : Walk H a d b := by
  induction p with
  | nil => exact .nil _
  | cons e _ ih => exact .cons (inc _ _ e) ih

theorem Walk.closed {V : Type} {G : V → V → Prop} (P : V → Prop)
    (next : ∀ u v,P u → G u v → P v) {u v d} (p : Walk G u d v) : P u → P v := by
  induction p with
  | nil => exact id
  | cons e _ ih => exact fun h => ih (next _ _ h e)

def reach {V : Type} (G : V → V → Prop) (a b : V) := ∃ d,Walk G a d b

def sym {V : Type} (G : V → V → Prop) (a b : V) := G a b ∨ G b a

def accessible (S : Q → U → Prop) (X : U → Prop) (q : Q) : V Q U → Prop
  | .source => True | .row r => r=q | .col x => S q x | .target => Hit S X q

theorem selected_class (S : Q → U → Prop) (X : U → Prop) (q : Q) (v : V Q U) :
    reach (fun a b => base S X a b ∨ sourceEdge q a b) .source v ↔ accessible S X q v := by
  constructor
  · rintro ⟨_,p⟩
    apply p.closed (accessible S X q) _ trivial
    intro u v hu hv
    rcases hv with h|⟨rfl,rfl⟩
    · cases u <;> cases v <;> simp_all [accessible,base,Hit]
      exact ⟨_,hu,h⟩
    · rfl
  · cases v with
    | source => intro; exact ⟨_,.nil _⟩
    | row r => rintro (rfl : r=q); exact ⟨_,.cons (Or.inr ⟨rfl,rfl⟩) (.nil _)⟩
    | col x => intro h; exact ⟨_,.cons (Or.inr ⟨rfl,rfl⟩) (.cons (Or.inl (show base S X (.row q) (.col x) from h)) (.nil _))⟩
    | target => rintro ⟨x,h,m⟩; exact ⟨_,.cons (Or.inr ⟨rfl,rfl⟩) (.cons (Or.inl (show base S X (.row q) (.col x) from h)) (.cons (Or.inl (show base S X (.col x) .target from m)) (.nil _)))⟩

theorem reach_iff (S : Q → U → Prop) (X : U → Prop) (q : Q) :
    reach (base S X) (.row q) .target ↔ Hit S X q := by
  constructor
  · rintro ⟨d,p⟩
    exact (selected_class S X q _).mp ⟨_,.cons (Or.inr ⟨rfl,rfl⟩) (p.mono (fun _ _ e => Or.inl e))⟩
  · rintro ⟨x,h,m⟩; exact ⟨2,.cons (show base S X (.row q) (.col x) from h) (.cons (show base S X (.col x) .target from m) (.nil _))⟩

theorem single_update (S : Q → U → Prop) (X : U → Prop) (x : U) (a b : V Q U) :
    base S (fun y => X y ∨ y=x) a b ↔ base S X a b ∨ (a=.col x ∧ b=.target) := by
  cases a <;> cases b <;> simp [base,eq_comm]

theorem short_iff (S : Q → U → Prop) (X : U → Prop) (q : Q) :
    (∃ d<4,Walk (sym (base S X)) (.row q) d .target) ↔ Hit S X q := by
  constructor
  · rintro ⟨d,hd,p⟩
    cases p with
    | cons e p =>
      rename_i b k
      cases b with
      | col x =>
        have hx : S q x := e.resolve_right (by simp [base])
        cases p with
        | cons e p =>
          rename_i v z
          cases v with
          | target => exact ⟨x,hx,e.resolve_right (by simp [base])⟩
          | col y => simp [sym,base] at e
          | source => simp [sym,base] at e
          | row r =>
            cases p with
            | cons e p =>
              cases p with
              | nil => simp [sym,base] at e
              | cons _ _ => omega
      | row r => simp [sym,base] at e
      | source => simp [sym,base] at e
      | target => simp [sym,base] at e
  · rintro ⟨x,h,m⟩; exact ⟨2,by decide,.cons (Or.inl (show base S X (.row q) (.col x) from h)) (.cons (Or.inl (show base S X (.col x) .target from m)) (.nil _))⟩

/-- In the vertex-activation version an outgoing incidence edge is traversable
exactly when its column vertex is active. -/
def enabled (S : Q → U → Prop) (X : U → Prop) : V Q U → V Q U → Prop
  | .row q,.col x | .col x,.row q => S q x ∧ X x
  | .target,.col x | .col x,.target => X x
  | _,_ => False

theorem subgraph_iff (S : Q → U → Prop) (X : U → Prop) (q : Q) :
    reach (enabled S X) (.row q) .target ↔ Hit S X q := by
  constructor
  · have first (b : V Q U) (edge : enabled S X (.row q) b) : Hit S X q := by
      cases b <;> try contradiction
      exact ⟨_,edge⟩
    rintro ⟨_,p⟩; cases p with
    | cons e _ => exact first _ e
  · rintro ⟨x,h,m⟩; exact ⟨2,.cons (show enabled S X (.row q) (.col x) from ⟨h,m⟩) (.cons (show enabled S X (.col x) .target from m) (.nil _))⟩

/-- The selected back edge lies on a directed cycle if and only if the
source row reached the target prior to that insertion. -/
theorem returning_cycle (S : Q → U → Prop) (X : U → Prop) (q : Q) :
    reach (fun a b => base S X a b ∨ returnEdge q a b) (.row q) .target ↔ Hit S X q := by
  constructor
  · rintro ⟨_,p⟩
    exact p.closed (accessible S X q) (by
      intro a b ha h; rcases h with h|⟨rfl,rfl⟩
      · cases a <;> cases b <;> simp_all [accessible,base,Hit]; exact ⟨_,ha,h⟩
      · rfl) rfl
  · intro h; obtain ⟨d,p⟩ := (reach_iff S X q).2 h
    exact ⟨d,p.mono (fun _ _ e => Or.inl e)⟩

end
end DisjointnessDraft.Applications.Graphs
