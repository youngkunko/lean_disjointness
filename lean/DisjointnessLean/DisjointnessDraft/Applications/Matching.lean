import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Logic.Equiv.Fintype
import Mathlib.Tactic.DeriveFintype

/-! The bipartite matching gadget. Each side is a copy of the same finite
vertex set. A perfect matching is a bijection using only literal graph edges. -/
namespace DisjointnessDraft.Applications.Matching
open Classical
noncomputable section
inductive V (Q U : Type) where
  | endpt | row (q : Q) | col (x : U)
  deriving DecidableEq, Fintype
variable {Q U : Type} [DecidableEq Q] [DecidableEq U]
def edge (S : Q → U → Prop) (X : U → Prop) (enable : Q → Prop) : V Q U → V Q U → Prop
  | .endpt,.row i => enable i
  | .row i,.row j => i=j
  | .row i,.col x => S i x
  | .col x,.col y => x=y
  | .col x,.endpt => X x
  | _,_ => False

def Perfect (E : V Q U → V Q U → Prop) := ∃ f : V Q U ≃ V Q U, ∀ a,E a (f a)

theorem update {Q U : Type} [DecidableEq Q] [DecidableEq U] (S : Q → U → Prop) (X : U → Prop) (enable : Q → Prop) (x : U) (a b) :
    edge S (fun y => X y ∨ y=x) enable a b ↔ edge S X enable a b ∨ (a=.col x ∧ b=.endpt) := by
  cases a <;> cases b <;> simp [edge]

theorem select {Q U : Type} [DecidableEq Q] [DecidableEq U] (S : Q → U → Prop) (X : U → Prop) (q : Q) (a b) :
    edge S X (·=q) a b ↔ edge S X (fun _ => False) a b ∨ (a=.endpt ∧ b=.row q) := by
  cases a <;> cases b <;> simp [edge]

theorem baseline {Q U : Type} [DecidableEq Q] [DecidableEq U] (S : Q → U → Prop) (X : U → Prop) (enable : Q → Prop)
    (v : V Q U) (h : v ≠ .endpt) : edge S X enable v v := by cases v <;> simp_all [edge]

theorem perfect_iff (S : Q → U → Prop) (X : U → Prop) (q : Q) :
    Perfect (edge S X (·=q)) ↔ ∃ x,S q x ∧ X x := by
  constructor
  · rintro ⟨f,h⟩
    have e := h .endpt
    have src : f .endpt=.row q := by
      cases E : f .endpt <;> simp [E,edge] at e ⊢
      exact e
    have a := h (.row q)
    cases A : f (.row q) with
    | endpt => simp [A,edge] at a
    | row r =>
      have rQ : q=r := by simpa [A,edge] using a
      subst r
      exact False.elim (by have := f.injective (A.trans src.symm); contradiction)
    | col x =>
      have inc : S q x := by simpa [A,edge] using a
      have b := h (.col x)
      cases B : f (.col x) with
      | endpt => exact ⟨x,inc,by simpa [B,edge] using b⟩
      | row r => simp [B,edge] at b
      | col y =>
        have xy : x=y := by simpa [B,edge] using b
        subst y
        exact False.elim (by have := f.injective (A.trans B.symm); contradiction)
  · rintro ⟨x,h,m⟩
    let f := (Equiv.swap (.endpt : V Q U) (.row q)).trans (Equiv.swap .endpt (.col x))
    refine ⟨f,?_⟩
    intro a
    cases a with
    | endpt => simp [f,edge,Equiv.swap_apply_def]
    | row r =>
      by_cases e : r=q <;> simp [f,edge,Equiv.swap_apply_def,e,h]
    | col y =>
      by_cases e : y=x <;> simp [f,edge,Equiv.swap_apply_def,e,m]

end
end DisjointnessDraft.Applications.Matching
