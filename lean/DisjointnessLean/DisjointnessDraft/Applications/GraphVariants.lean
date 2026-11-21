import DisjointnessDraft.Applications.Graphs

/-! Marking-only distances, incremental triangle detection, and the selected
undirected source/target distance. All walks use the literal target edges. -/
namespace DisjointnessDraft.Applications.GraphVariants
open Graphs Classical
variable {Q U : Type}
inductive MarkV (Q U : Type) where
  | row (q : Q) | col (x : U) | hubA | hubB | sentinel
  deriving DecidableEq,Fintype
def markEdge (S : Q → U → Prop) : MarkV Q U → MarkV Q U → Prop
  | .row q,.col x | .col x,.row q => S q x
  | .row _,.hubA | .hubA,.row _ | .hubA,.hubB | .hubB,.hubA
  | .hubB,.sentinel | .sentinel,.hubB | .hubB,.col _ | .col _,.hubB => True
  | _,_ => False
def marked (X : U → Prop) : MarkV Q U → Prop
  | .sentinel => True | .col x => X x | _ => False
def markSide : MarkV Q U → Bool | .row _ | .hubB => true | _ => false

private theorem flips (S : Q → U → Prop) {u v} (e : markEdge S u v) : markSide u = !markSide v := by
  cases u <;> cases v <;> simp_all [markEdge,markSide]

theorem marked_distance (S : Q → U → Prop) (X : U → Prop) (q : Q) :
    let d := if Hit S X q then 1 else 3
    (∃ v,marked X v ∧ Walk (markEdge S) (.row q) d v) ∧
    ∀ v e,marked X v → Walk (markEdge S) (.row q) e v → d≤e := by
  classical
  intro d
  refine ⟨?_,?_⟩
  · by_cases h : Hit S X q
    · obtain ⟨j,s,x⟩ := h
      refine ⟨.col j,x,?_⟩
      simpa [d,show Hit S X q from ⟨j,s,x⟩] using
        (Walk.cons (show markEdge S (.row q) (.col j) from s) (.nil _))
    · refine ⟨.sentinel,trivial,?_⟩
      simpa [d,h] using (Walk.cons (show markEdge S (.row q) .hubA from trivial)
        (.cons (show markEdge S .hubA .hubB from trivial) (.cons (show markEdge S .hubB .sentinel from trivial) (.nil _))))
  · intro v e m w
    have opposite : markSide v=false := by cases v <;> simp_all [marked,markSide]
    cases w with
    | nil => contradiction
    | cons edge tail =>
      by_cases h : Hit S X q
      · dsimp [d]; simp [h]
      · simp only [d,if_neg h]
        rename_i b k
        cases tail with
        | nil => cases v <;> simp_all [markEdge,marked,Hit]
        | cons next last =>
          cases last with
          | nil => have a := flips S edge; have b := flips S next
                   rw [opposite] at b; simp only [markSide,Bool.not_false] at a b; rw [b] at a; contradiction
          | cons _ _ => omega

def triEdge (S : Q → U → Prop) (X : U → Prop) (q : Q) (a b : V Q U) :=
  sym (base S X) a b ∨ (a=.row q ∧ b=.target) ∨ (a=.target ∧ b=.row q)

theorem triangle_iff (S : Q → U → Prop) (X : U → Prop) (q : Q) :
    (∃ a b c,triEdge S X q a b ∧ triEdge S X q b c ∧ triEdge S X q c a) ↔ Hit S X q := by
  constructor
  · rintro ⟨a,b,c,ab,bc,ca⟩
    cases a <;> cases b <;> cases c <;> simp_all [triEdge,sym,base,Hit] <;> aesop
  · rintro ⟨x,h,m⟩; exact ⟨.row q,.col x,.target,Or.inl (Or.inl h),Or.inl (Or.inl m),Or.inr (Or.inr ⟨rfl,rfl⟩)⟩

def fixedEdge (S : Q → U → Prop) (X : U → Prop) (q : Q) (a b : V Q U) :=
  sym (base S X) a b ∨ sourceEdge q a b ∨ sourceEdge q b a
def forget (q : Q) : V Q U → V Q U | .source => .row q | v => v

private theorem project (S : Q → U → Prop) (X : U → Prop) (q : Q) {u v d}
    (w : Walk (fixedEdge S X q) u d v) :
    ∃ e≤d,Walk (sym (base S X)) (forget q u) e (forget q v) := by
  have lift {a b} (h : sym (base S X) a b) : sym (base S X) (forget q a) (forget q b) := by
    cases a <;> cases b <;> simp_all [forget,sym,base]
  induction w with
  | nil => exact ⟨0,le_rfl,.nil _⟩
  | cons h _ ih =>
    obtain ⟨e,le,w⟩ := ih
    rcases h with h|⟨rfl,rfl⟩|⟨rfl,rfl⟩
    · exact ⟨e+1,by omega,.cons (lift h) w⟩
    · exact ⟨e,by omega,w⟩
    · exact ⟨e,by omega,w⟩

theorem fixed_short (S : Q → U → Prop) (X : U → Prop) (q : Q) :
    (∃ d<5,Walk (fixedEdge S X q) .source d .target) ↔ Hit S X q := by
  constructor
  · rintro ⟨d,hd,w⟩
    cases w with
    | cons edge w =>
      have e := edge
      rename_i a k
      have eq : a=.row q := by cases a <;> simp_all [fixedEdge,sym,base,sourceEdge]
      subst a
      obtain ⟨e,le,pr⟩ := project S X q w
      exact (short_iff S X q).1 ⟨e,by omega,pr⟩
  · rintro ⟨x,h,m⟩
    exact ⟨3,by decide,.cons (Or.inr (Or.inl ⟨rfl,rfl⟩)) (.cons (Or.inl (Or.inl (show base S X (.row q) (.col x) from h)))
      (.cons (Or.inl (Or.inl (show base S X (.col x) .target from m))) (.nil _)))⟩
end DisjointnessDraft.Applications.GraphVariants
