import DisjointnessDraft.Reverse
import Mathlib.SetTheory.Cardinal.Finite

namespace DisjointnessDraft.Applications.Components
open Graphs
noncomputable section
open Classical

variable {W Q U : Type}

theorem walk_join {E : W → W → Prop} {x y z k l} (p : Walk E x k y) (r : Walk E y l z) :
    Walk E x (k+l) z := by
  induction p with
  | nil => simpa using r
  | cons e p ih => simpa [Nat.succ_add] using Walk.cons e (ih r)

def component (E : W → W → Prop) : Setoid W where
  r a b := reach E a b ∧ reach E b a
  iseqv := ⟨fun a => ⟨⟨_,.nil a⟩,⟨_,.nil a⟩⟩,fun r => r.symm,by
    rintro a b c ⟨⟨_,ab⟩,⟨_,ba⟩⟩ ⟨⟨_,bc⟩,⟨_,cb⟩⟩
    exact ⟨⟨_,walk_join ab bc⟩,⟨_,walk_join cb ba⟩⟩⟩

def ret (S : Q→U→Prop) (X : U→Prop) (q : Q) (a b : V Q U) := base S X a b ∨ returnEdge q a b

def cycle (G : W→W→Prop) := ∃ v k,Walk G v (k+1) v

def rank {q : Q} (X : U→Prop) : V Q U → ℕ
  | .source => 0
  | .row r => if r=q then 3 else 0
  | .col x => if X x then 1 else 4
  | .target => 2

theorem increasing (S : Q→U→Prop) (X : U→Prop) (q : Q) (miss : ¬Hit S X q) {a b}
    (e : ret S X q a b) : rank (q:=q) X a<rank (q:=q) X b := by
  rcases e with e|⟨rfl,rfl⟩
  · cases a <;> cases b <;> simp only [base] at e <;> try contradiction
    · rename_i r x
      by_cases h : r=q
      · subst r; have notX : ¬X x := fun yes => miss ⟨x,e,yes⟩
        simp [rank,notX]
      · by_cases t : X x <;> simp [rank,h,t]
    · simp [rank,e]
  · simp [rank]

theorem paths_rise {E : W→W→Prop} (f : W→ℕ) (up : ∀ a b,E a b → f a<f b)
    {a b k} (p : Walk E a k b) : f a+k≤f b := by
  induction p with
  | nil => simp
  | cons e _ ih => have z := up _ _ e; omega

theorem cycle_iff (S : Q→U→Prop) (X : U→Prop) (q : Q) : cycle (ret S X q) ↔ Hit S X q := by
  constructor
  · rintro ⟨v,k,p⟩
    by_contra miss
    have no := paths_rise (rank (q:=q) X) (fun _ _ => increasing S X q miss) p
    omega
  · rintro ⟨x,hx,active⟩
    exact ⟨.row q,2,Walk.cons (show ret S X q (.row q) (.col x) from Or.inl hx) (.cons (show ret S X q (.col x) .target from Or.inl active) (.cons (show ret S X q .target (.row q) from Or.inr ⟨rfl,rfl⟩) (.nil _)))⟩

theorem pair_iff (S : Q→U→Prop) (X : U→Prop) (q : Q) :
    (component (ret S X q)).r (.row q) .target ↔ Hit S X q := by
  change (reach _ _ _ ∧ reach _ _ _) ↔ _
  unfold ret
  rw [returning_cycle]
  exact ⟨And.left,fun yes => ⟨yes,⟨1,.cons (Or.inr ⟨rfl,rfl⟩) (.nil _)⟩⟩⟩

theorem distinct_iff (S : Q→U→Prop) (X : U→Prop) (q : Q) :
    (∃ a b,a≠b ∧ (component (ret S X q)).r a b) ↔ Hit S X q := by
  constructor
  · rintro ⟨a,b,diff,⟨k,p⟩,⟨l,r⟩⟩
    by_contra miss
    have inc := fun u v => increasing S X q miss (a:=u) (b:=v)
    have h := paths_rise (rank (q:=q) X) inc p
    have j := paths_rise (rank (q:=q) X) inc r
    have kz : k=0 := by omega
    subst k; cases p; exact diff rfl
  · intro yes
    exact ⟨.row q,.target,by simp,(pair_iff S X q).mpr yes⟩

theorem component_count [Fintype W] (E : W→W→Prop) :
    Nat.card (Quotient (component E))<Fintype.card W ↔ ∃ a b,a≠b ∧ (component E).r a b := by
  let c := component E
  let projection : W → Quotient c := Quotient.mk c
  letI : Fintype (Quotient c) := Fintype.ofSurjective projection (Quotient.mk_surjective)
  rw [Nat.card_eq_fintype_card]
  constructor
  · intro less
    by_contra! no
    have inj : Function.Injective projection := fun a b eq => by
      by_contra ne
      exact no a b ne (Quotient.exact eq)
    exact (Nat.not_le_of_lt less) (Fintype.card_le_of_injective projection inj)
  · rintro ⟨a,b,ab,eq⟩
    exact Fintype.card_lt_of_surjective_not_injective projection Quotient.mk_surjective (fun inj => ab (inj (Quotient.sound eq)))

theorem largest_test [Fintype W] (E : W→W→Prop) :
    (∃ a,2≤(Finset.univ.filter ((component E).r a)).card) ↔ ∃ a b,a≠b ∧ (component E).r a b := by
  constructor
  · rintro ⟨a,two⟩
    obtain ⟨x,hx,y,hy,ne⟩ := Finset.one_lt_card.mp two
    by_cases h : a=x
    · exact ⟨a,y,h ▸ ne,(Finset.mem_filter.mp hy).2⟩
    · exact ⟨a,x,h,(Finset.mem_filter.mp hx).2⟩
  · rintro ⟨a,b,ne,eq⟩
    exact ⟨a,Finset.one_lt_card.mpr ⟨a,Finset.mem_filter.mpr ⟨Finset.mem_univ _,(component E).refl _⟩,b,
      Finset.mem_filter.mpr ⟨Finset.mem_univ _,eq⟩,ne⟩⟩

end
end DisjointnessDraft.Applications.Components
