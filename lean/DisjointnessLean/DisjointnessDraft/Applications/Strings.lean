import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic.Ring

/-! Finite text and document gadgets, with the sentinel separated from element
symbols. The Hamming reduction counts every encoded bit, including padding. -/
namespace DisjointnessDraft.Applications.Strings
open Classical Finset
open scoped BigOperators
noncomputable section
variable {Q U : Type} [DecidableEq U] [Fintype U]

def row (S : Q → Finset U) (q : Q) (x : U) : Option U := if x∈S q then some x else none
def text (S : Q → Finset U) : (Q × U) ⊕ U → Option U
  | .inl (q,x) => row S q x | .inr x => some x

theorem dictionary {Q U : Type} [DecidableEq U] [Fintype U] (S : Q → Finset U) (X : Finset U) (q : Q) :
    (∃ j∈X,∃ x,text S (.inl (q,x))=text S (.inr j)) ↔ (S q ∩ X).Nonempty := by
  constructor
  · rintro ⟨j,hj,x,h⟩; by_cases hx : x∈S q
    · have eq : x=j := by simpa [text,row,hx] using h
      exact ⟨j,Finset.mem_inter.mpr ⟨eq ▸ hx,hj⟩⟩
    · simp [text,row,hx] at h
  · rintro ⟨j,h⟩; exact ⟨j,(mem_inter.mp h).2,j,by simp [text,row,(mem_inter.mp h).1]⟩

inductive Symbol (Q : Type) where | mark | blank | label (q : Q) deriving DecidableEq
def document (S : Q → Finset U) (j : U) : Option Q → Symbol Q
  | none => .mark | some i => if j∈S i then .label i else .blank

theorem active_documents {Q U : Type} [DecidableEq U] [Fintype U] (S : Q → Finset U) (X : Finset U) (q : Q) :
    (∃ j∈X,(∃ i,document S j i=Symbol.label q) ∧ (∃ k,document S j k=Symbol.mark)) ↔ (S q∩X).Nonempty := by
  constructor
  · rintro ⟨j,hj,⟨i,eq⟩,_⟩
    cases i with
    | none => contradiction
    | some i =>
      by_cases h : j∈S i
      · have same : i=q := by simpa [document,h] using eq
        exact ⟨j,mem_inter.mpr ⟨same ▸ h,hj⟩⟩
      · simp [document,h] at eq
  · rintro ⟨j,h⟩; exact ⟨j,(mem_inter.mp h).2,⟨some q,by simp [document,(mem_inter.mp h).1]⟩,⟨none,rfl⟩⟩

def codeP (b : Bool) (t : Fin 3) := (t.val=1 || b)
def codeT (b : Bool) (t : Fin 3) := (t.val=0 || b)
def hd {A : Type} [Fintype A] (p t : A → Bool) : ℕ := ∑ i, if p i=t i then 0 else 1
theorem local_code (a b : Bool) : hd (codeP a) (codeT b) + (if a && b then 2 else 0)=2 := by
  cases a <;> cases b <;> decide

def overlap {A : Type} [Fintype A] (p t : A → Bool) := (univ.filter (fun i => p i && t i)).card

theorem hamming_count {A : Type} [Fintype A] (p t : A → Bool) :
    hd (fun i : A × Fin 3 => codeP (p i.1) i.2) (fun i => codeT (t i.1) i.2) +
      2*overlap p t=2*Fintype.card A := by
  have sum := Finset.sum_congr (rfl : (Finset.univ : Finset A)=Finset.univ) (fun i (_ : i∈(univ : Finset A)) => local_code (p i) (t i))
  rw [Finset.sum_add_distrib] at sum
  have eq : (∑ i, if p i && t i then 2 else 0)=2*overlap p t := by simp [overlap,Finset.sum_ite,Nat.mul_comm]
  rw [eq] at sum
  simpa only [hd,Fintype.sum_prod_type,Finset.sum_const,Finset.card_univ,nsmul_eq_mul,Nat.mul_comm 2] using sum

theorem hamming_threshold {n tail : ℕ} (S X : Finset (Fin n)) (after : Fin tail → Bool) (hn : 0<n) :
    let p : Fin n ⊕ Fin tail → Bool := Sum.elim (fun x => decide (x∈X)) (fun _ => false)
    let t : Fin n ⊕ Fin tail → Bool := Sum.elim (fun x => decide (x∈S)) after
    hd (fun i : (Fin n ⊕ Fin tail) × Fin 3 => codeP (p i.1) i.2) (fun i => codeT (t i.1) i.2)
      ≤ 2*(n+tail)-1 ↔ (S∩X).Nonempty := by
  intro p t
  have H := hamming_count p t
  rw [Fintype.card_sum,Fintype.card_fin,Fintype.card_fin] at H
  have pos : 0<overlap p t ↔ (S∩X).Nonempty := by
    rw [overlap,Finset.card_pos]; constructor
    · rintro ⟨i,hi⟩; cases i with
      | inl x => exact ⟨x,by simpa [p,t,and_comm] using hi⟩
      | inr y => simp [p,t] at hi
    · rintro ⟨x,h⟩; exact ⟨.inl x,by simpa [p,t,and_comm] using h⟩
  rw [←pos]; omega

theorem pattern_edits : List.filter (fun i => decide (codeP false i ≠ codeP true i)) (List.finRange 3) = [0,2] := by decide
end
end DisjointnessDraft.Applications.Strings
