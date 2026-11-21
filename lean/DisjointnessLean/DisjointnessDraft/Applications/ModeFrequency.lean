import DisjointnessDraft.Applications.ShortTransfer
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Fintype.BigOperators

/-! An ordinary interval mode determines the answer under any tie rule.
The doubled occurrences and three trailing sentinels make the query
endpoints fixed public arguments, eliminating auxiliary membership lookups. -/
namespace DisjointnessDraft.Applications.RangeMode
open Finset Classical
noncomputable section
abbrev Bucket (n : ℕ) := (Fin n × Bool) ⊕ Unit
abbrev Slot (n : ℕ) := (Fin n × Bool) ⊕ Fin 3
abbrev Pos (n : ℕ) := Bucket n × Slot n
inductive Color (n : ℕ) where
  | signal
  | data (x : Fin n)
  | filler (whereAt : Pos n)
  deriving DecidableEq
abbrev Array (n : ℕ) := Pos n → Color n
abbrev Window := (ℕ × ℕ) × (ℕ × ℕ)

def rank {n} : Bucket n → ℕ
  | .inl (i,false) => 2*i.val
  | .inl (i,true) => 2*i.val+1
  | .inr () => 2*n
def coordinate (p : Pos n) : ℕ × ℕ := (rank p.1,(Fintype.equivFin (Slot n) p.2).val)
def leKey (a b : ℕ × ℕ) := a.1<b.1 ∨ a.1=b.1 ∧ a.2≤b.2
def covers (w : Window) (p : Pos n) := leKey w.1 (coordinate p) ∧ leKey (coordinate p) w.2

theorem rank_injective (n : ℕ) : Function.Injective (@rank n) := by
  rintro (⟨i,b⟩|⟨⟩) (⟨j,c⟩|⟨⟩) h
  · cases b <;> cases c <;> simp [rank] at h ⊢ <;> try omega
  · have := i.isLt; cases b <;> simp [rank] at h <;> omega
  · have := j.isLt; cases c <;> simp [rank] at h <;> omega
  · rfl

theorem coordinate_injective (n : ℕ) : Function.Injective (@coordinate n) := by
  intro p q eq
  exact Prod.ext (rank_injective n (congrArg Prod.fst eq))
    ((Fintype.equivFin (Slot n)).injective (Fin.ext (congrArg Prod.snd eq)))

def frequency (a : Array n) (w : Window) (z : Color n) : ℕ :=
  ∑ b : Bucket n,∑ s : Slot n,if covers w (b,s) ∧ a (b,s)=z then 1 else 0
def chosen (q : Fin n) : Window := ((2*q.val+1,0),(2*n,Fintype.card (Slot n)-1))

theorem chosen_endpoints (q : Fin n) :
    (∃ p : Pos n, coordinate p = (chosen q).1) ∧
    (∃ p : Pos n, coordinate p = (chosen q).2) := by
  have h : 0 < Fintype.card (Slot n) := Fintype.card_pos_iff.mpr ⟨Sum.inr 0⟩
  let first : Fin (Fintype.card (Slot n)) := ⟨0,h⟩
  let last : Fin (Fintype.card (Slot n)) := ⟨Fintype.card (Slot n)-1,by omega⟩
  refine ⟨⟨(.inl (q,true),(Fintype.equivFin _).symm first),?_⟩,
    ⟨(.inr (),(Fintype.equivFin _).symm last),?_⟩⟩ <;> simp [coordinate,chosen,rank,first,last]
def active (q : Fin n) : Bucket n → Prop
  | .inl (i,false) => q < i
  | .inl (i,true) => q ≤ i
  | .inr () => True

theorem covered (q : Fin n) (b : Bucket n) (s : Slot n) : covers (chosen q) (b,s) ↔ active q b := by
  have slot := (Fintype.equivFin (Slot n) s).isLt
  cases b with
  | inl p => rcases p with ⟨i,c⟩; have := i.isLt; cases c <;> simp only [covers,leKey,coordinate,chosen,rank,active,Fin.lt_def,Fin.le_def] <;> omega
  | inr u =>
    cases u
    have start : 2*q.val+1 < 2*n := by have := q.isLt; omega
    have stop : (Fintype.equivFin (Slot n) s).val ≤ Fintype.card (Slot n)-1 := by omega
    exact ⟨fun _ => trivial,fun _ => ⟨Or.inl start,Or.inr ⟨rfl,stop⟩⟩⟩

def marked (f : Family n) (X : Finset (Fin n)) (p : Pos n) : Color n :=
  match p with
  | (.inl (i,half),.inl (j,_)) => if (if half then j∈f i else j∉f i) then .data j else .filler p
  | (.inl (_,half),.inr k) => if half=false ∧ k.val<2 then .signal else .filler p
  | (.inr (),.inl (j,_)) => if j∈X then .data j else .filler p
  | (.inr (),.inr _) => .signal

def localCount (a : Array n) (b : Bucket n) (z : Color n) : ℕ :=
  ∑ s : Slot n,if a (b,s)=z then 1 else 0

theorem frequency_chosen (a : Array n) (q : Fin n) (z : Color n) :
    frequency a (chosen q) z = ∑ b : Bucket n, if active q b then localCount a b z else 0 := by
  apply Finset.sum_congr rfl
  intro b _
  by_cases h : active q b <;> simp [localCount,covered,h]

theorem local_data (f : Family n) (X : Finset (Fin n)) (b : Bucket n) (x : Fin n) :
    localCount (marked f X) b (.data x)=
      match b with
      | .inl (i,half) => if (if half then x∈f i else x∉f i) then 2 else 0
      | .inr () => if x∈X then 2 else 0 := by
  have known (i j : Fin n) (half c : Bool) :
      (if marked f X (.inl (i,half),.inl (j,c))=.data x then 1 else 0 : ℕ)=
        if j=x then (if (if half then x∈f i else x∉f i) then 1 else 0) else 0 := by
    by_cases e : j=x
    · subst j; cases half <;> by_cases h : x∈f i <;> simp [marked,h]
    · cases half <;> by_cases h : j∈f i <;> simp [marked,h,e]
  have extra (i : Fin n) (half : Bool) (k : Fin 3) :
      (if marked f X (.inl (i,half),.inr k)=.data x then 1 else 0 : ℕ)=0 := by
    simp only [marked]; split_ifs <;> simp_all
  have last (j : Fin n) (c : Bool) :
      (if marked f X (.inr (),.inl (j,c))=.data x then 1 else 0 : ℕ)=
        if j=x then (if x∈X then 1 else 0) else 0 := by
    by_cases e : j=x
    · subst j; by_cases h : x∈X <;> simp [marked,h]
    · by_cases h : j∈X <;> simp [marked,h,e]
  have pad (k : Fin 3) : (if marked f X (.inr (),.inr k)=.data x then 1 else 0 : ℕ)=0 := rfl
  cases b with
  | inl p =>
    rcases p with ⟨i,half⟩
    simp only [localCount,Fintype.sum_sum_type,Fintype.sum_prod_type,Fintype.sum_bool,known,extra,sum_const_zero,add_zero]
    by_cases h : (if half then x∈f i else x∉f i) <;> simp [h,Finset.sum_add_distrib]
  | inr u =>
    cases u
    simp only [localCount,Fintype.sum_sum_type,Fintype.sum_prod_type,Fintype.sum_bool,last,pad,sum_const_zero,add_zero]
    by_cases h : x∈X <;> simp [h,Finset.sum_add_distrib]

theorem local_signal (f : Family n) (X : Finset (Fin n)) (b : Bucket n) :
    localCount (marked f X) b .signal =
      match b with | .inl (_,false) => 2 | .inl (_,true) => 0 | .inr () => 3 := by
  have dataSlot (b : Bucket n) (j : Fin n) (c : Bool) :
      (if marked f X (b,.inl (j,c))=.signal then 1 else 0 : ℕ)=0 := by
    rcases b with ⟨i,h⟩|⟨⟩ <;> simp only [marked] <;> split_ifs <;> simp_all
  have normal (i : Fin n) (h : Bool) (k : Fin 3) :
      (if marked f X (.inl (i,h),.inr k)=.signal then 1 else 0 : ℕ)=
      if h=false ∧ k.val<2 then 1 else 0 := by simp only [marked]; split_ifs <;> simp_all
  have last (k : Fin 3) : (if marked f X (.inr (),.inr k)=.signal then 1 else 0 : ℕ)=1 := rfl
  rcases b with ⟨i,h⟩|⟨⟩
  · cases h <;> simp only [localCount,Fintype.sum_sum_type,Fintype.sum_prod_type,Fintype.sum_bool,dataSlot,normal,
      add_zero,sum_const_zero,zero_add,Fin.sum_univ_three] <;> decide
  · simp only [localCount,Fintype.sum_sum_type,Fintype.sum_prod_type,Fintype.sum_bool,dataSlot,last,add_zero,sum_const_zero,zero_add,Fin.sum_univ_three]

def base (q : Fin n) : ℕ := ∑ i : Fin n, if q < i then 2 else 0

theorem signal_score (f : Family n) (X : Finset (Fin n)) (q : Fin n) :
    frequency (marked f X) (chosen q) .signal = base q+3 := by
  simp [frequency_chosen,Fintype.sum_sum_type,Fintype.sum_prod_type,Fintype.sum_bool,local_signal,active,base]

theorem data_score (f : Family n) (X : Finset (Fin n)) (q x : Fin n) :
    frequency (marked f X) (chosen q) (.data x)=base q+(if x∈f q then 2 else 0)+(if x∈X then 2 else 0) := by
  rw [frequency_chosen,Fintype.sum_sum_type,Fintype.sum_prod_type]
  simp only [Fintype.sum_bool,Fintype.sum_unique,active,if_true,local_data]
  congr 1
  calc _ = ∑ i : Fin n,((if q < i then 2 else 0)+(if i=q then (if x∈f i then 2 else 0) else 0)) := by
             apply Finset.sum_congr rfl; intro i _
             rcases lt_trichotomy i q with h|rfl|h
             · simp [h.ne,not_lt.mpr h.le,not_le.mpr h]
             · simp
             · by_cases p : x∈f i <;> simp [p,h,h.le,h.ne']
       _ = _ := by simp [sum_add_distrib,base]

theorem filler_origin (f : Family n) (X : Finset (Fin n)) (p a : Pos n) (h : marked f X p=.filler a) : p=a := by
  rcases p with ⟨(⟨i,b⟩|⟨⟩),(⟨j,c⟩|k)⟩ <;> simp only [marked] at h <;> (try split_ifs at h) <;> simp_all

theorem filler_score (f : Family n) (X : Finset (Fin n)) (q : Fin n) (p : Pos n) :
    frequency (marked f X) (chosen q) (.filler p)≤1 := by
  calc _ ≤ ∑ b : Bucket n, ∑ s : Slot n,if b=p.1 ∧ s=p.2 then 1 else 0 := by
             apply Finset.sum_le_sum; intro b _; apply Finset.sum_le_sum; intro s _
             by_cases hit : covers (chosen q) (b,s) ∧ marked f X (b,s)=.filler p
             · have e := filler_origin f X (b,s) p hit.2; simp [hit,←e]
             · simp [hit]
       _ = _ := by simp [ite_and]

end
end DisjointnessDraft.Applications.RangeMode
