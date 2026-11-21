import DisjointnessDraft.Applications.Points
import DisjointnessDraft.Applications.ShortTransfer

/-! Paired genuine and reference rows. The reference columns never receive
blockers. Their counts recover the static row size with physical queries. -/
namespace DisjointnessDraft.Applications.GeoPair
open Finset Transfer.Compiler Points
open Classical
noncomputable section
variable {n : ℕ}

def original (n : ℕ) : Fin n ↪ Fin (n+n) := ⟨fun j : Fin n => j.castAdd n, by intro a b h; exact Fin.ext (congrArg (fun z : Fin (n+n) => z.val) h)⟩
def shadow (n : ℕ) : Fin n ↪ Fin (n+n) := ⟨Fin.natAdd n, by intro a b h; apply Fin.ext; have := congrArg Fin.val h; simp at this; omega⟩
def first (q : Fin n) : Fin (n+n) := ⟨2*q.val,by have := q.isLt; omega⟩
def second (q : Fin n) : Fin (n+n) := ⟨2*q.val+1,by have := q.isLt; omega⟩
def paired (F : Family n) (i : Fin (n+n)) : Finset (Fin (n+n)) :=
  let q : Fin n := ⟨i.val/2,by have := i.isLt; omega⟩
  (F q).map (if i.val%2=0 then original n else shadow n)
theorem first_val (q : Fin n) : idx (second q)=idx (first q)+1 := by simp [idx,first,second]
@[simp] theorem first_row (F : Family n) (q : Fin n) : paired F (first q)=(F q).map (original n) := by simp [paired,first]
@[simp] theorem second_row (F : Family n) (q : Fin n) : paired F (second q)=(F q).map (shadow n) := by simp [paired,second,Nat.mul_add_div (by decide : 0<2)]
theorem fresh_shadow (S X : Finset (Fin n)) : Disjoint (S.map (shadow n)) (X.map (original n)) := by
  apply disjoint_left.mpr; intro j hs hx
  obtain ⟨i,_,rfl⟩ := mem_map.mp hs
  obtain ⟨k,_,e⟩ := mem_map.mp hx
  have z := congrArg Fin.val e
  change k.val=n+i.val at z; have := k.isLt; omega

theorem union_test (F : Family n) (xs : List (Fin n)) (q : Fin n) :
    decide (((paired F (first q))∪(xs.toFinset.map (original n))).card=
      ((paired F (second q))∪(xs.toFinset.map (original n))).card)=answer F xs q := by
  have dis := fresh_shadow (F q) xs.toFinset
  simp only [first_row,second_row,←Finset.map_union,card_union_of_disjoint dis,Finset.card_map]
  apply Bool.eq_iff_iff.mpr; simp only [answer,decide_eq_true_eq]
  rw [card_union_eq_card_add_card,disjoint_left]
  simp only [List.mem_toFinset]
  tauto

theorem difference_test (F : Family n) (xs : List (Fin n)) (q : Fin n) :
    decide (((paired F (first q))\(xs.toFinset.map (original n))).card=
      ((paired F (second q))\(xs.toFinset.map (original n))).card)=answer F xs q := by
  have a := card_sdiff_add_card (paired F (first q)) (xs.toFinset.map (original n))
  have b := card_sdiff_add_card (paired F (second q)) (xs.toFinset.map (original n))
  have eq : ((paired F (first q))\(xs.toFinset.map (original n))).card=
      ((paired F (second q))\(xs.toFinset.map (original n))).card ↔ _ :=
    show _ ↔ ((paired F (first q))∪(xs.toFinset.map (original n))).card=
      ((paired F (second q))∪(xs.toFinset.map (original n))).card by omega
  simpa only [eq] using union_test F xs q

def state {V Q : Type} (P : Finset V) (h : List (Instr V Q)) : Finset V :=
  P ∪ (h.filterMap (fun op => op.elim some (fun _ => none))).toFinset

@[simp] theorem on_data {V Q : Type} (P : Finset V) (g : Fin n → V) (xs : List (Fin n)) :
    state (Q:=Q) P (xs.map (Sum.inl ∘ g))=P∪xs.toFinset.image g := by
  ext x; simp [state]

@[simp] theorem on_insert {V Q : Type} [DecidableEq V] (P : Finset V) (h : List (Instr V Q)) (v : V) :
    state P (h++[.inl v])=insert v (state P h) := by ext x; simp [state]; tauto
@[simp] theorem on_query {V Q : Type} (P : Finset V) (h : List (Instr V Q)) (q : Q) :
    state P (h++[.inr q])=state P h := by simp [state]

theorem state_size {V Q : Type} (P : Finset V) (h : List (Instr V Q)) : (state P h).card≤P.card+h.length := by
  apply (card_union_le ..).trans
  exact Nat.add_le_add_left ((List.toFinset_card_le _).trans (List.length_filterMap_le ..)) _

theorem state_mem {V Q : Type} (P : Finset V) (h : List (Instr V Q)) (v : V) :
    v∈state P h ↔ v∈P ∨ Sum.inl v∈h := by
  simp [state,List.mem_filterMap,Sum.exists]

end
end DisjointnessDraft.Applications.GeoPair
