import DisjointnessDraft.Applications.Matrices
import DisjointnessDraft.Transfer.Compiler

/-! Entry assignments and identity padding for the two nonsingular-matrix
problems. Matrix inputs and query addresses use exactly N row/column indices. -/
namespace DisjointnessDraft.Applications.AlgebraicCosts
open Matrices Matrix Finset
open Classical
noncomputable section
variable {n N p : ℕ} [Fact p.Prime]
abbrev Core (n : ℕ) := Ix (Fin n) (Fin n)
abbrev Square (N p : ℕ) := Matrix (Fin N) (Fin N) (ZMod p)
abbrev Edit (N p : ℕ) := (Fin N × Fin N) × ZMod p
def write (M : Square N p) (e : Edit N p) : Square N p :=
  fun a b => if (a,b)=e.1 then e.2 else M a b

def core (F : Family n) (X : Finset (Fin n)) := A (incidence (K:=ZMod p) F) (flags X)

def layout (fit : 2*n+1≤N) : Core n ⊕ Fin (N-(2*n+1)) ≃ Fin N :=
  Fintype.equivOfCardEq (by simp [Core,Ix]; omega)
def pad (fit : 2*n+1≤N) (M : Matrix (Core n) (Core n) (ZMod p)) : Square N p :=
  Matrix.reindex (layout fit) (layout fit) (fromBlocks M 0 0 1)
def key (fit : 2*n+1≤N) (x : Core n) := layout fit (.inl x)
def last (fit : 2*n+1≤N) := key fit (.inr ())
def row (fit : 2*n+1≤N) (q : Fin n) := key fit (.inl (.inl q))
def col (fit : 2*n+1≤N) (j : Fin n) := key fit (.inl (.inr j))
def dataEdit (fit : 2*n+1≤N) (j : Fin n) : Edit N p := ((col fit j,last fit),1)
def selector (fit : 2*n+1≤N) (q : Fin n) : Edit N p := ((last fit,row fit q),1)

theorem det_pad (fit : 2*n+1≤N) (M : Matrix (Core n) (Core n) (ZMod p)) : (pad fit M).det=M.det := by
  simp [pad,det_reindex_self,det_fromBlocks_zero₂₁]

theorem inverse_pad (fit : 2*n+1≤N) (F : Family n) (X : Finset (Fin n)) (q : Fin n) :
    (pad fit (core (p:=p) F X))⁻¹ (row fit q) (last fit)=(core (p:=p) F X)⁻¹ (.inl (.inl q)) (.inr ()) := by
  have invert : IsUnit (core (p:=p) F X) := (Matrix.isUnit_iff_isUnit_det _).mpr (by simp [core,det_A])
  rw [pad,inv_reindex,inv_fromBlocks_zero₂₁_of_isUnit_iff _ _ _ (by simp [invert])]
  simp [row,last,key,reindex_apply,fromBlocks]

private theorem pad_replace (fit : 2*n+1≤N) (M M' : Matrix (Core n) (Core n) (ZMod p))
    (i j : Core n) (v : ZMod p) (h : ∀a b,M' a b=if a=i ∧ b=j then v else M a b) :
    write (pad fit M) ((key fit i,key fit j),v)=pad fit M' := by
  ext a b
  obtain ⟨a,rfl⟩ := (layout fit).surjective a
  obtain ⟨b,rfl⟩ := (layout fit).surjective b
  cases a <;> cases b <;> simp [write,pad,key,fromBlocks,reindex_apply,h]

theorem data_write (fit : 2*n+1≤N) (F : Family n) (X : Finset (Fin n)) (j : Fin n) :
    write (pad fit (core (p:=p) F X)) (dataEdit fit j)=pad fit (core F (insert j X)) :=
  pad_replace fit _ _ _ _ _ (new_entry F X j)

theorem selector_write (fit : 2*n+1≤N) (F : Family n) (X : Finset (Fin n)) (q : Fin n) :
    write (pad fit (core (p:=p) F X)) (selector fit q)=pad fit (core F X+selCol*selRow q) := by
  apply pad_replace
  intro a b; rw [Matrix.add_apply,selected_entries]
  split_ifs with h
  · obtain ⟨rfl,rfl⟩ := h; simp [core,A,fromBlocks]
  · simp

theorem data_history (fit : 2*n+1≤N) (F : Family n) (xs : List (Fin n)) :
    (xs.map (dataEdit (p:=p) fit)).foldl write (pad fit (core F ∅))=pad fit (core F xs.toFinset) := by
  induction xs using List.reverseRecOn with
  | nil => rfl
  | append_singleton xs j ih => simp [List.foldl_append,ih,data_write,Finset.union_comm,Finset.insert_eq]

theorem inverse_correct (fit : 2*n+1≤N) (field : n+1<p) (F : Family n) (xs : List (Fin n)) (q : Fin n) :
    let B := (xs.map (dataEdit (p:=p) fit)).foldl write (pad fit (core F ∅))
    B.det≠0 ∧ decide (B⁻¹ (row fit q) (last fit)=0)=answer F xs q := by
  rw [data_history]; dsimp only
  refine ⟨by simp [det_pad,core,det_A],?_⟩
  rw [inverse_pad]
  have z := (prime_tests (p:=p) (by simpa using field) F xs.toFinset q).1
  apply Bool.eq_iff_iff.mpr
  simp only [answer,decide_eq_true_eq]
  rw [show ((core (p:=p) F xs.toFinset)⁻¹ _ _=0) ↔ _ from z,Finset.disjoint_left]
  simp only [List.mem_toFinset]
  tauto

theorem determinant_correct (fit : 2*n+1≤N) (field : n+1<p) (F : Family n) (xs : List (Fin n)) (q : Fin n) :
    let B := ((xs.map (dataEdit (p:=p) fit)++[selector fit q]).foldl write (pad fit (core F ∅)))
    B.det≠0 ∧ decide (B.det=1)=answer F xs q := by
  simp only [List.foldl_append,List.foldl_cons,List.foldl_nil,data_history,selector_write,det_pad]
  have z := (prime_tests (p:=p) (by simpa using field) F xs.toFinset q).2
  refine ⟨z.2,?_⟩
  apply Bool.eq_iff_iff.mpr
  simp only [answer,decide_eq_true_eq]
  apply z.1.trans
  rw [Finset.disjoint_left]
  simp only [List.mem_toFinset]
  tauto
open Transfer.Compiler

def state {J : Type} (B : Square N p) (h : List (Instr (Edit N p) J)) :=
  h.foldl (fun M op => op.elim (write M) (fun _ => M)) B

def nonsingular {J : Type} (B : Square N p) (h : List (Instr (Edit N p) J)) :=
  ∀ t, t <+: h → (state B t).det≠0

def invSpec (B : Square N p) (h : List (Instr (Edit N p) (Fin N×Fin N))) (pair : Fin N×Fin N) :=
  decide ((state B h)⁻¹ pair.1 pair.2=0)
def detSpec (B : Square N p) (h : List (Instr (Edit N p) Unit)) (_ : Unit) :=
  decide ((state B h).det=1)

def invSchedule (fit : 2*n+1≤N) : Schedule n (Square N p) (Edit N p) (Fin N×Fin N) Bool :=
  ⟨fun F => pad fit (core F ∅),fun j => [dataEdit fit j],fun q => [.inr (row fit q,last fit)],fun _ l => l.headD false⟩
def detSchedule (fit : 2*n+1≤N) : Schedule n (Square N p) (Edit N p) Unit Bool :=
  ⟨fun F => pad fit (core F ∅),fun j => [dataEdit fit j],fun q => [.inl (selector fit q),.inr ()],fun _ l => l.headD false⟩

private theorem snoc_cases {T : Type} {h xs : List T} {e : T} (z : h<+:xs++[e]) : h<+:xs ∨ h=xs++[e] := by
  by_cases l : h.length≤xs.length
  · exact Or.inl (List.prefix_of_prefix_length_le z (List.prefix_append ..) l)
  · exact Or.inr (z.eq_of_length_le (by simp; omega))

private theorem state_data {J : Type} (B : Square N p) (fit : 2*n+1≤N) (xs : List (Fin n)) :
    state (J:=J) B (xs.map (Sum.inl ∘ dataEdit fit))=(xs.map (dataEdit fit)).foldl write B := by
  induction xs generalizing B with
  | nil => rfl
  | cons x xs ih => exact ih (write B (dataEdit fit x))

private theorem original_safe {J : Type} (fit : 2*n+1≤N) (F : Family n) (xs : List (Fin n))
    (t : List (Instr (Edit N p) J)) (h : t<+:xs.map (Sum.inl ∘ dataEdit fit)) : (state (pad fit (core F ∅)) t).det≠0 := by
  obtain ⟨ys,_,rfl⟩ := List.isPrefix_map_iff.mp h
  rw [state_data,data_history,det_pad]
  simp [core,det_A]

@[simp] theorem inverse_before (fit : 2*n+1≤N) (xs : List (Fin n)) :
    before (invSchedule (p:=p) fit) xs=xs.map (Sum.inl ∘ dataEdit fit) := by simp [before,invSchedule,←List.map_eq_flatMap]
@[simp] theorem determinant_before (fit : 2*n+1≤N) (xs : List (Fin n)) :
    before (detSchedule (p:=p) fit) xs=xs.map (Sum.inl ∘ dataEdit fit) := by simp [before,detSchedule,←List.map_eq_flatMap]

theorem inverse_valid (fit : 2*n+1≤N) (field : n+1<p) :
    Valid (invSchedule (p:=p) fit) nonsingular invSpec := by
  constructor
  · intro F xs q _ h pre t ht
    have he := ht.trans pre
    rw [inverse_before] at he
    rcases snoc_cases he with w|rfl
    · exact original_safe fit F xs t w
    · simp only [invSchedule,state,List.foldl_append,List.foldl_cons,List.foldl_nil,Sum.elim_inr]
      exact original_safe fit F xs _ (List.prefix_refl _)
  · intro F xs q _
    change decide ((state _ (before (invSchedule fit) xs))⁻¹ (row fit q) (last fit)=0)=_
    rw [inverse_before,state_data]
    exact (inverse_correct (p:=p) fit field F xs q).2

theorem determinant_valid (fit : 2*n+1≤N) (field : n+1<p) :
    Valid (detSchedule (p:=p) fit) nonsingular detSpec := by
  let I := fun xs : List (Fin n) => xs.map (Sum.inl (β:=Unit) ∘ dataEdit (p:=p) fit)
  have active (F : Family n) (xs : List (Fin n)) (q : Fin n) :
      state (pad fit (core F ∅)) (I xs ++ [.inl (selector fit q)])=
        write ((xs.map (dataEdit fit)).foldl write (pad fit (core F ∅))) (selector fit q) := by
    rw [state,List.foldl_append]; change write (state _ _) _=_; dsimp only [I]; rw [state_data]
  constructor
  · intro F xs q _ h pre t ht
    have he : t<+:(I xs++[.inl (selector fit q)])++[.inr ()] := by
      have e := ht.trans pre
      rw [determinant_before] at e
      simpa only [I,List.append_assoc,List.singleton_append] using e
    have safe : (state (pad fit (core F ∅)) (I xs++[.inl (selector (p:=p) fit q)])).det≠0 := by
      rw [active]; simpa only [List.foldl_append,List.foldl_cons,List.foldl_nil] using (determinant_correct fit field F xs q).1
    rcases snoc_cases he with w|rfl
    · rcases snoc_cases w with u|rfl
      · exact original_safe fit F xs t u
      · exact safe
    · exact (by simpa only [state,List.foldl_append,List.foldl_cons,List.foldl_nil,Sum.elim_inr] using safe)
  · intro F xs q _
    change decide ((state (pad fit (core F ∅)) (before (detSchedule fit) xs++[.inl (selector fit q)])).det=1)=_
    rw [determinant_before]; change decide ((state _ (I xs++_)).det=1)=_
    rw [active]
    simpa only [List.foldl_append,List.foldl_cons,List.foldl_nil] using (determinant_correct fit field F xs q).2


def invValue (B : Square N p) (h : List (Instr (Edit N p) (Fin N×Fin N))) (pair : Fin N×Fin N) :=
  (state B h)⁻¹ pair.1 pair.2
def detValue (B : Square N p) (h : List (Instr (Edit N p) Unit)) (_ : Unit) := (state B h).det

def invValueSchedule (fit : 2*n+1≤N) : Schedule n (Square N p) (Edit N p) (Fin N×Fin N) (ZMod p) :=
  ⟨(invSchedule fit).initial,(invSchedule fit).insert,(invSchedule fit).finish,fun _ l => decide (l.headD 0=0)⟩
def detValueSchedule (fit : 2*n+1≤N) : Schedule n (Square N p) (Edit N p) Unit (ZMod p) :=
  ⟨(detSchedule fit).initial,(detSchedule fit).insert,(detSchedule fit).finish,fun _ l => decide (l.headD 0=1)⟩

theorem inverse_value_valid (fit : 2*n+1≤N) (field : n+1<p) :
    Valid (invValueSchedule (p:=p) fit) nonsingular invValue :=
  ⟨(inverse_valid fit field).1,(inverse_valid fit field).2⟩

theorem determinant_value_valid (fit : 2*n+1≤N) (field : n+1<p) :
    Valid (detValueSchedule (p:=p) fit) nonsingular detValue :=
  ⟨(determinant_valid fit field).1,(determinant_valid fit field).2⟩

end
end DisjointnessDraft.Applications.AlgebraicCosts
