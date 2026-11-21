import DisjointnessDraft.Streaming.Upper
import Mathlib.Algebra.Order.Floor.Div
import Mathlib.Logic.Equiv.Fin.Basic

/-! Packed read-only incidence words for the selector scan. -/
namespace DisjointnessDraft.Streaming.PackedTable
open DisjointnessFoundations CellProbe WordProgram
open Classical
noncomputable section

/-- Number of physical words used by a bit table. -/
def wordCount (bits w : ℕ) := bits ⌈/⌉ w

def block {bits w : ℕ} (hw : 0<w) (i : Fin bits) : Fin (wordCount bits w) :=
  ⟨i.val/w,(Nat.div_lt_iff_lt_mul hw).mpr (by
    have room : bits ≤ w*(bits ⌈/⌉ w) := (ceilDiv_le_iff_le_mul hw).mp le_rfl
    simpa [wordCount,Nat.mul_comm] using i.isLt.trans_le room)⟩

def packWord {w : ℕ} (f : Fin w → Bool) : Word w :=
  ⟨(BitVec.ofBoolListLE (List.ofFn f)).toNat,by simpa using (BitVec.ofBoolListLE (List.ofFn f)).isLt⟩

theorem bit_packWord {w : ℕ} (f : Fin w → Bool) (j : Fin w) :
    (packWord f).val.testBit j = f j := by
  change (BitVec.ofBoolListLE (List.ofFn f)).getLsbD j = f j
  rw [BitVec.getLsb_ofBoolListLE]
  simp [List.getD_eq_getElem?_getD,j.isLt]

def contents {bits : ℕ} (w : ℕ) (f : Fin bits → Bool) (b : Fin (wordCount bits w)) : Word w :=
  packWord fun j => if h : b.val*w+j.val<bits then f ⟨_,h⟩ else false

theorem read_bit {bits w : ℕ} (hw : 0<w) (f : Fin bits → Bool) (i : Fin bits) :
    (contents w f (block hw i)).val.testBit (i.val%w) = f i := by
  have join : i.val/w*w+i.val%w=i.val := Nat.div_add_mod' _ _
  have bit := bit_packWord (fun j : Fin w =>
    if h : (block hw i).val*w+j.val<bits then f ⟨_,h⟩ else false) ⟨i.val%w,Nat.mod_lt _ hw⟩
  simpa [contents,block,join,i.isLt] using bit

/-- One tag, one head, and separate next-pointer and seen words for each data symbol. -/
abbrev Aux (n : ℕ) := Unit ⊕ Unit ⊕ Fin n ⊕ Fin n
abbrev Slot (n w : ℕ) := Aux n ⊕ Fin (wordCount (n*n) w)

theorem slot_count (n w : ℕ) : Fintype.card (Slot n w)=2*n+2+wordCount (n*n) w := by
  simp [Slot,Aux]; omega

def incidence (f : Family n) (k : Fin (n*n)) : Bool :=
  let p := finProdFinEquiv.symm k
  decide (p.2∈f p.1)

def entry (q j : Fin n) := finProdFinEquiv (q,j)

@[simp] theorem incidence_entry (f : Family n) (q j : Fin n) :
    incidence f (entry q j)=decide (j∈f q) := by simp [incidence,entry]

/-- Word-address encoding for the table and the mutable parser storage. -/
abbrev Layout (n w : ℕ) := Slot n w ↪ Word w

theorem room {n w : ℕ} (fit : 2*n+2+wordCount (n*n) w≤2^w) : Nonempty (Layout n w) :=
  Function.Embedding.nonempty_of_card_le (by
    change Fintype.card (Slot n w) ≤ Fintype.card (Fin (2^w))
    rw [slot_count,Fintype.card_fin]
    exact fit)

def tableAddress (L : Layout n w) (hw : 0<w) (q j : Fin n) :=
  L (.inr (block hw (entry q j)))

def nextAddress (L : Layout n w) (j : Fin n) := L (.inl (.inr (.inr (.inl j))))

def heap (L : Layout n w) (f : Family n) (aux : Aux n → Word w) : Memory w :=
  fun address => if h : ∃ slot, L slot = address then
    match Classical.choose h with
    | .inl a => aux a
    | .inr b => contents w (incidence f) b
  else 0

theorem heap_at (L : Layout n w) (f : Family n) (aux : Aux n → Word w) (s : Slot n w) :
    heap L f aux (L s)=Sum.elim aux (contents w (incidence f)) s := by
  have h : ∃ slot,L slot=L s := ⟨s,rfl⟩
  simp only [heap,dif_pos h,L.injective (Classical.choose_spec h)]
  cases s <;> rfl

@[simp] private theorem run_return (x : α) (m : Memory w) :
    (pure x : Program (Word w) (Word w) α).run m=(x,m,0) := rfl

def lookup (L : Layout n w) (hw : 0<w) (q j : Fin n) : Program (Word w) (Word w) Bool := do
  let v ← Program.load (tableAddress L hw q j)
  pure (v.val.testBit ((entry q j).val%w))

theorem lookup_run (L : Layout n w) (hw : 0<w) (f : Family n) (aux : Aux n → Word w) (q j : Fin n) :
    (lookup L hw q j).run (heap L f aux)=(decide (j∈f q),heap L f aux,1) := by
  simp [lookup,Program.run_bind,Program.run_load,tableAddress,heap_at,read_bit]

theorem table_capacity (bits w : ℕ) (hw : 0<w) :
    bits ≤ w*wordCount bits w ∧ w*wordCount bits w < bits+w := by
  refine ⟨(ceilDiv_le_iff_le_mul hw).mp le_rfl,?_⟩
  rw [wordCount,Nat.ceilDiv_eq_add_pred_div,Nat.mul_comm]
  exact (Nat.div_mul_le_self _ _).trans_lt (by omega)

def auxAddress : Aux n → Storage.Addr n n
  | .inl _ => .tag
  | .inr (.inl _) => .head
  | .inr (.inr (.inl j)) => .next j
  | .inr (.inr (.inr j)) => .seen j

abbrev ValueCode (n w : ℕ) := Storage.Val n ↪ Word w

theorem values_fit {n w : ℕ} (fit : n+7≤2^w) : Nonempty (ValueCode n w) :=
  Function.Embedding.nonempty_of_card_le (by
    change Fintype.card (Storage.Val n)≤Fintype.card (Fin (2^w))
    rw [Fintype.card_fin]
    exact (Storage.space n n).2.trans fit)

def auxWords (V : ValueCode n w) (f : Family n) (tag : Storage.Tag) (xs : List (Fin n))
    (a : Aux n) : Word w := V (Storage.words f tag xs (auxAddress a))

def pointer (V : ValueCode n w) (v : Word w) : Option (Fin n) :=
  match Function.invFun V v with
  | .ptr p => p
  | _ => none

/-- The selector's linked-list scan with a one-word packed lookup at each visit. -/
def scan (L : Layout n w) (V : ValueCode n w) (hw : 0<w) (q : Fin n) :
    ℕ → Option (Fin n) → Program (Word w) (Word w) Bool
  | 0,_ | _+1,none => pure true
  | k+1,some x => do
    let bit ← lookup L hw q x
    let ptr ← Program.load (nextAddress L x)
    let ok ← scan L V hw q k (pointer V ptr)
    pure (ok && !bit)

/-- Replacing the incidence read in the original scan preserves its answer
and exact probe count, for every starting pointer and every fuel bound. -/
theorem scan_equivalence (L : Layout n w) (V : ValueCode n w) (hw : 0<w) (f : Family n)
    (tag : Storage.Tag) (xs : List (Fin n)) (q : Fin n) (fuel : ℕ) (start : Option (Fin n)) :
    let mem := heap L f (auxWords V f tag xs)
    let logical := (Storage.scan q fuel start).run (Storage.words f tag xs)
    let physical := (scan L V hw q fuel start).run mem
    physical.1=logical.1 ∧ physical.2.1=mem ∧ physical.2.2=logical.2.2 := by
  dsimp only
  induction fuel generalizing start with
  | zero => exact ⟨rfl,rfl,rfl⟩
  | succ k ih =>
    cases start with
    | none => exact ⟨rfl,rfl,rfl⟩
    | some x =>
      have rec := ih (Storage.links xs x)
      simp only [scan,Storage.scan,Program.run_bind,lookup_run,Program.run_load,nextAddress,
        heap_at,Sum.elim_inl,auxWords,auxAddress,Storage.words,pointer,
        Function.leftInverse_invFun V.injective,run_return] at *
      rcases rec with ⟨value,memory,cost⟩
      rw [Function.leftInverse_invFun V.injective (Storage.Val.ptr (Storage.links xs x))]
      simp [value,memory,cost,Storage.Val.bit.injEq,Program.run_pure]
end
end DisjointnessDraft.Streaming.PackedTable
