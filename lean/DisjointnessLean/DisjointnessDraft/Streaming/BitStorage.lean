import DisjointnessDraft.Streaming.Decoder
import DisjointnessDraft.Streaming.BitMachine
import DisjointnessDraft.Streaming.Upper

/-! A real word-memory implementation. One additional address holds the
bounded decoder state. A complete valid block invokes the symbol processor
on the same heap, making exactly its probes. -/
namespace DisjointnessDraft.Streaming.Binary.BitStorage
open DisjointnessFoundations CellProbe WordProgram WordImage
open Classical
noncomputable section
abbrev Addresses (n : ℕ) := Option (Storage.Addr n n)
abbrev Values (n b : ℕ) := Storage.Val n ⊕ Buffer b
abbrev Layout (n b w : ℕ) := WordImage.Layout (Addresses n) (Values n b) w
def pack (u : Buffer b) (mem : Storage.Addr n n → Storage.Val n) : Addresses n → Values n b
  | none => .inr u
  | some a => .inl (mem a)
theorem pack_buffer (u v : Buffer b) (mem : Storage.Addr n n → Storage.Val n) :
    Function.update (pack u mem) none (.inr v)=pack v mem := by funext i; cases i <;> simp [pack,Function.update]
theorem pack_update (u : Buffer b) (mem : Storage.Addr n n → Storage.Val n) (a : Storage.Addr n n) (v : Storage.Val n) :
    Function.update (pack u mem) (some a) (.inl v)=pack u (Function.update mem a v) := by
  funext i; cases i with
  | none => simp [pack,Function.update]
  | some i => by_cases e : i=a <;> simp [pack,Function.update,e]

def symbolProgram (L : Layout n b w) : Storage.P n n Bool → Op w
  | .pure z => .pure z
  | .read a k => .read (L.addr (some a)) (fun v => symbolProgram L (k ((Function.invFun L.value v).getLeft?.getD default)))
  | .write a v k => .write (L.addr (some a)) (L.value (.inl v)) (symbolProgram L k)

theorem symbol_run (L : Layout n b w) (p : Storage.P n n Bool) (u : Buffer b)
    (mem : Storage.Addr n n → Storage.Val n) :
    (symbolProgram L p).run (image L (pack u mem)) =
      let z := p.run mem; (z.1,image L (pack u z.2.1),z.2.2) := by
  induction p generalizing mem with
  | pure x => rfl
  | read a k ih =>
    simp only [symbolProgram,Program.run,image_at,Function.leftInverse_invFun L.value.injective,pack,Sum.getLeft?_inl,Option.getD_some,ih]
    rw [Function.leftInverse_invFun L.value.injective (Sum.inl (mem a))]; rfl
  | write a v k ih => simp only [symbolProgram,Program.run,image_update,pack_update,ih]

def bitOp (L : Layout n b w) (C : Code (Symbol n n) b) (hb : 0<b) (x : Bool) : Op w := do
  let v ← Program.load (L.addr none)
  let old := (Function.invFun L.value v).getRight?.getD none
  let next := advanceBit C hb old x
  Program.store (L.addr none) (L.value (.inr next.1))
  match next.2 with
  | none => pure false
  | some s => symbolProgram L (Storage.operation s)

def nextStore (f : Family n) (s : Storage.Store n) : Option (Symbol n n) → Storage.Store n
  | none => s
  | some a => Storage.nextState f s a
def wordCost (s : Storage.Store n) : Option (Symbol n n) → ℕ
  | none => 0 | some a => Storage.probes s a

theorem bit_run (L : Layout n b w) (C : Code (Symbol n n) b) (hb : 0<b)
    (f : Family n) (s : Storage.Store n) (u : Buffer b) (x : Bool) (ok : Storage.valid s) :
    let next := advanceBit C hb u x
    let t := nextStore f s next.2
    (bitOp L C hb x).run (image L (pack u (Storage.words f s.1 s.2)))=
      (decide (aligned next.1) && accepted (Storage.parser t),image L (pack next.1 (Storage.words f t.1 t.2)),2+wordCost s next.2) := by
  dsimp only
  simp only [bitOp,Program.run_bind,Program.run_load,Program.run_store,image_at,
    Function.leftInverse_invFun L.value.injective,pack,Sum.getRight?_inr,Option.getD_some,image_update,pack_buffer]
  rw [Function.leftInverse_invFun L.value.injective (Sum.inr u)]
  simp only [Sum.getRight?_inr,Option.getD_some]
  cases eq : (advanceBit C hb u x).2 with
  | none =>
    have halt : ¬aligned (advanceBit C hb u x).1 := by simp [next_aligned,eq]
    simp [halt,nextStore,wordCost,Program.run_pure]; exact ⟨rfl,rfl,rfl⟩
  | some a =>
    have start : aligned (advanceBit C hb u x).1 := by simp [next_aligned,eq]
    simp [start,nextStore,wordCost,symbol_run,Storage.operation_run _ _ _ ok,Nat.add_assoc]; omega

def recover (C : Code (Symbol n n) b) (r : RegularExpression Bool) : Family n :=
  fun q => Finset.univ.filter (fun j => !(r.rmatch ((word [j] q).flatMap C.bits)))
theorem recover_exact (C : Code (Symbol n n) b) (hb : 0<b) (f : Family n) :
    recover C (substitute C.bits (expression f))=f := by
  ext q j
  have h : (substitute C.bits (expression f)).rmatch ((word [j] q).flatMap C.bits)=true ↔ j∉f q := by
    rw [RegularExpression.rmatch_iff_matches',C.reduction hb]; simp
  simp only [recover,Finset.mem_filter,Finset.mem_univ,true_and,Bool.not_eq_true']
  cases z : (substitute C.bits (expression f)).rmatch ((word [j] q).flatMap C.bits) <;> simp_all

def machine (L : Layout n b w) (C : Code (Symbol n n) b) (hb : 0<b) : BitMachine w where
  preload r := image L (pack (empty hb) (Storage.words (recover C r) .first []))
  bit := bitOp L C hb

theorem room (n b w : ℕ) (ha : n*n+2*n+3≤2^w) (hv : n+8+b*2^b≤2^w) : Nonempty (Layout n b w) := by
  have s := Storage.space n n
  have bsize := buffer_space b
  have a : Fintype.card (Addresses n)≤Fintype.card (Word w) := by simp [Addresses,Word]; omega
  have v : Fintype.card (Values n b)≤Fintype.card (Word w) := by simp only [Values,Fintype.card_sum,Word,Fintype.card_fin]; omega
  exact ⟨(Function.Embedding.nonempty_of_card_le a).some,(Function.Embedding.nonempty_of_card_le v).some,.inl default⟩

end
end DisjointnessDraft.Streaming.Binary.BitStorage
