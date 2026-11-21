import DisjointnessDraft.Streaming.BinaryLower
import DisjointnessDraft.Transfer.Scripts

/-! A bit program may depend on its entire master tape and the absolute input
position. Only word memory persists between operations. The marker, each data
codeword and the final selector use exactly the original positions and probes. -/
namespace DisjointnessDraft.Streaming.Binary.Indexed
open DisjointnessFoundations CellProbe WordProgram Transfer.Compiler MeasureTheory RegularExpression Classical
open Program (run_bind)
open scoped ENNReal
noncomputable section
structure Machine (w : ℕ) (Ω : Type) where
  preload : Ω → RegularExpression Bool → Memory w
  bit : Ω → ℕ → Bool → Op w

variable {n b w : ℕ} {Ω : Type} (D : Machine w Ω) (seed : Ω) (C : Code (Symbol n n) b)
def batch (i : ℕ) (last : Bool) : List Bool → Op w
  | [] => .pure last
  | x::xs => D.bit seed i x >>= fun r => batch (i+1) r xs

theorem append (i : ℕ) (last : Bool) (xs ys : List Bool) (mem : Memory w) :
    (batch D seed i last (xs++ys)).run mem =
    let z := (batch D seed i last xs).run mem
    let v := (batch D seed (i+xs.length) z.1 ys).run z.2.1
    (v.1,v.2.1,z.2.2+v.2.2) := by
  induction xs generalizing i last mem with
  | nil => simp [batch,Program.run]
  | cons x xs ih => simp [batch,run_bind,ih,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm]

theorem nonempty (last other : Bool) (xs : List Bool) (ne : xs≠[]) (i : ℕ) :
    batch D seed i last xs=batch D seed i other xs := by cases xs <;> simp_all [batch]

def input (f : Family n) (raw : List Bool) :=
  (batch D seed 0 false raw).run (D.preload seed (substitute C.bits (expression f)))

def Correct := ∀ (f : Family n) (text : List Bool),text≠[] →
  (input D seed C f text).1=(substitute C.bits (expression f)).rmatch text
def Budget (t : ℕ) := ∀ (f : Family n) (pre : List Bool) (bit : Bool),
  ((D.bit seed pre.length bit).run (input D seed C f pre).2.1).2.2≤t

theorem next (f : Family n) (pre xs : List Bool) (h : xs≠[]) (last : Bool) :
    let z := (batch D seed pre.length last xs).run (input D seed C f pre).2.1
    (input D seed C f (pre++xs)).1=z.1 ∧ (input D seed C f (pre++xs)).2.1=z.2.1 := by
  unfold input; rw [append]; simp only [Nat.zero_add]
  rw [nonempty D seed _ last xs h]; exact ⟨rfl,rfl⟩

theorem cost (t : ℕ) (budget : Budget D seed C t) (f : Family n) (pre xs : List Bool) (last : Bool) :
    ((batch D seed pre.length last xs).run (input D seed C f pre).2.1).2.2≤xs.length*t := by
  induction xs generalizing pre last with
  | nil => simp [batch,Program.run]
  | cons x xs ih =>
    let p := input D seed C f pre
    let z := (D.bit seed pre.length x).run p.2.1
    have eq : (input D seed C f (pre++[x])).2.1=z.2.1 := by
      simpa [batch,Program.run,run_bind,p,z] using (next D seed C f pre [x] (by simp) false).2
    have rec := ih (pre++[x]) z.1
    rw [eq] at rec; simp only [List.length_append,List.length_singleton] at rec
    have first : z.2.2≤t := budget f pre x
    change ((D.bit seed pre.length x >>= _).run _).2.2 ≤ (xs.length+1)*t
    rw [run_bind]; change z.2.2+((batch D seed (pre.length+1) z.1 xs).run z.2.1).2.2≤_; rw [Nat.add_mul,Nat.one_mul]; omega

abbrev History (n : ℕ) := List (Instr (Fin n) (Fin n))
def letter : Instr (Fin n) (Fin n) → Symbol n n := Sum.elim datum selector
def bits (h : History n) := C.bits marker ++ h.flatMap (fun z => C.bits (letter z))
theorem bit_length (h : History n) : (bits C h).length=b*(h.length+1) := by
  have len (h : History n) : (h.flatMap fun z => C.bits (letter z)).length=b*h.length := by
    induction h with | nil => simp | cons x xs ih => simp [ih,Nat.mul_add,Nat.add_comm]
  simp [bits,len,Nat.mul_add,Nat.add_comm]
theorem bits_step (h : History n) (u : Instr (Fin n) (Fin n)) :
    bits C (h++[u])=bits C h++C.bits (letter u) := by simp [bits,List.flatMap_append,List.append_assoc]
private theorem positive_code (z : Symbol n n) (hb : 0<b) : C.bits z≠[] := fun h => by
  have l := congrArg List.length h; simp at l; omega

def program (i : ℕ) (z : Symbol n n) : Op w := batch D seed (b*(i+1)) false (C.bits z)
def target : Target (Family n) (Fin n) (Fin n) Bool w Unit where
  init _ f := (input D seed C f (C.bits marker)).2.1
  update _ t x := program D seed C t (datum x) >>= fun _ => pure ()
  query _ t q := program D seed C t (selector q)

theorem agree (hb : 0<b) (f : Family n) (h : History n) :
    (observed (target D seed C) () f h).2.1=(input D seed C f (bits C h)).2.1 := by
  induction h using List.reverseRecOn with
  | nil => simp [observed,script,Program.run,target,bits]
  | append_singleton xs u ih =>
    rw [next_memory,ih,bits_step]
    have z := (next D seed C f (bits C xs) (C.bits (letter u)) (positive_code C _ hb) false).2.symm
    rw [bit_length] at z
    cases u <;> simpa [targetStep,target,program,letter,Program.run,run_bind] using z

def spec (f : Family n) (h : History n) (q : Fin n) :=
  (substitute C.bits (expression f)).rmatch (bits C h++C.bits (selector q))

theorem guarantees (hb : 0<b) (t : ℕ) (correct : Correct D seed C) (budget : Budget D seed C t) :
    Guarantees (Measure.dirac ()) (target D seed C) (fun _ _ => True) (spec C) (b*t) (b*t : ℕ) := by
  have expense' (f : Family n) (h : History n) (u : Instr (Fin n) (Fin n)) :
      expense (target D seed C) () f h u≤b*t := by
    have bill := cost D seed C t budget f (bits C h) (C.bits (letter u)) false
    rw [bit_length] at bill; simp only [Code.length] at bill
    unfold expense; rw [agree D seed C hb]
    cases u <;> simpa [targetStep,target,program,letter,Program.run,run_bind] using bill
  constructor
  · rintro ⟨⟩ f h u _; exact expense' f h (.inl u)
  · intro f h q _
    rw [lintegral_dirac' _ (by fun_prop)]
    rw [ENNReal.ofReal_natCast]; exact_mod_cast expense' f h (.inr q)
  · rintro ⟨⟩ f h q _
    rw [agree D seed C hb]
    have z := (next D seed C f (bits C h) (C.bits (selector q)) (positive_code C _ hb) false).1.symm
    rw [bit_length] at z
    exact z.trans (correct _ _ (by simp [positive_code C (selector q) hb]))
  · intros; exact Measurable.of_discrete

def plan (n : ℕ) : Schedule n (Family n) (Fin n) (Fin n) Bool := ⟨id,fun x => [x],fun q => [.inr q],fun _ xs => xs.headD false⟩
theorem valid (hb : 0<b) : Valid (plan n) (fun _ _ => True) (spec C) := by
  refine ⟨by simp,?_⟩
  intro f xs q _
  change (substitute C.bits (expression f)).rmatch (bits C (before (plan n) xs)++C.bits (selector q))=answer f xs q
  have text : bits C (before (plan n) xs)++C.bits (selector q)=(word xs q).flatMap C.bits := by
    simp [bits,before,plan,word,letter,List.flatMap_append,List.flatMap_map,Function.comp_def,List.append_assoc]
  rw [text]
  apply Bool.eq_iff_iff.mpr
  rw [RegularExpression.rmatch_iff_matches',Code.reduction C hb]
  simp [DisjointnessDraft.answer]
end
end DisjointnessDraft.Streaming.Binary.Indexed
