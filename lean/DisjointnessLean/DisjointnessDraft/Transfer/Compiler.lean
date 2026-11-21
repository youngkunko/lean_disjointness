import DisjointnessDraft.Fresh
import DisjointnessFoundations.LogicalWordLayout
import DisjointnessFoundations.QueryWriteOverlay

/-! Fixed lists of target operations implement each source operation. The
answers may have any type and the target may begin in an arbitrarily
preprocessed static state. -/
namespace DisjointnessDraft.Transfer.Compiler
open DisjointnessFoundations CellProbe WordProgram MeasureTheory
open scoped ENNReal
noncomputable section

abbrev Instr (U Q : Type) := U ⊕ Q

structure Schedule (n : ℕ) (F U Q A : Type) where
  initial : Family n → F
  insert : Fin n → List U
  finish : Fin n → List (Instr U Q)
  decode : Fin n → List A → Bool

def before (S : Schedule n F U Q A) (xs : List (Fin n)) : List (Instr U Q) :=
  (xs.flatMap S.insert).map Sum.inl

def answers (spec : F → List (Instr U Q) → Q → A) (f : F) (pre : List (Instr U Q)) :
    List (Instr U Q) → List A
  | [] => []
  | .inl u :: ops => answers spec f (pre++[.inl u]) ops
  | .inr q :: ops => spec f pre q :: answers spec f (pre++[.inr q]) ops

def Valid (S : Schedule n F U Q A) (legal : F → List (Instr U Q) → Prop)
    (spec : F → List (Instr U Q) → Q → A) : Prop :=
  (∀ f xs q, xs.Nodup → ∀ h : List (Instr U Q), h <+: before S xs ++ S.finish q → legal (S.initial f) h) ∧
  (∀ f xs q, xs.Nodup →
    S.decode q (answers spec (S.initial f) (before S xs) (S.finish q))=DisjointnessDraft.answer f xs q)

structure Target (F U Q A : Type) (w : ℕ) (Ω : Type) where
  init : Ω → F → Memory w
  update : Ω → ℕ → U → Program (Word w) (Word w) Unit
  query : Ω → ℕ → Q → Program (Word w) (Word w) A

abbrev Op (w : ℕ) (A : Type) := Program (Word w) (Word w) A

def targetStep (D : Target F U Q A w Ω) (a : Ω) (idx : ℕ) : Instr U Q → Op w (Option A)
  | .inl u => D.update a idx u >>= fun _ => pure none
  | .inr q => D.query a idx q >>= fun v => pure (some v)

def script (D : Target F U Q A w Ω) (a : Ω) : ℕ → List (Instr U Q) → Op w (List A)
  | _,[] => pure []
  | idx,x::xs => do
    let v ← targetStep D a idx x
    let vs ← script D a (idx+1) xs
    pure (v.toList ++ vs)

def observed (D : Target F U Q A w Ω) (a : Ω) (f : F) (past : List (Instr U Q)) :=
  (script D a 0 past).run (D.init a f)

def expense (D : Target F U Q A w Ω) (a : Ω) (f : F) (hist : List (Instr U Q)) (op : Instr U Q) : ℕ :=
  ((targetStep D a hist.length op).run (observed D a f hist).2.1).2.2

structure Costs [MeasurableSpace Ω] (μ : Measure Ω) (D : Target F U Q A w Ω)
    (legal : F → List (Instr U Q) → Prop) (tu : ℕ) (tq : ℝ) : Prop where
  update : ∀ a f h u, legal f (h++[.inl u]) → expense D a f h (.inl u) ≤ tu
  query : ∀ f h q, legal f (h++[.inr q]) →
    (∫⁻ a, (expense D a f h (.inr q):ℝ≥0∞) ∂μ) ≤ ENNReal.ofReal tq
  measurable : ∀ f h op, legal f (h++[op]) → Measurable (fun a => expense D a f h op)

structure Guarantees [MeasurableSpace Ω] (μ : Measure Ω) (D : Target F U Q A w Ω)
    (legal : F → List (Instr U Q) → Prop) (spec : F → List (Instr U Q) → Q → A) (tu : ℕ) (tq : ℝ) : Prop where
  update : ∀ a f h u, legal f (h++[.inl u]) → expense D a f h (.inl u) ≤ tu
  query : ∀ f h q, legal f (h++[.inr q]) →
    (∫⁻ a, (expense D a f h (.inr q):ℝ≥0∞) ∂μ) ≤ ENNReal.ofReal tq
  correct : ∀ a f h q, legal f (h++[.inr q]) →
    ((D.query a h.length q).run (observed D a f h).2.1).1=spec f h q
  measurable : ∀ f h op, legal f (h++[op]) → Measurable (fun a => expense D a f h op)

theorem Guarantees.costs [MeasurableSpace Ω] {μ : Measure Ω} {D : Target F U Q A w Ω}
    (g : Guarantees μ D legal spec tu tq) : Costs μ D legal tu tq :=
  ⟨g.update,g.query,g.measurable⟩

end
end DisjointnessDraft.Transfer.Compiler
