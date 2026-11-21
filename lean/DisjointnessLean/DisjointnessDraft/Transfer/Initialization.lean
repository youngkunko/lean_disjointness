import DisjointnessDraft.Transfer.Scripts

/-! A problem required to start empty can be initialized during source Phase I.
The setup contents depend on the family. Fixed setup length shifts the absolute
operation number in every subsequent invocation for every master tape. -/
namespace DisjointnessDraft.Transfer.Compiler
open DisjointnessFoundations CellProbe WordProgram MeasureTheory
open scoped ENNReal
noncomputable section
variable {F F' U Q A Ω : Type} {w : ℕ}

structure Initialization (F' F U Q : Type) where
  initial : F' → F
  steps : F' → List (Instr U Q)
  length : ℕ
  fixed : ∀ f,(steps f).length=length

def initialized (D : Target F U Q A w Ω) (I : Initialization F' F U Q) : Target F' U Q A w Ω where
  init a f := (observed D a (I.initial f) (I.steps f)).2.1
  update a t op := D.update a (I.length+t) op
  query a t op := D.query a (I.length+t) op

theorem shift_script (D : Target F U Q A w Ω) (I : Initialization F' F U Q) (a : Ω)
    (t : ℕ) (ops : List (Instr U Q)) :
    script (initialized D I) a t ops = script D a (I.length+t) ops := by
  induction ops generalizing t with
  | nil => rfl
  | cons op xs ih =>
    simp only [script,ih,Nat.add_assoc]
    cases op <;> rfl

theorem init_memory (D : Target F U Q A w Ω) (I : Initialization F' F U Q) (a : Ω) (f : F') (h : List (Instr U Q)) :
    (observed (initialized D I) a f h).2.1 = (observed D a (I.initial f) (I.steps f++h)).2.1 := by
  unfold observed
  rw [shift_script,script_append]
  simp only [Nat.add_zero,Nat.zero_add,I.fixed]; rfl

theorem init_expense (D : Target F U Q A w Ω) (I : Initialization F' F U Q) (a : Ω) (f : F') (h : List (Instr U Q)) (op : Instr U Q) :
    expense (initialized D I) a f h op=expense D a (I.initial f) (I.steps f++h) op := by
  unfold expense; rw [init_memory,List.length_append,I.fixed]; cases op <;> rfl

def initLegal (I : Initialization F' F U Q) (legal : F → List (Instr U Q) → Prop) (f : F') (h : List (Instr U Q)) :=
  legal (I.initial f) (I.steps f++h)

def initSpec (I : Initialization F' F U Q) (spec : F → List (Instr U Q) → Q → A) (f : F') (h : List (Instr U Q)) :=
  spec (I.initial f) (I.steps f++h)

theorem init_guarantees [MeasurableSpace Ω] (μ : Measure Ω) (D : Target F U Q A w Ω) (I : Initialization F' F U Q)
    {legal : F → List (Instr U Q) → Prop} {spec : F → List (Instr U Q) → Q → A} {tu : ℕ} {tq : ℝ}
    (H : Guarantees μ D legal spec tu tq) :
    Guarantees μ (initialized D I) (initLegal I legal) (initSpec I spec) tu tq := by
  constructor
  · intro a f h u ok; rw [init_expense]; apply H.update
    simpa only [initLegal,List.append_assoc] using ok
  · intro f h q ok; simp only [init_expense]; apply H.query
    simpa only [initLegal,List.append_assoc] using ok
  · intro a f h q ok; rw [init_memory]
    have g := H.correct a (I.initial f) (I.steps f++h) q (by simpa only [initLegal,List.append_assoc] using ok)
    simpa only [initSpec,initialized,List.length_append,I.fixed] using g
  · intro f h op ok; simp only [init_expense]; apply H.measurable
    simpa only [initLegal,List.append_assoc] using ok

end
end DisjointnessDraft.Transfer.Compiler
