import DisjointnessDraft.Transfer.RelInitialization

/-! Variable-length uncharged preprocessing on a target which must start empty.
One separate word stores the initial operation number; its read is charged
on each target invocation, including the final query. -/
namespace DisjointnessDraft.Transfer.Compiler
open DisjointnessFoundations CellProbe WordProgram MeasureTheory
open scoped ENNReal
noncomputable section
open Classical

variable {F F' U Q A Ω : Type} {w v : ℕ}
structure Setup (F' F U Q : Type) where
  initial : F' → F
  steps : F' → List (Instr U Q)

variable (L : Layout w v) (I : Setup F' F U Q) (D : Target F U Q A w Ω)
def shifted : Target F' U Q A v Ω where
  init a f := image L (I.steps f).length (observed D a (I.initial f) (I.steps f)).2.1
  update a t u := do let k ← Program.load L.clock; liftWord L (D.update a (k.val+t) u)
  query a t q := do let k ← Program.load L.clock; liftWord L (D.query a (k.val+t) q)

theorem shifted_step (a : Ω) (t off : ℕ) (m : Memory w) (op : Instr U Q) (room : off<2^v) :
    ((targetStep (shifted L I D) a t op).run (image L off m)) =
    let z := (targetStep D a (off+t) op).run m
    (z.1,image L off z.2.1,z.2.2+1) := by
  cases op <;> simp [targetStep,shifted,Program.run_bind,Program.run_load,lift_run,
    show image L off m L.clock=stamp v off by simp [image],stamp,Nat.mod_eq_of_lt room,Nat.add_comm]

theorem shifted_hist (a : Ω) (f : F') (h : List (Instr U Q)) (room : (I.steps f).length<2^v) :
    (observed (shifted L I D) a f h).2.1 =
      image L (I.steps f).length (observed D a (I.initial f) (I.steps f++h)).2.1 := by
  induction h using List.reverseRecOn with
  | nil => simp [observed,shifted,script]
  | append_singleton xs op ih =>
    rw [next_memory,ih,shifted_step L I D a _ _ _ op room,←List.append_assoc,next_memory,List.length_append]

theorem shifted_expense (a : Ω) (f : F') (h : List (Instr U Q)) (op : Instr U Q) (room : (I.steps f).length<2^v) :
    expense (shifted L I D) a f h op=expense D a (I.initial f) (I.steps f++h) op+1 := by
  unfold expense; rw [shifted_hist L I D _ _ _ room,shifted_step L I D _ _ _ _ _ room,List.length_append]

def setupLegal (I : Setup F' F U Q) (legal : F → List (Instr U Q) → Prop) (f : F') (h : List (Instr U Q)) :=
  legal (I.initial f) (I.steps f++h)
def setupSpec (I : Setup F' F U Q) (spec : F → List (Instr U Q) → Q → A) (f : F') (h : List (Instr U Q)) :=
  spec (I.initial f) (I.steps f++h)

theorem shifted_guarantees [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    {legal : F → List (Instr U Q) → Prop} {spec : F → List (Instr U Q) → Q → A} {tu : ℕ} {tq : ℝ}
    (qp : 0≤tq) (room : ∀ f,(I.steps f).length<2^v) (H : Guarantees μ D legal spec tu tq) :
    Guarantees μ (shifted L I D) (setupLegal I legal) (setupSpec I spec) (tu+1) (tq+1) := by
  constructor
  · intro a f h u ok; rw [shifted_expense L I D _ _ _ _ (room f)]
    exact Nat.add_le_add_right (H.update a _ _ _ (by simpa only [setupLegal,List.append_assoc] using ok)) 1
  · intro f h q ok
    have ok' : legal (I.initial f) ((I.steps f++h)++[.inr q]) := by simpa only [setupLegal,List.append_assoc] using ok
    have m := (measurable_of_countable (fun z : ℕ => (z:ℝ≥0∞))).comp (H.measurable _ _ _ ok')
    simp only [shifted_expense L I D _ _ _ _ (room f),Nat.cast_add,Nat.cast_one]
    change Measurable (fun a : Ω => (expense D a (I.initial f) (I.steps f++h) (.inr q) : ℝ≥0∞)) at m
    rw [lintegral_add_left m,lintegral_const,measure_univ,mul_one,ENNReal.ofReal_add qp (by norm_num)]
    simpa using add_le_add_right (H.query _ _ _ ok') 1
  · intro a f h q ok
    rw [shifted_hist L I D _ _ _ (room f)]
    simp only [shifted,Program.run_bind,Program.run_load,
      show ∀ m,image L (I.steps f).length m L.clock=stamp v (I.steps f).length by intro m; simp [image],
      stamp,Nat.mod_eq_of_lt (room f),lift_run]
    have g := H.correct a (I.initial f) (I.steps f++h) q (by simpa only [setupLegal,List.append_assoc] using ok)
    simpa only [setupSpec,List.length_append] using g
  · intro f h op ok
    simp only [shifted_expense L I D _ _ _ _ (room f)]
    exact (H.measurable _ _ _ (by simpa only [setupLegal,List.append_assoc] using ok)).add measurable_const

end
end DisjointnessDraft.Transfer.Compiler
