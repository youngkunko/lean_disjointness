import DisjointnessDraft.Transfer.Compiler

/-! Ordered script outputs and probe bills on an arbitrary fixed target history. -/
namespace DisjointnessDraft.Transfer.Compiler
open DisjointnessFoundations CellProbe WordProgram MeasureTheory
open scoped ENNReal
noncomputable section
variable {F U Q A Ω : Type} {w : ℕ}
@[simp] theorem pure_run (x : X) (mem : Memory w) : (Pure.pure x : Op w X).run mem=(x,mem,0) := rfl

theorem script_append (D : Target F U Q A w Ω) (a : Ω) (idx : ℕ) (xs ys : List (Instr U Q)) (mem : Memory w) :
    (script D a idx (xs++ys)).run mem =
    let u := (script D a idx xs).run mem
    let v := (script D a (idx+xs.length) ys).run u.2.1
    (u.1++v.1,v.2.1,u.2.2+v.2.2) := by
  induction xs generalizing idx mem with
  | nil => simp [script]
  | cons x xs ih => simp [script,Program.run_bind,ih,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm]

theorem next_memory (D : Target F U Q A w Ω) (a : Ω) (f : F) (h : List (Instr U Q)) (op : Instr U Q) :
    (observed D a f (h++[op])).2.1 = ((targetStep D a h.length op).run (observed D a f h).2.1).2.1 := by
  simp [observed,script_append,script,Program.run_bind]

def total (D : Target F U Q A w Ω) (a : Ω) (f : F) (pre : List (Instr U Q)) : List (Instr U Q) → ℕ
  | [] => 0
  | x::xs => expense D a f pre x + total D a f (pre++[x]) xs

theorem actual_bill (D : Target F U Q A w Ω) (a : Ω) (f : F) (pre ops : List (Instr U Q)) :
    ((script D a pre.length ops).run (observed D a f pre).2.1).2.2 = total D a f pre ops := by
  induction ops generalizing pre with
  | nil => simp [script,total]
  | cons x xs ih =>
    have eq := ih (pre++[x])
    rw [next_memory] at eq
    simp only [List.length_append,List.length_singleton] at eq
    simp [script,total,expense,Program.run_bind,eq]

def OnPath (legal : F → List (Instr U Q) → Prop) (f : F) (pre ops : List (Instr U Q)) :=
  ∀ h, h <+: ops → legal f (pre++h)

private theorem head_ok (v : OnPath legal f pre (x::xs)) : legal f (pre++[x]) :=
  v _ ⟨xs,rfl⟩
private theorem tail_ok (v : OnPath legal f pre (x::xs)) : OnPath legal f (pre++[x]) xs := by
  rintro h ⟨rest,eq⟩
  simpa using v (x::h) ⟨rest,by simp [eq]⟩

theorem actual_answers [MeasurableSpace Ω] (μ : Measure Ω) (D : Target F U Q A w Ω) (a : Ω)
    (spec : F → List (Instr U Q) → Q → A) (g : Guarantees μ D legal spec tu tq)
    (f : F) (pre ops : List (Instr U Q)) (ok : OnPath legal f pre ops) :
    ((script D a pre.length ops).run (observed D a f pre).2.1).1=answers spec f pre ops := by
  induction ops generalizing pre with
  | nil => rfl
  | cons x xs ih =>
    have eq := ih (pre++[x]) (tail_ok ok)
    rw [next_memory] at eq
    simp only [List.length_append,List.length_singleton] at eq
    simp only [script,Program.run_bind,eq,pure_run]
    cases x with
    | inl u => simp [answers,targetStep,Program.run_bind]
    | inr q => simp [answers,targetStep,Program.run_bind,g.correct a f pre q (head_ok ok)]

theorem insertion_cost [MeasurableSpace Ω] (μ : Measure Ω) (D : Target F U Q A w Ω) (a : Ω)
    (g : Costs μ D legal tu tq) (f : F) (pre : List (Instr U Q)) (us : List U)
    (ok : OnPath legal f pre (us.map Sum.inl)) :
    total D a f pre (us.map Sum.inl) ≤ us.length*tu := by
  induction us generalizing pre with
  | nil => simp [total]
  | cons x xs ih =>
    have h := g.update a f pre x (head_ok ok)
    have b := ih (pre++[Sum.inl x]) (tail_ok ok)
    simp [total,Nat.add_mul]; omega

def chargeOp (tu : ℕ) (tq : ℝ) : Instr U Q → ℝ≥0∞
  | .inl _ => tu
  | .inr _ => ENNReal.ofReal tq

theorem final_cost [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (D : Target F U Q A w Ω) (g : Costs μ D legal tu tq)
    (f : F) (pre ops : List (Instr U Q)) (ok : OnPath legal f pre ops) :
    Measurable (fun a => total D a f pre ops) ∧
      (∫⁻ a, (total D a f pre ops:ℝ≥0∞) ∂μ) ≤ (ops.map (chargeOp tu tq)).sum := by
  induction ops generalizing pre with
  | nil => simp [total]
  | cons x xs ih =>
    obtain ⟨meas,paid⟩ := ih (pre++[x]) (tail_ok ok)
    have single := g.measurable f pre x (head_ok ok)
    have exp : (∫⁻ a, (expense D a f pre x:ℝ≥0∞) ∂μ) ≤ chargeOp tu tq x := by
      cases x with
      | inr q => exact g.query f pre q (head_ok ok)
      | inl u =>
        calc _ ≤ ∫⁻ (_ : Ω), (tu:ℝ≥0∞) ∂μ := lintegral_mono (fun a => by exact_mod_cast g.update a f pre u (head_ok ok))
             _ = _ := by simp [chargeOp]
    refine ⟨single.add meas,?_⟩
    simp only [total,Nat.cast_add,List.map_cons,List.sum_cons]
    have sm : Measurable (fun a => (expense D a f pre x : ℝ≥0∞)) :=
      (measurable_of_countable (fun j : ℕ => (j:ℝ≥0∞))).comp single
    rw [lintegral_add_left sm]
    exact add_le_add exp paid

theorem insertion_bill [MeasurableSpace Ω] (μ : Measure Ω) (D : Target F U Q A w Ω) (a : Ω)
    (g : Guarantees μ D legal spec tu tq) (f : F) (pre : List (Instr U Q)) (us : List U)
    (ok : OnPath legal f pre (us.map Sum.inl)) :
    total D a f pre (us.map Sum.inl) ≤ us.length*tu := insertion_cost μ D a g.costs f pre us ok

theorem final_bill [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (D : Target F U Q A w Ω) (g : Guarantees μ D legal spec tu tq)
    (f : F) (pre ops : List (Instr U Q)) (ok : OnPath legal f pre ops) :
    Measurable (fun a => total D a f pre ops) ∧
      (∫⁻ a, (total D a f pre ops:ℝ≥0∞) ∂μ) ≤ (ops.map (chargeOp tu tq)).sum :=
  final_cost μ D g.costs f pre ops ok

end
end DisjointnessDraft.Transfer.Compiler
