import DisjointnessDraft.Transfer.Initialization
import DisjointnessDraft.Transfer.Relational

namespace DisjointnessDraft.Transfer.Compiler
open DisjointnessFoundations CellProbe WordProgram MeasureTheory
open scoped ENNReal
noncomputable section

theorem init_rel [MeasurableSpace Ω] (μ : Measure Ω) (D : Target F U Q A w Ω) (I : Initialization F' F U Q)
    {legal : F → List (Instr U Q) → Prop} {rel : F → List (Instr U Q) → Q → A → Prop} {tu : ℕ} {tq : ℝ}
    (H : RelGuarantees μ D legal rel tu tq) :
    RelGuarantees μ (initialized D I) (initLegal I legal) (fun f h => rel (I.initial f) (I.steps f++h)) tu tq := by
  refine ⟨⟨?_,?_,?_⟩,?_⟩
  · intro a f h u ok; rw [init_expense]; apply H.update
    simpa only [initLegal,List.append_assoc] using ok
  · intro f h q ok; simp only [init_expense]; apply H.query
    simpa only [initLegal,List.append_assoc] using ok
  · intro f h op ok; simp only [init_expense]; apply H.measurable
    simpa only [initLegal,List.append_assoc] using ok
  · intro a f h q ok; rw [init_memory]
    have g := H.correct a (I.initial f) (I.steps f++h) q (by simpa only [initLegal,List.append_assoc] using ok)
    simpa only [initialized,List.length_append,I.fixed] using g

end
end DisjointnessDraft.Transfer.Compiler
