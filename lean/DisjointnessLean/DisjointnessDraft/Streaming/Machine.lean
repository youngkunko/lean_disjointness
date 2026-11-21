import DisjointnessDraft.Model
import DisjointnessDraft.Streaming.Language
import DisjointnessFoundations.QueryWriteOverlay
import DisjointnessFoundations.PrefixInsertionEmbedding

/-! A streaming symbol has one transition engine with a Boolean report and
physical reads and writes. Its intermediate history keeps the resulting
memory. Its last symbol is read-only normalized at the original probe cost. -/
namespace DisjointnessDraft.Streaming
open DisjointnessFoundations CellProbe QueryNormalization MeasureTheory
open scoped ENNReal
noncomputable section

structure Engine (n m w : ℕ) (C : Type) where
  State : Type
  preprocess : C → Expr n m → Memory w
  start : C → Symbol n m → State
  step : State → Step (Word w) State

def forgetReport (step : S → Step W S) (s : S) : UpdateStep W S :=
  match step s with
  | .done _ => .done
  | .read a k => .read a k
  | .write a v k => .write a v k

variable {n w : ℕ} {C Ω : Type}

def process (E : Engine n n w C) : DataStructure w (Family n) (Symbol n n) (Symbol n n) C where
  UState := E.State
  QState := E.State × Local w
  preprocess coin f := E.preprocess coin (expression f)
  startUpdate := E.start
  updateStep := forgetReport E.step
  startQuery c x := (E.start c x,fun _ => none)
  queryStep := compile E.step

def reports (f : Family n) (xs : List (Symbol n n)) (x : Symbol n n) : Bool :=
  (expression f).rmatch (xs ++ [x])

def DataBound (E : Engine n n w C) (R : RandomTape Ω C) (ta : ℕ) : Prop :=
  ∀ seed (f : Family n) (xs : List (Symbol n n)) mem k,
    prefixRun (process E) R seed f xs = some (mem,k) →
    ∀ x : Fin n, cost (insertOne (process E) (R.insertion xs.length seed) (datum x) mem) ≤ ta

def SelectorBound [MeasurableSpace Ω] (μ : Measure Ω) (E : Engine n n w C)
    (R : RandomTape Ω C) (tc : ℝ) : Prop :=
  ∀ (f : Family n) (xs : List (Symbol n n)) (q : Fin n),
    (∫⁻ seed, cost (finalRun (process E) R seed f xs (selector q)) ∂μ) ≤ ENNReal.ofReal tc

def embedding (n : ℕ) :
    Padding.Embedding (Family n) (Fin n) (Fin n) (Family n) (Symbol n n) (Symbol n n) :=
  ⟨id,datum,selector,[marker]⟩

private theorem termination (E : Engine n n w C) (R : RandomTape Ω C)
    (correct : ZeroError (process E) R reports) : WorstUpdate (process E) R ⊤ := by
  intro seed f xs
  have ok := correct seed f xs marker
  cases h : prefixRun (process E) R seed f xs with
  | none => simp [finalRun,h] at ok
  | some v => exact ⟨v.1,v.2,rfl,fun _ => le_top⟩

theorem transfer [MeasurableSpace Ω] (μ : Measure Ω) (E : Engine n n w C) (R : RandomTape Ω C)
    (ta : ℕ) (tc : ℝ) (meas : MeasurableRuns (process E) R)
    (correct : ZeroError (process E) R reports) (data : DataBound E R ta) (sel : SelectorBound μ E R tc) :
    ∃ A : Machine n w (ℕ × Ω), MeasurableRuns A (Padding.tape Ω) ∧
      ZeroError A (Padding.tape Ω) answer ∧ WorstUpdate A (Padding.tape Ω) (ta:ℝ≥0∞) ∧
      QueryBound μ A (Padding.tape Ω) tc := by
  let T := embedding n
  let D := process E
  have total := termination E R correct
  let A := Padding.pullback T D R
  refine ⟨A,Padding.measurable_pullback T D R total meas,?_,?_,?_⟩
  · intro seed f xs q
    rw [Padding.final_compare T D R total,correct]
    apply congrArg some
    apply Bool.eq_iff_iff.mpr
    change (expression f).rmatch (word xs q) ↔ decide (∀ x ∈ xs, x ∉ f q) = true
    rw [RegularExpression.rmatch_iff_matches',reduction,decide_eq_true_eq]
  · intro seed f xs
    obtain ⟨mem,b,c,_,h,hh⟩ := Padding.prefix_compare T D R total seed f xs
    refine ⟨mem,c,h,fun x => ?_⟩
    have bound := data seed f (T.leading ++ xs.map T.element) mem (b+c) hh x
    simpa only [List.length_append,List.length_map] using bound
  · intro f xs q
    change (∫⁻ a, cost (finalRun (Padding.pullback T D R) (Padding.tape Ω) a f xs q) ∂μ) ≤ _
    simp_rw [Padding.final_compare T D R total]
    exact sel f (T.leading ++ xs.map T.element) q

/-- The last reported bit and probe count are the original read/write
computation's, at every truncation depth, including every write it performs. -/
theorem final_symbol (E : Engine n n w C) (coin : C) (x : Symbol n n) (mem : Memory w) (fuel : ℕ) :
    result (Simulation.run (process E).queryStep mem fuel ((process E).startQuery coin x)) =
      QueryNormalization.run E.step fuel (E.start coin x) mem :=
  QueryNormalization.correct E.step mem fuel (E.start coin x) (fun _ => none)

end
end DisjointnessDraft.Streaming
