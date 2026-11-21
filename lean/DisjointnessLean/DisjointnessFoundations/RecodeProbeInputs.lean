import DisjointnessFoundations.PrefixInsertionEmbedding
import DisjointnessFoundations.QueryWriteOverlay

namespace DisjointnessFoundations.InputReduction

open CellProbe Simulation MeasureTheory
open scoped ENNReal
noncomputable section

variable {w : ℕ} {F U Q F' U' Q' C Ω : Type}

structure Translation (F U Q F' U' Q' : Type) where
  preprocess : F → F'
  update : U → U'
  query : Q → Q'
  negate : Bool

def out (neg b : Bool) : Bool := if neg then !b else b

private theorem out_invol (neg b : Bool) : out neg (out neg b) = b := by
  cases neg <;> cases b <;> decide

def recode {S : Type} (neg : Bool) (step : S → QueryStep (Word w) (Word w) S) (s : S) :
    QueryStep (Word w) (Word w) S :=
  match step s with
  | .done b => .done (out neg b)
  | .read a k => .read a k

def mapped (A : Translation F U Q F' U' Q') (D : DataStructure w F' U' Q' C) : DataStructure w F U Q C where
  UState := D.UState
  QState := D.QState
  preprocess c f := D.preprocess c (A.preprocess f)
  startUpdate c u := D.startUpdate c (A.update u)
  updateStep := D.updateStep
  startQuery c q := D.startQuery c (A.query q)
  queryStep := recode A.negate D.queryStep

variable (A : Translation F U Q F' U' Q') (D : DataStructure w F' U' Q' C) (R : RandomTape Ω C)

theorem updates (a : Ω) (j : ℕ) (m : Memory w) (xs : List U) :
    insertAll (mapped A D) R a j m xs = insertAll D R a j m (xs.map A.update) := by
  induction xs generalizing j m with
  | nil => rfl
  | cons y ys ih =>
    simp only [insertAll,List.map_cons]
    change (insertOne D (R.insertion j a) (A.update y) m).bind _ = _
    cases insertOne D (R.insertion j a) (A.update y) m with
    | none => rfl
    | some p => obtain ⟨mem,c⟩ := p; simp [ih]

theorem prefix_eq (a : Ω) (f : F) (xs : List U) :
    prefixRun (mapped A D) R a f xs = prefixRun D R a (A.preprocess f) (xs.map A.update) := by
  unfold prefixRun
  exact updates A D R a 0 _ xs

theorem query_eq {S : Type} (step : S → QueryStep (Word w) (Word w) S) (neg : Bool)
    (m : Memory w) (i : ℕ) (s : S) :
    run (recode neg step) m i s =
      ⟨(run step m i s).probes,(run step m i s).answer.map (out neg)⟩ := by
  induction i generalizing s with
  | zero => cases h : step s <;> simp [run,recode,h]
  | succ n ih => cases h : step s <;> simp [run,recode,h,ih,Transcript.prepend]

private theorem finish_map {α β : Type} (f : ℕ → Option α) (g : α → β) :
    finish (fun n => (f n).map g) = (finish f).map g := by
  classical
  unfold finish
  simp only [Option.isSome_map']
  split <;> rfl

theorem final_eq (a : Ω) (f : F) (xs : List U) (q : Q) :
    finalRun (mapped A D) R a f xs q =
      (finalRun D R a (A.preprocess f) (xs.map A.update) (A.query q)).map (fun z => (out A.negate z.1,z.2)) := by
  unfold finalRun
  rw [prefix_eq]
  cases prefixRun D R a (A.preprocess f) (xs.map A.update) with
  | none => rfl
  | some p =>
    obtain ⟨m,c⟩ := p
    simp only [Option.bind_eq_bind,Option.some_bind]
    change finish (fun n => QueryNormalization.result (run (recode A.negate D.queryStep) m n
        (D.startQuery (R.query a) (A.query q)))) = _
    simp_rw [query_eq, QueryNormalization.result, Option.map_map]
    rw [←finish_map]
    simp_rw [Option.map_map]
    rfl

theorem cost_eq (a : Ω) (f : F) (xs : List U) (q : Q) :
    cost (finalRun (mapped A D) R a f xs q) = cost (finalRun D R a (A.preprocess f) (xs.map A.update) (A.query q)) := by
  rw [final_eq]
  cases finalRun D R a (A.preprocess f) (xs.map A.update) (A.query q) <;> rfl

private theorem event_eq (a : Ω) (f : F) (xs : List U) (q : Q) (b : Bool) :
    (finalRun (mapped A D) R a f xs q).map Prod.fst = some b ↔
      (finalRun D R a (A.preprocess f) (xs.map A.update) (A.query q)).map Prod.fst = some (out A.negate b) := by
  rw [final_eq]
  cases finalRun D R a (A.preprocess f) (xs.map A.update) (A.query q) with
  | none => simp
  | some p =>
    obtain ⟨z,c⟩ := p
    change some (out A.negate z) = some b ↔ some z = some (out A.negate b)
    simp only [Option.some.injEq]
    exact ⟨fun h => by rw [←h,out_invol],fun h => by rw [h,out_invol]⟩

theorem measurable [MeasurableSpace Ω] (hm : MeasurableRuns D R) : MeasurableRuns (mapped A D) R := by
  refine ⟨?_,?_,?_⟩
  · intro f xs; simp_rw [prefix_eq]; exact hm.1 _ _
  · intro f xs q; simp_rw [cost_eq]; exact hm.2.1 _ _ _
  · intro f xs q b
    have eq : {a | (finalRun (mapped A D) R a f xs q).map Prod.fst = some b} =
        {a | (finalRun D R a (A.preprocess f) (xs.map A.update) (A.query q)).map Prod.fst = some (out A.negate b)} :=
      Set.ext fun a => event_eq A D R a f xs q b
    rw [eq]
    exact hm.2.2 _ _ _ _

theorem error [MeasurableSpace Ω] (μ : Measure Ω) (spec : F → List U → Q → Bool)
    (spec' : F' → List U' → Q' → Bool) (δ : ℝ≥0∞)
    (consistent : ∀ f xs q, spec f xs q = out A.negate (spec' (A.preprocess f) (xs.map A.update) (A.query q)))
    (he : PointwiseError μ D R spec' δ) : PointwiseError μ (mapped A D) R spec δ := by
  intro f xs q
  have eq : {a | (finalRun (mapped A D) R a f xs q).map Prod.fst ≠ some (spec f xs q)} =
      {a | (finalRun D R a (A.preprocess f) (xs.map A.update) (A.query q)).map Prod.fst ≠ some (spec' (A.preprocess f) (xs.map A.update) (A.query q))} := by
    ext a
    simp only [Set.mem_setOf_eq, ne_eq, event_eq, consistent, out_invol]
  rw [eq]
  exact he _ _ _

theorem amortized [MeasurableSpace Ω] (μ : Measure Ω) (tu : ℝ≥0∞) (hu : AmortizedUpdate μ D R tu) :
    AmortizedUpdate μ (mapped A D) R tu := by
  intro f xs
  simp_rw [prefix_eq]
  simpa only [List.length_map] using hu (A.preprocess f) (xs.map A.update)

theorem worst (tu : ℝ≥0∞) (hu : WorstUpdate D R tu) : WorstUpdate (mapped A D) R tu := by
  intro a f xs
  obtain ⟨m,c,run,paid⟩ := hu a (A.preprocess f) (xs.map A.update)
  refine ⟨m,c,(prefix_eq A D R a f xs).trans run,fun x => ?_⟩
  simpa only [List.length_map] using paid (A.update x)

end
end DisjointnessFoundations.InputReduction
