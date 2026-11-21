import DisjointnessFoundations.UpdatePrefixAccounting
import Mathlib.MeasureTheory.Group.Arithmetic
import Mathlib.MeasureTheory.Constructions.BorelSpace.Real

namespace DisjointnessFoundations.Padding

open CellProbe ProtocolRun MeasureTheory
open scoped ENNReal BigOperators
noncomputable section
section Transport

variable {w : ℕ} {F E Q F' E' Q' Ω Coin : Type}

structure Embedding (F E Q F' E' Q' : Type) where
  family : F → F'
  element : E → E'
  index : Q → Q'
  leading : List E'

def tape (Ω : Type) : RandomTape Ω (ℕ × Ω) :=
  ⟨fun a => (0,a),fun j a => (j,a),fun a => (0,a)⟩

variable (A : Embedding F E Q F' E' Q') (D : DataStructure w F' E' Q' Coin)
  (R : RandomTape Ω Coin)

def pullback : DataStructure w F E Q (ℕ × Ω) where
  UState := D.UState
  QState := D.QState
  preprocess a f := afterPrefix D R a.2 (A.family f) A.leading
  startUpdate a x := D.startUpdate (R.insertion (A.leading.length+a.1) a.2) (A.element x)
  updateStep := D.updateStep
  startQuery a q := D.startQuery (R.query a.2) (A.index q)
  queryStep := D.queryStep

theorem insertAll_pullback (seed : Ω) (j : ℕ) (mem : Memory w) (xs : List E) :
    insertAll (pullback A D R) (tape Ω) seed j mem xs =
      insertAll D R seed (A.leading.length+j) mem (xs.map A.element) := by
  induction xs generalizing j mem with
  | nil => rfl
  | cons x xs ih =>
    simp only [insertAll,List.map_cons]
    change (insertOne D (R.insertion (A.leading.length+j) seed) (A.element x) mem).bind _ = _
    cases insertOne D (R.insertion (A.leading.length+j) seed) (A.element x) mem with
    | none => rfl
    | some z => obtain ⟨mid,c⟩ := z; simp [ih,Nat.add_assoc]

theorem prefix_compare {tu : ℝ≥0∞} (hu : WorstUpdate D R tu) (seed : Ω) (S : F) (xs : List E) :
    ∃ (mem : Memory w) (b c : ℕ),
      prefixRun D R seed (A.family S) A.leading =
        some (afterPrefix D R seed (A.family S) A.leading,b) ∧
      prefixRun (pullback A D R) (tape Ω) seed S xs = some (mem,c) ∧
      prefixRun D R seed (A.family S) (A.leading ++ xs.map A.element) = some (mem,b+c) := by
  obtain ⟨b,hb⟩ := prefix_ok D R hu seed (A.family S) A.leading
  obtain ⟨c,hc⟩ := suffix_ok D R hu seed (A.family S) A.leading (xs.map A.element)
  refine ⟨afterPrefix D R seed (A.family S) (A.leading ++ xs.map A.element),b,c,hb,?_,?_⟩
  · unfold prefixRun
    rw [insertAll_pullback, Nat.add_zero]
    exact hc
  · unfold prefixRun at hb ⊢
    rw [Chronogram.run_append,hb]
    simp [hc]

theorem final_compare {tu : ℝ≥0∞} (hu : WorstUpdate D R tu) (seed : Ω) (S : F) (xs : List E) (q : Q) :
    finalRun (pullback A D R) (tape Ω) seed S xs q =
      finalRun D R seed (A.family S) (A.leading ++ xs.map A.element) (A.index q) := by
  obtain ⟨m,b,c,_,hp,ht⟩ := prefix_compare A D R hu seed S xs
  rw [finalRun,hp,finalRun,ht]
  rfl

theorem worst_pullback {tu : ℝ≥0∞} (hu : WorstUpdate D R tu) :
    WorstUpdate (pullback A D R) (tape Ω) tu := by
  intro seed S xs
  obtain ⟨m,b,c,_,hp,ht⟩ := prefix_compare A D R hu seed S xs
  obtain ⟨m',cc,ht',pay⟩ := hu seed (A.family S) (A.leading ++ xs.map A.element)
  have mm := congrArg Prod.fst (Option.some.inj (ht'.symm.trans ht))
  change m' = m at mm
  subst m'
  refine ⟨m,c,hp,fun x => ?_⟩
  simpa only [List.length_append,List.length_map] using pay (A.element x)

theorem measurable_pullback [MeasurableSpace Ω] {tu : ℝ≥0∞} (hu : WorstUpdate D R tu)
    (h : MeasurableRuns D R) : MeasurableRuns (pullback A D R) (tape Ω) := by
  refine ⟨?_,?_,?_⟩
  · intro S xs
    have eq (a : Ω) : cost (prefixRun (pullback A D R) (tape Ω) a S xs) =
        cost (prefixRun D R a (A.family S) (A.leading ++ xs.map A.element)) -
        cost (prefixRun D R a (A.family S) A.leading) := by
      obtain ⟨m,b,c,hb,hp,ht⟩ := prefix_compare A D R hu a S xs
      rw [hp,ht,hb]
      simp [cost,ENNReal.add_sub_cancel_left]
    simp_rw [eq]
    exact (h.1 _ _).sub (h.1 _ _)
  · intro S xs q
    simp_rw [final_compare A D R hu]
    exact h.2.1 _ _ _
  · intro S xs q b
    simp_rw [final_compare A D R hu]
    exact h.2.2 _ _ _ _

theorem error_pullback [MeasurableSpace Ω] (μ : Measure Ω) {tu δ : ℝ≥0∞} (hu : WorstUpdate D R tu)
    (spec : F → List E → Q → Bool) (spec' : F' → List E' → Q' → Bool)
    (agree : ∀ S xs q, spec' (A.family S) (A.leading ++ xs.map A.element) (A.index q) = spec S xs q)
    (h : PointwiseError μ D R spec' δ) : PointwiseError μ (pullback A D R) (tape Ω) spec δ := by
  intro S xs q
  simpa only [agree,final_compare A D R hu] using h (A.family S) (A.leading ++ xs.map A.element) (A.index q)

end Transport
end
end DisjointnessFoundations.Padding
