import DisjointnessFoundations.QueryTraceInterpreter
import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Mathlib.Data.Finset.Basic

namespace DisjointnessFoundations.CellProbe

open MeasureTheory
open scoped ENNReal

abbrev Word (w : ℕ) := Fin (2^w)
abbrev Memory (w : ℕ) := Word w → Word w

inductive UpdateStep (W State : Type) where
  | done
  | read (a : W) (next : W → State)
  | write (a value : W) (next : State)

def updateRun {w : ℕ} {State : Type} (step : State → UpdateStep (Word w) State) :
    ℕ → State → Memory w → Option (Memory w × ℕ)
  | fuel,s,mem => match step s with
    | .done => some (mem,0)
    | .read a next => match fuel with
      | 0 => none
      | n+1 => (updateRun step n (next (mem a)) mem).map (fun (m,c) => (m,c+1))
    | .write a v next => match fuel with
      | 0 => none
      | n+1 => (updateRun step n next (Function.update mem a v)).map (fun (m,c) => (m,c+1))

theorem updateRun_mono {w : ℕ} {State : Type} (step : State → UpdateStep (Word w) State)
    {lo hi : ℕ} (hle : lo ≤ hi) (s : State) (mem : Memory w) {result}
    (hr : updateRun step lo s mem = some result) : updateRun step hi s mem = some result := by
  induction lo generalizing hi s mem result with
  | zero =>
    cases eq : step s with
    | done =>
      rw [updateRun,eq] at hr ⊢
      exact hr
    | read a k => rw [updateRun,eq] at hr; contradiction
    | write a v k => rw [updateRun,eq] at hr; contradiction
  | succ n ih =>
    obtain ⟨j,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (show hi ≠ 0 by omega)
    have nj : n ≤ j := Nat.le_of_succ_le_succ hle
    cases eq : step s with
    | done => rw [updateRun,eq] at hr ⊢; exact hr
    | read a k =>
      rw [updateRun,eq] at hr ⊢
      obtain ⟨p,hp,hresult⟩ := Option.map_eq_some_iff.mp hr
      exact Option.map_eq_some_iff.mpr ⟨p,ih nj _ _ hp,hresult⟩
    | write a v k =>
      rw [updateRun,eq] at hr ⊢
      obtain ⟨p,hp,hresult⟩ := Option.map_eq_some_iff.mp hr
      exact Option.map_eq_some_iff.mpr ⟨p,ih nj _ _ hp,hresult⟩

/-- Use the first successful fuel, or report nontermination when no fuel succeeds. -/
noncomputable def finish {α : Type*} (f : ℕ → Option α) : Option α := by
  classical
  exact if h : ∃ n, (f n).isSome then f (Nat.find h) else none

theorem finish_eq_some {α : Type*} (f : ℕ → Option α)
    (mono : ∀ {a b v}, a ≤ b → f a = some v → f b = some v)
    {n v} (h : f n = some v) : finish f = some v := by
  classical
  have has : ∃ j, (f j).isSome := ⟨n,by simp [h]⟩
  have isSome := Nat.find_spec has
  have le := Nat.find_min' has (show (f n).isSome by simp [h])
  unfold finish
  rw [dif_pos has]
  cases e : f (Nat.find has) with
  | none => simp [e] at isSome
  | some val => exact (mono le e).symm.trans h

structure RandomTape (Ω Coin : Type) where
  preprocess : Ω → Coin
  insertion : ℕ → Ω → Coin
  query : Ω → Coin

structure DataStructure (w : ℕ) (Family Element Index Coin : Type) where
  UState : Type
  QState : Type
  preprocess : Coin → Family → Memory w
  startUpdate : Coin → Element → UState
  updateStep : UState → UpdateStep (Word w) UState
  startQuery : Coin → Index → QState
  queryStep : QState → Simulation.QueryStep (Word w) (Word w) QState

variable {w : ℕ} {Family Element Index Coin Ω : Type}

noncomputable def insertOne (D : DataStructure w Family Element Index Coin)
    (coin : Coin) (x : Element) (mem : Memory w) : Option (Memory w × ℕ) :=
  finish fun fuel => updateRun D.updateStep fuel (D.startUpdate coin x) mem

noncomputable def insertAll (D : DataStructure w Family Element Index Coin) (R : RandomTape Ω Coin)
    (seed : Ω) : ℕ → Memory w → List Element → Option (Memory w × ℕ)
  | _, mem, [] => some (mem,0)
  | t, mem, x :: xs => do
    let (mem',c) ← insertOne D (R.insertion t seed) x mem
    let (last,d) ← insertAll D R seed (t+1) mem' xs
    pure (last,c+d)

noncomputable def prefixRun (D : DataStructure w Family Element Index Coin)
    (R : RandomTape Ω Coin) (seed : Ω) (S : Family) (xs : List Element) :
    Option (Memory w × ℕ) :=
  insertAll D R seed 0 (D.preprocess (R.preprocess seed) S) xs

noncomputable def finalRun (D : DataStructure w Family Element Index Coin)
    (R : RandomTape Ω Coin) (seed : Ω) (S : Family) (xs : List Element) (q : Index) :
    Option (Bool × ℕ) := do
  let (mem,_) ← prefixRun D R seed S xs
  finish fun fuel =>
    let tr := Simulation.run D.queryStep mem fuel (D.startQuery (R.query seed) q)
    tr.answer.map fun b => (b,tr.probes.length)

def cost {A : Type*} : Option (A × ℕ) → ℝ≥0∞
  | none => ⊤
  | some (_,n) => n

def WorstUpdate (D : DataStructure w Family Element Index Coin) (R : RandomTape Ω Coin)
    (tu : ℝ≥0∞) : Prop :=
  ∀ a S xs, ∃ mem c, prefixRun D R a S xs = some (mem,c) ∧
    ∀ x, cost (insertOne D (R.insertion xs.length a) x mem) ≤ tu

def AmortizedUpdate [MeasurableSpace Ω] (μ : Measure Ω)
    (D : DataStructure w Family Element Index Coin) (R : RandomTape Ω Coin) (tu : ℝ≥0∞) : Prop :=
  ∀ S xs, (∫⁻ a, cost (prefixRun D R a S xs) ∂μ) ≤ xs.length * tu

def PointwiseError [MeasurableSpace Ω] (μ : Measure Ω)
    (D : DataStructure w Family Element Index Coin) (R : RandomTape Ω Coin)
    (spec : Family → List Element → Index → Bool) (δ : ℝ≥0∞) : Prop :=
  ∀ S xs q, μ {a | (finalRun D R a S xs q).map Prod.fst ≠ some (spec S xs q)} ≤ δ

def MeasurableRuns [MeasurableSpace Ω]
    (D : DataStructure w Family Element Index Coin) (R : RandomTape Ω Coin) : Prop :=
  (∀ S xs, Measurable fun a => cost (prefixRun D R a S xs)) ∧
  (∀ S xs q, Measurable fun a => cost (finalRun D R a S xs q)) ∧
  (∀ S xs q b, MeasurableSet {a | (finalRun D R a S xs q).map Prod.fst = some b})

end DisjointnessFoundations.CellProbe
