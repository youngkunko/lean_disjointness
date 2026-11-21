import DisjointnessFoundations.ProbeMachineInterface

namespace DisjointnessFoundations.QueryNormalization

open CellProbe Simulation

variable {w : ℕ} {S F E I C Ω : Type}

inductive Step (W S : Type) where
  | done (b : Bool)
  | read (addr : W) (next : W → S)
  | write (addr value : W) (next : S)

def run (step : S → Step (Word w) S) : ℕ → S → Memory w → Option (Bool × ℕ)
  | n, s, m =>
    match step s with
    | .done b => some (b,0)
    | .read a k => match n with
      | 0 => none
      | n+1 => (run step n (k (m a)) m).map (fun (b,c) => (b,c+1))
    | .write a v k => match n with
      | 0 => none
      | n+1 => (run step n k (Function.update m a v)).map (fun (b,c) => (b,c+1))

abbrev Local (w : ℕ) := Word w → Option (Word w)

/-- A physical read is charged even when its value is overridden, and
a write is simulated by a charged read whose value is ignored. -/
def compile (step : S → Step (Word w) S) (s : S × Local w) : QueryStep (Word w) (Word w) (S × Local w) :=
  match step s.1 with
  | .done b => .done b
  | .read a k => .read a (fun v => (k ((s.2 a).getD v),s.2))
  | .write a v k => .read a (fun _ => (k,Function.update s.2 a (some v)))

def contents (m : Memory w) (localWrites : Local w) : Memory w :=
  fun a => (localWrites a).getD (m a)

theorem write_contents (m : Memory w) (p : Local w) (a v : Word w) :
    contents m (Function.update p a (some v)) = Function.update (contents m p) a v := by
  funext i
  by_cases h : i=a
  · subst i; simp [contents]
  · simp [contents,Function.update_of_ne h]

def result (t : Transcript (Word w) (Word w)) : Option (Bool × ℕ) :=
  t.answer.map (fun b => (b,t.probes.length))

private theorem result_prepend (a v : Word w) (t : Transcript (Word w) (Word w)) :
    result (t.prepend a v) = (result t).map (fun (b,c) => (b,c+1)) := by
  cases t with
  | mk l ans => cases ans <;> simp [Transcript.prepend,result,Nat.add_comm]

theorem correct (step : S → Step (Word w) S) (m : Memory w) (fuel : ℕ) (s : S) (p : Local w) :
    result (Simulation.run (compile step) m fuel (s,p)) = run step fuel s (contents m p) := by
  induction fuel generalizing s p with
  | zero => cases h : step s <;> simp [Simulation.run,compile,h,run,result]
  | succ n ih =>
    cases h : step s with
    | done b => simp [Simulation.run,compile,h,run,result]
    | read a k =>
      rw [Simulation.run,compile,h,run,h]
      rw [result_prepend,ih]
      rfl
    | write a v k =>
      rw [Simulation.run,compile,h,run,h]
      rw [result_prepend,ih,write_contents]

def algorithm (updates : DataStructure w F E I C) (start : C → I → S) (step : S → Step (Word w) S) :
    DataStructure w F E I C where
  UState := updates.UState
  QState := S × Local w
  preprocess := updates.preprocess
  startUpdate := updates.startUpdate
  updateStep := updates.updateStep
  startQuery c i := (start c i,fun _ => none)
  queryStep := compile step

noncomputable def finalRW (updates : DataStructure w F E I C) (R : RandomTape Ω C)
    (start : C → I → S) (step : S → Step (Word w) S) (a : Ω) (f : F) (xs : List E) (q : I) :
    Option (Bool × ℕ) := do
  let (m,_) ← prefixRun updates R a f xs
  finish (fun n => run step n (start (R.query a) q) m)

theorem final_eq (updates : DataStructure w F E I C) (R : RandomTape Ω C)
    (start : C → I → S) (step : S → Step (Word w) S) (a : Ω) (f : F) (xs : List E) (q : I) :
    finalRun (algorithm updates start step) R a f xs q = finalRW updates R start step a f xs q := by
  have ins : ∀ (ys : List E) (j : ℕ) (m : Memory w),
      insertAll (algorithm updates start step) R a j m ys = insertAll updates R a j m ys := by
    intro ys j m
    induction ys generalizing j m with
    | nil => rfl
    | cons y ys ih =>
      simp only [insertAll]
      have h : insertOne (algorithm updates start step) (R.insertion j a) y m =
          insertOne updates (R.insertion j a) y m := rfl
      rw [h]
      cases insertOne updates (R.insertion j a) y m <;> simp [ih]
  unfold finalRun finalRW
  have pre : prefixRun (algorithm updates start step) R a f xs = prefixRun updates R a f xs := by
    unfold prefixRun
    exact ins _ _ _
  rw [pre]
  cases h : prefixRun updates R a f xs with
  | none => rfl
  | some z =>
    obtain ⟨m,c⟩ := z
    change finish (fun n => result (Simulation.run (compile step) m n (start (R.query a) q,fun _ => none))) = _
    simp_rw [correct]
    rfl

end DisjointnessFoundations.QueryNormalization
