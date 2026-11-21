import DisjointnessDraft.Transfer.Auxiliary

/-! Physical histories produced by the controller. The target's operation
ordinal and argument list may vary with the preprocessed family and every
earlier source insertion. Query writes go to temporary memory. -/
namespace DisjointnessDraft.Transfer.Auxiliary
open DisjointnessFoundations CellProbe WordProgram Compiler QueryNormalization Classical
open Streaming.Binary (stepWord memory_and_cost bit_report)
noncomputable section

structure Stage (w : ℕ) (U Q : Type) where
  auxiliary : Memory w
  history : List (Instr U Q)
variable (C : Controller n w F U Q A) (D : Compiler.Target F U Q A w Ω)
def advance (s : Stage w U Q) (x : Fin n) : Stage w U Q :=
  let z := (C.insert x).run s.auxiliary
  ⟨z.2.1,s.history++z.1.2.map Sum.inl⟩
def stage (f : Family n) (xs : List (Fin n)) : Stage w U Q :=
  xs.foldl (advance C) ⟨C.auxiliary f,[]⟩
@[simp] theorem stage_snoc (f : Family n) (xs : List (Fin n)) (x : Fin n) :
    stage C f (xs++[x])=advance C (stage C f xs) x := by simp [stage,List.foldl_append]

def machine : Machine n (w+1) Ω where
  UState := Op (w+1) Bool
  QState := Op (w+1) Bool × Local (w+1)
  preprocess a f := image (D.init a (C.initial f)) (C.auxiliary f)
  startUpdate := update C D
  updateStep := Streaming.forgetReport stepWord
  startQuery a q := (query C D a q,fun _ => none)
  queryStep := compile stepWord

theorem physical_update (a : Ω) (x : Fin n) (m aux : Memory w) :
    let s := (C.insert x).run aux
    let z := (script D a s.1.1 (s.1.2.map Sum.inl)).run m
    insertOne (machine C D) a x (image m aux) = some (image z.2.1 s.2.1,s.2.2+z.2.2) := by
  have bound := memory_and_cost (update C D a x) (image m aux)
  have result := finish_eq_some _ (fun le ok => updateRun_mono _ le _ _ ok) bound
  change finish (fun k => updateRun (Streaming.forgetReport stepWord) k (update C D a x) _) = _
  rw [result,update_run]

theorem physical_query (a : Ω) (q : Fin n) (m aux : Memory w) :
    let s := (C.finish q).run aux
    let z := (script D a s.1.1 s.1.2.1).run m
    let M := machine C D
    finish (fun k => result (Simulation.run M.queryStep (image m aux) k (M.startQuery a q))) =
      some (s.1.2.2 z.1,s.2.2+z.2.2) := by
  let M := machine C D
  let op := query C D a q
  let mem := image m aux
  let z := op.run mem
  let kernel := fun k => result (Simulation.run M.queryStep mem k (M.startQuery a q))
  have done : kernel z.2.2=some (z.1,z.2.2) :=
    (QueryNormalization.correct _ _ _ _ (fun _ => none)).trans (bit_report op mem)
  have stable {l h : ℕ} {r : Bool×ℕ} (le : l≤h) (ok : kernel l=some r) : kernel h=some r := by
    obtain ⟨b,hb,_⟩ := Option.map_eq_some_iff.mp ok
    unfold kernel
    rw [VerifiedEpoch.run_stable M.queryStep mem l (M.startQuery a q) b hb h
      ((VerifiedEpoch.run_length_le _ _ _ _).trans le)]
    exact ok
  change finish kernel=_
  rw [finish_eq_some kernel stable done]
  simp [z,op,mem,query_run]

def represented (a : Ω) (f : Family n) (s : Stage w U Q) :=
  image (observed D a (C.initial f) s.history).2.1 s.auxiliary

theorem physical_history
    (idx : ∀ f xs x,(xs++[x]).Nodup →
       ((C.insert x).run (stage C f xs).auxiliary).1.1=(stage C f xs).history.length)
    (a : Ω) (f : Family n) (xs : List (Fin n)) (nd : xs.Nodup) :
    ∃ t,prefixRun (machine C D) (tape Ω) a f xs=some (represented C D a f (stage C f xs),t) := by
  induction xs using List.reverseRecOn with
  | nil => exact ⟨0,rfl⟩
  | append_singleton xs x ih =>
    obtain ⟨t,pre⟩ := ih (List.nodup_append.mp nd).1
    let st := stage C f xs
    let data := (C.insert x).run st.auxiliary
    have ex := physical_update C D a x (observed D a (C.initial f) st.history).2.1 st.auxiliary
    dsimp only at ex
    rw [idx f xs x nd] at ex
    have next := SingleSelector.snoc (machine C D) (tape Ω) a f xs x _ _ _ _ pre ex
    refine ⟨t+(data.2.2+((script D a st.history.length (data.1.2.map Sum.inl)).run
      (observed D a (C.initial f) st.history).2.1).2.2),?_⟩
    simpa only [represented,stage_snoc,advance,observed,script_append,st,data,Nat.zero_add] using next


/-- The controller supplies initialization and insertions. The query uses
`queryCode` in place of `C.finish`. It reads both address ranges and keeps
its writes local to the query. -/
def interleavedMachine (queryCode : Fin n → QueryProgram w U Q A) (budget : ℕ) : Machine n (w+1) Ω :=
  {machine C D with
    startQuery := fun a q => (encode (QueryProgram.physical D a (queryCode q) budget),fun _ => none)}

theorem interleavedPrefix (queryCode : Fin n → QueryProgram w U Q A) (budget : ℕ)
    (a : Ω) (f : Family n) (xs : List (Fin n)) :
    prefixRun (interleavedMachine C D queryCode budget) (tape Ω) a f xs =
      prefixRun (machine C D) (tape Ω) a f xs := by
  let M := interleavedMachine C D queryCode budget
  have same (j : ℕ) (mem : Memory (w+1)) (us : List (Fin n)) :
      insertAll M (tape Ω) a j mem us = insertAll (machine C D) (tape Ω) a j mem us := by
    induction us generalizing j mem with
    | nil => rfl
    | cons x xs ih =>
      simp only [insertAll]
      change (insertOne (machine C D) _ x mem).bind _ = (insertOne (machine C D) _ x mem).bind _
      cases insertOne (machine C D) ((tape Ω).insertion j a) x mem with
      | none => rfl
      | some z => obtain ⟨next,c⟩ := z; simp [ih]
  exact same 0 _ xs

theorem interleavedQuery (queryCode : Fin n → QueryProgram w U Q A) (budget : ℕ)
    (idx : ∀ f xs x,(xs++[x]).Nodup →
       ((C.insert x).run (stage C f xs).auxiliary).1.1=(stage C f xs).history.length)
    (a : Ω) (f : Family n) (xs : List (Fin n)) (q : Fin n) (nd : xs.Nodup)
    (indices : (QueryProgram.inspect (QueryProgram.observedAnswer D a) (C.initial f)
       (queryCode q) (stage C f xs).history (stage C f xs).auxiliary).ordinalsCorrect)
    (bound : (QueryProgram.inspect (QueryProgram.observedAnswer D a) (C.initial f)
       (queryCode q) (stage C f xs).history (stage C f xs).auxiliary).probes≤budget) :
    let s := stage C f xs
    let v := QueryProgram.inspect (QueryProgram.observedAnswer D a) (C.initial f) (queryCode q) s.history s.auxiliary
    finalRun (interleavedMachine C D queryCode budget) (tape Ω) a f xs q =
      some (v.answer,budget+total D a (C.initial f) s.history v.operations) := by
  let s := stage C f xs
  let M := interleavedMachine C D queryCode budget
  let op := encode (QueryProgram.physical D a (queryCode q) budget)
  let mem := represented C D a f s
  let z := op.run mem
  let kernel := fun k => result (Simulation.run M.queryStep mem k (M.startQuery a q))
  have done : kernel z.2.2=some (z.1,z.2.2) :=
    (QueryNormalization.correct _ _ _ _ (fun _ => none)).trans (bit_report op mem)
  have stable {l h : ℕ} {r : Bool×ℕ} (le : l≤h) (ok : kernel l=some r) : kernel h=some r := by
    obtain ⟨b,hb,_⟩ := Option.map_eq_some_iff.mp ok
    unfold kernel
    rw [VerifiedEpoch.run_stable M.queryStep mem l (M.startQuery a q) b hb h
      ((VerifiedEpoch.run_length_le _ _ _ _).trans le)]
    exact ok
  obtain ⟨t,hist⟩ := physical_history C D idx a f xs nd
  have hist' : prefixRun M (tape Ω) a f xs=some (mem,t) :=
    (interleavedPrefix C D queryCode budget a f xs).trans hist
  change finalRun M (tape Ω) a f xs q=_
  unfold finalRun; rw [hist']
  change finish kernel=_
  rw [finish_eq_some kernel stable done]
  simp [z,op,mem,represented,image,encoded_run,
    QueryProgram.physical_run D a (C.initial f) (queryCode q) s.history s.auxiliary budget indices bound,s]


end
end DisjointnessDraft.Transfer.Auxiliary
