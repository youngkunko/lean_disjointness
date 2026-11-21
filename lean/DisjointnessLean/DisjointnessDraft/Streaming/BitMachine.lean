import DisjointnessDraft.Streaming.Binary
import DisjointnessFoundations.AdaptiveTraceComparison
import DisjointnessDraft.Streaming.Machine
import DisjointnessFoundations.FiniteProbePrograms
import DisjointnessFoundations.LogicalWordLayout

/-! A bit-stream program may adaptively read and write memory in each bit
operation, returning its immediate report. Chaining exactly b such operations
implements one source symbol with their total number of probes. A finite
worst-case fuel bound reifies any read/write transition engine into this form. -/
namespace DisjointnessDraft.Streaming.Binary
open DisjointnessFoundations CellProbe WordProgram QueryNormalization Simulation
open Program (run_bind)
open MeasureTheory
open scoped ENNReal
noncomputable section
abbrev Op (w : ℕ) := Program (Word w) (Word w) Bool

structure BitMachine (w : ℕ) where
  preload : RegularExpression Bool → Memory w
  bit : Bool → Op w

def stepWord : Op w → Step (Word w) (Op w)
  | .pure b => .done b
  | .read a k => .read a k
  | .write a v k => .write a v k

def execute (step : S → Step (Word w) S) : ℕ → S → Memory w → Option (Bool × (Memory w) × ℕ)
  | t,s,mem => match step s with
    | .done b => some (b,mem,0)
    | .read a k => match t with
      | 0 => none
      | t+1 => (execute step t (k (mem a)) mem).map fun z => (z.1,z.2.1,z.2.2+1)
    | .write a v s' => match t with
      | 0 => none
      | t+1 => (execute step t s' (Function.update mem a v)).map fun z => (z.1,z.2.1,z.2.2+1)

def truncate (step : S → Step (Word w) S) : ℕ → S → Op w
  | fuel,s => match step s with
    | .done b => .pure b
    | .read a f => match fuel with
      | 0 => .pure false
      | t+1 => .read a (fun v => truncate step t (f v))
    | .write a v s' => match fuel with
      | 0 => .pure false
      | t+1 => .write a v (truncate step t s')

theorem truncate_correct (step : S → Step (Word w) S) (fuel : ℕ) (s : S) (mem : Memory w)
    (out : Bool × (Memory w) × ℕ) (finished : execute step fuel s mem=some out) :
    (truncate step fuel s).run mem=out := by
  induction fuel generalizing s mem out with
  | zero =>
    cases h : step s with
    | done b =>
      simp only [execute,h,Option.some.injEq] at finished
      subst out
      simp only [truncate,h,Program.run]
    | read | write => simp only [execute,h,reduceCtorEq] at finished
  | succ t ih =>
    cases h : step s with
    | done bit =>
      simp only [execute,h,Option.some.injEq] at finished
      subst out
      simp only [truncate,h,Program.run]
    | read a f =>
      rw [execute,h] at finished
      change (Option.map _ _) = some out at finished
      rw [Option.map_eq_some_iff] at finished
      obtain ⟨z,hz,rfl⟩ := finished
      rw [truncate,h]
      change (((truncate step t (f (mem a))).run mem).1,((truncate step t (f (mem a))).run mem).2.1,
        1+((truncate step t (f (mem a))).run mem).2.2) = _
      rw [ih _ _ _ hz]
      simp [Nat.add_comm]
    | write a v s' =>
      rw [execute,h] at finished
      change (Option.map _ _) = some out at finished
      rw [Option.map_eq_some_iff] at finished
      obtain ⟨z,hz,rfl⟩ := finished
      rw [truncate,h]
      change (((truncate step t s').run (Function.update mem a v)).1,
        ((truncate step t s').run (Function.update mem a v)).2.1,
        1+((truncate step t s').run (Function.update mem a v)).2.2) = _
      rw [ih _ _ _ hz]
      simp [Nat.add_comm]

theorem memory_and_cost (p : Op w) (mem : Memory w) :
    let z := p.run mem
    updateRun (forgetReport stepWord) z.2.2 p mem = some z.2 := by
  induction p generalizing mem with
  | pure b => rfl
  | read a k ih =>
    change updateRun _ (1+_) _ _ = _
    rw [Nat.add_comm,updateRun]
    change (updateRun _ _ (k (mem a)) mem).map _=_
    rw [ih]; simp [Program.run,Nat.add_comm]
  | write a v k ih =>
    change updateRun _ (1+_) _ _ = _
    rw [Nat.add_comm,updateRun]
    change (updateRun _ _ k (Function.update mem a v)).map _=_
    rw [ih]; simp [Program.run,Nat.add_comm]

theorem bit_report (p : Op w) (mem : Memory w) :
    let z := p.run mem
    QueryNormalization.run stepWord z.2.2 p mem=some (z.1,z.2.2) := by
  induction p generalizing mem with
  | pure b => rfl
  | read a k ih =>
    change QueryNormalization.run _ (1+_) _ _=_
    rw [Nat.add_comm,QueryNormalization.run,stepWord]
    dsimp only
    rw [ih]
    change some (_, _ + 1) = some (_,1+_)
    simp [Program.run,Nat.add_comm]
  | write a v k ih =>
    change QueryNormalization.run _ (1+_) _ _=_
    rw [Nat.add_comm,QueryNormalization.run,stepWord]
    dsimp only
    rw [ih]
    change some (_, _ + 1) = some (_,1+_)
    simp [Program.run,Nat.add_comm]

def batch (D : BitMachine w) : Bool → List Bool → Op w
  | b,[] => .pure b
  | _,x::xs => D.bit x >>= fun b => batch D b xs

theorem batch_append (D : BitMachine w) (b : Bool) (xs ys : List Bool) (mem : Memory w) :
    (batch D b (xs++ys)).run mem =
    let z := (batch D b xs).run mem
    let v := (batch D z.1 ys).run z.2.1
    (v.1,v.2.1,z.2.2+v.2.2) := by
  induction xs generalizing b mem with
  | nil => simp [batch,Program.run]
  | cons x xs ih => simp [batch,run_bind,ih,Nat.add_assoc]

theorem nonempty_batch (D : BitMachine w) (b c : Bool) (xs : List Bool) (h : xs ≠ []) :
    batch D b xs=batch D c xs := by cases xs <;> simp_all [batch]

def BitMachine.input (D : BitMachine w) (C : Code (Symbol n m) b)
    (f : Fin m → Finset (Fin n)) (raw : List Bool) :=
    (batch D false raw).run (D.preload (substitute C.bits (expression f)))

def BitCorrect (D : BitMachine w) (C : Code (Symbol n m) b) :=
  ∀ (f : Fin m → Finset (Fin n)) (raw : List Bool), raw≠[] →
  (D.input C f raw).1=(substitute C.bits (expression f)).rmatch raw

def BitBudget (D : BitMachine w) (C : Code (Symbol n m) b) (t : ℕ) :=
  ∀ (f : Fin m → Finset (Fin n)) (pre : List Bool) (x : Bool), ((D.bit x).run (D.input C f pre).2.1).2.2≤t

theorem batch_cost (D : BitMachine w) (C : Code (Symbol n m) b) (bound : BitBudget D C t)
    (f : Fin m → Finset (Fin n)) (pre xs : List Bool) (init : Bool) :
    ((batch D init xs).run (D.input C f pre).2.1).2.2 ≤ xs.length*t := by
  induction xs generalizing pre init with
  | nil => simp [batch,Program.run]
  | cons x xs ih =>
    let prior := D.input C f pre
    let one := (D.bit x).run prior.2.1
    have next : (D.input C f (pre++[x])).2.1 = one.2.1 := by
      simp [BitMachine.input,batch_append,batch,run_bind,Program.run,one,prior]
    have h := ih (pre++[x]) one.1
    rw [next] at h
    have single := bound f pre x
    change one.2.2≤t at single
    change ((D.bit x >>= _).run _).2.2≤_
    rw [run_bind]
    change one.2.2+((batch D one.1 xs).run one.2.1).2.2 ≤ (xs.length+1)*t
    rw [Nat.add_mul,Nat.one_mul]; omega

def combined (D : BitMachine w) (C : Code (Symbol n n) b) : Engine n n w Unit where
  State := Op w
  preprocess _ r := D.preload (substitute C.bits r)
  start _ c := batch D false (C.bits c)
  step := stepWord

def tape : RandomTape Unit Unit := ⟨fun _ => (),fun _ _ => (),fun _ => ()⟩

private theorem one (D : BitMachine w) (C : Code (Symbol n n) b) (z : Symbol n n) (mem : Memory w) :
    insertOne (process (combined D C)) () z mem=some ((batch D false (C.bits z)).run mem).2 := by
  apply finish_eq_some _ (fun le h => updateRun_mono _ le _ _ h) (memory_and_cost _ _)

private theorem one_report (D : BitMachine w) (C : Code (Symbol n n) b) (z : Symbol n n) (mem : Memory w) :
    let out := (batch D false (C.bits z)).run mem
    finish (fun fuel => result (Simulation.run (process (combined D C)).queryStep mem fuel
       ((process (combined D C)).startQuery () z))) = some (out.1,out.2.2) := by
  apply finish_eq_some _ _ ((final_symbol _ () z _ _).trans (bit_report _ _))
  intro a b val le ok
  obtain ⟨v,done,_⟩ := Option.map_eq_some_iff.mp ok
  rw [VerifiedEpoch.run_stable _ _ a _ v done b ((VerifiedEpoch.run_length_le _ _ _ _).trans le)]
  exact ok

theorem prefix_execution (D : BitMachine w) (C : Code (Symbol n n) b) (hb : 0<b)
    (f : Family n) (xs : List (Symbol n n)) :
    prefixRun (process (combined D C)) tape () f xs=some (D.input C f (xs.flatMap C.bits)).2 := by
  have suffix (ys : List (Symbol n n)) (mem : Memory w) (t : ℕ) (b₀ : Bool) :
      insertAll (process (combined D C)) tape () t mem ys=some ((batch D b₀ (ys.flatMap C.bits)).run mem).2 := by
    induction ys generalizing mem t b₀ with
    | nil => rfl
    | cons y ys ih =>
      have pos : C.bits y ≠ [] := fun eq => by have h := C.length y; rw [eq,List.length_nil] at h; omega
      rw [insertAll,List.flatMap_cons,batch_append,nonempty_batch D b₀ false _ pos]
      change (insertOne (process (combined D C)) () y _).bind _=_
      rw [one]
      simp [ih _ _ ((batch D false (C.bits y)).run mem).1]
  exact suffix xs _ 0 false

theorem final_execution (D : BitMachine w) (C : Code (Symbol n n) b) (hb : 0<b)
    (f : Family n) (xs : List (Symbol n n)) (z : Symbol n n) :
    finalRun (process (combined D C)) tape () f xs z =
      some ((D.input C f ((xs++[z]).flatMap C.bits)).1,
        ((batch D false (C.bits z)).run (D.input C f (xs.flatMap C.bits)).2.1).2.2) := by
  have pos : C.bits z ≠ [] := fun eq => by have h := C.length z; rw [eq,List.length_nil] at h; omega
  simp only [finalRun,prefix_execution _ _ hb,Option.bind_eq_bind,Option.some_bind]
  change finish (fun fuel => result (Simulation.run _ _ fuel _))=_
  rw [one_report]
  simp [BitMachine.input,List.flatMap_append,batch_append,nonempty_batch D _ false _ pos]

theorem implements (D : BitMachine w) (C : Code (Symbol n n) b) (hb : 0<b)
    (correct : BitCorrect D C) (bounded : BitBudget D C t) :
    MeasurableRuns (process (combined D C)) tape ∧ ZeroError (process (combined D C)) tape reports ∧
    DataBound (combined D C) tape (b*t) ∧ SelectorBound (MeasureTheory.Measure.dirac ())
    (combined D C) tape (b*t) := by
  refine ⟨⟨fun _ _ => measurable_of_finite _,fun _ _ _ => measurable_of_finite _,
    fun _ _ _ _ => (Set.toFinite _).measurableSet⟩,?_,?_,?_⟩
  · intro seed f xs x
    rw [final_execution _ _ hb]
    apply congrArg some
    have pos : ((xs++[x]).flatMap C.bits)≠[] := by
      intro e; have h := congrArg List.length e
      simp [List.flatMap_append,hb.ne'] at h
    rw [correct _ _ pos]
    apply Bool.eq_iff_iff.mpr
    simp only [reports,RegularExpression.rmatch_iff_matches',substitution]
    exact ⟨fun ⟨src,ok,e⟩ => C.encode_injective hb e ▸ ok,fun ok => ⟨_,ok,rfl⟩⟩
  · intro seed f xs mem k prefixOk x
    rw [prefix_execution _ _ hb] at prefixOk
    have mem_eq := congrArg Prod.fst (Option.some.inj prefixOk)
    change _ = mem at mem_eq
    subst mem
    rw [one]
    simp only [CellProbe.cost]
    have bound := batch_cost D C bounded f (xs.flatMap C.bits) (C.bits (datum x)) false
    rw [C.length] at bound
    exact_mod_cast bound
  · intro f xs q
    simp_rw [final_execution D C hb]
    simp only [MeasureTheory.lintegral_dirac,CellProbe.cost]
    have h := batch_cost D C bounded f (xs.flatMap C.bits) (C.bits (selector q)) false
    simp only [C.length] at h
    rw [ENNReal.ofReal_mul (Nat.cast_nonneg _),ENNReal.ofReal_natCast,ENNReal.ofReal_natCast]
    exact_mod_cast h

end
end DisjointnessDraft.Streaming.Binary
