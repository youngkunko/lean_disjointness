import DisjointnessFoundations.RecordingInterpreter
import DisjointnessFoundations.QueryWriteOverlay
import DisjointnessDraft.Applications.GraphVariants
import Mathlib.MeasureTheory.Measure.Typeclasses.Probability
import DisjointnessFoundations.FiniteProbePrograms
import Mathlib.Analysis.SpecialFunctions.Log.Base
import DisjointnessFoundations.UniformProductLaws
import DisjointnessFoundations.EpochSizesAndAverages
import Mathlib.Data.Nat.Sqrt
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Data.List.Sort
import DisjointnessFoundations.EntropyOfConditionedLaws
import DisjointnessFoundations.SparseProductApproximation
import Mathlib.Data.Complex.ExponentialBounds
import DisjointnessDraft.Information.Rectangle
import Mathlib.Data.Fin.Tuple.Basic
import DisjointnessFoundations.PolylogarithmicRegime
import DisjointnessDraft.Information.FiberEntropy
import DisjointnessDraft.Information.ProductRectangle
import DisjointnessDraft.Native.Scale
import DisjointnessDraft.Simulation.Lengths
import DisjointnessDraft.Simulation.Probability
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Order.Interval.Finset.Nat
import DisjointnessDraft.Simulation.Averaging
import DisjointnessDraft.Native.GoodMass
import Mathlib.MeasureTheory.Integral.Lebesgue.Map
import DisjointnessDraft.Maximum
import Mathlib.Data.List.Induction

/-!
# Amortized Disjointness

The two main theorems are `AmortizedBound.total_work` and
`AmortizedBound.query_tradeoff`. The former counts all probes in the
interleaved hard distribution. The latter bounds the expected cost of a
single query following a prefix of amortized insertions.

Check this file with the pinned dependencies of the audited Disjointness Lean
project. The accompanying verification note describes the mathematical scope
and gives the commands for the independent axiom and dependency check.
-/

/-! ## Model -/

/-! Randomized dynamic word probes, the fixed interleaved input distribution,
    and the statements of the two dynamic lower bounds. -/
namespace AmortizedBound
namespace Dynamic
open DisjointnessFoundations CellProbe QueryNormalization MeasureTheory Filter
open DisjointnessDraft.Applications
open scoped ENNReal BigOperators
open Classical
noncomputable section

/-- A completed operation exposes only a report and its new physical memory to
    the execution semantics. The trace is for analysis and never passed to the machine. -/
inductive Probe (w : ℕ) where
  | read (addr value : Word w)
  | write (addr value : Word w)
  deriving DecidableEq
structure Result (w : ℕ) where
  report : Bool
  memory : Memory w
  trace : List (Probe w)

def withProbe (p : Probe w) (r : Result w) : Result w := {r with trace := p :: r.trace}

def execute (step : S → Step (Word w) S) : ℕ → S → Memory w → Option (Result w)
  | fuel, s, m => match step s with
    | .done b => some ⟨b,m,[]⟩
    | .read a k => match fuel with
      | 0 => none
      | j+1 => (execute step j (k (m a)) m).map (withProbe (.read a (m a)))
    | .write a v k => match fuel with
      | 0 => none
      | j+1 => (execute step j k (Function.update m a v)).map (withProbe (.write a v))

theorem execute_mono (step : S → Step (Word w) S) {lo hi : ℕ} (le : lo ≤ hi)
    (s : S) (m : Memory w) {r} (done : execute step lo s m = some r) :
    execute step hi s m = some r := by
  induction lo generalizing hi s m r with
  | zero => cases eq : step s <;> simp_all [execute]
  | succ lo ih =>
    obtain ⟨hi,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : hi ≠ 0)
    have le' : lo ≤ hi := by omega
    cases eq : step s with
    | done => simpa [execute,eq] using done
    | read | write =>
      rw [execute,eq] at done ⊢
      obtain ⟨v,hv,h⟩ := Option.map_eq_some_iff.mp done
      exact Option.map_eq_some_iff.mpr ⟨v,ih le' _ _ hv,h⟩

/-- Per-operation computation can depend on the independent master tape, the
    current position and the current operation. Only word memory crosses operations. -/
structure Machine (w : ℕ) (F U Q Ω : Type) where
  State : Type
  init : Ω → F → Option (Memory w)
  start : Ω → ℕ → U ⊕ Q → State
  step : State → Step (Word w) State

variable {F U Q Ω : Type} {w : ℕ}

def operation (D : Machine w F U Q Ω) (a : Ω) (t : ℕ) (op : U ⊕ Q) (mem : Memory w) :=
  finish (fun fuel => execute D.step fuel (D.start a t op) mem)

theorem operation_of_fuel (D : Machine w F U Q Ω) {a t op mem fuel r}
    (h : execute D.step fuel (D.start a t op) mem = some r) : operation D a t op mem = some r :=
  finish_eq_some _ (fun le => execute_mono D.step le _ _) h

structure History (w : ℕ) where
  memory : Memory w
  probes : ℕ
  lastReport : Option Bool

def advance (D : Machine w F U Q Ω) (a : Ω) (t : ℕ) (op : U ⊕ Q) (before : History w) : Option (History w) := do
  let r ← operation D a t op before.memory
  return ⟨r.memory,before.probes+r.trace.length,op.elim (fun _ => none) (fun _ => some r.report)⟩

def runFrom (D : Machine w F U Q Ω) (a : Ω) : ℕ → History w → List (U ⊕ Q) → Option (History w)
  | _, state, [] => some state
  | t, state, op :: ops => (advance D a t op state).bind (fun next => runFrom D a (t+1) next ops)

def history (D : Machine w F U Q Ω) (a : Ω) (f : F) (ops : List (U ⊕ Q)) :=
  (D.init a f).bind fun m => runFrom D a 0 ⟨m,0,none⟩ ops

theorem runFrom_append (D : Machine w F U Q Ω) (a : Ω) (t : ℕ) (s : History w)
    (xs ys : List (U ⊕ Q)) :
    runFrom D a t s (xs++ys) = (runFrom D a t s xs).bind (fun v => runFrom D a (t+xs.length) v ys) := by
  induction xs generalizing s t with
  | nil => simp [runFrom]
  | cons x xs ih =>
    simp only [List.cons_append,runFrom,List.length_cons,Option.bind_assoc]
    cases h : advance D a t x s with
    | none => rfl
    | some next => simpa [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using ih (t+1) next

theorem history_snoc (D : Machine w F U Q Ω) (a : Ω) (f : F) (xs : List (U ⊕ Q)) (op) :
    history D a f (xs++[op]) = (history D a f xs).bind (advance D a xs.length op) := by
  simp [history,runFrom_append,runFrom,Option.bind_assoc]

/-- Writes of an operation in chronological order. A read contributes one
    unit of work and no log entry. -/
def writeLog (tr : List (Probe w)) : Execution.Log w :=
  tr.filterMap fun p => match p with
    | .read _ _ => none
    | .write a v => some (a,v)

theorem execute_memory (step : S → Step (Word w) S) (fuel : ℕ) (st : S) (mem : Memory w)
    {r : Result w} (ok : execute step fuel st mem=some r) :
    r.memory=DisjointnessFoundations.Simulation.applyWrites mem (writeLog r.trace) := by
  induction fuel generalizing st mem r with
  | zero => cases hs : step st <;> simp [execute,hs] at ok; cases ok; rfl
  | succ fuel ih =>
    cases hs : step st with
    | done b => simp [execute,hs] at ok; cases ok; rfl
    | read addr k =>
      rw [execute,hs] at ok
      obtain ⟨v,hv,rfl⟩ := Option.map_eq_some_iff.mp ok
      change v.memory = DisjointnessFoundations.Simulation.applyWrites mem (writeLog v.trace)
      exact ih _ _ hv
    | write addr value k =>
      rw [execute,hs] at ok
      obtain ⟨v,hv,rfl⟩ := Option.map_eq_some_iff.mp ok
      have eq : Function.update mem addr value=(fun i => if i=addr then value else mem i) := by
        funext i; by_cases h : i=addr <;> simp [h,Function.update]
      change v.memory=DisjointnessFoundations.Simulation.applyWrites (fun i => if i=addr then value else mem i) (writeLog v.trace)
      rw [←eq]
      exact ih _ _ hv

/-- The actual write log of any segment of input operations. -/
def segment (D : Machine w F U Q Ω) (a : Ω) : ℕ → Memory w → List (U ⊕ Q) → Execution.Log w
  | _,_,[] => []
  | t,mem,op::xs => match operation D a t op mem with
    | none => []
    | some r => writeLog r.trace ++ segment D a (t+1) r.memory xs

theorem segment_correct (D : Machine w F U Q Ω) (a : Ω) (t : ℕ) (s : History w) (ops : List (U ⊕ Q))
    {last : History w} (ok : runFrom D a t s ops = some last) :
    last.memory=DisjointnessFoundations.Simulation.applyWrites s.memory (segment D a t s.memory ops) ∧
    s.probes + (segment D a t s.memory ops).length ≤ last.probes := by
  induction ops generalizing t s with
  | nil => simp [runFrom] at ok; subst last; exact ⟨rfl,by simp [segment]⟩
  | cons op ops ih =>
    cases hr : operation D a t op s.memory with
    | none => simp [runFrom,advance,hr] at ok
    | some r =>
      let next : History w := ⟨r.memory,s.probes+r.trace.length,op.elim (fun _ => none) (fun _ => some r.report)⟩
      have run : runFrom D a (t+1) next ops = some last := by simpa [runFrom,advance,hr,next] using ok
      obtain ⟨mem,cost⟩ := ih (t+1) next run
      obtain ⟨fuel,works⟩ := Execution.finish_witness _ hr
      have phys := execute_memory _ fuel _ _ works
      simp only [segment,hr,Execution.applyWrites_append,List.length_append]
      refine ⟨?_,?_⟩
      · rw [←phys]; exact mem
      · change s.probes+r.trace.length + (segment D a (t+1) r.memory ops).length ≤ last.probes at cost
        have small : (writeLog r.trace).length ≤ r.trace.length := List.length_filterMap_le ..
        omega

/-- For any fixed finite collection of terminating inputs on a tape, one
    cutoff works for them all and can be chosen without the realized input. -/
theorem common_fuel {I : Type} [Fintype I] (step : S → Step (Word w) S)
    (st : I → S) (mem : I → Memory w) (out : I → Result w)
    (halts : ∀ i, finish (fun k => execute step k (st i) (mem i)) = some (out i)) :
    ∃ k, ∀ i, execute step k (st i) (mem i) = some (out i) := by
  have every (i : I) := Execution.finish_witness _ (halts i)
  choose k hk using every
  exact ⟨Finset.univ.sup k,fun i => execute_mono step (Finset.le_sup (Finset.mem_univ i)) _ _ (hk i)⟩

def totalCost (D : Machine w F U Q Ω) (a : Ω) (f : F) (h : List (U ⊕ Q)) : ℝ≥0∞ :=
  ((history D a f h).map fun v => (v.probes : ℝ≥0∞)).getD ⊤

def nextCost (D : Machine w F U Q Ω) (a : Ω) (f : F) (h : List (U ⊕ Q)) (q : Q) : ℝ≥0∞ :=
  ((history D a f h).bind (fun v => (operation D a h.length (.inr q) v.memory).map
    fun r => (r.trace.length : ℝ≥0∞))).getD ⊤

def lastReport (D : Machine w F U Q Ω) (a : Ω) (f : F) (h : List (U ⊕ Q)) :=
  (history D a f h).bind History.lastReport

abbrev Family (N : ℕ) := Fin N → Finset (Fin N)
abbrev Op (N : ℕ) := Fin N ⊕ Fin N
abbrev DataStructure (N w : ℕ) (Ω : Type) := Machine w (Family N) (Fin N) (Fin N) Ω

def insertions (ops : List (Op N)) := ops.filterMap (fun op => op.elim some (fun _ => none))
def answer (f : Family N) (ops : List (Op N)) (q : Fin N) := decide (∀ x ∈ insertions ops, x ∉ f q)
def error : ℝ≥0∞ := 1/4096

def legal (ops : List (Op N)) := (insertions ops).Nodup

/-- Model convention: termination almost surely on each fixed legal history.
    Probability of error is bounded separately for each particular query. -/
structure Correct [MeasurableSpace Ω] (μ : Measure Ω) (D : DataStructure N w Ω)
    (families : Family N → Prop) (histories : List (Op N) → Prop) : Prop where
  terminates : ∀ f, families f → ∀ ops, histories ops → ∀ᵐ a ∂μ, (history D a f ops).isSome
  measurableCost : ∀ f, families f → ∀ ops, histories ops → Measurable (fun a => totalCost D a f ops)
  measurableQuery : ∀ f, families f → ∀ h q, histories (h++[.inr q]) → Measurable (fun a => nextCost D a f h q)
  measurableReport : ∀ f, families f → ∀ h q b, histories (h++[.inr q]) →
    MeasurableSet {a | lastReport D a f (h++[.inr q]) = some b}
  perQuery : ∀ f, families f → ∀ h q, histories (h++[.inr q]) →
    μ {a | lastReport D a f (h++[.inr q]) ≠ some (answer f h q)} ≤ error

/-- The three factors are the independent query rows, the update vector and
    the query indices. Rows and vector coordinates have uniform product law. -/
abbrev Row (n : ℕ) := Fin n → Fin n
abbrev Input (n m : ℕ) := (Fin m → Row n) × Row n × (Fin n → Fin m)

def hardSize (N : ℕ) := N.sqrt.sqrt

theorem active_fits (N : ℕ) : hardSize N * hardSize N ≤ N :=
  (Nat.sqrt_le N.sqrt).trans (Nat.sqrt_le_self N)

def address (fit : n*n ≤ N) (t v : Fin n) : Fin N := Fin.castLE fit (finProdFinEquiv (t,v))

theorem address_injective (fit : n*n ≤ N) : Function.Injective (fun z : Fin n × Fin n => address fit z.1 z.2) :=
  (Fin.castLEEmb fit).injective.comp finProdFinEquiv.injective

def rowSet (fit : n*n ≤ N) (r : Row n) := Finset.univ.image (fun t => address fit t (r t))

theorem rowSet_card (fit : n*n ≤ N) (r : Row n) : (rowSet fit r).card = n := by
  have inj : Function.Injective (fun t => address fit t (r t)) := fun a b h => congrArg Prod.fst (@address_injective n N fit (a,r a) (b,r b) h)
  simp [rowSet,Finset.card_image_of_injective _ inj]

theorem coordinate_hit (fit : n*n ≤ N) (r x : Row n) :
    ¬Disjoint (rowSet fit r) (rowSet fit x) ↔ ∃ t, r t = x t := by
  rw [Finset.not_disjoint_iff_nonempty_inter]
  constructor
  · rintro ⟨v,h⟩
    obtain ⟨⟨a,ha⟩,⟨b,hb⟩⟩ : (∃ a,address fit a (r a) = v) ∧ (∃ b,address fit b (x b) = v) := by
      simpa [rowSet] using Finset.mem_inter.mp h
    have eq := @address_injective n N fit (a,r a) (b,x b) (ha.trans hb.symm)
    cases congrArg Prod.fst eq
    exact ⟨a,congrArg Prod.snd eq⟩
  · rintro ⟨i,eq⟩
    refine ⟨address fit i (r i), Finset.mem_inter.mpr ⟨?_,?_⟩⟩
    · exact Finset.mem_image.mpr ⟨i,Finset.mem_univ _,rfl⟩
    · exact Finset.mem_image.mpr ⟨i,Finset.mem_univ _,by rw [eq]⟩

def schedule (fit : n*n ≤ N) (x : Row n) (query : Fin n → Fin N) : List (Op N) :=
  (List.finRange n).flatMap fun t => [.inl (address fit t (x t)), .inr (query t)]

theorem schedule_properties (fit : n*n ≤ N) (x : Row n) (query : Fin n → Fin N) :
    (schedule fit x query).length=2*n ∧ legal (schedule fit x query) := by
  have go (ts : List (Fin n)) :
      ((ts.flatMap fun t => ([.inl (address fit t (x t)),.inr (query t)] : List (Op N))).length=2*ts.length) ∧
      insertions (ts.flatMap fun t => ([.inl (address fit t (x t)),.inr (query t)] : List (Op N))) = ts.map (fun t => address fit t (x t)) := by
    induction ts with
    | nil => simp [insertions]
    | cons t ts ih => simp_all [insertions,List.filterMap_append]; omega
  obtain ⟨len,ins⟩ := go (List.finRange n)
  refine ⟨by simpa [schedule] using len,?_⟩
  unfold legal schedule
  rw [ins]
  exact (List.nodup_finRange n).map (fun a b h => congrArg Prod.fst (@address_injective n N fit (a,x a) (b,x b) h))

/-- With a finite probe cutoff, an arbitrary state machine can be transmitted
    to the finite-program trace simulator, including both query reads and writes. -/
def truncate (step : S → Step (Word w) S) : ℕ → S → WordProgram.Program (Word w) (Word w) (Option Bool)
  | fuel, st => match step st with
    | .done b => .pure (some b)
    | .read addr k => match fuel with
      | 0 => .pure none
      | j+1 => .read addr fun value => truncate step j (k value)
    | .write addr value k => match fuel with
      | 0 => .pure none
      | j+1 => .write addr value (truncate step j k)

theorem truncate_exact (step : S → Step (Word w) S) (fuel : ℕ) (st : S) (mem : Memory w)
    {r : Result w} (ok : execute step fuel st mem = some r) :
    (truncate step fuel st).run mem = (some r.report,r.memory,r.trace.length) := by
  induction fuel generalizing st mem r with
  | zero =>
    cases hs : step st <;> simp [execute,hs] at ok
    cases ok
    simp [truncate,hs,WordProgram.Program.run]
  | succ fuel ih =>
    cases hs : step st with
    | done b => simp [execute,hs] at ok; cases ok; simp [truncate,hs,WordProgram.Program.run]
    | read addr k =>
      rw [execute,hs] at ok
      obtain ⟨v,hv,rfl⟩ := Option.map_eq_some_iff.mp ok
      rw [truncate,hs]
      simp only [WordProgram.Program.run,ih _ _ hv,withProbe,List.length_cons,Nat.one_add]
    | write addr value k =>
      rw [execute,hs] at ok
      obtain ⟨v,hv,rfl⟩ := Option.map_eq_some_iff.mp ok
      rw [truncate,hs]
      simp only [WordProgram.Program.run,ih _ _ hv,withProbe,List.length_cons,Nat.one_add]

/-- Exact full-input disjoint mass conditional on any fixed query row. -/
def avoiding (r : Row n) : Finset (Row n) := Fintype.piFinset (fun i => Finset.univ.erase (r i))

theorem avoiding_spec (r x : Row n) : x ∈ avoiding r ↔ ∀ t, x t ≠ r t := by simp [avoiding]

theorem avoiding_card (r : Row n) : (avoiding r).card = (n-1)^n := by simp [avoiding,Fintype.card_piFinset]

theorem disjoint_probability {n : ℕ} (hn : 2≤n) (r : Row n) :
    ((avoiding r).card : ℝ) / Fintype.card (Row n) = (1-1/(n:ℝ))^n ∧
    1/4 ≤ ((avoiding r).card : ℝ) / Fintype.card (Row n) := by
  have pos : (0:ℝ) < n := by exact_mod_cast (by omega : 0<n)
  have eq : ((avoiding r).card : ℝ) / Fintype.card (Row n) = (1-1/(n:ℝ))^n := by
    rw [avoiding_card]
    simp only [Row,Fintype.card_fun,Fintype.card_fin,Nat.cast_pow,Nat.cast_sub (by omega : 1≤n),Nat.cast_one,←div_pow]
    congr 1
    field_simp
  exact ⟨eq,eq.symm ▸ HardDistribution.quarter_le_no_hit_power hn⟩

/-- Every chosen query sees precisely the rows' coordinates inserted so far. -/
theorem answer_after_updates (fit : n*n ≤ N) (r : Fin N → Row n) (x : Row n)
    (ts : List (Fin n)) (q : Fin N) :
    answer (fun i => rowSet fit (r i)) (ts.map fun t => Sum.inl (address fit t (x t))) q =
      decide (∀ t ∈ ts, x t ≠ r q t) := by
  have mem (t : Fin n) : address fit t (x t) ∈ rowSet fit (r q) ↔ x t = r q t := by
    constructor
    · intro hit
      obtain ⟨i,_,eq⟩ := Finset.mem_image.mp hit
      have e := @address_injective n N fit (i,r q i) (t,x t) eq
      cases congrArg Prod.fst e
      exact (congrArg Prod.snd e).symm
    · intro eq
      exact Finset.mem_image.mpr ⟨t,Finset.mem_univ _,by rw [eq]⟩
  apply decide_eq_decide.mpr
  simp [insertions,List.filterMap_map,Function.comp_def,mem]

/-- Literal graph answers on each prefix. The selected triangle edge exists
    for the query and is removed before the next insertion. The extra isolated
    vertex in `Graphs.V` is padding. -/
theorem graph_answers (f : Family N) (ops : List (Op N)) (q : Fin N) :
    let S := fun i (x : Fin N) => x ∈ f i
    let X := fun x => x ∈ insertions ops
    let bit := answer f ops q
    (decide (Graphs.reach (Graphs.base S X) (.row q) .target) = !bit) ∧
    (decide (Graphs.reach (Graphs.enabled S X) (.row q) .target) = !bit) ∧
    (decide (∃ a b c,GraphVariants.triEdge S X q a b ∧ GraphVariants.triEdge S X q b c ∧
      GraphVariants.triEdge S X q c a) = !bit) := by
  simp only [Graphs.reach_iff,Graphs.subgraph_iff,GraphVariants.triangle_iff]
  have eq : decide (Graphs.Hit (fun i (x : Fin N) => x∈f i) (fun x => x∈insertions ops) q) = !(answer f ops q) := by
    apply Bool.eq_iff_iff.mpr
    simp [Graphs.Hit,answer]; tauto
  exact ⟨eq,eq,eq⟩

/-- Separating an arbitrary ordered choice of coordinates preserves all of
    the input information on the complementary coordinates. -/
def splitCoordinates {ι κ A : Type} (e : κ ↪ ι) :
    (ι → A) ≃ ((κ → A) × ({i : ι // i ∉ Set.range e} → A)) where
  toFun x := (x ∘ e,fun i => x i)
  invFun y i := if h : i ∈ Set.range e then y.1 h.choose else y.2 ⟨i,h⟩
  left_inv x := by
    funext i
    dsimp only
    split_ifs with h
    · exact congrArg x h.choose_spec
    · rfl
  right_inv y := by
    apply Prod.ext
    · funext j
      change (if h : e j ∈ Set.range e then _ else _) = _
      have h : e j ∈ Set.range e := ⟨j,rfl⟩
      rw [dif_pos h]
      exact congrArg y.1 (e.injective h.choose_spec)
    · funext j
      simp only [dif_neg j.property]

/-- A uniform word splits into independent uniform inside and outside words.
    The same factorization applies to the query-index tape at a selected time. -/
theorem uniform_split {ι κ A : Type} [Fintype ι] [Fintype κ] [Fintype A] [Nonempty A]
    [MeasurableSpace A] [MeasurableSingletonClass A] (e : κ ↪ ι) :
    (HardIndependence.unif (ι → A)).map (splitCoordinates (A:=A) e) =
      (HardIndependence.unif (κ → A)).prod (HardIndependence.unif ({i : ι // i ∉ Set.range e} → A)) :=
  (HardIndependence.uniform_equiv _).trans HardIndependence.uniform_prod

/-- Union bound for the event used to localize errors, conditional on any
    fixed update word. Only the epoch's cardinality enters the bound. -/
theorem in_epoch_count {n : ℕ} (x : Row n) (epoch : Finset (Fin n)) :
    (Finset.univ.filter (fun r : Row n => ∃ j∈epoch,r j=x j)).card ≤ epoch.card * n^(n-1) := by
  let one := fun j : Fin n => Fintype.piFinset (fun i : Fin n => if i=j then {x j} else Finset.univ)
  have card (j : Fin n) : (one j).card=n^(n-1) := by
    rw [Fintype.card_piFinset]
    classical
    rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ j)]
    simp only [if_pos,Finset.card_singleton,one_mul]
    have eq : (∏ i ∈ Finset.univ.erase j, (if i=j then {x j} else (Finset.univ : Finset (Fin n))).card) =
        ∏ _i ∈ Finset.univ.erase j,n := Finset.prod_congr rfl fun i hi => by simp [(Finset.mem_erase.mp hi).1]
    rw [eq]; simp
  have sub : Finset.univ.filter (fun r : Row n => ∃ j∈epoch,r j=x j) ⊆ epoch.biUnion one := by
    intro r hr
    obtain ⟨j,hj,same⟩ := (Finset.mem_filter.mp hr).2
    refine Finset.mem_biUnion.mpr ⟨j,hj,Fintype.mem_piFinset.mpr ?_⟩
    intro i
    by_cases eq : i=j
    · subst i; simp [same]
    · simp [eq]
  exact (Finset.card_le_card sub).trans (Finset.card_biUnion_le_card_mul epoch one _ (fun j _ => (card j).le))

/-- Finite uniform average over all hard inputs and an independent expectation over coins. -/
def interleavedWork [MeasurableSpace Ω] (μ : Measure Ω) (D : DataStructure N w Ω) : ℝ≥0∞ :=
  let n := hardSize N
  (∑ z : Input n N, ∫⁻ a, totalCost D a (fun q => rowSet (active_fits N) (z.1 q))
      (schedule (active_fits N) z.2.1 z.2.2) ∂μ) / Fintype.card (Input n N)

def totalScale (N : ℕ) := (Real.logb 2 N / Real.logb 2 (Real.logb 2 N))^2
def ratio (N w : ℕ) (tu : ℝ) := (Real.logb 2 N / Real.logb 2 (tu*w))^2

def hardFamilies (N : ℕ) (f : Family N) := ∀ q, (f q).card=hardSize N

def singleHistories (N : ℕ) (h : List (Op N)) := legal h ∧
  ∃ xs : List (Fin N), h = xs.map Sum.inl ∨ ∃ q : Fin N, h=xs.map Sum.inl++[.inr q]

structure PrefixBudgets [MeasurableSpace Ω] (μ : Measure Ω) (D : DataStructure N w Ω) (tu tq : ℝ) : Prop where
  updates : ∀ f, hardFamilies N f → ∀ xs : List (Fin N), xs.Nodup →
    (∫⁻ a, totalCost D a f (xs.map Sum.inl) ∂μ) ≤ xs.length * ENNReal.ofReal tu
  query : ∀ f, hardFamilies N f → ∀ xs : List (Fin N), xs.Nodup → ∀ q,
    (∫⁻ a, nextCost D a f (xs.map Sum.inl) q ∂μ) ≤ ENNReal.ofReal tq

def wordSize (lo hi : ℝ) (N w : ℕ) := lo*Real.logb 2 N ≤ w ∧ (w:ℝ) ≤ hi*Real.logb 2 N

/-- Statement of the manuscript's total-work theorem. -/
def TotalWorkBound : Prop := ∀ lo hi : ℝ, 0<lo → lo≤hi → ∃ c : ℝ, 0<c ∧
  ∀ᶠ N : ℕ in atTop, ∀ w, wordSize lo hi N w → ∀ (Ω : Type) [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (D : DataStructure N w Ω),
    Correct μ D (hardFamilies N) legal →
    ENNReal.ofReal (c * hardSize N * totalScale N) ≤ interleavedWork μ D

/-- Subpolynomial update budgets along the input-size sequence. -/
def Subpolynomial (tu : ℕ → ℝ) := ∀ ε : ℝ, 0<ε → ∀ᶠ N : ℕ in atTop, tu N ≤ (N:ℝ)^ε

/-- Statement of the manuscript's amortized insertion / expected query trade-off.
    The constant depends only on the word-size constants, not on the update budget. -/
def QueryTradeoff : Prop := ∀ lo hi : ℝ, 0<lo → lo≤hi → ∃ c : ℝ, 0<c ∧ ∀ tu : ℕ → ℝ,
  (∀ᶠ N : ℕ in atTop, 1 ≤ tu N) → Subpolynomial tu → ∀ᶠ N : ℕ in atTop, ∀ w, wordSize lo hi N w → ∀ tq : ℝ, 0≤tq →
    ∀ (Ω : Type) [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ] (D : DataStructure N w Ω),
    Correct μ D (hardFamilies N) (singleHistories N) → PrefixBudgets μ D (tu N) tq →
    c * ratio N w (tu N) ≤ tq

end
end Dynamic
end AmortizedBound

/-! ## Histories -/

namespace AmortizedBound.Dynamic
open DisjointnessFoundations CellProbe MeasureTheory
open scoped ENNReal
open Classical
noncomputable section

structure Epoch (n s : ℕ) where
  start : ℕ
  selected : Fin n
  beforeQuery : start+s ≤ selected.val

namespace Epoch
variable {n s N : ℕ} (e : Epoch n s)

def index : Fin s ↪ Fin n where
  toFun i := ⟨e.start+i.val, by have := e.beforeQuery; have := e.selected.isLt; omega⟩
  inj' := by intro i j h; apply Fin.ext; have := congrArg Fin.val h; dsimp at this; omega

def before : List (Fin n) := (List.finRange n).take e.start
def middle : List (Fin n) := ((List.finRange n).drop e.start).take s
def after : List (Fin n) := ((List.finRange n).drop (e.start+s)).take (e.selected.val-(e.start+s))

theorem parts : e.before ++ e.middle ++ e.after = (List.finRange n).take e.selected.val := by
  have bound := e.beforeQuery
  unfold before middle after
  rw [←List.take_add,←List.take_add]
  congr 1; omega

theorem before_outside {i : Fin n} (hi : i ∈ e.before) : i ∉ Set.range e.index := by
  change i∈(List.finRange n).take e.start at hi
  rw [List.mem_take_iff_getElem] at hi
  rcases hi with ⟨j,lim,heq⟩
  simp only [List.getElem_finRange] at heq
  rintro ⟨k,rfl⟩
  have eq := congrArg Fin.val heq
  dsimp [index] at eq
  omega

def Out := {i : Fin n // i ∉ Set.range e.index} → Fin n

def join (inside : Fin s → Fin n) (outside : e.Out) : Row n :=
  (splitCoordinates e.index).symm (inside,outside)

theorem join_outside (x : Fin s → Fin n) (o : e.Out) {t : Fin n} (h : t ∉ Set.range e.index) :
    e.join x o t = o ⟨t,h⟩ := dif_neg h

theorem join_inside (x : Fin s → Fin n) (o : e.Out) (j : Fin s) : e.join x o (e.index j)=x j :=
  congrFun (congrArg Prod.fst ((splitCoordinates e.index).apply_symm_apply (x,o))) j

/-- Each completed round includes the physical query in the interleaved
    setting. In the single-query setting it consists of the insertion alone. -/
def rounds (fit : n*n ≤ N) (interleaved : Bool) (x : Row n) (qs : Fin n → Fin N) (ts : List (Fin n)) : List (Op N) :=
  ts.flatMap fun t => Sum.inl (address fit t (x t)) :: (if interleaved then [Sum.inr (qs t)] else [])

theorem rounds_agree (fit : n*n ≤ N) (interleaved : Bool) (x y : Row n) (qs : Fin n → Fin N)
    (ts : List (Fin n)) (agree : ∀ t∈ts,x t=y t) : rounds fit interleaved x qs ts = rounds fit interleaved y qs ts := by
  unfold rounds
  induction ts with
  | nil => rfl
  | cons t ts ih => simp [agree t (by simp),ih (fun i hi => agree i (by simp [hi]))]

variable (fit : n*n ≤ N) (interleaved : Bool) (qs : Fin n → Fin N)

def oldOps (o : e.Out) := rounds fit interleaved (fun t => if h : t∈Set.range e.index then e.selected else o ⟨t,h⟩) qs e.before

def epochOps (x : Fin s → Fin n) (o : e.Out) := rounds fit interleaved (e.join x o) qs e.middle

def recentOps (x : Fin s → Fin n) (o : e.Out) : List (Op N) :=
  rounds fit interleaved (e.join x o) qs e.after ++ [.inl (address fit e.selected (e.join x o e.selected))]

def past (x : Fin s → Fin n) (o : e.Out) : List (Op N) :=
  rounds fit interleaved (e.join x o) qs ((List.finRange n).take e.selected.val) ++
    [.inl (address fit e.selected (e.join x o e.selected))]

theorem old_independent (x : Fin s → Fin n) (o : e.Out) :
    e.oldOps fit interleaved qs o = rounds fit interleaved (e.join x o) qs e.before := by
  apply rounds_agree
  intro t ht
  simp [e.before_outside ht,e.join_outside x o (e.before_outside ht)]

theorem split_past (x : Fin s → Fin n) (o : e.Out) :
    e.past fit interleaved qs x o = e.oldOps fit interleaved qs o ++
       e.epochOps fit interleaved qs x o ++ e.recentOps fit interleaved qs x o := by
  rw [e.old_independent fit interleaved qs x o]
  unfold past epochOps recentOps
  rw [←e.parts]
  simp [rounds,List.flatMap_append,List.append_assoc]

/-- Any legal selected history that terminates factors into the three actual
    physical executions. The memory before the epoch uses only the rows and
    outside update coordinates, with all earlier interleaved writes retained. -/
theorem actual_segments (D : DataStructure N w Ω) (seed : Ω) (rows : Family N)
    (x : Fin s → Fin n) (o : e.Out) {last : History w}
    (ok : history D seed rows (e.past fit interleaved qs x o)=some last) :
    let old := e.oldOps fit interleaved qs o
    let between := e.epochOps fit interleaved qs x o
    let recent := e.recentOps fit interleaved qs x o
    ∃ pre mid : History w, history D seed rows old = some pre ∧
      runFrom D seed old.length pre between = some mid ∧
      runFrom D seed (old.length+between.length) mid recent = some last ∧
      let eWrites := segment D seed old.length pre.memory between
      let lWrites := segment D seed (old.length+between.length) mid.memory recent
      last.memory=DisjointnessFoundations.Simulation.applyWrites (DisjointnessFoundations.Simulation.applyWrites pre.memory eWrites) lWrites ∧
        pre.probes+eWrites.length≤mid.probes ∧ mid.probes+lWrites.length≤last.probes := by
  let old := e.oldOps fit interleaved qs o
  let middle := e.epochOps fit interleaved qs x o
  let recent := e.recentOps fit interleaved qs x o
  have append (l r : List (Op N)) : history D seed rows (l++r) =
      (history D seed rows l).bind (fun st => runFrom D seed l.length st r) := by simp [history,runFrom_append,Option.bind_assoc]
  rw [e.split_past fit interleaved qs x o] at ok
  change history D seed rows ((old++middle)++recent)=some last at ok
  rw [append,append,List.length_append] at ok
  obtain ⟨mid,first,lastok⟩ := Option.bind_eq_some_iff.mp ok
  obtain ⟨pre,havePre,haveMid⟩ := Option.bind_eq_some_iff.mp first
  have hm := segment_correct D seed old.length pre middle haveMid
  have hl := segment_correct D seed (old.length+middle.length) mid recent lastok
  exact ⟨pre,mid,havePre,haveMid,lastok,hl.1.trans (congrArg (fun m => DisjointnessFoundations.Simulation.applyWrites m _) hm.1),hm.2,hl.2⟩

def stepCount (mixed : Bool) : ℕ := if mixed then 2 else 1

theorem rounds_length (x : Row n) (ts : List (Fin n)) :
    (rounds fit interleaved x qs ts).length = ts.length * stepCount interleaved := by
  induction ts with
  | nil => simp [rounds]
  | cons t ts ih => cases interleaved <;> simp_all [rounds,stepCount,Nat.add_mul]

theorem selected_ordinal (x : Fin s → Fin n) (o : e.Out) :
    (e.past fit interleaved qs x o).length=e.selected.val*stepCount interleaved+1 := by
  simp [past,rounds_length,List.length_take, Nat.min_eq_left (Nat.le_of_lt e.selected.isLt)]

theorem rounds_inserts (x : Row n) (ts : List (Fin n)) :
    insertions (rounds fit interleaved x qs ts)=ts.map (fun t => address fit t (x t)) := by
  induction ts with
  | nil => rfl
  | cons t ts ih => cases interleaved <;> simp_all [rounds,insertions,List.filterMap_append]

def timesThrough := (List.finRange n).take e.selected.val ++ [e.selected]

theorem through_eq : e.timesThrough=(List.finRange n).take (e.selected.val+1) := by
  rw [List.take_add_one]
  simp [timesThrough,e.selected.isLt]

theorem through_contains (t : Fin n) : t∈e.timesThrough ↔ t.val≤e.selected.val := by
  rw [e.through_eq,List.mem_take_iff_getElem]
  constructor
  · rintro ⟨j,lt,eq⟩
    have val := congrArg Fin.val eq
    simp at val
    simp only [List.length_finRange] at lt
    omega
  · intro h
    refine ⟨t.val,?_,?_⟩
    · simp only [List.length_finRange]; omega
    · simp

theorem past_inserts (x : Fin s → Fin n) (o : e.Out) :
    insertions (e.past fit interleaved qs x o)=e.timesThrough.map (fun t => address fit t (e.join x o t)) := by
  simp only [past,insertions,List.filterMap_append,List.filterMap_cons,List.filterMap_nil,Sum.elim_inl,List.nil_append,
    timesThrough,List.map_append,List.map_cons,List.map_nil]
  rw [show List.filterMap (fun op : Op N => op.elim some (fun _ => none))
    (rounds fit interleaved (e.join x o) qs ((List.finRange n).take e.selected.val)) = _ from rounds_inserts ..]

theorem selected_legal (x : Fin s → Fin n) (o : e.Out) (q : Fin N) :
    legal (e.past fit interleaved qs x o++[.inr q]) := by
  have ins : insertions (e.past fit interleaved qs x o++[.inr q])=insertions (e.past fit interleaved qs x o) := by
    simp [insertions,List.filterMap_append]
  unfold legal
  rw [ins,e.past_inserts,e.through_eq]
  have nd : ((List.finRange n).take (e.selected.val+1)).Nodup := (List.nodup_finRange n).take
  exact nd.map (fun a b h => congrArg Prod.fst
    (@address_injective n N fit (a,e.join x o a) (b,e.join x o b) h))

theorem single_rounds (x : Row n) (ts : List (Fin n)) :
    rounds fit false x qs ts=(ts.map (fun t => address fit t (x t))).map Sum.inl := by
  simp [rounds,←List.map_eq_flatMap,List.map_map,Function.comp_def]

theorem selected_single (x : Fin s → Fin n) (o : e.Out) (q : Fin N) :
    singleHistories N (e.past fit false qs x o++[.inr q]) := by
  refine ⟨e.selected_legal fit false qs x o q,?_,Or.inr ⟨q,?_⟩⟩
  exact e.timesThrough.map (fun t => address fit t (e.join x o t))
  simp [past,timesThrough,single_rounds,List.map_append]

def outsideOK (row : Row n) (o : e.Out) := decide (∀ t : {i : Fin n // i ∉ Set.range e.index}, row t ≠ o t)

theorem filtered_answer (F : Fin N → Row n) (x : Fin s → Fin n) (o : e.Out) (q : Fin N) :
    (answer (fun i => rowSet fit (F i)) (e.past fit interleaved qs x o) q && e.outsideOK (F q) o) =
      decide (∀ i, F q i ≠ e.join x o i) := by
  have member (j : Fin n) : address fit j (e.join x o j)∈rowSet fit (F q) ↔ F q j=e.join x o j := by
    constructor
    · intro hit; obtain ⟨i,_,eq⟩ := Finset.mem_image.mp hit
      have pair := @address_injective n N fit (i,F q i) (j,e.join x o j) eq
      cases congrArg Prod.fst pair
      exact congrArg Prod.snd pair
    · intro h; exact Finset.mem_image.mpr ⟨j,Finset.mem_univ _,by rw [h]⟩
  apply Bool.eq_iff_iff.mpr
  simp only [answer,outsideOK,Bool.and_eq_true,decide_eq_true_eq,e.past_inserts,List.forall_mem_map,member]
  constructor
  · rintro ⟨early,out⟩ i
    by_cases h : i∈Set.range e.index
    · obtain ⟨j,rfl⟩ := h
      apply early _ ((e.through_contains _).mpr ?_)
      have hb := e.beforeQuery
      change e.start+j.val≤e.selected.val; omega
    · simpa [e.join_outside x o h] using out ⟨i,h⟩
  · intro clean
    exact ⟨fun j _ => clean j,fun t => by simpa [e.join_outside x o t.property] using clean t⟩

end Epoch
end
end AmortizedBound.Dynamic

/-! ## Intersection -/

/-! The intersection bound for two independent finite laws on words. Coordinates
within each word may have arbitrary dependencies. All entropy deficits are in bits. -/
namespace AmortizedBound.Intersection
open DisjointnessFoundations FiniteSampling EntropyBridge InformationLoss ProductTransfer
open Finset Real Classical
noncomputable section

abbrev Law := InputLaw
abbrev Words (n s : ℕ) := Fin s → Fin n

def bits {A : Type} [Fintype A] (p : Law A) := shannon p / log 2

def mean {A : Type} [Fintype A] (p : Law A) (f : A → ℝ) := ∑ x,p.weight x * f x

private theorem mean_const {A : Type} [Fintype A] (p : Law A) (a : ℝ) : mean p (fun _ => a) = a := by
  simp [mean,←sum_mul,p.total]
private theorem mean_add {A : Type} [Fintype A] (p : Law A) (f g : A→ℝ) :
    mean p (fun x => f x+g x)=mean p f+mean p g := by simp [mean,mul_add,sum_add_distrib]
private theorem mean_sub {A : Type} [Fintype A] (p : Law A) (f g : A→ℝ) :
    mean p (fun x => f x-g x)=mean p f-mean p g := by simp [mean,mul_sub,sum_sub_distrib]
private theorem mean_scale {A : Type} [Fintype A] (p : Law A) (c : ℝ) (f : A→ℝ) :
    mean p (fun x => c*f x)=c*mean p f := by simp only [mean,mul_sum]; exact sum_congr rfl (fun _ _ => by ring)
private theorem mean_le {A : Type} [Fintype A] (p : Law A) {f g : A→ℝ} (le : ∀ x,f x≤g x) : mean p f≤mean p g :=
  sum_le_sum (fun x _ => mul_le_mul_of_nonneg_left (le x) (p.nonneg x))

def uniform (A : Type) [Fintype A] [Nonempty A] : Law A where
  weight _ := (Fintype.card A : ℝ)⁻¹
  nonneg _ := by positivity
  total := by simp [Fintype.card_ne_zero]

private theorem uniform_kl {A : Type} [Fintype A] [Nonempty A] (p : Law A) :
    kl p.weight (uniform A).weight = log (Fintype.card A) - shannon p := by
  have hc : (Fintype.card A:ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  have term (a : A) : p.weight a * log (p.weight a/(uniform A).weight a) =
      p.weight a*log (Fintype.card A) - negMulLog (p.weight a) := by
    by_cases h : p.weight a=0
    · simp [h]
    · simp only [uniform,div_inv_eq_mul,log_mul h hc,negMulLog]; ring
  simp only [kl,term,sum_sub_distrib,←sum_mul,p.total,one_mul,shannon]

private theorem deficit_nonneg {A : Type} [Fintype A] [Nonempty A] (p : Law A) :
    0 ≤ logb 2 (Fintype.card A) - bits p := by
  have h := kl_nonneg p (uniform A) (fun a zero => by simp [uniform,Fintype.card_ne_zero] at zero)
  rw [uniform_kl] at h
  rw [logb,bits,←sub_div]; exact div_nonneg h (log_pos (by norm_num)).le

private theorem triangle (p q r : Law (Fin n)) : tv p r ≤ tv p q + tv q r := by
  unfold tv
  have h := sum_le_sum (s:=univ) (fun (x : Fin n) _ => abs_sub_le (p.weight x) (q.weight x) (r.weight x))
  rw [sum_add_distrib] at h; linarith

def collision (p q : Law (Fin n)) := ∑ x,p.weight x*q.weight x

/-- Two single-letter laws with total entropy deficit at most one tenth of a
bit assign collision probability at least 1/(2n) under independent draws. -/
theorem good_collision {n : ℕ} [NeZero n] (p q : Law (Fin n))
    (good : (logb 2 n-bits p)+(logb 2 n-bits q)≤1/10) : 1≤2*(n:ℝ)*collision p q := by
  let u := uniform (Fin n)
  have hp := pinsker_sq p u (fun x h => by simp [u,uniform,NeZero.ne n] at h)
  have hq := pinsker_sq q u (fun x h => by simp [u,uniform,NeZero.ne n] at h)
  rw [show u=uniform (Fin n) from rfl,uniform_kl,Fintype.card_fin] at hp hq
  have ln : 0<log 2 := log_pos (by norm_num)
  have h := (mul_le_mul_of_nonneg_right good ln.le)
  simp only [Real.logb,bits] at h
  field_simp [ln.ne'] at h
  have t := triangle p u q
  rw [tv_symm u q] at t
  have sp : 0 ≤ tv p q := tv_nonneg p q
  have sq : (tv p q)^2 ≤ (tv p u + tv q u)^2 := pow_le_pow_left₀ sp t 2
  have gap : tv p q ≤ 2/7 := by nlinarith only [sq,sq_nonneg (tv p u-tv q u),hp,hq,h,Real.log_two_lt_d9]
  let m := fun x => min (p.weight x) (q.weight x)
  have mass : (∑x,m x)=1-tv p q := by
    have e (x) : 2 * m x = p.weight x + q.weight x - |p.weight x-q.weight x| := by
      dsimp [m]; rcases le_total (p.weight x) (q.weight x) with h|h
      · rw [min_eq_left h,abs_of_nonpos (sub_nonpos.mpr h)]; ring
      · rw [min_eq_right h,abs_of_nonneg (sub_nonneg.mpr h)]; ring
    have z := congrArg (fun f : Fin n→ℝ => ∑x,f x) (funext e)
    simp only [←mul_sum,sum_sub_distrib,sum_add_distrib,p.total,q.total] at z
    unfold tv; linarith
  have cs := sum_mul_sq_le_sq_mul_sq (R:=ℝ) univ (fun _ : Fin n => 1) m
  simp only [one_mul,one_pow,sum_const,card_univ,Fintype.card_fin,nsmul_eq_mul,mul_one] at cs
  have sm := sum_le_sum (s:=univ) (fun x _ => show (m x)^2≤p.weight x*q.weight x by
    rw [pow_two]; exact mul_le_mul (min_le_left ..) (min_le_right ..) (le_min (p.nonneg _) (q.nonneg _)) (p.nonneg _))
  have hsm := mul_le_mul_of_nonneg_left sm (Nat.cast_nonneg n : (0:ℝ)≤n)
  rw [mass] at cs
  unfold collision
  have low : (5/7:ℝ)^2 ≤ (1-tv p q)^2 := pow_le_pow_left₀ (by norm_num) (by linarith) 2
  nlinarith only [low,cs,hsm]

private theorem sum_words (f : Words n (s+1) → ℝ) :
    (∑v,f v) = ∑a : Fin n, ∑t : Words n s,f (Fin.cons a t) := by
  let e := Fin.consEquiv (n:=s) (fun _ => Fin n)
  exact (e.sum_comp f).symm.trans (Fintype.sum_prod_type _)

def head (p : Law (Words n (s+1))) : Law (Fin n) where
  weight a := ∑ t : Words n s,p.weight (Fin.cons a t)
  nonneg _ := sum_nonneg fun _ _ => p.nonneg _
  total := (sum_words p.weight).symm.trans p.total

def tail [NeZero n] (p : Law (Words n (s+1))) (a : Fin n) : Law (Words n s) :=
  if h : (head p).weight a = 0 then uniform _ else
    { weight := fun t => p.weight (Fin.cons a t)/(head p).weight a
      nonneg := fun t => div_nonneg (p.nonneg _) ((head p).nonneg a)
      total := by rw [←sum_div]; exact div_self h }

private theorem disintegrate [NeZero n] (p : Law (Words n (s+1))) (a : Fin n) (t : Words n s) :
    (head p).weight a*(tail p a).weight t=p.weight (Fin.cons a t) := by
  by_cases h : (head p).weight a=0
  · have le : p.weight (Fin.cons a t)≤(head p).weight a := single_le_sum (fun z _ => p.nonneg (Fin.cons a z)) (mem_univ t)
    rw [h,zero_mul]; linarith [p.nonneg (Fin.cons a t)]
  · simp [tail,h, mul_div_cancel₀, h, mul_comm ((head p).weight a)]

private theorem mean_words [NeZero n] (p : Law (Words n (s+1))) (f : Words n (s+1)→ℝ) :
    mean p f = mean (head p) (fun a => mean (tail p a) (fun t => f (Fin.cons a t))) := by
  unfold mean; rw [sum_words]; simp only [mul_sum,←mul_assoc,disintegrate]

/-- Shannon's chain rule at the first symbol. Iterating gives the expected
prefix deficit budget, including conditionals of zero-probability prefixes. -/
theorem entropy_chain [NeZero n] (p : Law (Words n (s+1))) :
    bits p = bits (head p) + mean (head p) (fun a => bits (tail p a)) := by
  have chain : shannon p = shannon (head p) + mean (head p) (fun a => shannon (tail p a)) := by
    unfold shannon mean
    rw [sum_words,←sum_add_distrib]
    apply sum_congr rfl; intro a _
    simp_rw [←disintegrate p a,negMulLog_mul,sum_add_distrib,←sum_mul,←mul_sum,(tail p a).total,one_mul]
  simp only [bits,chain,add_div,mean,mul_div_assoc, sum_div]

def deficit (p : Law (Words n s)) := (s:ℝ)*logb 2 n - bits p

private theorem word_deficit_nonneg [NeZero n] (p : Law (Words n s)) : 0≤deficit p := by
  have h := deficit_nonneg p
  simpa [Words,Fintype.card_pi,logb_pow,deficit] using h

private theorem chain_budget [NeZero n] (p : Law (Words n (s+1))) :
    deficit p = (logb 2 n - bits (head p)) + mean (head p) (fun a => deficit (tail p a)) := by
  dsimp only [deficit]
  rw [entropy_chain,mean_sub,mean_const,Nat.cast_succ]; ring

/-- Nested means are the joint expectation under the product of the two
whole-vector laws. No factorization inside either vector is imposed. -/
def productMean {A : Type} [Fintype A] (p q : Law A) (f : A→A→ℝ) := mean p (fun x => mean q (f x))

private theorem pm_const {A : Type} [Fintype A] (p q : Law A) (v : ℝ) :
    productMean p q (fun _ _ => v)=v := by simp [productMean,mean_const]
private theorem pm_add {A : Type} [Fintype A] (p q : Law A) (f g : A→A→ℝ) :
    productMean p q (fun a b => f a b + g a b) = productMean p q f + productMean p q g := by
  simp [productMean,mean_add]
private theorem pm_sub {A : Type} [Fintype A] (p q : Law A) (f g : A→A→ℝ) :
    productMean p q (fun a b => f a b - g a b) = productMean p q f - productMean p q g := by
  simp [productMean,mean_sub]
private theorem pm_scale {A : Type} [Fintype A] (p q : Law A) (c : ℝ) (f : A→A→ℝ) :
    productMean p q (fun a b => c*f a b) = c*productMean p q f := by simp [productMean,mean_scale]
private theorem pm_le {A : Type} [Fintype A] (p q : Law A) {f g : A→A→ℝ} (le : ∀x y,f x y≤g x y) :
    productMean p q f ≤ productMean p q g := mean_le p fun _ => mean_le q (le _)
private theorem pm_margins {A : Type} [Fintype A] (p q : Law A) (f g : A→ℝ) :
    productMean p q (fun a b => f a + g b)=mean p f + mean q g := by
  simp [productMean,mean_add,mean_const]
private theorem pm_eq (p q : Law (Fin n)) : productMean p q (fun a b => if a=b then 1 else 0)=collision p q := by
  simp [productMean,mean,collision,mul_ite]

private theorem pm_words [NeZero n] (p q : Law (Words n (s+1))) (f : Words n (s+1)→Words n (s+1)→ℝ) :
    productMean p q f = productMean (head p) (head q) (fun a b =>
      productMean (tail p a) (tail q b) (fun t u => f (Fin.cons a t) (Fin.cons b u))) := by
  unfold productMean
  rw [mean_words p]
  apply congrArg (mean (head p)); funext a
  simp_rw [mean_words q]
  unfold mean
  simp_rw [mul_sum,←mul_assoc]
  rw [sum_comm]
  apply sum_congr rfl; intro b _; apply sum_congr rfl; intro t _
  ring

def hit (p q : Law (Words n s)) := productMean p q (fun v w => if ∃ j,v j=w j then 1 else 0)

private theorem cons_hit (a b : Fin n) (v w : Words n s) :
    (∃ j : Fin (s+1), (Fin.cons a v : Words n (s+1)) j = (Fin.cons b w : Words n (s+1)) j) ↔ a=b ∨ ∃j,v j=w j := by
  simp only [Fin.exists_fin_succ,Fin.cons_zero,Fin.cons_succ]

/-- Either the leading symbols coincide or the first hit occurs in the two
tails. Conditioning on both symbols preserves independence of those tails. -/
theorem first_hit [NeZero n] (p q : Law (Words n (s+1))) :
    hit p q=productMean (head p) (head q) (fun a b => if a=b then 1 else hit (tail p a) (tail q b)) := by
  unfold hit
  rw [pm_words]
  apply congrArg (productMean (head p) (head q)); funext a b
  by_cases eq : a=b <;> simp [cons_hit,eq,pm_const]

private theorem hit_nonneg (p q : Law (Words n s)) : 0≤hit p q := by
  rw [←pm_const p q 0]; apply pm_le; intro x y
  change (0:ℝ) ≤ if ∃j,x j=y j then 1 else 0
  split <;> norm_num

private theorem head_budget [NeZero n] (p q : Law (Fin n)) :
    1≤2*(n:ℝ)*collision p q+10*((logb 2 n-bits p)+(logb 2 n-bits q)) := by
  have dp := deficit_nonneg p; have dq := deficit_nonneg q
  simp only [Fintype.card_fin] at dp dq
  by_cases good : (logb 2 n-bits p)+(logb 2 n-bits q)≤1/10
  · linarith [good_collision p q good]
  · have h : 0≤collision p q := sum_nonneg (fun i _ => mul_nonneg (p.nonneg i) (q.nonneg i))
    linarith [mul_nonneg (show (0:ℝ)≤2*n by positivity) h]

/-- Every bad prefix is charged ten times its entropy deficit. On a good
prefix a collision costs at most 2n times its probability. Induction sums
these charges only until the first hit; dropping the nonnegative charges
on later prefixes yields the unconditional entropy budget. -/
theorem first_hit_budget {n : ℕ} [NeZero n] (s : ℕ) (p q : Law (Words n s)) :
    (s:ℝ)*(1-hit p q) ≤ 2*(n:ℝ)*hit p q+10*(deficit p+deficit q) := by
  induction s with
  | zero =>
    simp only [Nat.cast_zero,zero_mul]
    exact add_nonneg (mul_nonneg (by positivity) (hit_nonneg p q))
      (mul_nonneg (by norm_num) (add_nonneg (word_deficit_nonneg p) (word_deficit_nonneg q)))
  | succ s ih =>
    let r := fun a b => if a=b then 1 else hit (tail p a) (tail q b)
    let i := fun a b : Fin n => if a=b then (1:ℝ) else 0
    have step (a b : Fin n) :
        (s:ℝ)*(1-r a b) ≤ 2*(n:ℝ)*(r a b-i a b)+10*(deficit (tail p a)+deficit (tail q b)) := by
      by_cases eq : a=b
      · simp only [r,i,if_pos eq,sub_self,mul_zero,zero_add]
        have h := add_nonneg (word_deficit_nonneg (tail p a)) (word_deficit_nonneg (tail q b))
        linarith
      · simpa only [r,i,if_neg eq,sub_zero] using ih (tail p a) (tail q b)
    have paid := pm_le (head p) (head q) step
    change productMean (head p) (head q) (fun a b => (s:ℝ)*(1-r a b)) ≤
      productMean (head p) (head q) (fun a b => 2*(n:ℝ)*(r a b-i a b)+10*(deficit (tail p a)+deficit (tail q b))) at paid
    rw [pm_add,pm_scale,pm_scale,pm_scale,pm_sub,pm_sub,pm_const,pm_margins] at paid
    have rh : productMean (head p) (head q) r=hit p q := (first_hit p q).symm
    have ri : productMean (head p) (head q) i=collision (head p) (head q) := pm_eq ..
    rw [rh,ri] at paid
    rw [chain_budget p,chain_budget q,Nat.cast_succ]
    linarith only [paid,head_budget (head p) (head q),hit_nonneg p q]

/-- The manuscript's intersection estimate for independent word-valued laws,
with explicit Shannon entropy in bits and no coordinate-independence assumption. -/
theorem intersection_bound {n s : ℕ} (hs : 1≤s) (hsn : s≤n) (p q : Law (Words n s))
    (hp : (s:ℝ)*logb 2 n-s/100 ≤ bits p) (hq : (s:ℝ)*logb 2 n-s/100 ≤ bits q) :
    let mass := ∑ z ∈ (univ : Finset (Words n s × Words n s)).filter (fun z => ∃ j,z.1 j=z.2 j),
      (DisjointnessDraft.Information.pairLaw p q).weight z
    4*(s:ℝ)/(5*(2*n+s)) ≤ mass ∧ (s:ℝ)/(4*n) ≤ 4*s/(5*(2*n+s)) := by
  letI : NeZero n := ⟨by omega⟩
  have positive : (0:ℝ)<n := by exact_mod_cast (show 0<n by omega)
  intro mass
  have prob : mass = hit p q := by
    change (∑ z ∈ (univ : Finset (Words n s × Words n s)).filter (fun z => ∃ j,z.1 j=z.2 j),p.weight z.1*q.weight z.2)=_
    rw [sum_filter,Fintype.sum_prod_type]
    simp only [hit,productMean,mean,mul_sum]
    apply sum_congr rfl; intro v _; apply sum_congr rfl; intro w _
    split_ifs <;> ring
  have paid := first_hit_budget s p q
  dsimp [deficit] at paid
  have sp : (0:ℝ)<s := by exact_mod_cast (show 0<s by omega)
  have den : (0:ℝ)<5*(2*n+s) := by positivity
  constructor
  · rw [prob,div_le_iff₀ den]; nlinarith only [paid,hp,hq]
  · rw [div_le_div_iff₀ (by positivity) den]
    have sn : (s:ℝ)≤n := by exact_mod_cast hsn
    nlinarith only [mul_le_mul_of_nonneg_left sn sp.le,mul_nonneg sp.le positive.le]

end
end AmortizedBound.Intersection

/-! ## Communication -/

/-! The fixed-public-coin communication game, on vectors of independent block
coordinates. Information-theoretic identities are applied to its actual messages
and the posterior laws of its accepted transcripts. -/
namespace AmortizedBound.Communication
open MeasureTheory ProbabilityTheory Finset Real
open DisjointnessFoundations.FiniteSampling DisjointnessFoundations.HardIndependence
open DisjointnessFoundations.EntropyBridge DisjointnessFoundations.InformationLoss
open DisjointnessDraft.Information (Family View rowPrefix history direct_sum reveal_test fresh_prefix
  flat guessAtom guess_max true_part pairLaw product_rectangle)
open scoped DisjointnessDraft.Information ProbabilityTheory BigOperators ENNReal
noncomputable section
open Classical
abbrev Block (n s : ℕ) := Fin s → Fin n
abbrev World (m n s : ℕ) (W O R : Type*) := Family m W × (Block n s × (O × R))

structure Game (m n s : ℕ) (W O R U P A : Type*) where
  block : W → Block n s
  merlin : Family m W → Block n s → O → U
  packet : U → Block n s → O → R → P
  reply : Family m W → O → P → Fin m → A
  verify : O → P → A → U → Bool


section
variable {m N s : ℕ} {W O R U P A : Type*}
namespace Game
variable (G : Game m N s W O R U P A)
def advice (v : World m N s W O R) := G.merlin v.1 v.2.1 v.2.2.1
def psi (v : World m N s W O R) := G.packet (G.advice v) v.2.1 v.2.2.1 v.2.2.2
def phi (v : World m N s W O R) := (v.2.2.1,G.psi v)
def answers (v : World m N s W O R) := G.reply v.1 v.2.2.1 (G.psi v)
def public (v : World m N s W O R) := (G.phi v,G.answers v)
def observed (q : Fin m) (v : World m N s W O R) : View m W O P A :=
  (G.public v,rowPrefix q.val v.1)
def accepted (q : Fin m) (v : World m N s W O R) := G.verify v.2.2.1 (G.psi v) (G.answers v q) (G.advice v)
def label (q : Fin m) (v : World m N s W O R) := (G.observed q v,G.accepted q v)
def row (q : Fin m) (v : World m N s W O R) := G.block (v.1 q)
end Game

variable [Fintype W] [MeasurableSpace W] [MeasurableSingletonClass W]
  [MeasurableSpace O] [MeasurableSpace R]

/-- The whole family and the epoch update are independent uniforms.
The outside updates and coins can each have an arbitrary independent law. -/
def experiment (m N s : ℕ) (W : Type*) [Fintype W] [MeasurableSpace W]
    (o : Measure O) (r : Measure R) [SFinite o] [SFinite r] : Measure (World m N s W O R) :=
  (DisjointnessFoundations.HardIndependence.unif (Family m W)).prod
    ((DisjointnessFoundations.HardIndependence.unif (Block N s)).prod (o.prod r))

def acceptance [Fintype O] [Fintype R] [MeasurableSingletonClass O] [MeasurableSingletonClass R]
    (G : Game m N s W O R U P A) (o : Measure O) (r : Measure R) [SFinite o] [SFinite r] :=
  (∑ q : Fin m, (experiment m N s W o r).real (G.accepted q ⁻¹' {true}))/m


end
section
variable {m N s : ℕ} {W O R U P A : Type*}
  [Fintype W] [MeasurableSpace W] [MeasurableSingletonClass W] [Nonempty W]
  [Fintype O] [MeasurableSpace O] [MeasurableSingletonClass O]
  [Fintype R] [MeasurableSpace R] [MeasurableSingletonClass R]
  [Fintype U] [MeasurableSpace U] [MeasurableSingletonClass U]
  [Fintype P] [MeasurableSpace P] [MeasurableSingletonClass P]
  [Fintype A] [MeasurableSpace A] [MeasurableSingletonClass A] [Nonempty (Block N s)]

instance experiment_probability (o : Measure O) (r : Measure R) [IsProbabilityMeasure o] [IsProbabilityMeasure r] :
    IsProbabilityMeasure (experiment m N s W o r) := by unfold experiment; infer_instance

theorem row_uniform {m N s : ℕ} {W O R U P A : Type*}
    [Fintype W] [MeasurableSpace W] [MeasurableSingletonClass W] [Nonempty W]
    [Fintype O] [MeasurableSpace O] [MeasurableSingletonClass O]
    [Fintype R] [MeasurableSpace R] [MeasurableSingletonClass R]
    [Fintype U] [MeasurableSpace U] [MeasurableSingletonClass U]
    [Fintype P] [MeasurableSpace P] [MeasurableSingletonClass P]
    [Fintype A] [MeasurableSpace A] [MeasurableSingletonClass A] [Nonempty (Block N s)]
    (G : Game m N s W O R U P A) (o : Measure O) (r : Measure R)
    [IsProbabilityMeasure o] [IsProbabilityMeasure r] (q : Fin m)
    (balanced : (unif W).map G.block = unif (Block N s)) :
    (experiment m N s W o r).map (G.row q)=unif (Block N s) := by
  change (experiment m N s W o r).map (G.block ∘ (fun f : Family m W => f q) ∘ Prod.fst) = _
  rw [←Measure.map_map (measurable_of_finite _) (measurable_of_finite _),
    ←Measure.map_map (measurable_of_finite _) (measurable_of_finite _)]
  simp [experiment,eval_uniform,balanced]

/-- Total query-side Shannon deficit across all indices, in natural units. -/
theorem query_charge (G : Game m N s W O R U P A) (o : Measure O) (r : Measure R)
    [IsProbabilityMeasure o] [IsProbabilityMeasure r] (ub ab : ℕ)
    (hu : Fintype.card U≤2^ub) (ha : Fintype.card A≤2^ab) :
    ∑q : Fin m, I[G.row q : G.label q ; experiment m N s W o r] ≤
      (ub+m*ab : ℕ)*Real.log 2 := by
  let μ := experiment m N s W o r
  let F : World m N s W O R → Family m W := Prod.fst
  let data : World m N s W O R → Block N s × (O×R) := Prod.snd
  letI : FiniteRange F := ⟨Set.toFinite _⟩
  letI : FiniteRange data := ⟨Set.toFinite _⟩
  let msgs := prod G.advice G.answers
  let big := prod msgs data
  let c := fun _ : World m N s W O R => ()
  have ind : IndepFun F data μ := indepFun_fst_snd
  have budget : I[F : big ; μ] ≤ (ub+m*ab : ℕ)*Real.log 2 := by
    rw [show big=prod msgs data from rfl,DisjointnessFoundations.Information.message_chain μ (measurable_of_finite F) (measurable_of_finite msgs) (measurable_of_finite data),
      ind.mutualInfo_eq_zero (measurable_of_finite F) (measurable_of_finite data),zero_add]
    apply (DisjointnessFoundations.Information.conditional_information_le_entropy μ (measurable_of_finite F) (measurable_of_finite msgs) (measurable_of_finite data)).trans
    apply DisjointnessFoundations.Information.entropy_of_bits
    simp only [Fintype.card_prod,Fintype.card_fun,Fintype.card_fin,pow_add]
    rw [mul_comm m ab,pow_mul]
    exact Nat.mul_le_mul hu (Nat.pow_le_pow_left ha _)
  have reduce (q : Fin m) : I[G.row q : G.label q ; μ] ≤
      I[(fun ω => F ω q) : big | history F c q.val ; μ] := by
    let whole := fun ω => F ω q
    letI : FiniteRange whole := ⟨Set.toFinite _⟩
    let hist := history F c q.val
    letI : FiniteRange hist := ⟨Set.toFinite _⟩
    have ind' := DisjointnessFoundations.ProtocolCorrelation.lift_independence (unif (Family m W))
      ((unif (Block N s)).prod (o.prod r)) (measurable_of_finite _) (measurable_of_finite _) (fresh_prefix (W:=W) q)
    have hi : IndepFun whole hist μ := ind'.comp measurable_id (measurable_of_finite (fun p => ((),p)))
    let decoder := fun p : ((U×(Fin m→A))×(Block N s×(O×R))) × (Unit×(Fin m→Option W)) =>
      let ψ := G.packet p.1.1.1 p.1.2.1 p.1.2.2.1 p.1.2.2.2
      ((((p.1.2.2.1,ψ),p.1.1.2),p.2.2),G.verify p.1.2.2.1 ψ (p.1.1.2 q) p.1.1.1)
    have d := DisjointnessFoundations.Information.information_of_function_le μ (measurable_of_finite whole)
      (measurable_of_finite (prod big hist)) decoder
    change I[whole : G.label q ; μ] ≤ I[whole : prod big hist ; μ] at d
    have proj := DisjointnessFoundations.Information.information_of_function_le μ (measurable_of_finite (G.label q))
      (measurable_of_finite whole) G.block
    rw [mutualInfo_comm (measurable_of_finite (G.label q)) (measurable_of_finite (G.block ∘ whole)),
      mutualInfo_comm (measurable_of_finite (G.label q)) (measurable_of_finite whole)] at proj
    apply proj.trans (d.trans_eq _)
    rw [DisjointnessFoundations.Information.message_chain μ (measurable_of_finite whole) (measurable_of_finite big) (measurable_of_finite hist),
      hi.mutualInfo_eq_zero (measurable_of_finite whole) (measurable_of_finite hist),zero_add]
  apply (Finset.sum_le_sum (s:=Finset.univ) (fun q _ => reduce q)).trans
  rw [direct_sum μ F big c]
  have inject := DisjointnessFoundations.Information.information_of_function_le μ (measurable_of_finite F) (measurable_of_finite big) (fun x => (x,()))
  change I[F : prod big c ; μ]≤I[F : big ; μ] at inject
  rw [DisjointnessFoundations.Information.message_chain μ (measurable_of_finite F) (measurable_of_finite big) (measurable_of_finite c)] at inject
  have zero : I[F : c ; μ]=0 := mutualInfo_const (measurable_of_finite F) ()
  rw [zero,zero_add] at inject
  exact inject.trans budget

/-- Total residual target correlation across indices, revealing the exact
transcript vector and the deterministic verification flag in each summand. -/
theorem correlation_charge (G : Game m N s W O R U P A) (o : Measure O) (r : Measure R)
    [IsProbabilityMeasure o] [IsProbabilityMeasure r] (ub : ℕ) (hu : Fintype.card U≤2^ub) :
    ∑q : Fin m, I[G.row q : (fun v => v.2.1) | G.label q ; experiment m N s W o r] ≤
      ub*Real.log 2 := by
  let μ := experiment m N s W o r
  let F : World m N s W O R → Family m W := Prod.fst
  let data : World m N s W O R → Block N s × (O×R) := Prod.snd
  let target := fun v : World m N s W O R => (v.2.1,G.advice v)
  have reduce (q : Fin m) : I[G.row q : (fun v => v.2.1) | G.label q ; μ] ≤
      I[(fun v => F v q) : target | history F G.public q.val ; μ] := by
    let whole := fun ω => F ω q
    have h := DisjointnessFoundations.Correlation.project_conditioned μ (measurable_of_finite whole)
      (measurable_of_finite target) (measurable_of_finite (G.label q)) G.block Prod.fst
    apply h.trans
    exact reveal_test μ whole target (G.observed q) (G.accepted q)
      (fun p => G.verify p.2.1.1.1 p.2.1.1.2 (p.2.1.2 q) p.1.2) rfl
  apply (Finset.sum_le_sum (s:=Finset.univ) (fun q _ => reduce q)).trans
  rw [direct_sum μ F target G.public,condMutualInfo_comm (measurable_of_finite F) (measurable_of_finite target)]
  have rev := reveal_test μ target F G.phi G.answers (fun p => G.reply p.1 p.2.1 p.2.2) rfl
  apply rev.trans
  rw [condMutualInfo_comm (measurable_of_finite target) (measurable_of_finite F)]
  have ind : IndepFun F data μ := indepFun_fst_snd
  have h := DisjointnessFoundations.Correlation.advice_budget μ (measurable_of_finite F) (measurable_of_finite data)
    (measurable_of_finite G.advice) ind (fun p => (p.2.1,p.1)) (fun p => (p.2.2.1,G.packet p.1 p.2.1 p.2.2.1 p.2.2.2))
  exact h.trans (DisjointnessFoundations.Information.entropy_of_bits μ G.advice ub hu)


end
section
variable {m N s : ℕ} {W O R U P A : Type*}
  [Fintype W] [MeasurableSpace W] [MeasurableSingletonClass W] [Nonempty W]
  [Fintype O] [MeasurableSpace O] [MeasurableSingletonClass O]
  [Fintype R] [MeasurableSpace R] [MeasurableSingletonClass R]
  [adviceFinite : Fintype U] [adviceMeasurable : MeasurableSpace U] [singleAdvice : MeasurableSingletonClass U]
  [Fintype P] [packetMeasurable : MeasurableSpace P] [singlePacket : MeasurableSingletonClass P]
  [Fintype A] [responseMeasurable : MeasurableSpace A] [singleResponse : MeasurableSingletonClass A] [nonemptyLayer : Nonempty (Block N s)]

omit nonemptyLayer in
/-- Even a prediction chosen from the whole family, outside updates, and
private randomness succeeds with probability exactly one uniform atom. -/
theorem blind_guess (o : Measure O) (r : Measure R) [IsProbabilityMeasure o] [IsProbabilityMeasure r]
    (f : Family m W → O × R → Block N s) :
    (experiment m N s W o r).real {v | v.2.1=f v.1 v.2.2} = (Fintype.card (Block N s):ℝ)⁻¹ := by
  unfold experiment
  rw [measureReal_def,Measure.prod_apply (Set.toFinite _).measurableSet]
  have inner (F : Family m W) :
      ((unif (Block N s)).prod (o.prod r)) ((fun v => (F,v)) ⁻¹' {v | v.2.1=f v.1 v.2.2}) =
        (Fintype.card (Block N s):ℝ≥0∞)⁻¹ := by
    rw [Measure.prod_apply_symm (Set.toFinite _).measurableSet]
    change ∫⁻ y, (unif (Block N s)) {f F y} ∂(o.prod r) = _
    simp [one_atom]
  simp_rw [inner]
  simp

omit adviceFinite adviceMeasurable singleAdvice packetMeasurable singlePacket responseMeasurable singleResponse in
/-- The accepted joint mass of the best guess in every transcript has a
single packet-alphabet bound; no cost is charged for the verification bit. -/
theorem packet_guess (G : Game m N s W O R U P A) (o : Measure O) (r : Measure R)
    [IsProbabilityMeasure o] [IsProbabilityMeasure r] (q : Fin m) (g : View m W O P A→Block N s) :
    (∑ z, (experiment m N s W o r).real ((G.label q ⁻¹' {(z,true)}) ∩
      ((fun v : World m N s W O R => v.2.1) ⁻¹' {g z}))) ≤ Fintype.card P/(Fintype.card (Block N s):ℝ) := by
  let μ := experiment m N s W o r
  let C := fun z => (G.label q ⁻¹' {(z,true)}) ∩ ((fun v : World m N s W O R => v.2.1) ⁻¹' {g z})
  let predict := fun ψ (F : Family m W) (y : O×R) => g (((y.1,ψ),G.reply F y.1 ψ),rowPrefix q.val F)
  let E := fun ψ => {v : World m N s W O R | v.2.1=predict ψ v.1 v.2.2}
  have dis : Pairwise (fun z t => Disjoint (C z) (C t)) := by
    intro z t ne
    apply Set.disjoint_left.mpr
    intro v v₁ v₂
    exact ne (congrArg Prod.fst ((show G.label q v=(z,true) from v₁.1).symm.trans (show G.label q v=(t,true) from v₂.1)))
  have sub : (⋃z,C z) ⊆ ⋃ψ,E ψ := by
    intro v hv
    obtain ⟨z,hz⟩ := Set.mem_iUnion.mp hv
    apply Set.mem_iUnion.mpr
    refine ⟨G.psi v,?_⟩
    have view := congrArg Prod.fst (show G.label q v=(z,true) from hz.1)
    change G.observed q v=z at view
    exact (show v.2.1=g z from hz.2).trans (congrArg g view.symm)
  calc _ = μ.real (⋃z,C z) := (measureReal_iUnion_fintype dis (fun _ => (Set.toFinite _).measurableSet)).symm
       _ ≤ μ.real (⋃ψ,E ψ) := measureReal_mono sub
       _ ≤ ∑ψ, μ.real (E ψ) := measureReal_iUnion_fintype_le E
       _ = _ := by
         have atom (ψ : P) : μ.real (E ψ)=(Fintype.card (Block N s):ℝ)⁻¹ := blind_guess o r (predict ψ)
         simp [atom,div_eq_mul_inv]

omit adviceFinite adviceMeasurable singleAdvice in
/-- The same guessing bound expressed with the actual per-label posterior. -/
theorem posterior_guess (G : Game m N s W O R U P A) (o : Measure O) (r : Measure R)
    [IsProbabilityMeasure o] [IsProbabilityMeasure r] (q : Fin m) :
    let μ := experiment m N s W o r
    let x := fun v : World m N s W O R => v.2.1
    let px := fun z => posterior μ x (measurable_of_finite x) (G.label q) (z,true)
    ∑ z, (law μ (G.label q) (measurable_of_finite _)).weight (z,true) * (px z).weight (guessAtom (px z).weight)
      ≤ Fintype.card P/(Fintype.card (Block N s):ℝ) := by
  dsimp only
  simp_rw [posterior_weight]
  exact packet_guess G o r q _


end
section
variable {m N s : ℕ} {W O R U P A : Type*}
  [Fintype W] [MeasurableSpace W] [MeasurableSingletonClass W] [Nonempty W]
  [Fintype O] [MeasurableSpace O] [MeasurableSingletonClass O]
  [Fintype R] [MeasurableSpace R] [MeasurableSingletonClass R]
  [Fintype U] [MeasurableSpace U] [MeasurableSingletonClass U]
  [Fintype P] [MeasurableSpace P] [MeasurableSingletonClass P]
  [Fintype A] [MeasurableSpace A] [MeasurableSingletonClass A] [Nonempty (Block N s)]

namespace Game
variable (G : Game m N s W O R U P A) (o : Measure O) (r : Measure R) [IsProbabilityMeasure o] [IsProbabilityMeasure r]
abbrev Key (m : ℕ) (W O P A : Type*) := Fin m × View m W O P A
def event (v : Key m W O P A) := G.label v.1 ⁻¹' {(v.2,true)}
def mass (v : Key m W O P A) := (experiment m N s W o r).real (G.event v)
def qcost (v : Key m W O P A) :=
  kl (posterior (experiment m N s W o r) (G.row v.1) (measurable_of_finite _) (G.label v.1) (v.2,true)).weight
    (flat (Block N s)).weight
def corr (v : Key m W O P A) :=
  I[G.row v.1 : (fun w => w.2.1) ; (experiment m N s W o r)[|G.event v]]
def atomCost (v : Key m W O P A) :=
  let μ := experiment m N s W o r
  let x := fun w : World m N s W O R => w.2.1
  let p := posterior μ x (measurable_of_finite x) (G.label v.1) (v.2,true)
  p.weight (guessAtom p.weight)*Fintype.card (Block N s)

omit [Fintype U] [MeasurableSpace U] [MeasurableSingletonClass U] [MeasurableSpace P]
  [MeasurableSingletonClass P] [MeasurableSpace A] [MeasurableSingletonClass A] in
theorem mass_sum (pos : 0<m) : ∑ v,G.mass o r v=m*acceptance G o r := by
  let μ := experiment m N s W o r
  rw [acceptance,mul_div_cancel₀ _ (by exact_mod_cast pos.ne' : (m:ℝ)≠0),Fintype.sum_prod_type]
  apply sum_congr rfl; intro q _
  let S := fun z : View m W O P A => G.event (q,z)
  have dis : Pairwise (fun u v => Disjoint (S u) (S v)) := by
    intro u v ne; apply Set.disjoint_left.mpr; intro w h k
    exact ne (congrArg Prod.fst ((show G.label q w=(u,true) from h).symm.trans k))
  have eq : (⋃z,S z)=G.accepted q ⁻¹' {true} := by
    ext w; constructor
    · intro h; obtain ⟨z,hz⟩ := Set.mem_iUnion.mp h
      exact congrArg Prod.snd (show G.label q w=(z,true) from hz)
    · intro h; exact Set.mem_iUnion.mpr ⟨G.observed q w,Prod.ext rfl h⟩
  exact (measureReal_iUnion_fintype (μ:=μ) dis (fun _ => (Set.toFinite _).measurableSet)).symm.trans (congrArg μ.real eq)

omit [Fintype U] [MeasurableSpace U] [MeasurableSingletonClass U] [Fintype P]
  [MeasurableSpace P] [MeasurableSingletonClass P] [Fintype A] [MeasurableSpace A] [MeasurableSingletonClass A] in
theorem qcost_nonnegative (v : Key m W O P A) : 0≤G.qcost o r v := by
  apply kl_nonneg
  intro a h
  have c : (0:ℝ)<Fintype.card (Block N s) := by exact_mod_cast Fintype.card_pos
  exact False.elim ((inv_pos.mpr c).ne' h)

theorem qcost_sum (balanced : (unif W).map G.block=unif (Block N s))
    (ub ab : ℕ) (hu : Fintype.card U≤2^ub) (ha : Fintype.card A≤2^ab) :
    ∑v, G.mass o r v*G.qcost o r v ≤ (ub+m*ab : ℕ)*log 2 := by
  let μ := experiment m N s W o r
  rw [Fintype.sum_prod_type]
  apply le_trans _ (query_charge G o r ub ab hu ha)
  apply sum_le_sum; intro q _
  let z := G.label q
  let y := G.row q
  let nr := law μ z (measurable_of_finite _)
  let post := posterior μ y (measurable_of_finite y) z
  let F := flat (Block N s)
  have reflaw : (law μ y (measurable_of_finite y)).weight=F.weight := by
    funext a
    change μ.real (y ⁻¹' {a})=(Fintype.card (Block N s):ℝ)⁻¹
    rw [←map_measureReal_apply (measurable_of_finite y) (.singleton a),row_uniform G o r q balanced,
      measureReal_def,one_atom]; simp
  have h := expected_posterior_kl μ y (measurable_of_finite _) z (measurable_of_finite _)
  rw [reflaw] at h
  simp only [klBits,←mul_div_assoc,←sum_div] at h
  have full : (∑ t,nr.weight t*kl (post t).weight F.weight) = I[y:z;μ] :=
    (div_left_inj' (log_pos (by norm_num : (1:ℝ)<2)).ne').mp h
  apply (true_part (fun t => nr.weight t*kl (post t).weight F.weight) _).trans_eq full
  intro t
  apply mul_nonneg (nr.nonneg t)
  apply kl_nonneg
  intro a e
  have pos : (0:ℝ)<(Fintype.card (Block N s):ℝ) := by exact_mod_cast Fintype.card_pos
  exact False.elim ((inv_pos.mpr pos).ne' e)

theorem corr_sum (ub : ℕ) (hu : Fintype.card U≤2^ub) :
    ∑v,G.mass o r v*G.corr o r v≤ub*log 2 := by
  let μ := experiment m N s W o r
  rw [Fintype.sum_prod_type]
  apply le_trans _ (correlation_charge G o r ub hu)
  apply sum_le_sum; intro q _
  rw [condMutualInfo_eq_sum' (measurable_of_finite (G.label q))]
  let x := fun v : World m N s W O R => v.2.1
  exact true_part (fun t : View m W O P A × Bool => μ.real (G.label q ⁻¹' {t})*I[G.row q:x;μ[|G.label q ← t]]) (fun t => mul_nonneg measureReal_nonneg (mutualInfo_nonneg (measurable_of_finite (G.row q)) (measurable_of_finite x) _))

omit [Fintype U] [MeasurableSpace U] [MeasurableSingletonClass U] in
theorem atom_sum : ∑v,G.mass o r v*G.atomCost o r v≤m*(Fintype.card P:ℝ) := by
  let μ := experiment m N s W o r
  rw [Fintype.sum_prod_type]
  calc _ ≤ ∑_q : Fin m,(Fintype.card P:ℝ) := by
         apply sum_le_sum; intro q _
         have h := posterior_guess G o r q
         dsimp only at h
         have cp : (0:ℝ)<Fintype.card (Block N s) := by exact_mod_cast Fintype.card_pos
         have bound := (le_div_iff₀ cp).mp h
         unfold atomCost; simp only [←mul_assoc,←sum_mul]
         exact bound
       _ = _ := by simp

end Game
end
section
variable {m N s : ℕ} {W O R U P A : Type*}
  [Fintype W] [MeasurableSpace W] [MeasurableSingletonClass W] [Nonempty W]
  [Fintype O] [MeasurableSpace O] [MeasurableSingletonClass O]
  [Fintype R] [MeasurableSpace R] [MeasurableSingletonClass R]
  [Fintype U] [MeasurableSpace U] [MeasurableSingletonClass U]
  [Fintype P] [MeasurableSpace P] [MeasurableSingletonClass P]
  [Fintype A] [MeasurableSpace A] [MeasurableSingletonClass A] [Nonempty (Block N s)]
namespace Game
variable (G : Game m N s W O R U P A) (o : Measure O) (r : Measure R)
  [IsProbabilityMeasure o] [IsProbabilityMeasure r]

def acceptedLaw (hm : 0<m) (hr : 0<acceptance G o r) : InputLaw (Key m W O P A) where
  weight v := G.mass o r v/(m*acceptance G o r)
  nonneg _ := div_nonneg measureReal_nonneg (by positivity)
  total := by rw [←sum_div,G.mass_sum o r hm,div_self (by positivity)]

def queryPosterior (v : Key m W O P A) :=
  posterior (experiment m N s W o r) (G.row v.1) (measurable_of_finite _) (G.label v.1) (v.2,true)

def updatePosterior (v : Key m W O P A) :=
  posterior (experiment m N s W o r) (fun w => w.2.1) (measurable_of_finite _) (G.label v.1) (v.2,true)

omit [Fintype U] [MeasurableSpace U] [MeasurableSingletonClass U] [MeasurableSpace P]
  [MeasurableSingletonClass P] [MeasurableSpace A] [MeasurableSingletonClass A] in
theorem accepted_mean (hm : 0<m) (hr : 0<acceptance G o r) (f : Key m W O P A→ℝ) :
    (∑v,(G.acceptedLaw o r hm hr).weight v*f v)=(∑v,G.mass o r v*f v)/(m*acceptance G o r) := by
  simp only [acceptedLaw,div_mul_eq_mul_div,←sum_div]

theorem query_mean (hm : 0<m) (hr : 0<acceptance G o r)
    (bal : (unif W).map G.block=unif (Block N s)) (ub ab : ℕ)
    (hu : Fintype.card U≤2^ub) (ha : Fintype.card A≤2^ab) :
    (∑v,(G.acceptedLaw o r hm hr).weight v*(G.qcost o r v/log 2)) ≤
      (ub+m*ab : ℕ)/(m*acceptance G o r) := by
  simp only [←mul_div_assoc,←sum_div,G.accepted_mean o r hm hr]
  have norm : (0:ℝ)<m*acceptance G o r := by positivity
  have lp := log_pos (by norm_num : (1:ℝ)<2)
  rw [div_right_comm]
  apply div_le_div_of_nonneg_right _ norm.le
  exact (div_le_iff₀ lp).mpr (G.qcost_sum o r bal ub ab hu ha)

omit [Fintype U] [MeasurableSpace U] [MeasurableSingletonClass U] in
theorem atom_mean (hm : 0<m) (hr : 0<acceptance G o r) :
    (∑v,(G.acceptedLaw o r hm hr).weight v*G.atomCost o r v) ≤ Fintype.card P/acceptance G o r := by
  rw [G.accepted_mean]
  apply (div_le_iff₀ (by positivity)).mpr
  calc _ ≤ (m:ℝ)*Fintype.card P := G.atom_sum o r
       _ = _ := by field_simp; ring

theorem corr_mean (hm : 0<m) (hr : 0<acceptance G o r) (ub : ℕ) (hu : Fintype.card U≤2^ub) :
    (∑v,(G.acceptedLaw o r hm hr).weight v*(G.corr o r v/log 2)) ≤ (ub:ℝ)/(m*acceptance G o r) := by
  simp only [←mul_div_assoc,←sum_div,G.accepted_mean o r hm hr]
  rw [div_right_comm]
  apply div_le_div_of_nonneg_right _ (by positivity)
  exact (div_le_iff₀ (log_pos (by norm_num : (1:ℝ)<2))).mpr (G.corr_sum o r ub hu)

end Game
end
end

section
variable {L : Type*} [Fintype L] [Nonempty L]

theorem flat_deficit (p : InputLaw L) :
    kl p.weight (flat L).weight = log (Fintype.card L)-shannon p := by
  have card : 0<(Fintype.card L:ℝ) := by exact_mod_cast Fintype.card_pos
  have term (x : L) : p.weight x*log (p.weight x/(flat L).weight x) =
      p.weight x*log (Fintype.card L)-negMulLog (p.weight x) := by
    by_cases z : p.weight x=0
    · simp [z,negMulLog]
    · simp [flat,div_eq_mul_inv,log_mul z card.ne',negMulLog]; ring
  simp only [kl,term,sum_sub_distrib,←sum_mul,p.total,one_mul,shannon]

theorem capped_deficit (p : InputLaw L) {k : ℝ}
    (h : ∀x,p.weight x*(Fintype.card L:ℝ)≤k) :
    kl p.weight (flat L).weight≤log k := by
  have card : 0<(Fintype.card L:ℝ) := by exact_mod_cast Fintype.card_pos
  calc _ ≤ ∑x,p.weight x*log k := by
             apply sum_le_sum; intro x _
             by_cases z : p.weight x=0
             · simp [z]
             · have pos := mul_pos (lt_of_le_of_ne (p.nonneg x) (Ne.symm z)) card
               exact mul_le_mul_of_nonneg_left (by simpa [flat,div_eq_mul_inv] using log_le_log pos (h x)) (p.nonneg x)
       _ = _ := by rw [←sum_mul,p.total,one_mul]

private theorem simultaneous {T : Type*} [Fintype T] (p : InputLaw T)
    (f : Fin 4 → T → ℝ) (nn : ∀i v,0≤f i v) (t : Fin 4 → ℝ) (pos : ∀i,0<t i)
    (budget : ∀i,(∑v,p.weight v*f i v)≤t i/8) :
    ∃ v, 0<p.weight v ∧ ∀i, f i v≤t i := by
  let score := fun v => ∑i,f i v/t i
  have small : (∑v,p.weight v*score v) ≤ 1/2 := by
    simp only [score,mul_sum]
    rw [sum_comm]
    calc _ ≤ ∑_i : Fin 4,(1/8:ℝ) := by
               apply sum_le_sum; intro i _
               simp only [←mul_div_assoc,←sum_div]
               apply (div_le_iff₀ (pos i)).mpr
               linarith only [budget i]
         _ = _ := by norm_num
  by_contra! misses
  have big : (∑v,p.weight v)≤∑v,p.weight v*score v := by
    apply sum_le_sum
    intro v _
    by_cases w : p.weight v=0
    · simp [w]
    obtain ⟨i,hi⟩ := misses v (lt_of_le_of_ne (p.nonneg v) (Ne.symm w))
    have a : 1≤f i v/t i := (one_le_div (pos i)).mpr hi.le
    have b : f i v/t i≤score v := single_le_sum (fun j _ => div_nonneg (nn j v) (pos j).le) (mem_univ i)
    simpa using mul_le_mul_of_nonneg_left (a.trans b) (p.nonneg v)
  linarith only [p.total,big,small]

end

namespace Game
noncomputable section
open Classical
set_option maxHeartbeats 2000000
variable {m n s : ℕ} {W O R U P A : Type*}
  [Fintype W] [MeasurableSpace W] [MeasurableSingletonClass W] [Nonempty W]
  [Fintype O] [MeasurableSpace O] [MeasurableSingletonClass O]
  [Fintype R] [MeasurableSpace R] [MeasurableSingletonClass R]
  [Fintype U] [MeasurableSpace U] [MeasurableSingletonClass U]
  [Fintype P] [MeasurableSpace P] [MeasurableSingletonClass P]
  [Fintype A] [MeasurableSpace A] [MeasurableSingletonClass A]
  [Nonempty (Block n s)]
variable (G : Game m n s W O R U P A) (o : Measure O) (r : Measure R)
  [IsProbabilityMeasure o] [IsProbabilityMeasure r]

def overlaps (a b : Block n s) : Prop := ∃ j, a j=b j

def jointError : ℝ :=
  (∑q : Fin m, (experiment m n s W o r).real ((G.accepted q ⁻¹' {true}) ∩
    {v | overlaps (G.row q v) v.2.1}))/m

def fiberHit (v : Key m W O P A) : ℝ :=
  (experiment m n s W o r)[|G.event v].real {w | overlaps (G.row v.1 w) w.2.1}

omit [Fintype U] [MeasurableSpace U] [MeasurableSingletonClass U] [MeasurableSpace P] [MeasurableSingletonClass P] [MeasurableSpace A] [MeasurableSingletonClass A] in
theorem hit_mean (hm : 0<m) (hr : 0<acceptance G o r) :
    (∑v,(G.acceptedLaw o r hm hr).weight v*G.fiberHit o r v) =
      G.jointError o r/acceptance G o r := by
  let μ := experiment m n s W o r
  have cell (v : Key m W O P A) :
      G.mass o r v*G.fiberHit o r v=μ.real (G.event v ∩ {w | overlaps (G.row v.1 w) w.2.1}) := by
    change μ.real (G.event v)*(μ[|G.event v]).real _=_
    rw [cond_real_apply (Set.toFinite _).measurableSet,←mul_assoc]
    by_cases z : μ.real (G.event v)=0
    · have empty : μ.real (G.event v ∩ {w | overlaps (G.row v.1 w) w.2.1}) ≤ μ.real (G.event v) :=
        measureReal_mono Set.inter_subset_left
      rw [z] at empty
      simp [z,le_antisymm empty measureReal_nonneg]
    · simp [z]
  have per (q : Fin m) :
      ∑z : View m W O P A, μ.real (G.event (q,z) ∩ {w | overlaps (G.row q w) w.2.1}) =
        μ.real ((G.accepted q ⁻¹' {true}) ∩ {w | overlaps (G.row q w) w.2.1}) := by
    let S := fun z : View m W O P A => G.event (q,z) ∩ {w | overlaps (G.row q w) w.2.1}
    have dis : Pairwise (fun a b => Disjoint (S a) (S b)) := by
      intro a b h; apply Set.disjoint_left.mpr
      intro w ha hb
      exact h (congrArg Prod.fst ((show G.label q w=(a,true) from ha.1).symm.trans hb.1))
    have eq : (⋃z,S z) = (G.accepted q ⁻¹' {true}) ∩ {w | overlaps (G.row q w) w.2.1} := by
      ext w; constructor
      · intro hw; obtain ⟨z,hz⟩ := Set.mem_iUnion.mp hw
        exact ⟨congrArg Prod.snd (show G.label q w=(z,true) from hz.1),hz.2⟩
      · rintro ⟨ha,hit⟩; exact Set.mem_iUnion.mpr ⟨G.observed q w,Prod.ext rfl ha,hit⟩
    exact (measureReal_iUnion_fintype (μ:=μ) dis (fun _ => (Set.toFinite _).measurableSet)).symm.trans (congrArg μ.real eq)
  rw [G.accepted_mean]
  simp only [cell,Fintype.sum_prod_type,per,jointError,μ,div_div]

/-- A positive-mass accepted transcript with simultaneous entropy, information
and intersection bounds. The four numerical hypotheses compare actual
message alphabets and acceptance to the desired cutoffs. -/
theorem conditioning (hm : 0<m) (hr : 0<acceptance G o r)
    (bal : (unif W).map G.block=unif (Block n s)) (ub ab : ℕ)
    (hu : Fintype.card U≤2^ub) (ha : Fintype.card A≤2^ab)
    {d κ t : ℝ} (hd : 0<d) (hk : 0<κ) (ht : 0<t)
    (rowBudget : ((ub+m*ab:ℕ):ℝ)/(m*acceptance G o r)≤d/8)
    (packetBudget : (Fintype.card P:ℝ)/acceptance G o r≤(2:ℝ)^d/8)
    (infoBudget : (ub:ℝ)/(m*acceptance G o r)≤κ/8)
    (overlapBudget : G.jointError o r/acceptance G o r≤t/8) :
    ∃v,0<G.mass o r v ∧
      logb 2 (n:ℝ)*s-d ≤ shannon (G.queryPosterior o r v)/log 2 ∧
      logb 2 (n:ℝ)*s-d ≤ shannon (G.updatePosterior o r v)/log 2 ∧
      G.corr o r v/log 2≤κ ∧ G.fiberHit o r v≤t := by
  let w := G.acceptedLaw o r hm hr
  let metrics : Fin 4 → Key m W O P A → ℝ :=
    ![fun v => G.qcost o r v/log 2,G.atomCost o r,fun v => G.corr o r v/log 2,G.fiberHit o r]
  let cuts : Fin 4 → ℝ := ![d,(2:ℝ)^d,κ,t]
  have lp := log_pos (by norm_num : (1:ℝ)<2)
  have nn (i : Fin 4) (v : Key m W O P A) : 0≤metrics i v := by
    fin_cases i
    · exact div_nonneg (G.qcost_nonnegative o r v) lp.le
    · exact mul_nonneg ((G.updatePosterior o r v).nonneg _) (Nat.cast_nonneg _)
    · exact div_nonneg (mutualInfo_nonneg (measurable_of_finite _) (measurable_of_finite _) _) lp.le
    · exact measureReal_nonneg
  have pos (i : Fin 4) : 0<cuts i := by
    fin_cases i
    · exact hd
    · exact rpow_pos_of_pos (by norm_num) _
    · exact hk
    · exact ht
  have budgets (i : Fin 4) : (∑v,w.weight v*metrics i v)≤cuts i/8 := by
    fin_cases i
    · exact (G.query_mean o r hm hr bal ub ab hu ha).trans rowBudget
    · exact (G.atom_mean o r hm hr).trans packetBudget
    · exact (G.corr_mean o r hm hr ub hu).trans infoBudget
    · exact (G.hit_mean o r hm hr).le.trans overlapBudget
  obtain ⟨v,vp,bounds⟩ := simultaneous w metrics nn cuts pos budgets
  have qbound : kl (G.queryPosterior o r v).weight (flat (Block n s)).weight /log 2≤d := bounds 0
  have xbound : G.atomCost o r v≤(2:ℝ)^d := bounds 1
  have cap (x : Block n s) : (G.updatePosterior o r v).weight x * (Fintype.card (Block n s):ℝ) ≤ (2:ℝ)^d :=
    (mul_le_mul_of_nonneg_right (guess_max _ x) (Nat.cast_nonneg _)).trans xbound
  have u := capped_deficit (G.updatePosterior o r v) cap
  rw [log_rpow (by norm_num : (0:ℝ)<2)] at u
  have card : log (Fintype.card (Block n s):ℝ)=s*log n := by
    simp [Block,Fintype.card_fun,log_pow]
  rw [flat_deficit,card] at qbound u
  have a := (div_le_iff₀ lp).mp qbound
  have conv (H : ℝ) (h : s*log n-H≤d*log 2) : logb 2 (n:ℝ)*s-d≤H/log 2 := by
    apply (le_div_iff₀ lp).mpr
    rw [sub_mul,logb]
    field_simp at *
    linarith
  exact ⟨v,(div_pos_iff_of_pos_right (by positivity : 0<(m:ℝ)*acceptance G o r)).mp vp,
    conv _ a,conv _ u,bounds 2,bounds 3⟩

omit [Fintype U] [MeasurableSpace U] [MeasurableSingletonClass U] [Fintype P]
  [MeasurableSpace P] [MeasurableSingletonClass P] [Fintype A] [MeasurableSpace A] [MeasurableSingletonClass A] in
/-- The product of the two actual posterior marginals has almost the same
overlap probability as the accepted joint execution (Step 3). -/
theorem product_overlap (v : Key m W O P A) (vp : 0<G.mass o r v) {t κ : ℝ}
    (small : G.fiberHit o r v≤t) (info : G.corr o r v/log 2≤κ) :
    ∑z ∈ Finset.univ.filter (fun z : Block n s × Block n s => overlaps z.1 z.2),
       (pairLaw (G.queryPosterior o r v) (G.updatePosterior o r v)).weight z ≤
       t+sqrt ((log 2/2)*κ) := by
  let μ := experiment m n s W o r
  have nz : μ (G.event v)≠0 := fun z => vp.ne' (by change μ.real (G.event v)=0; simp [measureReal_def,z])
  let ν := μ[|G.event v]
  letI : IsProbabilityMeasure ν := cond_isProbabilityMeasure nz
  let x := fun w : World m n s W O R => w.2.1
  let a := G.row v.1
  let E := univ.filter (fun z : Block n s × Block n s => overlaps z.1 z.2)
  have hit : ν.real ((prod a x) ⁻¹' (E : Set _))≤t := by
    simpa only [E,a,x,Set.preimage,Set.mem_setOf_eq,Finset.mem_coe,Finset.mem_filter,
      Finset.mem_univ,true_and,prod] using small
  have b1 (z) : ν.real (a ⁻¹' {z})≤1 := measureReal_le_one
  have b2 (z) : ν.real (x ⁻¹' {z})≤1 := measureReal_le_one
  have use := (product_rectangle ν a x E 1 t κ b1 b2 hit info).2.2
  have nl : μ (G.label v.1 ⁻¹' {(v.2,true)})≠0 := nz
  simpa only [queryPosterior,updatePosterior,posterior,dif_neg nl,μ,ν,a,x,E,event] using use

end
end Game


open Filter
/-- Arithmetic translating the manuscript's bit budgets into the four cutoffs
for the fixed-coin protocol. -/
theorem budget_geometry : ∀ᶠ n : ℕ in atTop, ∀ m s ub ab : ℕ, ∀ packet ρ : ℝ,
    (n:ℝ)^(2/3:ℝ)/3≤s → n^4≤m →
    (ub:ℝ)≤(n:ℝ)^(5/4:ℝ) → (ab:ℝ)≤(logb 2 n)^3 →
    packet≤(2:ℝ)^((s:ℝ)/200) → (n:ℝ)^(-1/2:ℝ)≤ρ →
    (((ub+m*ab:ℕ):ℝ)/(m*ρ)≤((s:ℝ)/100)/8) ∧
    (packet/ρ≤(2:ℝ)^((s:ℝ)/100)/8) ∧
    ((ub:ℝ)/(m*ρ)≤(16*(n:ℝ)^(-9/4:ℝ))/8) ∧
    ((s:ℝ)/(8*n)+sqrt ((log 2/2)*(16*(n:ℝ)^(-9/4:ℝ))) < s/(4*n)) := by
  have small := (DisjointnessFoundations.FinalBounds.polylog_budget 4800).filter_mono
    (show Filter.map (fun n : ℕ => (n:ℝ)) atTop ≤ atTop from tendsto_natCast_atTop_atTop)
  filter_upwards [small,eventually_ge_atTop 2] with n small two
  intro m s ub ab packet ρ geom size advice replies packetSize accept
  change 4800*(logb 2 (n:ℝ))^3≤(n:ℝ)^(1/50:ℝ) at small
  have n2 : 2≤(n:ℝ) := by exact_mod_cast two
  have np : 0<(n:ℝ) := by linarith
  have n1 : 1≤(n:ℝ) := by linarith
  have logbig : 1≤logb 2 (n:ℝ) := by simpa using logb_le_logb_of_le (b:=2) (by norm_num) (by norm_num : (0:ℝ)<2) n2
  have logcube : 1≤(logb 2 (n:ℝ))^3 := one_le_pow₀ logbig
  have logle : logb 2 (n:ℝ)≤(logb 2 (n:ℝ))^3 := by
    nlinarith only [mul_le_mul_of_nonneg_left (one_le_pow₀ (n:=2) logbig) (by linarith : 0≤logb 2 (n:ℝ))]
  have mp : 0<(m:ℝ) := lt_of_lt_of_le (pow_pos np 4) (by exact_mod_cast size)
  have ρp := (rpow_pos_of_pos np (-1/2:ℝ)).trans_le accept
  have invρ : 1/ρ≤(n:ℝ)^(1/2:ℝ) := by
    have hn : (n:ℝ)^(-1/2:ℝ)=((n:ℝ)^(1/2:ℝ))⁻¹ := by rw [←rpow_neg np.le]; norm_num
    rw [hn] at accept
    simpa [one_div] using inv_anti₀ (inv_pos.mpr (rpow_pos_of_pos np (1/2:ℝ))) accept
  have advm : (ub:ℝ)≤m :=
    advice.trans ((rpow_le_rpow_of_exponent_le n1 (show (5/4:ℝ)≤4 by norm_num)).trans (by exact_mod_cast size))
  have rows : ((ub+m*ab:ℕ):ℝ)/(m*ρ) ≤ (1+(logb 2 (n:ℝ))^3)*(n:ℝ)^(1/2:ℝ) := by
    have le : (ub:ℝ)/m+(ab:ℝ)≤1+(logb 2 (n:ℝ))^3 := add_le_add ((div_le_one mp).mpr advm) replies
    calc _ = ((ub:ℝ)/m+(ab:ℝ))*(1/ρ) := by push_cast; field_simp; ring
         _ ≤ _ := mul_le_mul le invρ (by positivity) (by positivity)
  have scale (a b : ℝ) (le : a≤b) : (n:ℝ)^a≤(n:ℝ)^b := rpow_le_rpow_of_exponent_le n1 le
  have small' : 4800*(logb 2 (n:ℝ))^3≤(n:ℝ)^(1/6:ℝ) := small.trans (scale _ _ (by norm_num))
  have row2 := mul_le_mul_of_nonneg_right small' (rpow_nonneg np.le (1/2:ℝ))
  rw [←rpow_add np] at row2
  norm_num at row2
  have e1 : (((ub+m*ab:ℕ):ℝ)/(m*ρ)≤((s:ℝ)/100)/8) := by
    nlinarith only [rows,row2,geom,mul_le_mul_of_nonneg_right logcube (rpow_nonneg np.le (1/2:ℝ))]
  have room : 3+(logb 2 (n:ℝ))/2 ≤ (s:ℝ)/200 := by
    have d := small.trans (scale _ (2/3:ℝ) (by norm_num))
    linarith only [d,geom,logle,logcube]
  have packetScale : 8*(n:ℝ)^(1/2:ℝ) ≤ (2:ℝ)^((s:ℝ)/200) := by
    have eq : (2:ℝ)^(3+logb 2 n/2) = 8*(n:ℝ)^(1/2:ℝ) := by
      rw [rpow_add (by norm_num : (0:ℝ)<2),show logb 2 n/2=logb 2 n*(1/2) by ring,rpow_mul (by norm_num : (0:ℝ)≤2),rpow_logb (by norm_num) (by norm_num) np]
      norm_num
    rw [←eq]; exact rpow_le_rpow_of_exponent_le (by norm_num) room
  have e2 : packet/ρ≤(2:ℝ)^((s:ℝ)/100)/8 := by
    have one := div_le_div_of_nonneg_right packetSize ρp.le
    rw [div_eq_mul_inv packet,div_eq_mul_inv ((2:ℝ)^((s:ℝ)/200))] at one
    have a := mul_le_mul_of_nonneg_left invρ (rpow_nonneg (by norm_num : (0:ℝ)≤2) ((s:ℝ)/200))
    have b := mul_le_mul_of_nonneg_left packetScale (rpow_nonneg (by norm_num : (0:ℝ)≤2) ((s:ℝ)/200))
    rw [←rpow_add (by norm_num : (0:ℝ)<2),show (s:ℝ)/200+s/200=s/100 by ring] at b
    rw [one_div] at a
    rw [div_eq_mul_inv packet]; nlinarith only [one,a,b]
  have mn : (n:ℝ)^(4:ℝ)≤m := by rw [show (4:ℝ)=(4:ℕ) by norm_num, rpow_natCast]; exact_mod_cast size
  have denom := mul_le_mul mn accept (rpow_nonneg np.le _) mp.le
  rw [←rpow_add np,show (4:ℝ)+ -1/2=7/2 by norm_num] at denom
  have early := mul_le_mul_of_nonneg_left denom (rpow_nonneg np.le (-9/4:ℝ))
  rw [←rpow_add np,show (-9/4:ℝ)+7/2=5/4 by norm_num] at early
  have e3 : (ub:ℝ)/(m*ρ)≤(16*(n:ℝ)^(-9/4:ℝ))/8 := by
    apply (div_le_iff₀ (mul_pos mp ρp)).mpr
    nlinarith only [advice,early,mul_nonneg (rpow_nonneg np.le (-9/4:ℝ)) (mul_nonneg mp.le ρp.le)]
  have s1 : 1≤(s:ℝ) := by
    have d := small.trans (scale _ (2/3:ℝ) (by norm_num))
    linarith only [d,logcube,geom]
  have eight : 24<(n:ℝ)^(1/8:ℝ) := by
    have d := small.trans (scale _ (1/8:ℝ) (by norm_num))
    linarith only [d,logcube]
  have sq : sqrt ((log 2/2)*(16*(n:ℝ)^(-9/4:ℝ))) ≤ 3*(n:ℝ)^(-9/8:ℝ) := by
    apply Real.sqrt_le_iff.mpr ⟨by positivity,?_⟩
    rw [mul_pow,←rpow_mul_natCast np.le,show (-9/8:ℝ)*(2:ℕ)= -9/4 by norm_num]
    nlinarith only [mul_le_mul_of_nonneg_right (log_le_sub_one_of_pos (by norm_num : (0:ℝ)<2)) (rpow_nonneg np.le (-9/4:ℝ)),rpow_nonneg np.le (-9/4:ℝ)]
  have aux := mul_lt_mul_of_pos_right eight (rpow_pos_of_pos np (-9/8:ℝ))
  rw [←rpow_add np,show (1/8:ℝ)+ -9/8= -1 by norm_num,rpow_neg_one] at aux
  refine ⟨e1,e2,e3,?_⟩
  have per : 3*(n:ℝ)^(-9/8:ℝ)<(s:ℝ)/(8*n) := by
    calc _ < (n:ℝ)⁻¹/8 := by linarith only [aux]
         _ = (1:ℝ)/(8*n) := by field_simp; ring
         _ ≤ _ := div_le_div_of_nonneg_right s1 (by positivity)
  linarith only [sq,per,show (s:ℝ)/(4*n)=s/(8*n)+s/(8*n) by field_simp; ring]
/-- Restricting a uniformly random complete query row to any injectively
indexed epoch preserves the independent uniform coordinate distribution. -/
theorem restrict_uniform {n s : ℕ} [Nonempty (Fin n)] (e : Fin s ↪ Fin n) :
    (unif (Fin n → Fin n)).map (fun v j => v (e j)) = unif (Block n s) := by
  have ind := (independent_rows (β:=fun _ : Fin n => Fin n)).precomp e.injective
  have h := (iIndepFun_iff_map_fun_eq_pi_map (fun j : Fin s => (measurable_pi_apply (e j)).aemeasurable)).mp ind
  simp_rw [eval_uniform] at h
  exact h.trans (uniform_pi (β:=fun _ : Fin s => Fin n)).symm

/-- Communication lower bound for the 2.5-round fixed-public-coin game on
vector blocks. Acceptance and error are probabilities of actual executions;
the verifier may accept erroneous answers. -/
theorem robust_communication :
    ∀ᶠ n : ℕ in Filter.atTop, ∀ m s : ℕ, ∀ (W O R U P A : Type)
    [Fintype W] [MeasurableSpace W] [MeasurableSingletonClass W] [Nonempty W]
    [Fintype O] [MeasurableSpace O] [MeasurableSingletonClass O]
    [Fintype R] [MeasurableSpace R] [MeasurableSingletonClass R]
    [Fintype U] [MeasurableSpace U] [MeasurableSingletonClass U]
    [Fintype P] [MeasurableSpace P] [MeasurableSingletonClass P]
    [Fintype A] [MeasurableSpace A] [MeasurableSingletonClass A],
    ∀ (G : Game m n s W O R U P A) (o : Measure O) (r : Measure R)
    [IsProbabilityMeasure o] [IsProbabilityMeasure r],
    ∀ ub ab : ℕ, (n:ℝ)^(2/3:ℝ)/3≤s → s≤n → n^4≤m →
    (unif W).map G.block=unif (Block n s) →
    Fintype.card U≤2^ub → (ub:ℝ)≤(n:ℝ)^(5/4:ℝ) →
    (Fintype.card P:ℝ)≤(2:ℝ)^((s:ℝ)/200) →
    Fintype.card A≤2^ab → (ab:ℝ)≤(logb 2 n)^3 →
    (n:ℝ)^(-1/2:ℝ)≤acceptance G o r →
    (s:ℝ)/(64*n)<G.jointError o r/acceptance G o r := by
  filter_upwards [budget_geometry,Filter.eventually_ge_atTop 2] with n numeric two
  intro m s W O R U P A _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ G o r _ _ ub ab geom sn size bal hu advice packet ha replies accept
  have np : 0<(n:ℝ) := by exact_mod_cast (by omega : 0<n)
  haveI : Nonempty (Fin n) := ⟨⟨0,by omega⟩⟩
  have sreal := (div_pos (rpow_pos_of_pos np (2/3:ℝ)) (by norm_num : (0:ℝ)<3)).trans_le geom
  have sr : 1≤s := by exact_mod_cast (show 0<s by exact_mod_cast sreal)
  have hm : 0<m := lt_of_lt_of_le (Nat.pow_pos (by omega : 0<n)) size
  have hr := (rpow_pos_of_pos np (-1/2:ℝ)).trans_le accept
  obtain ⟨qb,xb,ib,tv⟩ := numeric m s ub ab (Fintype.card P) _ geom size advice replies packet accept
  by_contra! rare
  have hit : G.jointError o r/acceptance G o r≤((s:ℝ)/(8*n))/8 := by
    apply rare.trans_eq
    rw [div_div]; congr 1; ring
  obtain ⟨v,vp,query,update,corr,overlap⟩ := G.conditioning o r hm hr bal ub ab hu ha
    (d:=(s:ℝ)/100) (κ:=16*(n:ℝ)^(-9/4:ℝ)) (t:=(s:ℝ)/(8*n))
    (by positivity) (by positivity) (by positivity) qb xb ib hit
  have close := (G.product_overlap o r v vp overlap corr).trans_lt tv
  have many := AmortizedBound.Intersection.intersection_bound sr sn
    (G.queryPosterior o r v) (G.updatePosterior o r v)
    (by simpa [AmortizedBound.Intersection.bits,mul_comm] using query)
    (by simpa [AmortizedBound.Intersection.bits,mul_comm] using update)
  apply (not_lt_of_ge (many.2.trans many.1))
  convert close using 2
  ext z
  simp only [mem_filter,mem_univ,true_and,Game.overlaps]

end AmortizedBound.Communication

/-! ## Parameters -/

/-! Dyadic parameters and maximal backwards epochs for the amortized chronogram. -/
namespace AmortizedBound.Parameters

open Filter Real
open scoped Topology
noncomputable section

/-- Binary exponent of the rounded-up value of `(a*w)^2`. -/
def exponent (a w : ℝ) : ℕ := ⌈2 * logb 2 (a*w)⌉₊
def base (a w : ℝ) : ℕ := 2 ^ exponent a w
def sampleExponent (a w : ℝ) : ℕ := exponent a w + 1

def occupied (β : ℕ) : ℕ → ℕ
  | 0 => 0
  | d+1 => occupied β d + β^(d+1)

/-- The maximal depth that fits in the first half of the timeline. -/
def depth (n β : ℕ) : ℕ := Nat.findGreatest (fun d => occupied β d ≤ n/2) n

def candidates (d : ℕ) : Finset ℕ := Finset.Icc (d - ((d+1)/3) + 1) d

def cutoff (b : ℝ) (k : ℕ) : ℕ := ⌈32 * b / k⌉₊

def dyadicRate (a w : ℝ) : ℝ := (1/2 : ℝ)^sampleExponent a w

theorem rounded {a w : ℝ} (h : 1 ≤ a*w) :
    2 * logb 2 (a*w) ≤ exponent a w ∧
    (exponent a w : ℝ) < 2 * logb 2 (a*w) + 1 := by
  exact ⟨Nat.le_ceil _, Nat.ceil_lt_add_one (mul_nonneg (by norm_num) (logb_nonneg (by norm_num) h))⟩

theorem log_base (a w : ℝ) : logb 2 (base a w) = exponent a w := by
  simp [base, logb_pow, logb_self_eq_one]

theorem base_lower {a w : ℝ} (h : 1 ≤ a*w) : (a*w)^2 ≤ (base a w : ℝ) := by
  have pos : 0 < a*w := by linarith
  apply (logb_le_logb (b:=2) (by norm_num) (sq_pos_of_pos pos) (by simp [base])).mp
  rw [log_base, logb_pow]
  simpa using (rounded h).1

theorem rate_formula (a w : ℝ) : dyadicRate a w = 1/(2 * (base a w : ℝ)) := by
  simp [base, dyadicRate, sampleExponent, div_pow, pow_succ, mul_comm]

theorem prefix_ge {β : ℕ} (hb : 1 ≤ β) (d : ℕ) : d ≤ occupied β d := by
  induction d with
  | zero => simp [occupied]
  | succ d ih =>
    have : 0 < β^(d+1) := pow_pos (by omega) _
    simp only [occupied]; omega

theorem prefix_le {β : ℕ} (hb : 2 ≤ β) (d : ℕ) : occupied β d ≤ 2 * β^d := by
  induction d with
  | zero => simp [occupied]
  | succ d ih =>
    have h := Nat.mul_le_mul_left (β^d) hb
    rw [occupied, pow_succ]; nlinarith

theorem fits (n β : ℕ) : occupied β (depth n β) ≤ n/2 :=
  Nat.findGreatest_spec (P:=fun d => occupied β d ≤ n/2) (Nat.zero_le _) (by simp [occupied] : occupied β 0 ≤ n/2)

theorem maximal {n β : ℕ} (hb : 1 ≤ β) : n/2 < occupied β (depth n β + 1) := by
  by_contra! small
  exact Nat.findGreatest_is_greatest (P:=fun d => occupied β d ≤ n/2)
    (Nat.lt_succ_self (depth n β)) (by have := prefix_ge hb (depth n β+1); omega) small

theorem next_scale {n β : ℕ} (hb : 2 ≤ β) : n < 4*β^(depth n β+1) := by
  have := maximal (n:=n) (by omega : 1≤β)
  have := prefix_le hb (depth n β+1)
  omega

theorem mem_candidates {i d : ℕ} : i ∈ candidates d ↔ 1 ≤ i ∧ i ≤ d ∧ 2*(d+1) ≤ 3*i := by
  rw [candidates, Finset.mem_Icc]; omega

theorem count (d : ℕ) : (candidates d).card = (d+1)/3 := by
  rw [candidates, Nat.card_Icc]; omega

theorem candidate_bounds {n β i : ℕ} (hb : 2 ≤ β) (hi : i ∈ candidates (depth n β)) :
    n^2 ≤ 16*(β^i)^3 ∧ β^i ≤ n/2 ∧ β * occupied β (i-1) ≤ 2 * β^i := by
  obtain ⟨ip, il, large⟩ := mem_candidates.mp hi
  have nx := (next_scale (n:=n) hb).le
  have size := Nat.pow_le_pow_right (by omega : 0 < β) large
  rw [mul_comm 2, mul_comm 3, pow_mul, pow_mul] at size
  constructor
  · have h := Nat.pow_le_pow_left nx 2
    rw [mul_pow] at h
    exact h.trans (Nat.mul_le_mul_left 16 size)
  constructor
  · have dl : 0 < depth n β := by omega
    have fit := fits n β
    obtain ⟨t,ht⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt dl)
    rw [ht, occupied] at fit
    exact (Nat.pow_le_pow_right (by omega : 0 < β) (show i ≤ t+1 by omega)).trans (by omega)
  · have e : i-1+1=i := by omega
    calc β * occupied β (i-1) ≤ β*(2*β^(i-1)) := Nat.mul_le_mul_left _ (prefix_le hb _)
         _ = 2*β^i := by conv_rhs => rw [←e, pow_succ]
                         ring

theorem candidate_size {n β i : ℕ} (hb : 2 ≤ β) (hi : i ∈ candidates (depth n β)) :
    (n:ℝ)^(2/3:ℝ)/3 ≤ β^i := by
  have h : (n:ℝ)^2 ≤ 16*((β^i:ℕ):ℝ)^3 := by exact_mod_cast (candidate_bounds hb hi).1
  have b0 : (0:ℝ) ≤ (β^i:ℕ) := by positivity
  have n0 : (0:ℝ) ≤ n := by positivity
  have e : ((n:ℝ)^(2/3:ℝ))^3 = (n:ℝ)^2 := by
    rw [←Real.rpow_natCast, ←Real.rpow_mul n0]; norm_num
  apply (div_le_iff₀ (by norm_num : (0:ℝ)<3)).mpr
  apply le_of_not_gt
  intro contra
  have hp := pow_lt_pow_left₀ contra (by positivity) (by norm_num : 3 ≠ 0)
  push_cast at h b0
  rw [e] at hp
  nlinarith [pow_nonneg b0 3]


/-- Exact number of eligible epochs at the protocol's base. -/
def epochs (n : ℕ) (a w : ℝ) : ℕ := (candidates (depth n (base a w))).card

theorem base_two {a w : ℝ} (aw : 2 ≤ a*w) : 2 ≤ base a w := by
  have h := base_lower (by linarith : 1≤a*w)
  exact_mod_cast (show (2:ℝ) ≤ (base a w : ℝ) by nlinarith)

theorem logprod_ge {a w : ℝ} (aw : 2 ≤ a*w) : 1 ≤ logb 2 (a*w) := by
  simpa using logb_le_logb_of_le (b:=2) (by norm_num) (by norm_num : (0:ℝ)<2) aw

theorem count_scale {n : ℕ} {a w : ℝ} (np : 0<n) (aw : 2 ≤ a*w)
    (room : 40*logb 2 (a*w) ≤ logb 2 n) :
    logb 2 n ≤ 12 * epochs n a w * logb 2 (a*w) ∧
    (epochs n a w : ℝ)*logb 2 (a*w) ≤ logb 2 n := by
  let d := depth n (base a w)
  let k := epochs n a w
  let x := logb 2 (a*w)
  have kdef : k = (d+1)/3 := count _
  have d1 : (d:ℝ)+1 ≤ 3*k+2 := by exact_mod_cast (show d+1≤3*k+2 by omega)
  have x1 := logprod_ge aw
  have e := rounded (by linarith : 1≤a*w)
  have hb := base_two aw
  have br : 0<(base a w : ℝ) := by exact_mod_cast (by omega : 0<base a w)
  have npos : (0:ℝ)<n := by exact_mod_cast np
  have h := next_scale (n:=n) hb
  have le := logb_le_logb_of_le (b:=2) (by norm_num) npos
    (by exact_mod_cast h.le : (n:ℝ) ≤ 4*(base a w : ℝ)^(d+1))
  rw [logb_mul (by norm_num) (ne_of_gt (pow_pos br _)),logb_pow,log_base] at le
  have four : logb 2 4=2 := by rw [show (4:ℝ)=2^(2:ℕ) by norm_num, logb_pow]; simp
  rw [four] at le
  push_cast at le
  change logb 2 n ≤ 12*k*x ∧ (k:ℝ)*x ≤ logb 2 n
  change 1≤x at x1
  change 2*x ≤ _ ∧ _ < 2*x+1 at e
  change 40*x≤_ at room
  have bnd : (exponent a w:ℝ) ≤ 3*x := by linarith
  constructor
  · have t := mul_le_mul d1 bnd (Nat.cast_nonneg _) (by positivity)
    nlinarith only [le,t,room,x1]
  · by_cases dk : d = 0
    · have : k=0 := by omega
      rw [this]; simp; linarith
    · obtain ⟨j,jh⟩ := Nat.exists_eq_succ_of_ne_zero dk
      have fit : occupied (base a w) d ≤ n/2 := fits _ _
      rw [jh,occupied] at fit
      have low : (base a w)^d ≤ n := by rw [jh]; change (base a w)^(j+1) ≤ n; omega
      have lh := logb_le_logb_of_le (b:=2) (by norm_num) (pow_pos br d)
        (by exact_mod_cast low : (base a w : ℝ)^d ≤ n)
      rw [logb_pow,log_base] at lh
      have kd : (k:ℝ) ≤ d := by exact_mod_cast (show k≤d by omega)
      exact (mul_le_mul kd (by linarith : x≤(exponent a w : ℝ)) (by linarith) (Nat.cast_nonneg _)).trans lh

theorem cutoff_scale {n : ℕ} {a w b : ℝ} (np : 0<n) (aw : 2 ≤ a*w) (bp : 0≤b)
    (room : 40*logb 2 (a*w) ≤ logb 2 n) :
    (sampleExponent a w : ℝ)*cutoff b (epochs n a w) ≤
      1536*b*(logb 2 (a*w))^2/logb 2 n + 4*logb 2 (a*w) := by
  let k := epochs n a w
  let x := logb 2 (a*w)
  let L := logb 2 n
  have x1 : 1≤x := logprod_ge aw
  have kr : L ≤ 12*k*x := (count_scale np aw room).1
  have Lpos : 0<L := by change 40*x≤L at room; linarith
  have kp : (0:ℝ)<k := by
    by_contra! h
    have z := Nat.cast_nonneg (α:=ℝ) k
    have kz : (k:ℝ)=0 := by linarith
    rw [kz] at kr
    linarith
  have he := (rounded (by linarith : 1≤a*w)).2
  have h4 : (sampleExponent a w : ℝ) ≤ 4*x := by
    change (↑(exponent a w + 1) : ℝ) ≤ 4*x
    push_cast; change _ < 2*x+1 at he; linarith
  have cut : (cutoff b k : ℝ) ≤ 32*b/k+1 := (Nat.ceil_lt_add_one (by positivity)).le
  have h := mul_le_mul h4 cut (Nat.cast_nonneg _) (by positivity)
  have inv : 1/(k:ℝ) ≤ 12*x/L := by
    apply (div_le_div_iff₀ kp Lpos).mpr; nlinarith only [kr]
  have bnd := mul_le_mul_of_nonneg_left inv (show 0≤128*b*x by positivity)
  change (sampleExponent a w:ℝ)*(cutoff b k:ℝ) ≤ 1536*b*x^2/L+4*x
  calc _ ≤ 4*x*(32*b/k+1) := h
       _ = (128*b*x)*(1/k) + 4*x := by ring
       _ ≤ (128*b*x)*(12*x/L)+4*x := by linarith only [bnd]
       _ = _ := by ring

/-- The three asymptotic hypotheses of the simulation, also usable on a
subsequence by choosing a finer filter than `atTop`. -/
structure Fast (f : Filter ℕ) (a w b : ℕ → ℝ) : Prop where
  large : f ≤ atTop
  positive : ∀ᶠ n : ℕ in f, 1 ≤ a n ∧ 1 ≤ b n
  update : ∀ ε : ℝ, 0 < ε → ∀ᶠ n : ℕ in f, a n ≤ (n:ℝ)^ε
  word : ∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∀ᶠ n : ℕ in f,
    c * logb 2 n ≤ w n ∧ w n ≤ C * logb 2 n
  query : ∀ ε : ℝ, 0 < ε → ∀ᶠ n : ℕ in f,
    b n ≤ ε * (logb 2 n / logb 2 (a n*w n))^2

variable {f : Filter ℕ} {a w b : ℕ → ℝ}

/-- Update costs and word growth before a query-cost function is chosen. -/
structure PhysicalScale (f : Filter ℕ) (a w : ℕ → ℝ) : Prop where
  large : f ≤ atTop
  positive : ∀ᶠ n : ℕ in f, 1 ≤ a n
  update : ∀ ε : ℝ, 0 < ε → ∀ᶠ n : ℕ in f, a n ≤ (n:ℝ)^ε
  word : ∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∀ᶠ n : ℕ in f,
    c * logb 2 n ≤ w n ∧ w n ≤ C * logb 2 n

theorem Fast.physical (fast : Fast f a w b) : PhysicalScale f a w :=
  ⟨fast.large,fast.positive.mono fun _ => And.left,fast.update,fast.word⟩

private theorem word_power (C e : ℝ) (ep : 0<e) :
    ∀ᶠ n : ℕ in atTop, C * logb 2 n ≤ (n:ℝ)^e := by
  have h := (isLittleO_log_rpow_atTop ep).const_mul_left (C/log 2)
  have he := (h.bound (by norm_num : (0:ℝ)<1)).filter_mono
    (show Filter.map (fun n : ℕ => (n:ℝ)) atTop ≤ atTop from tendsto_natCast_atTop_atTop)
  change ∀ᶠ n : ℕ in atTop, C * logb 2 n ≤ (n:ℝ)^e
  filter_upwards [show ∀ᶠ n : ℕ in atTop, ‖(C/log 2)*Real.log (n:ℝ)‖≤1*‖(n:ℝ)^e‖ from he] with n h
  rw [Real.norm_eq_abs,Real.norm_eq_abs,abs_of_nonneg (rpow_nonneg (Nat.cast_nonneg _) _),one_mul] at h
  exact (show C*logb 2 n=(C/log 2)*Real.log n by rw [logb]; ring).le.trans ((le_abs_self _).trans h)

theorem PhysicalScale.growing (fast : PhysicalScale f a w) (D : ℝ) : ∀ᶠ n : ℕ in f, D ≤ a n*w n := by
  obtain ⟨c,C,cp,_,ww⟩ := fast.word
  filter_upwards [fast.positive, ww, (DisjointnessFoundations.Tradeoff.log_tends.eventually_ge_atTop
    (max 0 D/c)).filter_mono fast.large] with n ab word h
  have ww0 := (div_le_iff₀ cp).mp h
  have wp : 0 ≤ w n := by linarith only [word.1,ww0,le_max_left 0 D]
  have mul := mul_le_mul_of_nonneg_right ab wp
  linarith only [word.1,ww0,mul,le_max_right 0 D]

theorem PhysicalScale.product_power (fast : PhysicalScale f a w) {e : ℝ} (ep : 0<e) :
    ∀ᶠ n : ℕ in f, a n*w n ≤ (n:ℝ)^e := by
  obtain ⟨_,C,_,_,ww⟩ := fast.word
  have half : 0<e/2 := by linarith
  filter_upwards [fast.update (e/2) half, (word_power C (e/2) half).filter_mono fast.large,
    ww, fast.positive, fast.growing 2, (eventually_ge_atTop 1).filter_mono fast.large] with n aa bb word ap pos np
  have wp : 0 ≤ w n := by by_contra! neg; nlinarith [mul_neg_of_pos_of_neg (by linarith : 0<a n) neg]
  have nn : (0:ℝ)<n := by exact_mod_cast np
  calc a n*w n ≤ (n:ℝ)^(e/2)*(n:ℝ)^(e/2) :=
        mul_le_mul aa (word.2.trans bb) wp (rpow_nonneg nn.le _)
       _ = _ := by rw [←Real.rpow_add nn, add_halves]

theorem PhysicalScale.log_product (fast : PhysicalScale f a w) {e : ℝ} (ep : 0<e) :
    ∀ᶠ n : ℕ in f, logb 2 (a n*w n) ≤ e*logb 2 n := by
  filter_upwards [fast.product_power ep, fast.growing 2,
    (eventually_ge_atTop 1).filter_mono fast.large] with n h ap np
  have nn : (0:ℝ)<n := by exact_mod_cast np
  have lh := logb_le_logb_of_le (b:=2) (by norm_num) (by linarith : 0<a n*w n) h
  rwa [Real.logb_rpow_eq_mul_logb_of_pos nn] at lh


theorem growing_product (fast : Fast f a w b) (D : ℝ) : ∀ᶠ n : ℕ in f, D ≤ a n*w n := fast.physical.growing D

theorem product_power (fast : Fast f a w b) {e : ℝ} (ep : 0<e) :
    ∀ᶠ n : ℕ in f, a n*w n ≤ (n:ℝ)^e := fast.physical.product_power ep

theorem log_product (fast : Fast f a w b) {e : ℝ} (ep : 0<e) :
    ∀ᶠ n : ℕ in f, logb 2 (a n*w n) ≤ e*logb 2 n := fast.physical.log_product ep

theorem good_count (fast : Fast f a w b) :
    ∀ᶠ n : ℕ in f, logb 2 n ≤ 12*epochs n (a n) (w n)*logb 2 (a n*w n) ∧
      (epochs n (a n) (w n):ℝ)*logb 2 (a n*w n) ≤ logb 2 n := by
  filter_upwards [log_product fast (by norm_num : (0:ℝ)<1/40), growing_product fast 2,
    (eventually_ge_atTop 1).filter_mono fast.large] with n h aw np
  exact count_scale np aw (by linarith)

theorem cutoff_little (fast : Fast f a w b) {e : ℝ} (ep : 0<e) :
    ∀ᶠ n : ℕ in f, (sampleExponent (a n) (w n):ℝ)*cutoff (b n) (epochs n (a n) (w n)) ≤ e*logb 2 n := by
  filter_upwards [log_product fast (by norm_num : (0:ℝ)<1/40),
    log_product fast (show 0<e/8 by linarith), growing_product fast 2,
    fast.query (e/3072) (by positivity), fast.positive,
    (eventually_ge_atTop 1).filter_mono fast.large] with n room small aw q ab np
  let L := logb 2 n
  let x := logb 2 (a n*w n)
  have x1 : 1≤x := logprod_ge aw
  have Lpos : 0<L := by change x≤1/40*L at room; linarith
  have hr := cutoff_scale np aw (by linarith : 0≤b n) (by linarith)
  change _ ≤ 1536*b n*x^2/L+4*x at hr
  change b n ≤ (e/3072)*(L/x)^2 at q
  have u := mul_le_mul_of_nonneg_right q (sq_nonneg x)
  have ux : (e/3072)*(L/x)^2*x^2=(e/3072)*L^2 := by field_simp [show x≠0 by linarith]; ring
  rw [ux] at u
  have z : 1536*b n*x^2/L ≤ e/2*L := (div_le_iff₀ Lpos).mpr (by nlinarith only [u])
  change x≤e/8*L at small
  linarith only [hr,z,small]

theorem normalizer (fast : Fast f a w b) {e : ℝ} (ep : 0<e) :
    ∀ᶠ n : ℕ in f, (n:ℝ)^(-e) ≤
      (dyadicRate (a n) (w n))^(cutoff (b n) (epochs n (a n) (w n))) := by
  filter_upwards [cutoff_little fast ep, (eventually_ge_atTop 1).filter_mono fast.large] with n hr np
  let h := sampleExponent (a n) (w n)
  let r := cutoff (b n) (epochs n (a n) (w n))
  have nn : (0:ℝ)<n := by exact_mod_cast np
  have e2 := Real.rpow_le_rpow_of_exponent_le (by norm_num : (1:ℝ)≤2) hr
  change (2:ℝ)^((h:ℝ)*(r:ℝ)) ≤ 2^(e*logb 2 n) at e2
  rw [mul_comm e (logb 2 n), Real.rpow_mul (by norm_num : (0:ℝ)≤2) (logb 2 n) e,
    Real.rpow_logb (by norm_num) (by norm_num) nn] at e2
  rw [Real.rpow_neg nn.le]
  change _ ≤ ((1/2:ℝ)^h)^r
  rw [←pow_mul,div_pow,one_pow,one_div]
  exact inv_anti₀ (by positivity) ((by
    rw [←Real.rpow_natCast, Nat.cast_mul]
    exact e2) : (2:ℝ)^(h*r) ≤ (n:ℝ)^e)

theorem base_power (fast : Fast f a w b) {e : ℝ} (ep : 0<e) :
    ∀ᶠ n : ℕ in f, (base (a n) (w n):ℝ) ≤ (n:ℝ)^e := by
  filter_upwards [log_product fast (show 0<e/4 by positivity), growing_product fast 2,
    (DisjointnessFoundations.Tradeoff.log_tends.eventually_ge_atTop (2/e)).filter_mono fast.large,
    (eventually_ge_atTop 1).filter_mono fast.large] with n h aw lg np
  have nn : (0:ℝ)<n := by exact_mod_cast np
  have br : 0<(base (a n) (w n):ℝ) := by simp [base]
  apply (logb_le_logb (b:=2) (by norm_num) br (Real.rpow_pos_of_pos nn _)).mp
  rw [log_base,Real.logb_rpow_eq_mul_logb_of_pos nn]
  have gap := (div_le_iff₀ ep).mp lg
  have e2 := (rounded (by linarith : 1≤a n*w n)).2
  linarith

theorem packet_budget (fast : Fast f a w b) (C : ℝ) :
    ∀ᶠ n : ℕ in f, ∀ i ∈ candidates (depth n (base (a n) (w n))),
      let s : ℝ := (base (a n) (w n) : ℝ)^i
      600*(a n*w n)*s/(base (a n) (w n):ℝ) + C*logb 2 n ≤ s/200 := by
  filter_upwards [growing_product fast 240000,
    (word_power (1200*C) (2/3) (by norm_num)).filter_mono fast.large] with n aw small
  intro i hi
  let β := base (a n) (w n)
  let s : ℝ := (β:ℝ)^i
  have bp : (0:ℝ)<β := by dsimp [β]; simp [base]
  have low := base_lower (by linarith : 1 ≤ a n*w n)
  have cap : 240000*(a n*w n) ≤ (β:ℝ) :=
    (by nlinarith only [mul_le_mul_of_nonneg_right aw (show 0≤a n*w n by linarith)] : 240000*(a n*w n)≤(a n*w n)^2) |>.trans low
  have h := candidate_size (base_two (by linarith : 2≤a n*w n)) hi
  change (n:ℝ)^(2/3:ℝ)/3≤s at h
  have frac : 600*(a n*w n)*s/(β:ℝ)≤s/400 := (div_le_iff₀ bp).mpr (by
    nlinarith only [mul_le_mul_of_nonneg_right cap (show 0≤s by dsimp [s]; positivity)])
  change 600*(a n*w n)*s/(β:ℝ)+C*logb 2 n ≤ s/200
  linarith

theorem advice_budget (fast : Fast f a w b) {C : ℝ} (cp : 0≤C) :
    ∀ᶠ n : ℕ in f, C * (a n*w n*(n:ℝ) + (logb 2 n)^2) ≤ (n:ℝ)^(5/4:ℝ) := by
  have grow := (tendsto_rpow_atTop (by norm_num : (0:ℝ)<1/8)).comp tendsto_natCast_atTop_atTop
  filter_upwards [product_power fast (by norm_num : (0:ℝ)<1/8),
    ((word_power 1 (1/2) (by norm_num)).filter_mono fast.large),
    (grow.eventually_ge_atTop (2*C)).filter_mono fast.large, growing_product fast 2,
    (eventually_ge_atTop 1).filter_mono fast.large] with n prod word big aw np
  have nn : (1:ℝ)≤n := by exact_mod_cast np
  have pos : (0:ℝ)<n := by linarith
  have logpos := logb_nonneg (by norm_num : (1:ℝ)<2) nn
  simp only [one_mul] at word
  have sq := pow_le_pow_left₀ logpos word 2
  rw [←rpow_mul_natCast pos.le] at sq
  norm_num at sq
  have hC : 2*C ≤ (n:ℝ)^(1/8:ℝ) := big
  have first := mul_le_mul hC prod (by linarith : 0≤a n*w n) (rpow_nonneg pos.le _)
  rw [←rpow_add pos] at first
  norm_num at first
  have c2 := hC.trans (rpow_le_rpow_of_exponent_le nn (by norm_num : (1/8:ℝ)≤1/4))
  have one := mul_le_mul_of_nonneg_right first pos.le
  have two := mul_le_mul_of_nonneg_right c2 pos.le
  have sq2 := mul_le_mul_of_nonneg_left sq cp
  have ident : (n:ℝ)^(1/4:ℝ)*(n:ℝ)=(n:ℝ)^(5/4:ℝ) := by
    rw [←Real.rpow_add_one pos.ne']; norm_num
  rw [ident] at one two
  nlinarith only [one,two,sq2]

theorem reply_budget (fast : Fast f a w b) {C : ℝ} (cp : 0<C) :
    ∀ᶠ n : ℕ in f, C*(w n*b n + logb 2 n) ≤ (logb 2 n)^3 := by
  obtain ⟨_,W,_,Wp,ww⟩ := fast.word
  have ep : 0 < 1/(2*C*W) := by positivity
  filter_upwards [ww,fast.query _ ep, growing_product fast 2, fast.positive,
    (DisjointnessFoundations.Tradeoff.log_tends.eventually_ge_atTop (max 1 (2*C))).filter_mono fast.large] with n word q aw ab lg
  let L := logb 2 n
  let x := logb 2 (a n*w n)
  have x1 : 1≤x := logprod_ge aw
  have l1 : 1≤L := (le_max_left ..).trans lg
  have lc : 2*C≤L := (le_max_right ..).trans lg
  have d : L/x ≤ L := (div_le_iff₀ (by linarith)).mpr (by nlinarith only [mul_le_mul_of_nonneg_left x1 (show 0≤L by linarith)])
  have ratio := pow_le_pow_left₀ (show 0≤L/x by positivity) d 2
  have upper := q.trans (mul_le_mul_of_nonneg_left ratio ep.le)
  have two : (2*C*W)*b n ≤ L^2 := by
    change b n ≤ 1/(2*C*W)*L^2 at upper
    have pp : 0<2*C*W := by positivity
    rw [one_div, inv_mul_eq_div] at upper
    nlinarith only [(le_div_iff₀ pp).mp upper]
  have wbound := mul_le_mul_of_nonneg_right word.2 (show 0≤b n by linarith [ab.2])
  have u := mul_le_mul_of_nonneg_left wbound (show 0≤2*C by positivity)
  have v := mul_le_mul_of_nonneg_right two (show 0≤L by linarith)
  have u2 := mul_le_mul_of_nonneg_right lc (show 0≤L by linarith)
  have v2 := mul_le_mul_of_nonneg_right l1 (sq_nonneg L)
  change C*(w n*b n+L) ≤ L^3
  change w n*b n ≤ W*L*b n at wbound
  change 2*C*(w n*b n) ≤ 2*C*(W*L*b n) at u
  nlinarith only [u,v,u2,v2]

/-- The additive sampling tail is exponentially smaller than the dyadic
normalizing probability, uniformly in the eligible epoch. -/
theorem relative_tail (fast : Fast f a w b) :
    ∀ᶠ n : ℕ in f, ∀ i ∈ candidates (depth n (base (a n) (w n))),
      let s : ℝ := (base (a n) (w n) : ℝ)^i
      let K := ⌊64*a n*s⌋₊
      let p := dyadicRate (a n) (w n)
      exp (-(p*K)/3) ≤ p^(cutoff (b n) (epochs n (a n) (w n))) * (2:ℝ)^(-√(n:ℝ)) := by
  filter_upwards [base_power fast (by norm_num : (0:ℝ)<1/6),
    normalizer fast (by norm_num : (0:ℝ)<1), fast.positive, growing_product fast 2,
    (word_power (log 2) (1/2) (by norm_num)).filter_mono fast.large,
    (eventually_ge_atTop 1).filter_mono fast.large] with n baseCap gamma ab aw small np
  intro i hi
  let β := base (a n) (w n)
  let s := (β:ℝ)^i
  let K := ⌊64*a n*s⌋₊
  let p := dyadicRate (a n) (w n)
  have nn : (0:ℝ)<n := by exact_mod_cast np
  have bp : (0:ℝ)<β := by dsimp [β]; simp [base]
  have b1 : (1:ℝ) ≤ β := by exact_mod_cast (show 1≤β from (by dsimp [β]; exact Nat.one_le_pow _ _ (by norm_num)))
  have s1 : 1≤s := one_le_pow₀ b1
  have slo := candidate_size (base_two aw) hi
  change (n:ℝ)^(2/3:ℝ)/3 ≤ s at slo
  have rt := mul_le_mul_of_nonneg_right baseCap (Real.sqrt_nonneg n)
  rw [Real.sqrt_eq_rpow,←Real.rpow_add nn] at rt
  norm_num at rt
  change (β:ℝ)*((n:ℝ)^(1/2:ℝ)) ≤ _ at rt
  have sf := mul_le_mul_of_nonneg_right ab.1 (show 0≤s by linarith)
  have fl : 64*a n*s - 1 < (K:ℝ) := Nat.sub_one_lt_floor _
  have low : 63*s ≤ (K:ℝ) := by nlinarith only [s1,sf,fl]
  have force : 2*√(n:ℝ) ≤ p*K/3 := by
    change 2*√(n:ℝ) ≤ dyadicRate (a n) (w n)*K/3
    rw [rate_formula]
    change 2*√(n:ℝ) ≤ (1/(2*(β:ℝ)))*K/3
    rw [one_div, inv_mul_eq_div, div_div]
    apply (le_div_iff₀ (by positivity)).mpr
    rw [sqrt_eq_rpow]
    nlinarith only [rt,slo,low]
  rw [←sqrt_eq_rpow] at small
  have log_le : log (n:ℝ) ≤ √(n:ℝ) := by
    rw [logb, mul_div_cancel₀ _ (ne_of_gt (log_pos (by norm_num : (1:ℝ)<2)))] at small
    exact small
  have logtwo : log 2 ≤ 1 := by linarith only [Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ)<2)]
  have neg := mul_le_mul_of_nonneg_right logtwo (sqrt_nonneg (n:ℝ))
  change exp (-(p*(K:ℝ))/3) ≤ _
  calc exp (-(p*(K:ℝ))/3) ≤ exp (log (n:ℝ)*(-1) + log 2*(-√(n:ℝ))) :=
        Real.exp_le_exp.mpr (by linarith only [force, log_le, neg])
       _ = (n:ℝ)^(-(1:ℝ))*(2:ℝ)^(-√(n:ℝ)) := by
         rw [Real.exp_add,Real.rpow_def_of_pos nn,Real.rpow_def_of_pos (by norm_num : (0:ℝ)<2)]
       _ ≤ _ := mul_le_mul_of_nonneg_right gamma (by positivity)

/-- Direct specialization to the three finite message alphabets, including
the abort flag, both integer roundings and the independent padding string. -/
theorem encoded_budgets {W : ℕ → ℕ} (fast : Fast f a (fun n => (W n:ℝ)) b) :
    ∀ᶠ n : ℕ in f, ∀ i ∈ candidates (depth n (base (a n) (W n))),
      let β := base (a n) (W n)
      let s := β^i
      let e := ⌊64*a n*s⌋₊
      let l := ⌊64*a n*occupied β (i-1)⌋₊
      let cap := ⌊2*dyadicRate (a n) (W n)*e⌋₊
      let h := sampleExponent (a n) (W n)
      let r := cutoff (b n) (epochs n (a n) (W n))
      (DisjointnessDraft.PhysicalProtocol.adviceBits (W n) e l + 1 : ℕ) ≤ (n:ℝ)^(5/4:ℝ) ∧
      ((DisjointnessDraft.PhysicalProtocol.packetBits (W n) l cap + h*r : ℕ):ℝ) ≤ (s:ℝ)/200 ∧
      (DisjointnessDraft.PhysicalProtocol.replyBits (W n) ⌊32*b n⌋₊ : ℝ) ≤ (logb 2 n)^3 := by
  filter_upwards [advice_budget fast (by norm_num : (0:ℝ)≤400), packet_budget fast 2,
    reply_budget fast (by norm_num : (0:ℝ)<100), cutoff_little fast (by norm_num : (0:ℝ)<1),
    growing_product fast 2, fast.positive,
    (DisjointnessFoundations.Tradeoff.log_tends.eventually_ge_atTop 1).filter_mono fast.large] with n adv pkg rep hr aw ab L1
  intro i hi
  let W' : ℝ := W n
  let A := a n
  let B := b n
  let β := base A W'
  let s := β^i
  let t := occupied β (i-1)
  let e := ⌊64*A*s⌋₊
  let l := ⌊64*A*t⌋₊
  let cap := ⌊2*dyadicRate A W'*e⌋₊
  let h := sampleExponent A W'
  let r := cutoff B (epochs n A W')
  have wp : 1 ≤ W n := by
    apply Nat.pos_of_ne_zero
    intro eq
    norm_num [eq] at aw
  have w1 : 1≤W' := by dsimp [W']; exact_mod_cast wp
  have a1 : 1≤A := ab.1
  have b1 : 1≤B := ab.2
  have hb : 2≤β := base_two aw
  have bp : (0:ℝ)<β := by exact_mod_cast (by omega : 0<β)
  obtain ⟨_,sn,ts⟩ := candidate_bounds hb hi
  have ns : (s:ℝ)≤n := by exact_mod_cast sn.trans (Nat.div_le_self _ _)
  have ts' : (β:ℝ)*t ≤ 2*s := by exact_mod_cast ts
  have ts2 : (t:ℝ)≤s := by
    have b2 : (2:ℝ)≤β := by exact_mod_cast hb
    nlinarith only [ts',mul_le_mul_of_nonneg_right b2 (Nat.cast_nonneg (α:=ℝ) t)]
  have w3 : 2*W'+1 ≤ 3*W' := by linarith
  have ep : (e:ℝ)≤64*A*s := Nat.floor_le (by positivity)
  have lp : (l:ℝ)≤64*A*t := Nat.floor_le (by positivity)
  have cap0 : 0≤dyadicRate A W' := by rw [rate_formula]; positivity
  have cp : (cap:ℝ)≤2*dyadicRate A W'*e := Nat.floor_le (by positivity)
  rw [rate_formula] at cp
  have cp1 : (cap:ℝ) ≤ (e:ℝ)/β := cp.trans_eq (by dsimp [β]; field_simp; ring)
  have cpβ := (le_div_iff₀ bp).mp cp1
  have lβ := mul_le_mul_of_nonneg_right lp bp.le
  have ltBound := mul_le_mul_of_nonneg_left ts' (show 0≤64*A by positivity)
  have table : ((l:ℝ)+cap)*(β:ℝ) ≤ 192*A*s := by nlinarith only [lβ,ltBound,cpβ,ep]
  have u := mul_le_mul_of_nonneg_left ts2 (show 0≤64*A by positivity)
  have v := mul_le_mul_of_nonneg_left ns (show 0≤128*A by positivity)
  have es : (e:ℝ)+l≤128*A*n := by linarith only [ep,lp,u,v]
  have boundU := mul_le_mul w3 es (by positivity) (by positivity)
  have boundP0 := mul_le_mul_of_nonneg_right w3 (show 0≤((l:ℝ)+cap) by positivity)
  have boundP1 := mul_le_mul_of_nonneg_right boundP0 bp.le
  have boundP2 := mul_le_mul_of_nonneg_left table (show 0≤3*W' by positivity)
  have boundP : (2*W'+1)*((l:ℝ)+cap) ≤ 600*(A*W')*s/β := (le_div_iff₀ bp).mpr (by
    nlinarith only [boundP1,boundP2,mul_nonneg (mul_nonneg (by linarith : 0≤A) (by linarith : 0≤W')) (Nat.cast_nonneg (α:=ℝ) s)])
  have pkt := pkg i hi
  change 600*(A*W')*((β:ℝ)^i)/β+2*logb 2 n ≤ ((β:ℝ)^i)/200 at pkt
  have eqs : (s:ℝ)=(β:ℝ)^i := by simp [s]
  rw [←eqs] at pkt
  have fuel : (⌊32*B⌋₊:ℝ) ≤ 32*B := Nat.floor_le (by positivity)
  have boundR := mul_le_mul w3 fuel (by positivity) (by positivity)
  change 400*(A*W'*n+(logb 2 n)^2) ≤ (n:ℝ)^(5/4:ℝ) at adv
  change 100*(W'*B+logb 2 n) ≤ (logb 2 n)^3 at rep
  change (h:ℝ)*r ≤ 1*logb 2 n at hr
  change ((DisjointnessDraft.PhysicalProtocol.adviceBits (W n) e l+1:ℕ):ℝ) ≤ _ ∧
    ((DisjointnessDraft.PhysicalProtocol.packetBits (W n) l cap+h*r:ℕ):ℝ) ≤ (s:ℝ)/200 ∧
    (DisjointnessDraft.PhysicalProtocol.replyBits (W n) ⌊32*B⌋₊:ℝ) ≤ _
  simp only [DisjointnessDraft.PhysicalProtocol.adviceBits,DisjointnessDraft.PhysicalProtocol.packetBits,
    DisjointnessDraft.PhysicalProtocol.replyBits,Nat.cast_add,Nat.cast_mul,Nat.cast_ofNat,Nat.cast_one]
  change (2*W'+1)*((e:ℝ)+l)+1 ≤ _ ∧ (2*W'+1)*((l:ℝ)+cap)+1+(h:ℝ)*r ≤ _ ∧
    (2*W'+1)*(⌊32*B⌋₊:ℝ)+2 ≤ _
  refine ⟨?_, by linarith only [boundP,pkt,hr,L1], ?_⟩
  · nlinarith only [adv,boundU,mul_nonneg (mul_nonneg (by linarith : 0≤A) (by linarith : 0≤W')) (Nat.cast_nonneg (α:=ℝ) n), sq_nonneg (logb 2 n-1),L1]
  · nlinarith only [rep,boundR,L1,mul_nonneg (by linarith : 0≤W') (by linarith : 0≤B)]

/-- Saturating a potentially subunit query cost at one preserves its
little-o bound because the target ratio tends to infinity. -/
theorem fast_single (scale : PhysicalScale f a w)
    (small : ∀ ε : ℝ, 0<ε → ∀ᶠ n : ℕ in f, b n ≤ ε*(logb 2 n/logb 2 (a n*w n))^2) :
    Fast f a w (fun n => max 1 (b n)) := by
  refine ⟨scale.large,scale.positive.mono (fun n hn => ⟨hn,le_max_left ..⟩),scale.update,scale.word,?_⟩
  intro ε ep
  have root := Real.sqrt_pos.mpr ep
  filter_upwards [small ε ep,scale.log_product root,scale.growing 2] with n bnd logbnd aw
  refine max_le ?_ bnd
  let L := logb 2 n
  let x := logb 2 (a n*w n)
  have xp : 0<x := by have := logprod_ge aw; dsimp [x]; linarith
  have hx : 1/√ε ≤ L/x := (div_le_div_iff₀ root xp).mpr (by
    change x≤√ε*L at logbnd; linarith)
  have sq := mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) hx 2) ep.le
  have eq : ε*(1/√ε)^2=1 := by rw [div_pow,Real.sq_sqrt ep.le]; field_simp
  exact eq.ge.trans sq

/-- The real cap satisfies the claimed uniform lower bound, with every
positive exponent slack allowed. -/
theorem sigma_scale (fast : Fast f a w b) {ε : ℝ} (ep : 0<ε) :
    ∀ᶠ n : ℕ in f, ∀ i ∈ candidates (depth n (base (a n) (w n))),
      (n:ℝ)^(2/3-ε:ℝ) ≤ 64*dyadicRate (a n) (w n)*a n*(base (a n) (w n):ℝ)^i := by
  filter_upwards [base_power fast ep,fast.positive,growing_product fast 2,
    (eventually_ge_atTop 1).filter_mono fast.large] with n cap ab aw np
  intro i hi
  let β := base (a n) (w n)
  let s : ℝ := (β:ℝ)^i
  have bp : (0:ℝ)<β := by dsimp [β]; simp [base]
  have nn : (0:ℝ)<n := by exact_mod_cast np
  have sl := candidate_size (base_two aw) hi
  change (n:ℝ)^(2/3:ℝ)/3 ≤ s at sl
  have low := mul_le_mul_of_nonneg_right cap (rpow_nonneg nn.le (2/3-ε:ℝ))
  rw [←rpow_add nn,show ε+(2/3-ε)=(2/3:ℝ) by ring] at low
  rw [rate_formula]
  change (n:ℝ)^(2/3-ε:ℝ) ≤ 64*(1/(2*(β:ℝ)))*a n*s
  have eq : 64*(1/(2*(β:ℝ)))*a n*s = 32*a n*s/β := by field_simp; ring
  rw [eq]
  apply (le_div_iff₀ bp).mpr
  have le := mul_le_mul_of_nonneg_right ab.1 (show 0≤s by dsimp [s]; positivity)
  nlinarith only [low,sl,le,show 0≤s by dsimp [s]; positivity]

theorem cutoff_vs_sigma (fast : Fast f a w b) {ε : ℝ} (ep : 0<ε) :
    ∀ᶠ n : ℕ in f, ∀ i ∈ candidates (depth n (base (a n) (w n))),
      (cutoff (b n) (epochs n (a n) (w n)):ℝ) ≤
        ε*(64*dyadicRate (a n) (w n)*a n*(base (a n) (w n):ℝ)^i) := by
  filter_upwards [cutoff_little fast ep,sigma_scale fast (by norm_num : (0:ℝ)<1/6),
    (word_power 1 (1/2) (by norm_num)).filter_mono fast.large] with n hr sig lg
  intro i hi
  have h1 : (1:ℝ) ≤ sampleExponent (a n) (w n) := by unfold sampleExponent; push_cast; linarith [Nat.cast_nonneg (α:=ℝ) (exponent (a n) (w n))]
  have h := mul_le_mul_of_nonneg_right h1 (Nat.cast_nonneg (α:=ℝ) (cutoff (b n) (epochs n (a n) (w n))))
  have bound := sig i hi
  norm_num at bound lg
  rw [one_mul] at h
  exact h.trans (hr.trans (mul_le_mul_of_nonneg_left (lg.trans bound) ep.le))

/-- A counterexample sequence for total interleaved work produces the
simulation parameters `a=max 1 τ` and `b=2a`. -/
theorem fast_total {τ : ℕ → ℝ} (large : f ≤ atTop)
    (word : ∃ c C : ℝ, 0<c ∧ 0<C ∧ ∀ᶠ n : ℕ in f,
      c*logb 2 n ≤ w n ∧ w n ≤ C*logb 2 n)
    (small : ∀ ε : ℝ, 0<ε → ∀ᶠ n : ℕ in f,
      τ n ≤ ε*(logb 2 n/logb 2 (logb 2 n))^2) :
    Fast f (fun n => max 1 (τ n)) w (fun n => 2*max 1 (τ n)) := by
  let L (n : ℕ) := logb 2 n
  let A (n : ℕ) := max 1 (τ n)
  have unit : PhysicalScale f (fun _ => 1) L := by
    refine ⟨large,Eventually.of_forall (fun _ => le_rfl),?_,1,1,by norm_num,by norm_num,?_⟩
    · intro e ep
      filter_upwards [(eventually_ge_atTop 1).filter_mono large] with n np
      exact Real.one_le_rpow (by exact_mod_cast np) ep.le
    · exact Eventually.of_forall fun n => by simp [L]
  have baseline := fast_single (b:=τ) unit (by simpa [L] using small)
  have bounded : ∀ᶠ n : ℕ in f, A n ≤ (L n)^2 := by
    filter_upwards [baseline.query 1 (by norm_num),
      (DisjointnessFoundations.Tradeoff.log_tends.eventually_ge_atTop 2).filter_mono large] with n h lg
    have x1 : 1≤logb 2 (L n) := by
      simpa using logb_le_logb_of_le (b:=2) (by norm_num) (by norm_num : (0:ℝ)<2) lg
    have lnn : 0≤L n := by change 2≤L n at lg; linarith
    have d : L n/logb 2 (L n) ≤ L n := (div_le_iff₀ (by linarith)).mpr (by
      nlinarith only [mul_le_mul_of_nonneg_left x1 lnn])
    simp only [one_mul] at h
    exact h.trans (pow_le_pow_left₀ (by positivity) d 2)
  have physical : PhysicalScale f A w := by
    refine ⟨large,Eventually.of_forall (fun _ => le_max_left ..),?_,word⟩
    intro e ep
    filter_upwards [bounded,(word_power 1 (e/2) (by positivity)).filter_mono large,
      (eventually_ge_atTop 1).filter_mono large] with n bnd lp np
    have nn : (0:ℝ)<n := by exact_mod_cast np
    have pos : 0≤L n := logb_nonneg (by norm_num) (by exact_mod_cast np)
    simp only [one_mul] at lp
    have sq := pow_le_pow_left₀ pos lp 2
    rw [←rpow_mul_natCast nn.le,show e/2*(↑(2:ℕ):ℝ)=e by push_cast; ring] at sq
    exact bnd.trans sq
  obtain ⟨c,C,cp,_,ww⟩ := word
  refine ⟨large,?_,physical.update,physical.word,?_⟩
  · exact Eventually.of_forall fun n => ⟨le_max_left ..,by linarith [le_max_left 1 (τ n)]⟩
  · intro e ep
    filter_upwards [baseline.query (e/32) (by positivity),physical.growing 2,bounded,ww,
      (DisjointnessFoundations.Tradeoff.log_tends.eventually_ge_atTop (max 2 C)).filter_mono large] with n low aw bound wordSize lg
    let S := L n
    let x := logb 2 (A n*w n)
    let y := logb 2 S
    have s2 : 2≤S := (le_max_left ..).trans lg
    have cs : C≤S := (le_max_right ..).trans lg
    have y1 : 1≤y := by
      simpa [y] using logb_le_logb_of_le (b:=2) (by norm_num) (by norm_num : (0:ℝ)<2) s2
    have x1 : 1≤x := logprod_ge aw
    have a1 : 1≤A n := le_max_left ..
    have w0 : 0≤w n := (mul_nonneg cp.le (show 0≤S by linarith)).trans wordSize.1
    have ws : w n ≤ S^2 := by
      have wh : w n ≤ C*S := wordSize.2
      nlinarith only [wh,mul_le_mul_of_nonneg_right cs (show 0≤S by linarith)]
    have p : A n*w n ≤ S^4 := by
      calc A n*w n ≤ S^2*S^2 := mul_le_mul bound ws w0 (sq_nonneg _)
           _ = S^4 := by ring
    have logp := logb_le_logb_of_le (b:=2) (by norm_num) (by linarith : 0<A n*w n) p
    rw [logb_pow] at logp
    change x≤(↑(4:ℕ):ℝ)*y at logp
    norm_num at logp
    have rat : S/y ≤ 4*(S/x) := by
      rw [mul_div_assoc',div_le_div_iff₀ (by linarith : 0<y) (by linarith : 0<x)]
      nlinarith only [mul_le_mul_of_nonneg_left logp (show 0≤S by linarith)]
    have sq := pow_le_pow_left₀ (by positivity : 0≤S/y) rat 2
    simp only [one_mul] at low
    change A n ≤ e/32*(S/y)^2 at low
    change 2*A n ≤ e*(S/x)^2
    nlinarith only [low,mul_le_mul_of_nonneg_left sq ep.le]

/-- Failure of an eventual lower bound gives a nontrivial cofinal filter
along which the proposed counterexample costs are little-o of the target. -/
theorem countersequence {cost target : ℕ → ℝ} (nn : ∀ n, 0≤target n)
    (fails : ¬∃ c : ℝ, 0<c ∧ ∀ᶠ n : ℕ in atTop, c*target n ≤ cost n) :
    ∃ f : Filter ℕ, f.NeBot ∧ f ≤ atTop ∧
      ∀ ε : ℝ, 0<ε → ∀ᶠ n : ℕ in f, cost n ≤ ε*target n := by
  classical
  have freq (u : ℝ) (up : 0<u) : ∃ᶠ n : ℕ in atTop, cost n < u*target n := by
    by_contra! h
    apply fails
    exact ⟨u,up,by simpa using h⟩
  have pick (j : ℕ) : ∃ n : ℕ, j ≤ n ∧ cost n < (1/((j:ℝ)+1))*target n :=
    frequently_atTop.mp (freq _ (by positivity)) j
  choose idx hi bad using pick
  have cofinal : Tendsto idx atTop atTop := tendsto_atTop_mono hi tendsto_id
  refine ⟨Filter.map idx atTop,inferInstance,cofinal,?_⟩
  intro ε ep
  change ∀ᶠ j : ℕ in atTop, cost (idx j) ≤ ε*target (idx j)
  filter_upwards [tendsto_one_div_add_atTop_nhds_zero_nat.eventually (Iio_mem_nhds ep)] with j jlarge
  exact (bad j).le.trans (mul_le_mul_of_nonneg_right (le_of_lt jlarge) (nn _))

/-- The usual omega conclusion, expressed directly in terms of all
nontrivial cofinal filters. -/
theorem lower_of_no_fast {cost target : ℕ → ℝ} (nn : ∀ n, 0≤target n)
    (noFast : ∀ (f : Filter ℕ), f.NeBot → f ≤ atTop →
      (∀ ε : ℝ, 0<ε → ∀ᶠ n : ℕ in f, cost n ≤ ε*target n) → False) :
    ∃ c : ℝ, 0<c ∧ ∀ᶠ n : ℕ in atTop, c*target n ≤ cost n := by
  by_contra failure
  obtain ⟨f,proper,large,small⟩ := countersequence nn failure
  exact noFast f proper large small

end
end AmortizedBound.Parameters

/-! ## Simulation -/

/-! Random query windows, the private equalization experiment and selection
of a fixed public protocol for the amortized-bound draft. -/
namespace AmortizedBound.Simulation
open Finset Real MeasureTheory Classical
open DisjointnessFoundations DisjointnessDraft.PhysicalProtocol
open DisjointnessFoundations.FiniteSampling DisjointnessFoundations.ProtocolInformation
open scoped BigOperators
noncomputable section

def times (n : ℕ) := Icc (n/2) n

def window (n d h T : ℕ) (cost : ℕ → ℝ) :=
  ∑ t ∈ Icc 1 n, if t+d≤T ∧ T<t+d+h then cost t else 0

def timeMean (n : ℕ) (f : ℕ → ℝ) := (∑ T ∈ times n,f T)/(times n).card

theorem window_sum (n d h : ℕ) (cost : ℕ → ℝ) (nonneg : ∀ t,0≤cost t) :
    ∑ T ∈ times n,window n d h T cost ≤ h*∑t∈Icc 1 n,cost t := by
  unfold window
  rw [sum_comm,mul_sum]
  apply sum_le_sum
  intro t ht
  let S := (times n).filter (fun T => t+d≤T ∧ T<t+d+h)
  have card : S.card≤h := by
    apply (card_le_card (show S⊆Ico (t+d) (t+d+h) from
      fun x hx => mem_Ico.mpr (mem_filter.mp hx).2)).trans
    simp
  rw [←sum_filter]
  change (∑ _∈S,cost t)≤_
  simpa [nsmul_eq_mul] using mul_le_mul_of_nonneg_right (by exact_mod_cast card : (S.card:ℝ)≤h) (nonneg t)

theorem window_mean {n : ℕ} (hn : 0<n) (d h : ℕ) (cost : ℕ → ℝ) (nonneg : ∀ t,0≤cost t) :
    timeMean n (fun T => window n d h T cost) ≤ (2*h/n)*∑ t∈Icc 1 n,cost t := by
  have card : (times n).card=n+1-n/2 := by simp [times]
  have cp : 0<(times n).card := by omega
  have cap : n≤2*(times n).card := by omega
  have rcap : (n:ℝ)≤2*(times n).card := by exact_mod_cast cap
  have rn : (0:ℝ)<n := by exact_mod_cast hn
  have rc : (0:ℝ)<(times n).card := by exact_mod_cast cp
  let S := ∑ t∈Icc 1 n,cost t
  have pos : 0≤(h:ℝ)*S := mul_nonneg (by positivity) (sum_nonneg fun t _ => nonneg t)
  apply (div_le_iff₀ rc).mpr
  apply (window_sum n d h cost nonneg).trans
  change h*S≤(2*h/n)*S*(times n).card
  have comp := mul_le_mul_of_nonneg_left rcap pos
  calc _ ≤ (2*h*S*(times n).card)/n := (le_div_iff₀ rn).mpr (by nlinarith only [comp])
       _ = _ := by ring

theorem random_window {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    {n : ℕ} (hn : 0<n) (d h : ℕ) (c : Ω→ℕ→ℝ) (nonneg : ∀ ω t,0≤c ω t)
    (windowInt : Integrable (fun ω => timeMean n (fun T => window n d h T (c ω))) μ)
    (totalInt : Integrable (fun ω => ∑ t∈Icc 1 n,c ω t) μ) :
    (∫ ω,timeMean n (fun T => window n d h T (c ω)) ∂μ) ≤
      (2*h/n)*(∫ ω,∑ t∈Icc 1 n,c ω t ∂μ) := by
  rw [←integral_const_mul]
  exact integral_mono windowInt (totalInt.const_mul _) fun ω => window_mean hn d h _ (nonneg ω)

theorem window_budget {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) {n : ℕ} (hn : 0<n)
    (d h : ℕ) (a : ℝ) (c : Ω→ℕ→ℝ) (nonneg : ∀ω t,0≤c ω t)
    (wi : Integrable (fun ω => timeMean n (fun T => window n d h T (c ω))) μ)
    (ti : Integrable (fun ω => ∑t∈Icc 1 n,c ω t) μ)
    (total : (∫ω,∑t∈Icc 1 n,c ω t ∂μ) ≤ n*a) :
    (∫ω,timeMean n (fun T => window n d h T (c ω)) ∂μ)≤2*a*h := by
  have rn : (0:ℝ)<n := by exact_mod_cast hn
  apply (random_window μ hn d h c nonneg wi ti).trans
  calc _ ≤ (2*h/n)*(n*a) := mul_le_mul_of_nonneg_left total (by positivity)
       _ = _ := by field_simp; ring

/-- Separation of disjoint cell ranges bounds the expectation over an
independent uniform candidate epoch by the selected-query budget divided by k. -/
theorem epoch_average {Ω J : Type*} [MeasurableSpace Ω] (μ : Measure Ω) (epochs : Finset J)
    (nonempty : epochs.Nonempty) (hits : J→Ω→ℝ) (reads : Ω→ℝ) (b : ℝ)
    (hi : ∀j∈epochs,Integrable (hits j) μ) (ri : Integrable reads μ)
    (charge : ∀ω,(∑j∈epochs,hits j ω)≤reads ω) (budget : (∫ω,reads ω ∂μ)≤b) :
    (∑j∈epochs,∫ω,hits j ω ∂μ)/(epochs.card:ℝ)≤b/epochs.card := by
  apply div_le_div_of_nonneg_right _ (by exact_mod_cast (card_pos.mpr nonempty).le : (0:ℝ)≤epochs.card)
  rw [←integral_finset_sum epochs hi]
  exact (integral_mono (integrable_finset_sum _ hi) ri charge).trans budget

def increment (cumulative : ℕ→ℝ) (t : ℕ) := cumulative t-cumulative (t-1)

theorem window_increment {n d h T : ℕ} (ends : T≤n) (starts : d+h≤T) (C : ℕ→ℝ) :
    window n d h T (increment C)=C (T-d)-C (T-d-h) := by
  let add1 : ℕ ↪ ℕ := ⟨Nat.succ,Nat.succ_injective⟩
  have eq : (Icc 1 n).filter (fun t => t+d≤T ∧ T<t+d+h)=
      (Ico (T-d-h) (T-d)).map add1 := by
    ext t
    simp only [mem_filter,mem_Icc,mem_map,mem_Ico,exists_prop]
    constructor
    · intro good; exact ⟨t-1,⟨by omega,by omega⟩,by dsimp [add1]; omega⟩
    · rintro ⟨j,⟨_,_⟩,rfl⟩; dsimp [add1]; omega
  unfold window
  rw [←sum_filter,eq,sum_map]
  change (∑ k∈Ico (T-d-h) (T-d), (C (k+1)-C k))=_
  rw [sum_Ico_eq_sub _ (Nat.sub_le _ _),sum_range_sub,sum_range_sub]
  ring

theorem total_increment (n : ℕ) (C : ℕ→ℝ) :
    (∑t∈Icc 1 n,increment C t)=C n-C 0 := by
  have eq := window_increment (n:=n) (T:=n) (d:=0) (h:=n) le_rfl (by omega) C
  simp only [Nat.sub_zero,Nat.sub_self] at eq
  rw [←eq]
  apply sum_congr rfl
  intro t h
  obtain ⟨left,right⟩ := mem_Icc.mp h
  simp [right,show n<t+n by omega]

theorem chance_mono (rate : SamplingRate) (P Q : (Fin cells→Bool) → Prop)
    (sub : ∀ b,P b → Q b) : chance rate P≤chance rate Q := by
  apply sum_le_sum; intro mask _
  have pos := bitWeight_nonneg rate mask
  by_cases p : P mask
  · simp [p,sub mask p]
  · by_cases q : Q mask <;> simp [p,q,pos]

def fair : SamplingRate := ⟨1/2,by norm_num,by norm_num⟩

def prefixBits (h r d : ℕ) : Finset (Fin (h*r)) :=
  univ.filter fun i => i.val<h*(r-d)

theorem prefix_card (h r d : ℕ) : (prefixBits h r d).card=h*(r-d) := by
  let emb : Fin (h*(r-d)) ↪ Fin (h*r) := Fin.castLEEmb (Nat.mul_le_mul_left _ (Nat.sub_le _ _))
  have eq : prefixBits h r d=univ.map emb := by
    ext i
    simp only [prefixBits,mem_filter,mem_univ,true_and,mem_map,exists_prop]
    constructor
    · intro small; exact ⟨⟨i.val,small⟩,Fin.ext rfl⟩
    · rintro ⟨j,rfl⟩; exact j.isLt
  simp [eq]

theorem padding_chance (rate : SamplingRate) (h r d : ℕ) (dyadic : rate.p=(1/2:ℝ)^h) :
    chance fair (fun F => ∀j∈prefixBits h r d,F j=true)=rate.p^(r-d) := by
  rw [chance_cover,prefix_card,dyadic,pow_mul]; rfl

/-- Fresh fair bits and the Bernoulli cell mask are independent. A true fair
bit encodes a zero in the transmitted test string. The integer r is the
chosen epoch-probe cutoff. -/
def privateAccept (rate : SamplingRate) (h r K : ℕ) (all required : Finset (Fin cells)) :=
  chance rate (fun mask => (∀ a∈required,mask a=true) ∧
    (all.filter (fun a => mask a)).card≤⌊2*rate.p*K⌋₊) *
  chance fair (fun F => ∀ j∈prefixBits h r required.card,F j=true)

theorem private_bounds (rate : SamplingRate) (h r K : ℕ) (dyadic : rate.p=(1/2:ℝ)^h)
    (all required : Finset (Fin cells)) (size : all.card≤K) (hits : required.card≤r) :
    rate.p^r - exp (-(rate.p*K)/3) ≤ privateAccept rate h r K all required ∧
      privateAccept rate h r K all required ≤ rate.p^r := by
  let cover := fun mask : Fin cells→Bool => ∀ a∈required,mask a=true
  let bad := fun mask : Fin cells→Bool => ⌊2*rate.p*K⌋₊ < (all.filter fun a => mask a).card
  let good := fun mask : Fin cells→Bool => cover mask ∧ (all.filter fun a => mask a).card≤⌊2*rate.p*K⌋₊
  have alpha := chance_difference rate cover bad good (fun _ hc hs => ⟨hc,Nat.le_of_not_gt hs⟩)
  have cap := chance_cap rate all K size
  have cov : chance rate cover=rate.p^required.card := chance_cover rate _
  have low : rate.p^required.card-exp (-(rate.p*K)/3)≤chance rate good :=
    (sub_le_sub cov.ge cap).trans alpha
  have high := (chance_mono rate good cover fun _ g => g.1).trans_eq cov
  let pad := rate.p^(r-required.card)
  have pp : 0≤pad := pow_nonneg rate.positive.le _
  have one : pad≤1 := pow_le_one₀ rate.positive.le rate.le_one
  have eq : rate.p^required.card*pad=rate.p^r := by
    rw [show pad=rate.p^(r-required.card) from rfl,←pow_add,Nat.add_sub_of_le hits]
  unfold privateAccept
  rw [padding_chance rate _ _ _ dyadic]
  change _ ≤ chance rate good*pad ∧ chance rate good*pad≤_
  refine ⟨?_,(mul_le_mul_of_nonneg_right high pp).trans_eq eq⟩
  have lb := mul_le_mul_of_nonneg_right low pp
  have penalty := mul_le_mul_of_nonneg_left one (exp_pos (-(rate.p*K)/3)).le
  rw [sub_mul,eq] at lb
  linarith

/-- The mean is taken over public coins only. The original input law can
therefore be used unchanged after selecting the witness. -/
theorem fixed_public {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (rho err size : Ω→ℝ) (n γ : ℝ) (hn : 0<n) (hg : 0<γ)
    (sizes : ∀ω,0<size ω) (errors : ∀ω,0≤err ω)
    (ri : Integrable rho μ) (ei : Integrable (fun ω => n/size ω*err ω) μ)
    (yes : γ/16≤∫ω,rho ω ∂μ) (rare : (∫ω,n/size ω*err ω ∂μ)≤γ/4096) :
    ∃ ω,γ/32≤rho ω ∧ err ω/rho ω≤size ω/(64*n) := by
  let score := fun ω => rho ω-64*(n/size ω*err ω)
  have integ : Integrable score μ := ri.sub (ei.const_mul 64)
  have gain : 3*γ/64≤∫ω,score ω ∂μ := by
    dsimp only [score]; rw [integral_sub ri (ei.const_mul _),integral_const_mul]
    linarith only [yes,rare]
  have witness : ∃ω,γ/32≤score ω := by
    by_contra! no
    have up := integral_mono integ (integrable_const (γ/32)) (fun ω => (no ω).le)
    simp only [integral_const,measureReal_univ_eq_one,one_smul] at up
    linarith
  obtain ⟨ω,quality⟩ := witness
  dsimp only [score] at quality
  have ep := mul_nonneg (div_nonneg hn.le (sizes ω).le) (errors ω)
  have positive : 0<rho ω := by linarith
  refine ⟨ω,by linarith, (div_le_div_iff₀ positive (by positivity : 0<64*n)).mpr ?_⟩
  have sc : 64*(n/size ω*err ω)≤rho ω := by linarith
  have div : (64*n*err ω)/size ω≤rho ω := by convert sc using 1; ring
  have prod := (div_le_iff₀ (sizes ω)).mp div
  nlinarith only [prod]

/-- Apply Markov to the sum of the four costs after dividing each by its
own expected-cost budget. This gives the four-cutoff union estimate. -/
theorem four_cutoffs {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (charge : Fin 4→Ω→ℝ) (nonneg : ∀j ω,0≤charge j ω)
    (integ : ∀j,Integrable (charge j) μ) (budget : ∀j,(∫ω,charge j ω ∂μ)≤1) :
    μ.real {ω | ∃j, 32 < charge j ω} ≤ 1/8 := by
  let work := fun ω => ∑ j,charge j ω
  have nn : ∀ω,0≤work ω := fun ω => sum_nonneg fun j _ => nonneg j ω
  have wi : Integrable work μ := integrable_finset_sum _ fun j _ => integ j
  have mean : (∫ω,work ω ∂μ)≤4 := by
    rw [show work=(fun ω => ∑ j,charge j ω) from rfl,integral_finset_sum _ (fun j _ => integ j)]
    calc _ ≤ ∑ _j : Fin 4,(1:ℝ) := sum_le_sum fun j _ => budget j
         _ = 4 := by simp
  have incl : {ω | ∃j,32<charge j ω} ⊆ {ω | 32≤work ω} := by
    intro ω ⟨j,hj⟩
    exact hj.le.trans (single_le_sum (fun k _ => nonneg k ω) (mem_univ j))
  have h := mul_meas_ge_le_integral_of_nonneg (ae_of_all μ nn) wi 32
  linarith only [h,mean,measureReal_mono (μ:=μ) incl]

/-- Count correctly answered disjoint inputs that also pass the four good
execution tests. No independence between these three events is needed. -/
theorem accepted_yes_mean {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (yes rejected wrong : Set Ω) (rho : Ω→ℝ) (γ η : ℝ) (g : 0<γ) (tail : η≤1/4)
    (pos : ∀ω,0≤rho ω) (integ : Integrable rho μ)
    (accept : ∀ ω∈yes,ω∉rejected → ω∉wrong → γ*(1-η)≤rho ω)
    (y : 1/4≤μ.real yes) (e : μ.real rejected≤1/8) (d : μ.real wrong≤1/4096) :
    γ/16≤∫ω,rho ω ∂μ := by
  let G := {ω | ω∈yes ∧ ω∉rejected ∧ ω∉wrong}
  have sub : yes⊆G∪rejected∪wrong := by intro ω h; simp_all [G]; tauto
  have first := measureReal_mono (μ:=μ) sub
  have second := measureReal_union_le (G∪rejected) wrong (μ:=μ)
  have third := measureReal_union_le G rejected (μ:=μ)
  have enough : 1/9≤μ.real G := by linarith only [first,second,third,y,e,d]
  have incl : G⊆{ω|γ*(1-η)≤rho ω} := fun ω h => accept ω h.1 h.2.1 h.2.2
  have mass := enough.trans (measureReal_mono (μ:=μ) incl)
  have lb := mul_meas_ge_le_integral_of_nonneg (ae_of_all μ pos) integ (γ*(1-η))
  have coeff : γ*(3/4)≤γ*(1-η) := mul_le_mul_of_nonneg_left (by linarith) g.le
  have aux := mul_le_mul coeff mass (by norm_num : (0:ℝ)≤1/9) (by nlinarith : 0≤γ*(1-η))
  linarith only [aux,lb,g]

/-- Pointwise input error gives the extra factor proportional to the rare
input event, before any public tape is fixed. -/
theorem localized_error {I Ω : Type*} [Fintype I] [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (weight : I→ℝ) (nw : ∀i,0≤weight i)
    (rare : Finset I) (wrong : I→Set Ω) (joint : I→Ω→ℝ)
    (γ δ space : ℝ) (g : 0≤γ) (d : 0≤δ)
    (errors : ∀i,μ.real (wrong i)≤δ) (meas : ∀i,MeasurableSet (wrong i))
    (integ : ∀i,Integrable (joint i) μ)
    (cap : ∀i ω,joint i ω ≤ (if i∈rare ∧ ω∈wrong i then γ else 0))
    (rareMass : ∑i∈rare,weight i≤space) :
    ∑i,weight i*(∫ω,joint i ω ∂μ)≤γ*δ*space := by
  have point (i : I) : (∫ω,joint i ω ∂μ) ≤ (if i∈rare then γ*δ else 0) := by
    by_cases h : i∈rare
    · rw [if_pos h]
      have bound : ∀ω,joint i ω≤(wrong i).indicator (fun _ => γ) ω := by
        intro ω; simpa [h,Set.indicator] using cap i ω
      have z := integral_mono (integ i) ((integrable_const γ).indicator (meas i)) bound
      rw [integral_indicator (meas i),setIntegral_const,smul_eq_mul] at z
      exact z.trans ((mul_le_mul_of_nonneg_right (errors i) g).trans_eq (mul_comm _ _))
    · rw [if_neg h]; have t := integral_mono (integ i) (integrable_const (0:ℝ)) (fun ω => by simpa [h] using cap i ω)
      simpa using t
  calc _ ≤ ∑i,weight i*(if i∈rare then γ*δ else 0) := sum_le_sum fun i _ => mul_le_mul_of_nonneg_left (point i) (nw i)
       _ = (∑ i∈rare,weight i)*(γ*δ) := by simp [mul_ite,←sum_filter,sum_mul]
       _ ≤ _ := (mul_le_mul_of_nonneg_right rareMass (mul_nonneg g d)).trans_eq (mul_comm _ _)

namespace Physical
open WordProgram
variable {A W Y : Type} [DecidableEq A]

def overlay (mem : A→W) (localWords : A→Option W) (a : A) := (localWords a).getD (mem a)

/-- All words fetched from the initial memory, with every read and write
also entered in the operation's free local workspace. -/
def replay (mem : A→W) (p : Program A W Y) (localWords : A→Option W) : Y × List (A×W) :=
  match p with
  | .pure y => (y,[])
  | .write a v k => replay mem k (Function.update localWords a (some v))
  | .read a k => match localWords a with
    | some v => replay mem (k v) localWords
    | none =>
      let v := mem a
      let z := replay mem (k v) (Function.update localWords a (some v))
      (z.1,(a,v)::z.2)

theorem overlay_write (mem : A→W) (l : A→Option W) (a : A) (v : W) :
    overlay mem (Function.update l a (some v))=Function.update (overlay mem l) a v := by
  funext x; by_cases h : x=a <;> simp [overlay,Function.update,h]

theorem overlay_fill (mem : A→W) (l : A→Option W) (a : A) (h : l a=none) :
    overlay mem (Function.update l a (some (mem a)))=overlay mem l := by
  funext x; by_cases z : x=a <;> simp [overlay,Function.update,z,h]

theorem replay_correct (mem : A→W) (p : Program A W Y) (l : A→Option W) :
    (replay mem p l).1=(p.run (overlay mem l)).1 ∧
      (replay mem p l).2.length≤(p.run (overlay mem l)).2.2 := by
  induction p generalizing l with
  | pure y => exact ⟨rfl,Nat.le_refl _⟩
  | write a v k ih =>
    have z := ih (Function.update l a (some v)); rw [overlay_write] at z
    simp only [replay,Program.run]
    exact ⟨z.1,by omega⟩
  | read a k ih =>
    cases h : l a with
    | some v =>
      have z := ih v l
      have val : overlay mem l a=v := by simp [overlay,h]
      simp only [replay,h,Program.run,val]
      exact ⟨z.1,by omega⟩
    | none =>
      have z := ih (mem a) (Function.update l a (some (mem a)))
      rw [overlay_fill mem l a h] at z
      have val : overlay mem l a=mem a := by simp [overlay,h]
      simp only [replay,h,Program.run,val,List.length_cons]
      exact ⟨z.1,by omega⟩

theorem trace_entries (mem : A→W) (p : Program A W Y) (l : A→Option W) :
    ((replay mem p l).2.map Prod.fst).Nodup ∧
      ∀ z∈(replay mem p l).2,l z.1=none ∧ z.2=mem z.1 := by
  induction p generalizing l with
  | pure y => simp [replay]
  | write a v k ih =>
    obtain ⟨nd,good⟩ := ih (Function.update l a (some v))
    refine ⟨nd,?_⟩; intro z hz
    obtain ⟨fresh,word⟩ := good z hz
    by_cases eq : z.1=a
    · rw [eq,Function.update_self] at fresh; contradiction
    · exact ⟨by simpa [Function.update,eq] using fresh,word⟩
  | read a k ih =>
    cases h : l a with
    | some v => simpa [replay,h] using ih v l
    | none =>
      let tail := replay mem (k (mem a)) (Function.update l a (some (mem a)))
      obtain ⟨nd,good⟩ := ih (mem a) (Function.update l a (some (mem a)))
      have diff (z : A×W) (hz : z∈tail.2) : z.1≠a := by
        intro eq; have v := (good z hz).1; rw [eq,Function.update_self] at v; contradiction
      have absent : a∉tail.2.map Prod.fst := by
        rintro ha; obtain ⟨z,hz,eq⟩ := List.mem_map.mp ha; exact diff z hz eq
      simp only [replay,h,List.map_cons,List.nodup_cons,List.mem_cons,forall_eq_or_imp]
      exact ⟨⟨absent,nd⟩,⟨trivial,trivial⟩,fun z hz => ⟨by
        simpa [Function.update,diff z hz] using (good z hz).1,(good z hz).2⟩⟩

theorem replay_congr (left right : A→W) (p : Program A W Y) (l : A→Option W)
    (same : ∀ z∈(replay left p l).2,left z.1=right z.1) :
    replay left p l=replay right p l := by
  induction p generalizing l with
  | pure => rfl
  | write a v k ih => exact ih _ same
  | read a k ih =>
    cases h : l a with
    | some v =>
      simp only [replay,h] at same ⊢
      exact ih _ _ same
    | none =>
      simp only [replay,h,List.mem_cons,forall_eq_or_imp] at same ⊢
      have eq : left a=right a := same.1
      rw [←eq]
      rw [ih _ _ same.2]

/-- The packet determines the restored memory. Only last-written epoch words
which Bob did not send may differ from the true memory. -/
def simulatedMemory (old actual : A→W) (epoch later : Finset A) (sample : A→Bool) (a : A) :=
  if a∈later ∨ (a∈epoch ∧ sample a=true) then actual a else old a

def covered (epoch : Finset A) (sample : A→Bool) (log : List (A×W)) :=
  ∀z∈log,z.1∈epoch → sample z.1=true

theorem agree_on_covered (old actual : A→W) (epoch later : Finset A) (sample : A→Bool)
    (old_ok : ∀ a,a∉epoch → a∉later → old a=actual a)
    (log : List (A×W)) (covers : covered epoch sample log) :
    ∀z∈log,simulatedMemory old actual epoch later sample z.1=actual z.1 := by
  intro z hz; by_cases e : z.1∈epoch
  · simp [simulatedMemory,e,covers z hz e]
  · by_cases t : z.1∈later <;> simp_all [simulatedMemory]

/-- Successful verification is exactly coverage of the distinct true epoch
reads. On that event Alice's result and complete transcript agree, including
the effects of earlier writes inside the selected query. -/
theorem verified_iff (old actual : A→W) (epoch later : Finset A) (sample : A→Bool)
    (old_ok : ∀ a,a∉epoch → a∉later → old a=actual a) (p : Program A W Y) :
    let simulated := replay (simulatedMemory old actual epoch later sample) p (fun _ => none)
    let truth := replay actual p (fun _ => none)
    covered epoch sample simulated.2 ↔ covered epoch sample truth.2 ∧ simulated=truth := by
  intro simulated truth
  constructor
  · intro cover
    have eq : simulated=truth := replay_congr _ _ _ _
      (agree_on_covered old actual epoch later sample old_ok _ cover)
    exact ⟨eq ▸ cover,eq⟩
  · rintro ⟨cover,eq⟩; rwa [eq]

theorem complete_of_covered (old actual : A→W) (epoch later : Finset A) (sample : A→Bool)
    (old_ok : ∀ a,a∉epoch → a∉later → old a=actual a) (p : Program A W Y)
    (cover : covered epoch sample (replay actual p (fun _ => none)).2) :
    replay actual p (fun _ => none)=replay (simulatedMemory old actual epoch later sample) p (fun _ => none) := by
  apply replay_congr
  intro z hz
  exact (agree_on_covered old actual epoch later sample old_ok _ cover z hz).symm

def needed (epoch : Finset A) (log : List (A×W)) := epoch∩(log.map Prod.fst).toFinset

theorem needed_iff (epoch : Finset A) (mask : A→Bool) (log : List (A×W)) :
    covered epoch mask log ↔ ∀a∈needed epoch log,mask a=true := by
  constructor
  · intro c a ha
    obtain ⟨he,hl⟩ := mem_inter.mp ha
    obtain ⟨z,hz,rfl⟩ := List.mem_map.mp (List.mem_toFinset.mp hl)
    exact c z hz he
  · intro c z hz he
    exact c _ (mem_inter.mpr ⟨he,List.mem_toFinset.mpr (List.mem_map.mpr ⟨z,hz,rfl⟩)⟩)

theorem sum_epoch_hits {J : Type*} (epochs : Finset J) (E : J→Finset A) (log : List (A×W))
    (sep : epochs.toSet.PairwiseDisjoint E) :
    (∑j∈epochs,(needed (E j) log).card)≤log.length := by
  have dis : epochs.toSet.PairwiseDisjoint (fun j => needed (E j) log) :=
    fun i hi j hj ne => (sep hi hj ne).mono inter_subset_left inter_subset_left
  rw [←card_biUnion dis]
  have sub : epochs.biUnion (fun j => needed (E j) log)⊆(log.map Prod.fst).toFinset := by
    intro a ha
    obtain ⟨j,_,found⟩ := mem_biUnion.mp ha
    exact (mem_inter.mp found).2
  exact (card_le_card sub).trans ((List.toFinset_card_le _).trans (List.length_map _).le)

open DisjointnessFoundations.Simulation

def epochCells (epoch later : Log w) := touched epoch \ touched later
def trueMemory (old : Cell w→Cell w) (epoch later : Log w) := applyWrites (applyWrites old epoch) later

theorem trueSnapshot (old : Cell w→Cell w) (epoch later : Log w) :
    ∀ a,a∉epochCells epoch later → a∉touched later → old a=trueMemory old epoch later a := by
  intro a early late
  have en : a∉touched epoch := fun hit => early (mem_sdiff.mpr ⟨hit,late⟩)
  have le : ¬Written later a := by simpa using late
  have ee : ¬Written epoch a := by simpa using en
  simp [trueMemory,applyWrites_of_unwritten _ _ _ le,applyWrites_of_unwritten _ _ _ ee]

theorem epoch_cell_budgets (epoch later : Log w) :
    (epochCells epoch later).card≤epoch.length ∧ (touched later).card≤later.length := by
  refine ⟨(card_le_card sdiff_subset).trans ?_,?_⟩
  · exact (List.toFinset_card_le _).trans (List.length_map _).le
  · exact (List.toFinset_card_le _).trans (List.length_map _).le

/-- The check after decoding a non-aborting packet. The bounded transcript
and transmitted fair bits suffice for these tests. -/
def pointTest (h r fuel : ℕ) (epoch : Finset A) (mask : A→Bool)
    (F : Fin (h*r)→Bool) (outside : Bool) (log : Option Bool × List (A×W)) : Prop :=
  outside=true ∧ log.1=some true ∧ log.2.length≤fuel ∧ (needed epoch log.2).card≤r ∧
    covered epoch mask log.2 ∧ ∀j∈prefixBits h r (needed epoch log.2).card,F j=true

def eligibleYes (r fuel : ℕ) (epoch : Finset A) (outside : Bool) (log : Option Bool × List (A×W)) : Prop :=
  outside=true ∧ log.1=some true ∧ log.2.length≤fuel ∧ (needed epoch log.2).card≤r

theorem experiment_iff (h r fuel : ℕ) (old actual : A→W) (epoch later : Finset A)
    (mask : A→Bool) (F : Fin (h*r)→Bool) (outside : Bool)
    (old_ok : ∀ a,a∉epoch → a∉later → old a=actual a) (p : Program A W (Option Bool)) :
    let simulated := replay (simulatedMemory old actual epoch later mask) p (fun _ => none)
    let truth := replay actual p (fun _ => none)
    pointTest h r fuel epoch mask F outside simulated ↔
      eligibleYes r fuel epoch outside truth ∧ (∀a∈needed epoch truth.2,mask a=true) ∧
      ∀j∈prefixBits h r (needed epoch truth.2).card,F j=true := by
  intro simulated truth
  constructor
  · rintro ⟨out,yes,short,few,cover,test⟩
    obtain ⟨c,eq⟩ := (verified_iff old actual epoch later mask old_ok p).mp cover
    change simulated=truth at eq
    rw [eq] at yes short few test
    exact ⟨⟨out,yes,short,few⟩,(needed_iff ..).mp c,test⟩
  · rintro ⟨⟨out,yes,short,few⟩,cover,test⟩
    have c := (needed_iff ..).mpr cover
    have eq : truth=simulated := complete_of_covered old actual epoch later mask old_ok p c
    rw [←eq]
    exact ⟨out,yes,short,few,c,test⟩

end Physical

/-- The actual joint law of the two independent private coin strings. -/
def privateChance (rate : SamplingRate) (P : (Fin cells→Bool) → (Fin bits→Bool) → Prop) :=
  ∑ mask,bitWeight rate mask*chance fair (P mask)

def privateWeights (rate : SamplingRate) (cells bits : ℕ) :
    InputLaw ((Fin cells→Bool)×(Fin bits→Bool)) where
  weight z := bitWeight rate z.1*bitWeight fair z.2
  nonneg z := mul_nonneg (bitWeight_nonneg _ _) (bitWeight_nonneg _ _)
  total := by
    rw [Fintype.sum_prod_type]
    simp_rw [←mul_sum,show (∑f : Fin bits→Bool,bitWeight fair f)=1 from totalWeights _ _,mul_one]
    exact totalWeights _ _

def privateLaw (rate : SamplingRate) (cells bits : ℕ) :
    Measure ((Fin cells→Bool)×(Fin bits→Bool)) := (pmf (privateWeights rate cells bits)).toMeasure

instance (rate : SamplingRate) (cells bits : ℕ) : IsProbabilityMeasure (privateLaw rate cells bits) := by
  unfold privateLaw; infer_instance

theorem prob_private (rate : SamplingRate) (P : (Fin cells→Bool)→(Fin bits→Bool)→Prop) :
    (privateLaw rate cells bits).real {z | P z.1 z.2}=privateChance rate P := by
  rw [privateLaw,pmf_real,Fintype.sum_prod_type]
  unfold privateChance chance
  apply sum_congr rfl; intro m _
  rw [mul_sum]; apply sum_congr rfl; intro f _
  by_cases h : P m f <;> simp [privateWeights,h]

theorem privateChance_congr (rate : SamplingRate) (P Q : (Fin cells→Bool)→(Fin bits→Bool)→Prop)
    (eq : ∀m f,P m f ↔ Q m f) : privateChance rate P=privateChance rate Q := by
  simp only [privateChance,chance]; simp_rw [fun m f => propext (eq m f)]

theorem privateChance_product (rate : SamplingRate) (P : (Fin cells→Bool)→Prop) (Q : (Fin bits→Bool)→Prop) :
    privateChance rate (fun m f => P m ∧ Q f)=chance rate P*chance fair Q := by
  unfold privateChance
  rw [chance,sum_mul]
  apply sum_congr rfl; intro mask _
  by_cases ok : P mask <;> simp [chance,ok]

theorem privateChance_false (rate : SamplingRate) :
    privateChance (cells:=cells) (bits:=bits) rate (fun _ _ => False)=0 := by simp [privateChance,chance]

open Physical WordProgram

/-- For a fixed query, old memory, writes and public coins, the acceptance
probability on output one is exactly the capped, equalized mask experiment.
Merlin's earlier abort can be incorporated by setting the external good flag. -/
theorem protocol_pointwise (rate : SamplingRate) (h r K fuel : ℕ) (old actual : Fin cells→W)
    (epoch later : Finset (Fin cells)) (old_ok : ∀a,a∉epoch → a∉later → old a=actual a)
    (prog : Program (Fin cells) W (Option Bool)) (outside : Bool) (merlinOK : Prop) :
    let truth := Physical.replay actual prog (fun _ => none)
    privateChance rate (fun mask F => merlinOK ∧ (epoch.filter fun a => mask a).card≤⌊2*rate.p*K⌋₊ ∧
      pointTest h r fuel epoch mask F outside (Physical.replay (simulatedMemory old actual epoch later mask) prog (fun _ => none))) =
    if merlinOK ∧ eligibleYes r fuel epoch outside truth then
      privateAccept rate h r K epoch (needed epoch truth.2) else 0 := by
  intro truth
  by_cases ok : merlinOK ∧ eligibleYes r fuel epoch outside truth
  · rw [if_pos ok]
    unfold privateAccept
    rw [←privateChance_product]
    apply privateChance_congr; intro m f
    have step := experiment_iff h r fuel old actual epoch later m f outside old_ok prog
    dsimp only at step
    rw [step]
    dsimp only [truth] at ok ⊢
    tauto
  · rw [if_neg ok,←privateChance_false (cells:=cells) (bits:=h*r) rate]
    apply privateChance_congr; intro m f
    have step := experiment_iff h r fuel old actual epoch later m f outside old_ok prog
    dsimp only at step
    rw [step]
    simp only [iff_false]
    rintro ⟨hm,_,he,_,_⟩
    exact ok ⟨hm,he⟩

theorem message_budgets (w e l cap h r fuel : ℕ) :
    Fintype.card (Option (Advice w e l))≤2^(adviceBits w e l+1) ∧
    Fintype.card (Packet w l cap × (Fin (h*r)→Bool))≤2^(packetBits w l cap+h*r) ∧
    Fintype.card (Description.TraceCode w fuel)≤2^(replyBits w fuel) := by
  refine ⟨?_,?_,reply_bits w fuel⟩
  · rw [Fintype.card_option,pow_succ]
    have b := advice_bits w e l
    have pos : 0<2^(adviceBits w e l) := by positivity
    omega
  · rw [Fintype.card_prod,Fintype.card_fun,Fintype.card_bool,Fintype.card_fin,pow_add]
    exact Nat.mul_le_mul_right _ (packet_bits w l cap)

namespace Accounting
open Dynamic

def runPrefix (fit : n*n≤N) (interleaved : Bool) (x : Row n) (qs : Fin n→Fin N) (t : ℕ) :=
  Epoch.rounds fit interleaved x qs ((List.finRange n).take t)

theorem extendPrefix (fit : n*n≤N) (interleaved : Bool) (x : Row n) (qs : Fin n→Fin N)
    {i j : ℕ} (h : i≤j) :
    runPrefix fit interleaved x qs i <+: runPrefix fit interleaved x qs j := by
  obtain ⟨u,rfl⟩ := Nat.exists_eq_add_of_le h
  refine ⟨Epoch.rounds fit interleaved x qs (((List.finRange n).drop i).take u),?_⟩
  simp [runPrefix,List.take_add,Epoch.rounds,List.flatMap_append]

theorem prefix_history (D : Machine w F U Q Ω) (seed : Ω) (family : F) {xs ys : List (U ⊕ Q)}
    (pref : xs <+: ys) {last : History w} (ran : history D seed family ys=some last) :
    ∃ first,history D seed family xs=some first ∧ first.probes≤last.probes := by
  obtain ⟨rest,rfl⟩ := pref
  have eq : history D seed family (xs++rest)=
      (history D seed family xs).bind (fun z => runFrom D seed xs.length z rest) := by
    simp [history,runFrom_append,Option.bind_assoc]
  rw [eq] at ran
  cases h : history D seed family xs with
  | none => simp [h] at ran
  | some first =>
    simp only [h,Option.bind_some] at ran
    have cost := (segment_correct D seed xs.length first rest ran).2
    exact ⟨first,rfl,by omega⟩

def cumulative (D : DataStructure N w Ω) (seed : Ω) (family : Family N)
    (fit : n*n≤N) (interleaved : Bool) (x : Row n) (qs : Fin n→Fin N) (t : ℕ) : ℝ :=
  ((history D seed family (runPrefix fit interleaved x qs t)).map History.probes).getD 0

theorem monotone_prefix (D : DataStructure N w Ω) (seed : Ω) (family : Family N)
    (fit : n*n≤N) (interleaved : Bool) (x : Row n) (qs : Fin n→Fin N)
    (finished : ∃ last,history D seed family (runPrefix fit interleaved x qs n)=some last) :
    Monotone (cumulative D seed family fit interleaved x qs) := by
  intro i j ij
  let ops := runPrefix fit interleaved x qs
  have upto (t : ℕ) : ops t=ops (min t n)  := by
    by_cases h : t≤n
    · simp [min_eq_left h]
    · have hn : n≤t := by omega
      have hl : (List.finRange n).length≤t := by simpa using hn
      have eq : (List.finRange n).take n=List.finRange n := List.take_of_length_le (by simp)
      simp [ops,runPrefix,min_eq_right hn,List.take_of_length_le hl,eq]
  obtain ⟨last,hlast⟩ := finished
  obtain ⟨y,hy,_⟩ := prefix_history D seed family (extendPrefix fit interleaved x qs (min_le_right j n)) hlast
  have runJ : history D seed family (ops j)=some y := (upto j) ▸ hy
  obtain ⟨z,hz,hcost⟩ := prefix_history D seed family (extendPrefix fit interleaved x qs ij) runJ
  change ((history D seed family (ops i)).map History.probes).getD 0 ≤
    (((history D seed family (ops j)).map History.probes).getD 0 : ℝ)
  change history D seed family (ops i)=some z at hz
  rw [hz,runJ]
  exact_mod_cast hcost

theorem epoch_end (e : Epoch n s) (fit : n*n≤N) (interleaved : Bool) (qs : Fin n→Fin N)
    (x : Fin s→Fin n) (o : e.Out) :
    e.oldOps fit interleaved qs o ++ e.epochOps fit interleaved qs x o =
      runPrefix fit interleaved (e.join x o) qs (e.start+s) := by
  rw [e.old_independent fit interleaved qs x o]
  simp [runPrefix,Epoch.epochOps,Epoch.before,Epoch.middle,Epoch.rounds,List.take_add,List.flatMap_append]

theorem selected_round (e : Epoch n s) (fit : n*n≤N) (interleaved : Bool) (qs : Fin n→Fin N)
    (x : Fin s→Fin n) (o : e.Out) :
    e.past fit interleaved qs x o ++ (if interleaved then [.inr (qs e.selected)] else []) =
      runPrefix fit interleaved (e.join x o) qs (e.selected.val+1) := by
  have before : e.selected.val<(List.finRange n).length := by simp
  rw [runPrefix,List.take_succ_eq_append_getElem before]
  cases interleaved <;> simp [Epoch.past,Epoch.rounds,List.flatMap_append,List.append_assoc]

/-- The epoch and later write lists of the actual machine are charged to
    the corresponding intervals of the full run. The selected query belongs
    to the full last round even when its probes are excluded from the later list. -/
theorem actual_windows (e : Epoch n s) (fit : n*n≤N) (interleaved : Bool)
    (qs : Fin n→Fin N) (D : DataStructure N w Ω) (seed : Ω) (rows : Family N)
    (x : Fin s→Fin n) (o : e.Out)
    (completed : ∃z,history D seed rows (runPrefix fit interleaved (e.join x o) qs n)=some z) :
    let old := e.oldOps fit interleaved qs o
    let middle := e.epochOps fit interleaved qs x o
    let recent := e.recentOps fit interleaved qs x o
    let C := cumulative D seed rows fit interleaved (e.join x o) qs
    let T := e.selected.val+1
    let d := T-(e.start+s)
    ∃ pre mid last : History w,history D seed rows old=some pre ∧
      runFrom D seed old.length pre middle=some mid ∧
      runFrom D seed (old.length+middle.length) mid recent=some last ∧
      history D seed rows (e.past fit interleaved qs x o)=some last ∧
      (mid.probes:ℝ)-pre.probes=window n d s T (increment C) ∧
      (last.probes:ℝ)-mid.probes≤window n 0 d T (increment C) ∧
      (segment D seed old.length pre.memory middle).length ≤ window n d s T (increment C) ∧
      (segment D seed (old.length+middle.length) mid.memory recent).length ≤ window n 0 d T (increment C) := by
  intro old middle recent C T d
  have sel := e.selected.isLt
  have before := e.beforeQuery
  have time : T≤n := by dsimp [T]; omega
  obtain ⟨all,hall⟩ := completed
  obtain ⟨z,zok,_⟩ := prefix_history D seed rows (extendPrefix fit interleaved (e.join x o) qs time) hall
  obtain ⟨last,lastok,lz⟩ := prefix_history D seed rows
    (show e.past fit interleaved qs x o <+: runPrefix fit interleaved (e.join x o) qs T from
     ⟨_,selected_round e fit interleaved qs x o⟩) zok
  obtain ⟨pre,mid,pok,mok,rok,_,ec,lc⟩ := e.actual_segments fit interleaved qs D seed rows x o lastok
  have oldeq : old=runPrefix fit interleaved (e.join x o) qs e.start := e.old_independent fit interleaved qs x o
  have mideq : old++middle=runPrefix fit interleaved (e.join x o) qs (e.start+s) := epoch_end e fit interleaved qs x o
  have pm : history D seed rows (old++middle)=(history D seed rows old).bind
      (fun st => runFrom D seed old.length st middle) := by simp [history,runFrom_append,Option.bind_assoc]
  have mids : history D seed rows (runPrefix fit interleaved (e.join x o) qs (e.start+s))=some mid := by
    rw [←mideq,pm,pok]; exact mok
  change history D seed rows old=some pre at pok
  have initial : C e.start=pre.probes := by simp [C,cumulative,←oldeq,pok]
  have final : C (e.start+s)=mid.probes := by simp [C,cumulative,mids]
  have zz : C T=z.probes := by simp [C,cumulative,zok]
  have dprop : d+s≤T := by dsimp [d,T]; omega
  have a : T-d=e.start+s := by dsimp [d,T]; omega
  refine ⟨pre,mid,last,pok,mok,rok,lastok,?_,?_,?_,?_⟩
  · rw [window_increment time dprop,a,Nat.add_sub_cancel,initial,final]
  · rw [window_increment time (show 0+d≤T by omega),Nat.sub_zero,a,zz,final]
    exact sub_le_sub_right (by exact_mod_cast lz) _
  · rw [window_increment time dprop,a,Nat.add_sub_cancel,initial,final]
    apply le_sub_iff_add_le.mpr
    rw [add_comm,←Nat.cast_add]
    exact_mod_cast ec
  · rw [window_increment time (show 0+d≤T by omega),Nat.sub_zero,a,zz,final]
    apply le_sub_iff_add_le.mpr
    rw [add_comm,←Nat.cast_add]
    exact_mod_cast lc.trans lz


theorem segment_append (D : Machine w F U Q Ω) (seed : Ω) (offset : ℕ)
    (st : History w) (ops tail : List (U⊕Q)) {mid : History w}
    (ran : runFrom D seed offset st ops=some mid) :
    segment D seed offset st.memory (ops++tail) =
      segment D seed offset st.memory ops ++ segment D seed (offset+ops.length) mid.memory tail := by
  induction ops generalizing offset st with
  | nil => simp [runFrom] at ran; subst mid; simp [Dynamic.segment]
  | cons op rest ih =>
    cases hr : operation D seed offset op st.memory with
    | none => simp [runFrom,advance,hr] at ran
    | some r =>
      let next : History w := ⟨r.memory,st.probes+r.trace.length,op.elim (fun _ => none) (fun _ => some r.report)⟩
      have run : runFrom D seed (offset+1) next rest=some mid := by simpa [runFrom,advance,hr,next] using ran
      have eq := ih (offset+1) next run
      simp only [List.cons_append,Dynamic.segment,hr,List.append_assoc,List.length_cons]
      simpa [next,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using congrArg (List.append (writeLog r.trace)) eq

theorem history_append (D : Machine w F U Q Ω) (seed : Ω) (rows : F) (xs ys : List (U⊕Q)) :
    history D seed rows (xs++ys)=(history D seed rows xs).bind (fun v => runFrom D seed xs.length v ys) := by
  simp [history,runFrom_append,Option.bind_assoc]

theorem ordered_prefix (e : Epoch n s) (f : Epoch n r) (order : e.start+s≤f.start)
    (fit : n*n≤N) (mixed : Bool) (qs : Fin n→Fin N)
    (x : Fin s→Fin n) (o : e.Out) (y : Fin r→Fin n) (p : f.Out) (same : e.join x o=f.join y p) :
    e.oldOps fit mixed qs o ++ e.epochOps fit mixed qs x o <+: f.oldOps fit mixed qs p := by
  rw [epoch_end,f.old_independent fit mixed qs y p,←same]
  exact extendPrefix fit mixed (e.join x o) qs order

/-- The last-write sets of two time-ordered intervals of one execution
    are disjoint, even if the same address is written in both intervals. -/
theorem actual_disjoint (D : Machine w F U Q Ω) (seed : Ω) (rows : F)
    (oldA blockA tailA oldB blockB tailB : List (U⊕Q))
    (order : oldA++blockA <+: oldB) (same : oldA++blockA++tailA=oldB++blockB++tailB)
    (preA midA preB midB : History w)
    (ha : history D seed rows oldA=some preA) (ma : runFrom D seed oldA.length preA blockA=some midA)
    (hb : history D seed rows oldB=some preB) (mb : runFrom D seed oldB.length preB blockB=some midB) :
    Disjoint (Physical.epochCells (segment D seed oldA.length preA.memory blockA)
          (segment D seed (oldA.length+blockA.length) midA.memory tailA))
      (Physical.epochCells (segment D seed oldB.length preB.memory blockB)
          (segment D seed (oldB.length+blockB.length) midB.memory tailB)) := by
  obtain ⟨gap,hgap⟩ := order
  have go : history D seed rows (oldA++blockA)=some midA := by rw [history_append,ha]; exact ma
  have run : runFrom D seed (oldA.length+blockA.length) midA gap=some preB := by
    rw [←hgap,history_append,go,List.length_append] at hb; exact hb
  have tail : tailA=gap++(blockB++tailB) := by
    apply List.append_cancel_left (as:=oldA++blockA)
    simpa only [←hgap,List.append_assoc] using same
  have len : oldA.length+blockA.length+gap.length=oldB.length := by simp [←hgap,Nat.add_assoc]
  have eq := segment_append D seed (oldA.length+blockA.length) midA gap (blockB++tailB) run
  rw [len,segment_append D seed oldB.length preB blockB tailB mb] at eq
  rw [tail,eq,Finset.disjoint_left]
  intro a ia ib
  have late := (mem_sdiff.mp ia).2
  have early := (mem_sdiff.mp ib).1
  apply late
  unfold touched at *
  simpa only [List.map_append,List.toFinset_append,mem_union] using
    (show _ ∨ (a∈(List.map Prod.fst (segment D seed oldB.length preB.memory blockB)).toFinset ∨ _) from Or.inr (Or.inl early))


open Parameters

abbrev Candidate (n β : ℕ) := {i : ℕ // i ∈ candidates (depth n β)}

theorem occupied_monotone (β : ℕ) : Monotone (occupied β) :=
  monotone_nat_of_le_succ fun i => by simp [occupied]

/-- Backward epoch boundaries use the one-based round label T and a
    zero-based start for list prefixes. Every eligible epoch has a more
    recent epoch separating it from the selected query. -/
def candidateEpoch {n β : ℕ} (positive : 1≤β) (t : Fin n) (inHalf : n/2≤t.val+1)
    (i : Candidate n β) : Epoch n (β^i.val) where
  start := (t.val+1)-occupied β i.val
  selected := t
  beforeQuery := by
    obtain ⟨lo,hi,dense⟩ := mem_candidates.mp i.property
    have prep : i.val-1+1=i.val := by omega
    have split : occupied β i.val=occupied β (i.val-1)+β^i.val := by
      conv_lhs => rw [←prep,occupied]
      rw [prep]
    have room := (occupied_monotone β hi).trans (fits n β)
    have thick := prefix_ge positive (i.val-1)
    omega

theorem candidate_offset {n β : ℕ} (positive : 1≤β) (t : Fin n) (inHalf : n/2≤t.val+1)
    (i : Candidate n β) :
    (t.val+1)-((candidateEpoch positive t inHalf i).start+β^i.val)=occupied β (i.val-1) := by
  obtain ⟨lo,hi,_⟩ := mem_candidates.mp i.property
  have prep : i.val-1+1=i.val := by omega
  have split : occupied β i.val=occupied β (i.val-1)+β^i.val := by
    conv_lhs => rw [←prep,occupied]
    rw [prep]
  have room := (occupied_monotone β hi).trans (fits n β)
  change t.val+1-(t.val+1-occupied β i.val+β^i.val)=_
  omega

theorem candidate_order {n β : ℕ} (positive : 1≤β) (t : Fin n) (inHalf : n/2≤t.val+1)
    {i j : Candidate n β} (order : j.val < i.val) :
    (candidateEpoch positive t inHalf i).start+β^i.val≤(candidateEpoch positive t inHalf j).start := by
  have hi := (mem_candidates.mp i.property).2.1
  have prep : i.val-1+1=i.val := by omega
  have split : occupied β i.val=occupied β (i.val-1)+β^i.val := by
    conv_lhs => rw [←prep,occupied]
    rw [prep]
  have room := (occupied_monotone β hi).trans (fits n β)
  have separated := occupied_monotone β (show j.val ≤ i.val-1 by omega)
  change (t.val+1-occupied β i.val)+β^i.val≤t.val+1-occupied β j.val
  omega

/-- The physical cells charged to all candidate epochs by one selected
    read trace are charged at most once. The prefix and midpoint witnesses
    are exactly the machine states included in the epoch snapshot. -/
theorem candidate_hits {n β : ℕ} (positive : 1≤β) (t : Fin n) (inHalf : n/2≤t.val+1)
    (fit : n*n≤N) (mixed : Bool) (qs : Fin n→Fin N) (x : Row n)
    (D : DataStructure N w Ω) (seed : Ω) (rows : Family N)
    (pre mid : Candidate n β→History w) (trace : Log w) :
    let e := candidateEpoch positive t inHalf
    let pair := fun i => splitCoordinates (e i).index x
    let old := fun i => (e i).oldOps fit mixed qs (pair i).2
    let block := fun i => (e i).epochOps fit mixed qs (pair i).1 (pair i).2
    let tail := fun i => (e i).recentOps fit mixed qs (pair i).1 (pair i).2
    (∀i,history D seed rows (old i)=some (pre i)) →
    (∀i,runFrom D seed (old i).length (pre i) (block i)=some (mid i)) →
    (∑i : Candidate n β,(Physical.needed (Physical.epochCells
      (segment D seed (old i).length (pre i).memory (block i))
      (segment D seed ((old i).length+(block i).length) (mid i).memory (tail i))) trace).card)≤trace.length := by
  intro e pair old block tail exactPre exactMid
  let cells := fun i => Physical.epochCells
    (segment D seed (old i).length (pre i).memory (block i))
    (segment D seed ((old i).length+(block i).length) (mid i).memory (tail i))
  have joined (i) : (e i).join (pair i).1 (pair i).2=x := (splitCoordinates (e i).index).symm_apply_apply x
  have equalPast (i j : Candidate n β) : old i++block i++tail i=old j++block j++tail j := by
    rw [←(e i).split_past fit mixed qs (pair i).1 (pair i).2,←(e j).split_past fit mixed qs (pair j).1 (pair j).2]
    simp only [Epoch.past,joined]; rfl
  have ordered (i j : Candidate n β) (h : j.val < i.val) : Disjoint (cells i) (cells j) := by
    apply actual_disjoint D seed rows (old i) (block i) (tail i) (old j) (block j) (tail j) _ (equalPast i j)
      (pre i) (mid i) (pre j) (mid j) (exactPre i) (exactMid i) (exactPre j) (exactMid j)
    exact ordered_prefix (e i) (e j) (candidate_order positive t inHalf h) fit mixed qs
      (pair i).1 (pair i).2 (pair j).1 (pair j).2 ((joined i).trans (joined j).symm)
  apply Physical.sum_epoch_hits univ cells trace
  intro i _ j _ ne
  rcases lt_or_gt_of_ne (fun same => ne (Subtype.ext same)) with h | h
  · exact (ordered j i h).symm
  · exact ordered i j h


open HardDistribution

abbrev Time (n : ℕ) := {t : ℕ // t ∈ times n}

theorem times_nonempty (n : ℕ) : (times n).Nonempty := ⟨n,mem_Icc.mpr ⟨Nat.div_le_self ..,le_rfl⟩⟩

instance (n : ℕ) : Nonempty (Time n) := (times_nonempty n).to_subtype
theorem mean_time (n : ℕ) (f : ℕ→ℝ) : mean (fun t : Time n => f t.val)=timeMean n f := by
  simp [mean,timeMean,Finset.sum_coe_sort,Finset.sum_attach]

private theorem avg_mono {A : Type*} [Fintype A] {f g : A→ℝ} (bound : ∀i,f i≤g i) :
    mean f≤mean g := div_le_div_of_nonneg_right (sum_le_sum fun i _ => bound i) (by positivity)

private theorem avg_add {A : Type*} [Fintype A] (f g : A→ℝ) :
    mean (fun x => f x+g x)=mean f+mean g := by simp [mean,sum_add_distrib,add_div]

private theorem avg_div {A : Type*} [Fintype A] (f : A→ℝ) (k : ℝ) :
    mean (fun x => f x/k)=mean f/k := by simp [mean,←sum_div,div_div,mul_comm]

private theorem avg_swap {A B : Type*} [Fintype A] [Fintype B] (f : A→B→ℝ) :
    mean (fun x => mean (f x)) = mean (fun y => mean (fun x => f x y)) := by
  simp only [mean,←sum_div,div_div]
  rw [sum_comm,mul_comm]

def charge (a b : ℝ) (k s d : ℕ) (E L reads hits : ℝ) :=
  E/(2*a*s)+L/(2*a*d)+reads/b+hits/(b/k)

theorem normalized_charge_pointwise {n : ℕ} (hn : 0<n)
    {J : Type*} [Fintype J] [Nonempty J] (s d : J→ℕ) (hs : ∀i,0<s i) (hd : ∀i,0<d i)
    {a b : ℝ} (ap : 0<a) (bp : 0<b) (cost : ℕ→ℝ) (nn : ∀t,0≤cost t)
    (E L hit : Time n→J→ℝ) (reads : Time n→ℝ)
    (early : ∀T i,E T i≤window n (d i) (s i) T.val cost)
    (late : ∀T i,L T i≤window n 0 (d i) T.val cost)
    (unique : ∀T,(∑i,hit T i)≤reads T) :
    mean (fun T => mean (fun i => charge a b (Fintype.card J) (s i) (d i) (E T i) (L T i) (reads T) (hit T i)))
    ≤ 2*((∑t∈Icc 1 n,cost t)/(n*a))+2*(mean reads/b) := by
  let tot := ∑t∈Icc 1 n,cost t
  have rn : (0:ℝ)<n := by exact_mod_cast hn
  have kpos : (0:ℝ)<Fintype.card J := by positivity
  have segmentBound (δ h : J→ℕ) (pos : ∀i,0<h i) (f : Time n→J→ℝ)
      (win : ∀T i,f T i≤window n (δ i) (h i) T.val cost) :
      mean (fun T => mean (fun i => f T i/(2*a*h i)))≤tot/(n*a) := by
    rw [avg_swap]
    refine (avg_mono fun i => ?_).trans_eq (mean_const (tot/(n*a)))
    have hp : (0:ℝ)<h i := by exact_mod_cast pos i
    rw [avg_div]
    apply (div_le_div_of_nonneg_right (avg_mono fun T => win T i) (by positivity)).trans
    rw [mean_time n (fun t => window n (δ i) (h i) t cost)]
    apply (div_le_div_of_nonneg_right (window_mean hn (δ i) (h i) cost nn) (by positivity)).trans_eq
    dsimp only [tot]; field_simp; ring
  have eh := segmentBound d s hs E early
  have lh := segmentBound (fun _ => 0) d hd L late
  have hitBound (T : Time n) : mean (fun i => hit T i/(b/Fintype.card J))≤reads T/b := by
    rw [avg_div,mean,div_div]
    have cancel : (Fintype.card J:ℝ)*(b/(Fintype.card J))=b := by field_simp
    rw [cancel]
    exact div_le_div_of_nonneg_right (unique T) bp.le
  have hhit := (avg_mono hitBound).trans_eq (avg_div reads b)
  unfold charge
  simp only [avg_add,mean_const,avg_div reads b]
  linarith only [eh,lh,hhit]

/-- Consume the two expected physical budgets after averaging times and
    epochs. The law may already include the hard input and the machine tape. -/
theorem normalized_charge_expectation {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    {a b : ℝ} {n : ℕ} (ap : 0<a) (bp : 0<b) (np : 0<n)
    (work query score : Ω→ℝ) (wi : Integrable work μ) (qi : Integrable query μ)
    (si : Integrable score μ) (cap : ∀ᵐ ω ∂μ, score ω≤2*(work ω/(n*a))+2*(query ω/b))
    (total : (∫ω,work ω ∂μ)≤n*a) (selected : (∫ω,query ω ∂μ)≤b) :
    (∫ω,score ω ∂μ)≤4 := by
  have denom : (0:ℝ)<n*a := mul_pos (by exact_mod_cast np) ap
  have w := (div_le_one denom).mpr total
  have q := (div_le_one bp).mpr selected
  have dom := integral_mono_ae si (((wi.div_const _).const_mul 2).add ((qi.div_const _).const_mul 2)) cap
  change (∫ω,score ω ∂μ) ≤ ∫ω,2*(work ω/(n*a))+2*(query ω/b) ∂μ at dom
  rw [integral_add ((wi.div_const _).const_mul 2) ((qi.div_const _).const_mul 2),
    integral_const_mul,integral_const_mul,integral_div,integral_div] at dom
  linarith


theorem cumulative_toReal (D : DataStructure N w Ω) (seed : Ω) (rows : Family N)
    (fit : n*n≤N) (mixed : Bool) (x : Row n) (qs : Fin n→Fin N) (t : ℕ) :
    cumulative D seed rows fit mixed x qs t=(totalCost D seed rows (runPrefix fit mixed x qs t)).toReal := by
  unfold cumulative totalCost
  cases history D seed rows (runPrefix fit mixed x qs t) <;> simp

theorem cumulative_zero (D : DataStructure N w Ω) (seed : Ω) (rows : Family N)
    (fit : n*n≤N) (mixed : Bool) (x : Row n) (qs : Fin n→Fin N) :
    cumulative D seed rows fit mixed x qs 0=0 := by
  unfold cumulative
  simp only [runPrefix,List.take_zero,Epoch.rounds,List.flatMap_nil,history]
  cases D.init seed rows <;> simp [runFrom]

def timeIndex {n : ℕ} (hn : 2≤n) (T : Time n) : Fin n :=
  ⟨T.val-1,by obtain ⟨lo,hi⟩ := mem_Icc.mp T.property; omega⟩

theorem timeIndex_label {n : ℕ} (hn : 2≤n) (T : Time n) : (timeIndex hn T).val+1=T.val := by
  obtain ⟨lo,hi⟩ := mem_Icc.mp T.property
  dsimp [timeIndex]; omega

def throughUpdate (fit : n*n≤N) (mixed : Bool) (x : Row n) (qs : Fin n→Fin N) (t : Fin n) :=
  runPrefix fit mixed x qs t.val ++ [.inl (address fit t (x t))]

theorem end_round (fit : n*n≤N) (mixed : Bool) (x : Row n) (qs : Fin n→Fin N) (t : Fin n) :
    throughUpdate fit mixed x qs t ++ (if mixed then [.inr (qs t)] else []) =
      runPrefix fit mixed x qs (t.val+1) := by
  have lim : t.val<(List.finRange n).length := by simp
  rw [throughUpdate,runPrefix,runPrefix,List.take_succ_eq_append_getElem lim]
  cases mixed <;> simp [Epoch.rounds,List.flatMap_append,List.append_assoc]

theorem interleaved_query (fit : n*n≤N) (x : Row n) (qs : Fin n→Fin N) (t : Fin n)
    (D : DataStructure N w Ω) (seed : Ω) (rows : Family N)
    (completed : ∃z,history D seed rows (runPrefix fit true x qs n)=some z) :
    (nextCost D seed rows (throughUpdate fit true x qs t) (qs t)).toReal ≤
      increment (cumulative D seed rows fit true x qs) (t.val+1) := by
  let before := runPrefix fit true x qs t.val
  let past := throughUpdate fit true x qs t
  have endeq : past++[.inr (qs t)]=runPrefix fit true x qs (t.val+1) := end_round fit true x qs t
  obtain ⟨z,hz⟩ := completed
  obtain ⟨v,hv,_⟩ := prefix_history D seed rows (extendPrefix fit true x qs t.isLt) hz
  have det : history D seed rows (past++[.inr (qs t)])=some v := endeq ▸ hv
  obtain ⟨p,hp,_⟩ := prefix_history D seed rows (show past <+: past++[.inr (qs t)] from ⟨_,rfl⟩) det
  obtain ⟨pre,hpre,hc⟩ := prefix_history D seed rows (show before <+: past from ⟨_,rfl⟩) hp
  rw [history_snoc,hp] at det
  cases op : operation D seed past.length (.inr (qs t)) p.memory with
  | none => simp [advance,op] at det
  | some r =>
    have probe : v.probes=p.probes+r.trace.length := by
      simp [advance,op] at det; rw [←det]
    have out : (nextCost D seed rows past (qs t)).toReal=r.trace.length := by simp [nextCost,hp,op]
    have lhs : cumulative D seed rows fit true x qs t.val=pre.probes := by
      change history D seed rows (runPrefix fit true x qs t.val)=some pre at hpre
      simp [cumulative,hpre]
    have rhs : cumulative D seed rows fit true x qs (t.val+1)=v.probes := by simp [cumulative,hv]
    change _ ≤ increment _ _
    rw [show throughUpdate fit true x qs t=past from rfl,out]
    unfold increment
    rw [Nat.add_sub_cancel,rhs,lhs]
    apply le_sub_iff_add_le.mpr
    rw [←Nat.cast_add]; exact_mod_cast (by omega : r.trace.length+pre.probes≤v.probes)

theorem interleaved_query_mean (fit : n*n≤N) (hn : 2≤n) (x : Row n) (qs : Fin n→Fin N)
    (D : DataStructure N w Ω) (seed : Ω) (rows : Family N)
    (completed : ∃z,history D seed rows (runPrefix fit true x qs n)=some z) :
    mean (fun T : Time n => (nextCost D seed rows (throughUpdate fit true x qs (timeIndex hn T))
      (qs (timeIndex hn T))).toReal) ≤ (2/n)*(totalCost D seed rows (runPrefix fit true x qs n)).toReal := by
  let C := cumulative D seed rows fit true x qs
  have mono := monotone_prefix D seed rows fit true x qs completed
  have cc (j) : 0 ≤ increment C j := sub_nonneg.mpr (mono (Nat.sub_le j 1))
  have point (T : Time n) : (nextCost D seed rows (throughUpdate fit true x qs (timeIndex hn T))
      (qs (timeIndex hn T))).toReal ≤ window n 0 1 T.val (increment C) := by
    obtain ⟨lo,hi⟩ := mem_Icc.mp T.property
    have q := interleaved_query fit x qs (timeIndex hn T) D seed rows completed
    rw [timeIndex_label] at q
    rw [window_increment hi (by omega),Nat.sub_zero]
    exact q
  refine (avg_mono point).trans ?_
  rw [mean_time n (fun t => window n 0 1 t (increment C))]
  have win := window_mean (show 0<n by omega) 0 1 (increment C) cc
  rw [total_increment,show C 0=0 from cumulative_zero ..,sub_zero,show C n=_ from cumulative_toReal ..] at win
  simpa using win


end Accounting

end
end AmortizedBound.Simulation

/-! ## Protocol -/

/-! The fixed public execution gives bounded advice, Bob's message, Alice's
trace and a verifier. The truth memory is reconstructed from actual writes,
independently of the query used after the epoch. -/
namespace AmortizedBound.Protocol
open DisjointnessFoundations CellProbe WordProgram Description
open DisjointnessDraft.PhysicalProtocol
open AmortizedBound.Simulation (prefixBits)
open AmortizedBound.Simulation.Physical
open Finset Classical Real
noncomputable section
set_option maxHeartbeats 1200000

abbrev Address (w : ℕ) := Fin (2^w)
abbrev Log (w : ℕ) := List (Address w × Address w)
abbrev Rows (m : ℕ) (W : Type) := Fin m → W
abbrev Block (n s : ℕ) := Communication.Block n s
abbrev Coins (w h r : ℕ) := (Address w → Bool) × (Fin (h*r) → Bool)
abbrev AdviceMsg (w e l : ℕ) := Option (Advice w e l)
abbrev BobMsg (w l cap h r : ℕ) := Packet w l cap × (Fin (h*r) → Bool)

/-- The physical data at one fixed public tape, query time and epoch. Segment
costs include all operations charged to their respective windows. -/
structure Snapshot (m n s w : ℕ) (W O : Type) where
  block : W → Block n s
  old : Rows m W → O → Memory w
  epochLog : Rows m W → Block n s → O → Log w
  laterLog : Rows m W → Block n s → O → Log w
  epochCost : Rows m W → Block n s → O → ℕ
  laterCost : Rows m W → Block n s → O → ℕ
  epochPaid : ∀ f x o,(epochLog f x o).length≤epochCost f x o
  laterPaid : ∀ f x o,(laterLog f x o).length≤laterCost f x o
  query : Fin m → Program (Address w) (Address w) (Option Bool)
  outsideDisjoint : W → O → Bool

namespace Snapshot
variable (S : Snapshot m n s w W O)
def actual (f : Rows m W) (x : Block n s) (o : O) :=
  DisjointnessFoundations.Simulation.applyWrites
    (DisjointnessFoundations.Simulation.applyWrites (S.old f o) (S.epochLog f x o)) (S.laterLog f x o)
def recent (f : Rows m W) (x : Block n s) (o : O) := touched (S.laterLog f x o)
def early (f : Rows m W) (x : Block n s) (o : O) := touched (S.epochLog f x o) \ S.recent f x o
def bounded (e l : ℕ) (f : Rows m W) (x : Block n s) (o : O) :=
  S.epochCost f x o≤e ∧ S.laterCost f x o≤l

private theorem early_cap (e l : ℕ) (f : Rows m W) (x : Block n s) (o : O)
    (ok : S.bounded e l f x o) : (S.early f x o).card≤e :=
  (card_le_card sdiff_subset).trans ((List.toFinset_card_le _).trans
    ((List.length_map _).le.trans ((S.epochPaid ..).trans ok.1)))
private theorem recent_cap (e l : ℕ) (f : Rows m W) (x : Block n s) (o : O)
    (ok : S.bounded e l f x o) : (S.recent f x o).card≤l :=
  (List.toFinset_card_le _).trans ((List.length_map _).le.trans ((S.laterPaid ..).trans ok.2))

def tables (e l : ℕ) (f : Rows m W) (x : Block n s) (o : O) (ok : S.bounded e l f x o) : Advice w e l :=
  (table (S.early f x o) (S.actual f x o) (S.early_cap e l f x o ok),
   table (S.recent f x o) (S.actual f x o) (S.recent_cap e l f x o ok))

def merlin (e l : ℕ) (f : Rows m W) (x : Block n s) (o : O) : AdviceMsg w e l :=
  if ok : S.bounded e l f x o then some (S.tables e l f x o ok) else none

def packet (u : AdviceMsg w e l) (coins : Coins w h r) (cap : ℕ) : BobMsg w l cap h r :=
  (u.bind (fun t => send t coins.1 cap),coins.2)

def reply (fuel : ℕ) (f : Rows m W) (o : O) (p : BobMsg w l cap h r) (q : Fin m) : TraceCode w fuel :=
  match p.1 with
  | none => encodeTrace w fuel ⟨[],none⟩
  | some tab =>
    let y := replay (fun a => (tab.val a).getD (S.old f o a)) (S.query q) (fun _ => none)
    if y.2.length≤fuel then
      encodeTrace w fuel ⟨y.2,y.1.map (fun b => b && S.outsideDisjoint (f q) o)⟩
    else encodeTrace w fuel ⟨[],none⟩

def verify (u : AdviceMsg w e l) (p : BobMsg w l cap h r) (code : TraceCode w fuel) : Bool :=
  match u,p.1 with
  | some tab,some message =>
    let tr := decodeTrace w fuel code
    let E := domain tab.1.val
    let d := (E ∩ touched tr.probes).card
    decide (tr.answer=some true ∧
      (∀ pair∈tr.probes, ∀ a, listed tab pair.1=some a → pair.2=a) ∧
      covered E (fun a => (message.val a).isSome) tr.probes ∧
      d≤r ∧ ∀j∈prefixBits h r d,p.2 j=true)
  | _,_ => false

def game (e l cap fuel h r : ℕ) :
    Communication.Game m n s W O (Coins w h r) (AdviceMsg w e l) (BobMsg w l cap h r) (TraceCode w fuel) where
  block := S.block
  merlin := S.merlin e l
  packet := fun u _ _ coins => packet u coins cap
  reply := S.reply fuel
  verify := fun _ p t u => verify u p t

def truth (f : Rows m W) (x : Block n s) (o : O) (q : Fin m) :=
  replay (S.actual f x o) (S.query q) (fun _ => none)

theorem intact (f : Rows m W) (x : Block n s) (o : O) (a : Address w)
    (e : a∉S.early f x o) (l : a∉S.recent f x o) : S.old f o a=S.actual f x o a := by
  open DisjointnessFoundations.Simulation in
  have er : ¬ Written (S.epochLog f x o) a := by
    intro h; exact e (mem_sdiff.mpr ⟨(mem_touched _ _).mpr h,l⟩)
  have lr : ¬DisjointnessFoundations.Simulation.Written (S.laterLog f x o) a := by simpa [recent] using l
  simp [actual,DisjointnessFoundations.Simulation.applyWrites_of_unwritten _ _ _ lr,
    DisjointnessFoundations.Simulation.applyWrites_of_unwritten _ _ _ er]

private theorem listed_value (e l : ℕ) (f : Rows m W) (x : Block n s) (o : O) (ok : S.bounded e l f x o)
    (a : Address w) : listed (S.tables e l f x o ok) a =
    if a∈S.recent f x o ∨ a∈S.early f x o then some (S.actual f x o a) else none := by
  by_cases t : a∈S.recent f x o <;> by_cases i : a∈S.early f x o <;> simp [tables,listed,t,i]

private theorem sent_table (e l cap : ℕ) (f : Rows m W) (x : Block n s) (o : O)
    (ok : S.bounded e l f x o) (mask : Address w → Bool) (tab : Table w (l+cap))
    (sent : send (S.tables e l f x o ok) mask cap=some tab) (a : Address w) :
    tab.val a = if a∈S.recent f x o ∨ (a∈S.early f x o ∧ mask a=true)
      then some (S.actual f x o a) else none := by
  simp only [send] at sent
  split at sent
  · cases sent
    simp only [table_val,sampled,tables,table_domain,mem_union,mem_filter]
    by_cases t : a∈S.recent f x o <;> by_cases i : a∈S.early f x o <;>
      cases h : mask a <;> simp [listed,tables,t,i,table_val,h]
  · contradiction


def targets (E : Finset (Address w)) (ps : Log w) := E ∩ touched ps

def acceptsTrace (E : Finset (Address w)) (coins : Coins w h r)
    (fuel : ℕ) (outside : Bool) (run : Option Bool × Log w) : Prop :=
  run.2.length≤fuel ∧ run.1=some true ∧ outside=true ∧
    covered E coins.1 run.2 ∧ (targets E run.2).card≤r ∧
    ∀j∈prefixBits h r (targets E run.2).card, coins.2 j=true

private theorem packet_iff (e l cap fuel h r : ℕ) (f : Rows m W) (x : Block n s) (o : O)
    (ok : S.bounded e l f x o) (q : Fin m) (coins : Coins w h r) (tab : Table w (l+cap))
    (sent : send (S.tables e l f x o ok) coins.1 cap=some tab) :
    let p : BobMsg w l cap h r := (some tab,coins.2)
    verify (some (S.tables e l f x o ok)) p (S.reply fuel f o p q)=true ↔
      acceptsTrace (S.early f x o) coins fuel (S.outsideDisjoint (f q) o) (S.truth f x o q) := by
  dsimp only
  let E := S.early f x o
  let L := S.recent f x o
  let m' := fun a => (tab.val a).getD (S.old f o a)
  let sim := replay m' (S.query q) (fun _ => none)
  let act := S.truth f x o q
  have memory : m'=simulatedMemory (S.old f o) (S.actual f x o) E L coins.1 := by
    funext a; unfold m'; rw [S.sent_table e l cap f x o ok coins.1 tab sent]
    by_cases late : a∈L <;> by_cases early : a∈E <;> cases bit : coins.1 a <;> simp_all [simulatedMemory,E,L]
  have check : covered E coins.1 sim.2 ↔ covered E coins.1 act.2 ∧ sim=act := by
    dsimp only [sim,act,truth]; rw [memory]
    exact verified_iff _ _ E L _ (S.intact f x o) _
  have restore (c : covered E coins.1 act.2) : sim=act := by
    dsimp only [sim,act,truth]; rw [memory]
    exact (complete_of_covered _ _ E L _ (S.intact f x o) _ c).symm
  have flag (a : Address w) (inE : a∈E) : (tab.val a).isSome=coins.1 a := by
    have no : a∉S.recent f x o := (mem_sdiff.mp inE).2
    rw [S.sent_table e l cap f x o ok coins.1 tab sent]
    cases h : coins.1 a <;> simp [no,inE,E] at *
  have covers (ps : Log w) :
      covered E (fun a => (tab.val a).isSome) ps ↔ covered E coins.1 ps := by
    constructor
    · intro test z hz he; exact (flag z.1 he).symm.trans (test z hz he)
    · intro test z hz he; exact (flag z.1 he).trans (test z hz he)
  have vals (z : Address w × Address w) (hz : z∈act.2) (val : Address w)
      (listed' : listed (S.tables e l f x o ok) z.1=some val) : z.2=val := by
    rw [S.listed_value] at listed'
    split at listed'
    · exact ((trace_entries (S.actual f x o) (S.query q) (fun _ => none)).2 z hz).2.trans (Option.some.inj listed')
    · contradiction
  change verify (some (S.tables e l f x o ok)) (some tab,coins.2)
      (if sim.2.length≤fuel then encodeTrace w fuel ⟨sim.2,sim.1.map (fun b => b && S.outsideDisjoint (f q) o)⟩
       else encodeTrace w fuel ⟨[],none⟩)=true ↔ acceptsTrace E coins fuel (S.outsideDisjoint (f q) o) act
  by_cases short : sim.2.length≤fuel
  · rw [if_pos short]
    simp only [verify,decode_encode w fuel ⟨sim.2,sim.1.map (fun b => b && S.outsideDisjoint (f q) o)⟩ short,decide_eq_true_eq]
    simp only [tables,table_domain]
    change (sim.1.map (fun b => b && S.outsideDisjoint (f q) o)=some true ∧
      (∀z∈sim.2,∀val, listed (S.tables e l f x o ok) z.1=some val → z.2=val) ∧
      covered E (fun a => (tab.val a).isSome) sim.2 ∧ (targets E sim.2).card≤r ∧ _) ↔ _
    rw [covers]
    constructor
    · rintro ⟨yes,_,cov,d,pad⟩
      obtain ⟨hc,eq⟩ := check.mp cov
      rw [eq] at yes short d pad
      obtain ⟨b,report,both⟩ := Option.map_eq_some_iff.mp yes
      obtain ⟨rfl,out⟩ := Bool.and_eq_true_iff.mp both
      exact ⟨short,report,out,hc,d,pad⟩
    · rintro ⟨_,yes,out,cov,d,pad⟩
      rw [restore cov]
      exact ⟨by simp [yes,out],vals,cov,d,pad⟩
  · rw [if_neg short]
    have nil := decode_encode w fuel ⟨[],none⟩ (by simp)
    simp only [verify,nil,reduceCtorEq,false_and,decide_false,Bool.false_eq_true,false_iff]
    rintro ⟨len,_,_,cov,_,_⟩
    exact short ((restore cov) ▸ len)

theorem accepted_iff (e l cap fuel h r : ℕ) (f : Rows m W) (x : Block n s) (o : O)
    (q : Fin m) (coins : Coins w h r) :
    (S.game e l cap fuel h r).accepted q (f,x,o,coins)=true ↔
    S.bounded e l f x o ∧ ((S.early f x o).filter (fun a => coins.1 a)).card≤cap ∧
      acceptsTrace (S.early f x o) coins fuel (S.outsideDisjoint (f q) o) (S.truth f x o q) := by
  by_cases ok : S.bounded e l f x o
  · let u := S.tables e l f x o ok
    have m : S.merlin e l f x o=some u := by simp [merlin,ok,u]
    have size : sampled u.1 coins.1=(S.early f x o).filter (fun a => coins.1 a) := by simp [sampled,u,tables]
    change verify (S.merlin e l f x o) (packet (S.merlin e l f x o) coins cap)
      (S.reply fuel f o (packet (S.merlin e l f x o) coins cap) q)=true ↔ _
    rw [m]
    change verify (some u) (send u coins.1 cap,coins.2) (S.reply fuel f o (send u coins.1 cap,coins.2) q)=true ↔ _
    cases sent : send u coins.1 cap with
    | none =>
      have over : ¬((S.early f x o).filter (fun a => coins.1 a)).card≤cap := by
        intro fits; have h : (sampled u.1 coins.1).card≤cap := size ▸ fits
        simp [send,h] at sent
      simp [verify,over]
    | some tab =>
      have fits : ((S.early f x o).filter (fun a => coins.1 a)).card≤cap := by
        by_contra bad
        have h : ¬(sampled u.1 coins.1).card≤cap := by rw [size]; exact bad
        simp [send,h] at sent
      simpa only [ok,fits,true_and] using S.packet_iff e l cap fuel h r f x o ok q coins tab sent
  · simp [Communication.Game.accepted,Communication.Game.answers,Communication.Game.psi,Communication.Game.advice,
      game,merlin,ok,packet,verify]


open AmortizedBound.Simulation (privateChance privateLaw privateAccept private_bounds privateChance_congr privateChance_false privateChance_product prob_private message_budgets)
open DisjointnessFoundations.FiniteSampling DisjointnessFoundations.HardIndependence
  DisjointnessFoundations.VerifierLaw DisjointnessFoundations.ActualAcceptance
  DisjointnessFoundations.HardDistribution
open MeasureTheory
open scoped DisjointnessDraft.Information ENNReal

def eligible (e l fuel r : ℕ) (f : Rows m W) (x : Block n s) (o : O) (q : Fin m) : Prop :=
  S.bounded e l f x o ∧ eligibleYes r fuel (S.early f x o) (S.outsideDisjoint (f q) o) (S.truth f x o q)

def privateYes (rate : SamplingRate) (e l fuel h r : ℕ) (f : Rows m W) (x : Block n s) (o : O) (q : Fin m) :=
  privateChance rate fun mask F => (S.game e l ⌊2*rate.p*e⌋₊ fuel h r).accepted q (f,x,o,mask,F)=true

theorem private_exact (rate : SamplingRate) (e l fuel h r : ℕ) (f : Rows m W) (x : Block n s) (o : O) (q : Fin m) :
    S.privateYes rate e l fuel h r f x o q =
    if S.eligible e l fuel r f x o q then
      privateAccept rate h r e (S.early f x o) (targets (S.early f x o) (S.truth f x o q).2) else 0 := by
  unfold privateYes
  by_cases ok : S.eligible e l fuel r f x o q
  · rw [if_pos ok,privateAccept,←privateChance_product]
    apply privateChance_congr; intro mask F
    rw [S.accepted_iff]; unfold eligible eligibleYes at ok
    unfold acceptsTrace
    rw [needed_iff]
    change (_ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _) ↔ _
    exact ⟨fun z => ⟨⟨z.2.2.2.2.2.1,z.2.1⟩,z.2.2.2.2.2.2.2⟩,
      fun z => ⟨ok.1,z.1.2,ok.2.2.2.1,ok.2.2.1,ok.2.1,z.1.1,ok.2.2.2.2,z.2⟩⟩
  · rw [if_neg ok,←privateChance_false (cells:=2^w) (bits:=h*r) rate]
    apply privateChance_congr; intro mask F
    rw [S.accepted_iff,iff_false]
    rintro ⟨paid,_,len,yes,out,_,d,_⟩
    exact ok ⟨paid,out,yes,len,d⟩

theorem private_upper (rate : SamplingRate) (e l fuel h r : ℕ) (dyadic : rate.p=(1/2:ℝ)^h)
    (f : Rows m W) (x : Block n s) (o : O) (q : Fin m) :
    S.privateYes rate e l fuel h r f x o q ≤ rate.p^r := by
  rw [S.private_exact]; split
  · rename_i ok
    exact (private_bounds rate h r e dyadic _ _ (S.early_cap _ _ _ _ _ ok.1) ok.2.2.2.2).2
  · exact pow_nonneg rate.positive.le _

theorem private_lower (rate : SamplingRate) (e l fuel h r : ℕ) (dyadic : rate.p=(1/2:ℝ)^h)
    (f : Rows m W) (x : Block n s) (o : O) (q : Fin m) (ok : S.eligible e l fuel r f x o q) :
    rate.p^r-exp (-(rate.p*e)/3) ≤ S.privateYes rate e l fuel h r f x o q := by
  rw [S.private_exact,if_pos ok]
  exact (private_bounds rate h r e dyadic _ _ (S.early_cap _ _ _ _ _ ok.1) ok.2.2.2.2).1

/-- A positive erroneous intersection has a true yes output, passes the
outside test and intersects at a coordinate of the selected epoch. -/
theorem accepted_collision (e l cap fuel h r : ℕ) (f : Rows m W) (x : Block n s) (o : O)
    (q : Fin m) (coins : Coins w h r)
    (accept : (S.game e l cap fuel h r).accepted q (f,x,o,coins)=true)
    (hit : Communication.Game.overlaps (S.block (f q)) x) :
    (S.truth f x o q).1=some true ∧ S.outsideDisjoint (f q) o=true ∧ ∃j,S.block (f q) j=x j := by
  obtain ⟨_,_,_,yes,out,_,_,_⟩ := (S.accepted_iff ..).mp accept
  exact ⟨yes,out,hit⟩

abbrev Input (m n s : ℕ) (W O : Type) := Fin m × (Rows m W × (Block n s × O))

private theorem uniform_section {A B : Type} [Fintype A] [MeasurableSpace A] [MeasurableSingletonClass A]
    [Fintype B] [MeasurableSpace B] [MeasurableSingletonClass B] (μ : Measure B) [IsFiniteMeasure μ]
    (E : Set (A × B)) : ((unif A).prod μ).real E = mean (fun a => μ.real (Prod.mk a ⁻¹' E)) := by
  rw [prod_event _ _ _ (Set.toFinite _).measurableSet]
  simp only [real_unif_atom,mean,←Finset.mul_sum,div_eq_inv_mul]

private theorem mean_pair {A B : Type} [Fintype A] [Fintype B] (f : A × B → ℝ) :
    mean f = mean (fun a => mean fun b => f (a,b)) := mean_prod (fun a b => f (a,b))

variable [Fintype W] [MeasurableSpace W] [MeasurableSingletonClass W]
  [Fintype O] [MeasurableSpace O] [MeasurableSingletonClass O]

/-- The protocol's actual acceptance is the uniform average of its pointwise
private-coin acceptance on the original inputs. -/
theorem average_acceptance (rate : SamplingRate) (e l fuel h r : ℕ) :
    Communication.acceptance (S.game e l ⌊2*rate.p*e⌋₊ fuel h r) (unif O) (privateLaw rate (2^w) (h*r)) =
    mean (fun d : Input m n s W O => S.privateYes rate e l fuel h r d.2.1 d.2.2.1 d.2.2.2 d.1) := by
  simp_rw [mean_pair]
  unfold Communication.acceptance Communication.experiment
  simp_rw [uniform_section]
  unfold privateYes
  simp_rw [←prob_private]
  simp only [mean,Fintype.card_fin]
  rfl

theorem average_error [Nonempty O] (rate : SamplingRate) (e l fuel h r : ℕ) :
    (S.game e l ⌊2*rate.p*e⌋₊ fuel h r).jointError (unif O) (privateLaw rate (2^w) (h*r)) =
    mean (fun d : Input m n s W O => if Communication.Game.overlaps (S.block (d.2.1 d.1)) d.2.2.1
      then S.privateYes rate e l fuel h r d.2.1 d.2.2.1 d.2.2.2 d.1 else 0) := by
  let G := S.game e l ⌊2*rate.p*e⌋₊ fuel h r
  have point (q : Fin m) (f : Rows m W) (x : Block n s) (o : O) :
      (if Communication.Game.overlaps (S.block (f q)) x then S.privateYes rate e l fuel h r f x o q else 0)=
      privateChance rate (fun mask F => G.accepted q (f,x,o,mask,F)=true ∧ Communication.Game.overlaps (S.block (f q)) x) := by
    by_cases hit : Communication.Game.overlaps (S.block (f q)) x
    · rw [if_pos hit]; apply privateChance_congr; intro mask F; simp only [hit,and_true]; rfl
    · rw [if_neg hit,←privateChance_false (cells:=2^w) (bits:=h*r) rate]
      apply privateChance_congr; intro mask F; simp only [hit,and_false]
  simp_rw [point,mean_pair]
  unfold Communication.Game.jointError Communication.experiment
  simp_rw [uniform_section,←prob_private]
  simp only [mean,Fintype.card_fin]
  rfl

/-- If a fixed physical snapshot has the three claimed message budgets and
sufficient acceptance, the communication theorem forces accepted errors. -/
theorem fixed_snapshot :
    ∀ᶠ n : ℕ in Filter.atTop, ∀ m s w e l fuel h r : ℕ, ∀ (W O : Type)
    [Fintype W] [MeasurableSpace W] [MeasurableSingletonClass W] [Nonempty W]
    [Fintype O] [MeasurableSpace O] [MeasurableSingletonClass O] [Nonempty O],
    ∀ (S : Snapshot m n s w W O) (rate : SamplingRate),
    let cap := ⌊2*rate.p*e⌋₊
    let G := S.game e l cap fuel h r
    let ρ := Communication.acceptance G (unif O) (privateLaw rate (2^w) (h*r))
    (n:ℝ)^(2/3:ℝ)/3≤s → s≤n → n^4≤m →
    (unif W).map S.block=unif (Block n s) →
    ((adviceBits w e l+1:ℕ):ℝ)≤(n:ℝ)^(5/4:ℝ) →
    ((packetBits w l cap+h*r:ℕ):ℝ)≤(s:ℝ)/200 →
    (replyBits w fuel:ℝ)≤(logb 2 n)^3 → (n:ℝ)^(-1/2:ℝ)≤ρ →
    (s:ℝ)/(64*n)<G.jointError (unif O) (privateLaw rate (2^w) (h*r))/ρ := by
  filter_upwards [Communication.robust_communication] with n robust
  intro m s w e l fuel h r W O _ _ _ _ _ _ _ _ S rate cap G ρ geom sn big bal advice packet reply mass
  obtain ⟨au,bu,cu⟩ := message_budgets w e l cap h r fuel
  have packetBound : (Fintype.card (BobMsg w l cap h r):ℝ)≤(2:ℝ)^((s:ℝ)/200) := by
    calc _ ≤ (2:ℝ)^(packetBits w l cap+h*r) := by exact_mod_cast bu
         _ = (2:ℝ)^((packetBits w l cap+h*r:ℕ):ℝ) := (rpow_natCast ..).symm
         _ ≤ _ := rpow_le_rpow_of_exponent_le (by norm_num) packet
  exact robust m s W O (Coins w h r) (AdviceMsg w e l) (BobMsg w l cap h r) (TraceCode w fuel) G
    (unif O) (privateLaw rate (2^w) (h*r)) _ _ geom sn big bal au advice packetBound cu reply mass

end Snapshot
end
end AmortizedBound.Protocol

/-! ## MachineProtocol -/

namespace AmortizedBound.Dynamic.Epoch
open DisjointnessFoundations CellProbe MeasureTheory
open scoped ENNReal
open Classical
noncomputable section

variable {n s N w : ℕ} {Ω : Type} (e : Epoch n s) (fit : n*n ≤ N)
    (mixed : Bool) (qs : Fin n → Fin N) (D : DataStructure N w Ω) (seed : Ω)

private def blank : History w := ⟨fun _ => 0,0,none⟩

def preState (F : Fin N → Row n) (o : e.Out) : History w :=
  (history D seed (fun q => rowSet fit (F q)) (e.oldOps fit mixed qs o)).getD blank

def midState (F : Fin N → Row n) (x : Fin s → Fin n) (o : e.Out) : History w :=
  let pre := e.preState fit mixed qs D seed F o
  (runFrom D seed (e.oldOps fit mixed qs o).length pre (e.epochOps fit mixed qs x o)).getD pre

def lastState (F : Fin N → Row n) (x : Fin s → Fin n) (o : e.Out) : History w :=
  let mid := e.midState fit mixed qs D seed F x o
  (runFrom D seed ((e.oldOps fit mixed qs o).length+(e.epochOps fit mixed qs x o).length) mid
    (e.recentOps fit mixed qs x o)).getD mid

def epochWrites (F : Fin N → Row n) (x : Fin s → Fin n) (o : e.Out) :=
  segment D seed (e.oldOps fit mixed qs o).length (e.preState fit mixed qs D seed F o).memory (e.epochOps fit mixed qs x o)

def recentWrites (F : Fin N → Row n) (x : Fin s → Fin n) (o : e.Out) :=
  segment D seed ((e.oldOps fit mixed qs o).length+(e.epochOps fit mixed qs x o).length)
    (e.midState fit mixed qs D seed F x o).memory (e.recentOps fit mixed qs x o)

theorem states_exact (F : Fin N → Row n) (x : Fin s → Fin n) (o : e.Out) {last : History w}
    (ok : history D seed (fun q => rowSet fit (F q)) (e.past fit mixed qs x o)=some last) :
    let pre := e.preState fit mixed qs D seed F o
    let mid := e.midState fit mixed qs D seed F x o
    let ew := e.epochWrites fit mixed qs D seed F x o
    let lw := e.recentWrites fit mixed qs D seed F x o
    e.lastState fit mixed qs D seed F x o = last ∧
    last.memory=DisjointnessFoundations.Simulation.applyWrites (DisjointnessFoundations.Simulation.applyWrites pre.memory ew) lw ∧
      pre.probes+ew.length≤mid.probes ∧ mid.probes+lw.length≤last.probes := by
  obtain ⟨pre,mid,hp,hm,hl,mem,c1,c2⟩ := e.actual_segments fit mixed qs D seed _ x o ok
  simp only [preState,midState,lastState,epochWrites,recentWrites,hp,hm,hl,Option.getD_some]
  exact ⟨trivial,mem,c1,c2⟩

/-- A physical snapshot for every fixed choice of public inputs. The default
    branches totalize failed executions. `snapshot_exact` removes them whenever
    the actual selected history terminates. -/
def snapshot (fuel : ℕ) : Protocol.Snapshot N n s w (Row n) e.Out where
  block row := row ∘ e.index
  old F o := (e.preState fit mixed qs D seed F o).memory
  epochLog := e.epochWrites fit mixed qs D seed
  laterLog := e.recentWrites fit mixed qs D seed
  epochCost F x o := max (e.epochWrites fit mixed qs D seed F x o).length
    ((e.midState fit mixed qs D seed F x o).probes-(e.preState fit mixed qs D seed F o).probes)
  laterCost F x o := max (e.recentWrites fit mixed qs D seed F x o).length
    ((e.lastState fit mixed qs D seed F x o).probes-(e.midState fit mixed qs D seed F x o).probes)
  epochPaid _ _ _ := le_max_left _ _
  laterPaid _ _ _ := le_max_left _ _
  query q := truncate D.step fuel (D.start seed (e.selected.val*stepCount mixed+1) (.inr q))
  outsideDisjoint := e.outsideOK

theorem snapshot_exact (fuel : ℕ) (F : Fin N → Row n) (x : Fin s → Fin n) (o : e.Out) {last : History w}
    (ok : history D seed (fun q => rowSet fit (F q)) (e.past fit mixed qs x o)=some last) :
    let S := e.snapshot fit mixed qs D seed fuel
    let pre := e.preState fit mixed qs D seed F o
    let mid := e.midState fit mixed qs D seed F x o
    S.actual F x o=last.memory ∧ S.epochCost F x o=mid.probes-pre.probes ∧
      S.laterCost F x o=last.probes-mid.probes := by
  obtain ⟨heq,mem,early,late⟩ := e.states_exact fit mixed qs D seed F x o ok
  refine ⟨mem.symm,?_,?_⟩
  · apply max_eq_right; omega
  · change max _ ((e.lastState fit mixed qs D seed F x o).probes-_) = _
    rw [heq]; apply max_eq_right; omega

def SeedHalts := ∀ (F : Fin N → Row n) (x : Fin s → Fin n) (o : e.Out) (q : Fin N),
  (history D seed (fun j => rowSet fit (F j)) (e.past fit mixed qs x o ++ [.inr q])).isSome

/-- For each of the two execution schedules, a common set of tapes of full
    measure terminates on every one of its finitely many hard inputs. -/
theorem seedHalts_ae [MeasurableSpace Ω] (μ : Measure Ω)
    (familySize : n=hardSize N)
    (ok : Correct μ D (hardFamilies N) (if mixed then legal else singleHistories N)) :
    ∀ᵐ a ∂μ, e.SeedHalts fit mixed qs D a := by
  letI : Fintype e.Out := by unfold Out; infer_instance
  unfold SeedHalts
  apply ae_all_iff.mpr; intro F
  apply ae_all_iff.mpr; intro x
  apply ae_all_iff.mpr; intro o
  apply ae_all_iff.mpr; intro q
  apply ok.terminates
  · intro j; rw [rowSet_card,familySize]
  · cases mixed with
    | true => exact e.selected_legal fit true qs x o q
    | false => exact e.selected_single fit qs x o q

/-- For a fixed tape, one cutoff suffices for every terminating query at every
relevant position and from every physical memory. Divergent memories do not
affect this choice. The cutoff is shared across epochs and hard inputs. -/
theorem universal_fuel (D : DataStructure N w Ω) (seed : Ω) (limit : ℕ) :
    ∃ k, ∀ (j : Fin limit) (q : Fin N) (m : Memory w) (r : Result w),
    operation D seed j.val (.inr q) m=some r →
    execute D.step k (D.start seed j.val (.inr q)) m=some r := by
  let I := Fin limit × Fin N × Memory w
  let run (i : I) := operation D seed i.1.val (.inr i.2.1) i.2.2
  let J := {i : I // (run i).isSome}
  let result (i : J) := (run i.val).get i.property
  have halts (i : J) : run i.val=some (result i) := (Option.some_get _).symm
  obtain ⟨k,allk⟩ := common_fuel (I:=J) D.step (fun i => D.start seed i.val.1.val (.inr i.val.2.1))
    (fun i => i.val.2.2) result halts
  refine ⟨k,?_⟩; intro j q m r hr
  let i : J := ⟨(j,q,m),by change (operation D seed j.val (.inr q) m).isSome; simp [hr]⟩
  have eq : result i=r := Option.some.inj ((halts i).symm.trans hr)
  exact eq ▸ allk i

noncomputable def fuel (D : DataStructure N w Ω) (seed : Ω) (n : ℕ) : ℕ :=
  (universal_fuel D seed (2*n+1)).choose

/-- This same finite cutoff yields the actual answer and cost for both execution
schedules at all selected positions and epochs. -/
theorem snapshot_query_common (halts : e.SeedHalts fit mixed qs D seed) :
    ∀ (F : Fin N → Row n) (x : Fin s → Fin n) (o : e.Out) (q : Fin N),
      let S := e.snapshot fit mixed qs D seed (fuel D seed n)
      let rows := fun j => rowSet fit (F j)
      let past := e.past fit mixed qs x o
      let physical := (S.query q).run (S.actual F x o)
      lastReport D seed rows (past++[.inr q])=physical.1 ∧ nextCost D seed rows past q=physical.2.2 := by
  letI : Fintype e.Out := by unfold Out; infer_instance
  let I : Type := (Fin N → Row n) × (Fin s → Fin n) × e.Out × Fin N
  let rows := fun (z : I) j => rowSet fit (z.1 j)
  let past := fun (z : I) => e.past fit mixed qs z.2.1 z.2.2.1
  have one (z : I) : ∃ (st : History w) (r : Result w),
      history D seed (rows z) (past z)=some st ∧
      operation D seed (e.selected.val*stepCount mixed+1) (.inr z.2.2.2) st.memory=some r := by
    have h := halts z.1 z.2.1 z.2.2.1 z.2.2.2
    change (history D seed (rows z) (past z++[.inr z.2.2.2])).isSome at h
    rw [history_snoc] at h
    cases hp : history D seed (rows z) (past z) with
    | none => simp [hp] at h
    | some st =>
      let op := operation D seed (past z).length (.inr z.2.2.2) st.memory
      cases hr : op with
      | none => simp [hp,advance,← show operation D seed (past z).length (.inr z.2.2.2) st.memory=op from rfl,op] at h; simp_all [op]
      | some r => exact ⟨st,r,rfl,by simpa only [op,past,e.selected_ordinal] using hr⟩
  choose st r hp hr using one
  let start := fun (z : I) => D.start seed (e.selected.val*stepCount mixed+1) (.inr z.2.2.2)
  let k := fuel D seed n
  have ordinalBound : e.selected.val*stepCount mixed+1 < 2*n+1 := by
    have lt := e.selected.isLt
    cases mixed <;> simp [stepCount] <;> omega
  have allk (z : I) := (universal_fuel D seed (2*n+1)).choose_spec
      ⟨e.selected.val*stepCount mixed+1,ordinalBound⟩ z.2.2.2 (st z).memory (r z) (hr z)
  intro F x o q
  let z : I := (F,x,o,q)
  obtain ⟨actual,_,_⟩ := e.snapshot_exact fit mixed qs D seed k F x o (hp z)
  have op := truncate_exact D.step k (start z) (st z).memory (allk z)
  have run : (((e.snapshot fit mixed qs D seed k).query q).run ((e.snapshot fit mixed qs D seed k).actual F x o)) =
      (some (r z).report,(r z).memory,(r z).trace.length) := by rw [actual]; exact op
  have ordinal : (past z).length=e.selected.val*stepCount mixed+1 := e.selected_ordinal ..
  change lastReport D seed (rows z) (past z++[.inr q])=_ ∧ nextCost D seed (rows z) (past z) q=_
  dsimp only [k] at run
  simp only [run,lastReport,nextCost,history_snoc,hp z,Option.bind_some,advance,ordinal]
  have action : operation D seed (e.selected.val*stepCount mixed+1) (Sum.inr q) (st z).memory=some (r z) := hr z
  simp [action]

theorem snapshot_query (halts : e.SeedHalts fit mixed qs D seed) :
    ∃ k, ∀ (F : Fin N → Row n) (x : Fin s → Fin n) (o : e.Out) (q : Fin N),
      let S := e.snapshot fit mixed qs D seed k
      let rows := fun j => rowSet fit (F j)
      let past := e.past fit mixed qs x o
      let physical := (S.query q).run (S.actual F x o)
      lastReport D seed rows (past++[.inr q])=physical.1 ∧ nextCost D seed rows past q=physical.2.2 :=
  ⟨fuel D seed n,e.snapshot_query_common fit mixed qs D seed halts⟩

end
end AmortizedBound.Dynamic.Epoch

/-! ## ActualCharge -/

/-! Probe accounting for the actual snapshots on one fixed hard input
and one fixed machine tape, averaged over the random time and epoch. -/
namespace AmortizedBound.ActualCharge
open DisjointnessFoundations CellProbe HardDistribution
open Simulation Simulation.Accounting Dynamic Parameters Finset Classical
noncomputable section

def half {n : ℕ} (hn : 2≤n) (T : Time n) : n/2≤(timeIndex hn T).val+1 := by
  rw [timeIndex_label]
  exact (mem_Icc.mp T.property).1

def epochAt {n β : ℕ} (hn : 2≤n) (pos : 1≤β) (T : Time n) (i : Candidate n β) :=
  candidateEpoch pos (timeIndex hn T) (half hn T) i

variable {n β N w : ℕ} {Ω : Type} (hn : 2≤n) (pos : 1≤β) (fit : n*n≤N) (mixed : Bool)
    (D : DataStructure N w Ω) (seed : Ω) (F : Fin N→Row n) (x : Row n) (qs : Fin n→Fin N)

def snap (T : Time n) (i : Candidate n β) :=
  (epochAt hn pos T i).snapshot fit mixed qs D seed (Epoch.fuel D seed n)

def split (T : Time n) (i : Candidate n β) := splitCoordinates (epochAt hn pos T i).index x

theorem join_split (T : Time n) (i : Candidate n β) :
    (epochAt hn pos T i).join (split hn pos x T i).1 (split hn pos x T i).2=x :=
  (splitCoordinates (epochAt hn pos T i).index).symm_apply_apply x

def rows := fun j => rowSet fit (F j)

def recentPast (T : Time n) := throughUpdate fit mixed x qs (timeIndex hn T)

theorem past_eq (T : Time n) (i : Candidate n β) :
    (epochAt hn pos T i).past fit mixed qs (split hn pos x T i).1 (split hn pos x T i).2=
      recentPast hn fit mixed x qs T := by
  simp only [Epoch.past,join_split]; rfl

def state (T : Time n) : History w :=
  (history D seed (rows fit F) (recentPast hn fit mixed x qs T)).getD ⟨fun _ => 0,0,none⟩

def commonTrace (T : Time n) :=
  Physical.replay (state hn fit mixed D seed F x qs T).memory
    (truncate D.step (Epoch.fuel D seed n) (D.start seed
      ((timeIndex hn T).val*Epoch.stepCount mixed+1) (.inr (qs (timeIndex hn T))))) (fun _ => none)

def queryCost (T : Time n) :=
  (nextCost D seed (rows fit F) (recentPast hn fit mixed x qs T) (qs (timeIndex hn T))).toReal

structure Counts where
  epoch : ℕ
  recent : ℕ
  reads : ℕ
  hits : ℕ

def counts (T : Time n) (i : Candidate n β) : Counts :=
  let S := snap hn pos fit mixed D seed qs T i
  let p := split hn pos x T i
  let tr := (S.truth F p.1 p.2 (qs (timeIndex hn T))).2
  ⟨S.epochCost F p.1 p.2,S.laterCost F p.1 p.2,tr.length,(Physical.needed (S.early F p.1 p.2) tr).card⟩

def value (a b : ℝ) (T : Time n) (i : Candidate n β) :=
  let c := counts hn pos fit mixed D seed F x qs T i
  charge a b (Fintype.card (Candidate n β)) (β^i.val) (occupied β (i.val-1)) c.epoch c.recent c.reads c.hits

def Completed := ∃z,history D seed (rows fit F) (runPrefix fit mixed x qs n)=some z

theorem past_state (completed : Completed fit mixed D seed F x qs) (T : Time n) :
    history D seed (rows fit F) (recentPast hn fit mixed x qs T)=some (state hn fit mixed D seed F x qs T) := by
  obtain ⟨z,hz⟩ := completed
  obtain ⟨last,lok,_⟩ := prefix_history D seed _ (extendPrefix fit mixed x qs (timeIndex hn T).isLt) hz
  obtain ⟨p,ok,_⟩ := prefix_history D seed _ (show recentPast hn fit mixed x qs T <+:
    runPrefix fit mixed x qs ((timeIndex hn T).val+1) from ⟨_,end_round fit mixed x qs (timeIndex hn T)⟩) lok
  simp [state,ok]

theorem snapshot_bounds (completed : Completed fit mixed D seed F x qs) (T : Time n) (i : Candidate n β) :
    let S := snap hn pos fit mixed D seed qs T i
    let pair := split hn pos x T i
    let C := cumulative D seed (rows fit F) fit mixed x qs
    let d := occupied β (i.val-1)
    (S.epochCost F pair.1 pair.2:ℝ) ≤ window n d (β^i.val) T.val (increment C) ∧
    (S.laterCost F pair.1 pair.2:ℝ) ≤ window n 0 d T.val (increment C) ∧
    S.truth F pair.1 pair.2 (qs (timeIndex hn T))=commonTrace hn fit mixed D seed F x qs T := by
  intro S pair C d
  let e := epochAt hn pos T i
  let st := state hn fit mixed D seed F x qs T
  have good : history D seed (rows fit F) (e.past fit mixed qs pair.1 pair.2)=some st := by
    rw [past_eq hn pos fit mixed x qs T i]; exact past_state hn fit mixed D seed F x qs completed T
  obtain ⟨actual,early,late⟩ := e.snapshot_exact fit mixed qs D seed (Epoch.fuel D seed n) F pair.1 pair.2 good
  have join : e.join pair.1 pair.2=x := join_split hn pos x T i
  have source := actual_windows e fit mixed qs D seed (rows fit F) pair.1 pair.2 (join ▸ completed)
  dsimp only at source
  rw [join] at source
  obtain ⟨pre,mid,last,preok,midok,recentok,lastok,ew,lw,_,_⟩ := source
  have eq0 : e.preState fit mixed qs D seed F pair.2=pre := by
    change history D seed (fun q => rowSet fit (F q)) _ = some pre at preok
    simp [Epoch.preState,preok]
  have eq1 : e.midState fit mixed qs D seed F pair.1 pair.2=mid := by
    simp only [Epoch.midState,eq0,midok,Option.getD_some]
  have eq2 : last=st := Option.some.inj (lastok.symm.trans good)
  have mo0 : pre.probes≤mid.probes := by have := (segment_correct D seed _ pre _ midok).2; omega
  have mo1 : mid.probes≤last.probes := by
    have := (segment_correct D seed _ mid _ recentok).2; omega
  have offset : e.selected.val+1-(e.start+β^i.val)=d := candidate_offset pos (timeIndex hn T) (half hn T) i
  have label : e.selected.val+1=T.val := timeIndex_label hn T
  rw [offset,label] at ew lw
  change S.epochCost F pair.1 pair.2=_ at early
  change S.laterCost F pair.1 pair.2=_ at late
  rw [eq1,eq0] at early
  rw [eq1,←eq2] at late
  refine ⟨?_,?_,?_⟩
  · rw [early,Nat.cast_sub mo0]; exact ew.le
  · rw [late,Nat.cast_sub mo1]; exact lw
  · change Physical.replay _ _ _ = _
    rw [show S.actual F pair.1 pair.2=st.memory from actual]
    rfl

theorem state_facts (completed : Completed fit mixed D seed F x qs) (T : Time n) (i : Candidate n β) :
    let e := epochAt hn pos T i
    let pair := split hn pos x T i
    let pre := e.preState fit mixed qs D seed F pair.2
    let mid := e.midState fit mixed qs D seed F pair.1 pair.2
    history D seed (rows fit F) (e.oldOps fit mixed qs pair.2)=some pre ∧
    runFrom D seed (e.oldOps fit mixed qs pair.2).length pre (e.epochOps fit mixed qs pair.1 pair.2)=some mid := by
  intro e pair pre mid
  have st := past_state hn fit mixed D seed F x qs completed T
  rw [←past_eq hn pos fit mixed x qs T i] at st
  obtain ⟨p,m,op,om,_⟩ := e.actual_segments fit mixed qs D seed (rows fit F) pair.1 pair.2 st
  change history D seed (fun q => rowSet fit (F q)) _=some p at op
  have eq : pre=p := by simp [pre,Epoch.preState,op]
  rw [eq]
  have eqm : mid=m := by simp only [mid,Epoch.midState,show e.preState fit mixed qs D seed F pair.2=p from eq,om,Option.getD_some]
  exact ⟨op,eqm ▸ om⟩

theorem sum_hits (completed : Completed fit mixed D seed F x qs) (T : Time n) :
    (∑i : Candidate n β,(counts hn pos fit mixed D seed F x qs T i).hits) ≤
      (commonTrace hn fit mixed D seed F x qs T).2.length := by
  let e := epochAt hn pos T
  let z := split hn pos x T
  let p := fun i => (e i).preState fit mixed qs D seed F (z i).2
  let m := fun i => (e i).midState fit mixed qs D seed F (z i).1 (z i).2
  have b := candidate_hits pos (timeIndex hn T) (half hn T) fit mixed qs x D seed (rows fit F)
    p m (commonTrace hn fit mixed D seed F x qs T).2
    (fun i => (state_facts hn pos fit mixed D seed F x qs completed T i).1)
    (fun i => (state_facts hn pos fit mixed D seed F x qs completed T i).2)
  apply le_trans (le_of_eq ?_) b
  apply sum_congr rfl
  intro i _
  dsimp only [counts]
  rw [(snapshot_bounds hn pos fit mixed D seed F x qs completed T i).2.2]
  rfl

theorem common_cost (completed : Completed fit mixed D seed F x qs) (T : Time n) (i : Candidate n β)
    (halts : (epochAt hn pos T i).SeedHalts fit mixed qs D seed) :
    ((commonTrace hn fit mixed D seed F x qs T).2.length : ℝ)≤queryCost hn fit mixed D seed F x qs T := by
  let e := epochAt hn pos T i
  let S := snap hn pos fit mixed D seed qs T i
  let z := split hn pos x T i
  let q := qs (timeIndex hn T)
  have tc := (e.snapshot_query_common fit mixed qs D seed halts F z.1 z.2 q).2
  have rr := (Physical.replay_correct (S.actual F z.1 z.2) (S.query q) (fun _ => none)).2
  have eq := (snapshot_bounds hn pos fit mixed D seed F x qs completed T i).2.2
  change S.truth F z.1 z.2 q=commonTrace hn fit mixed D seed F x qs T at eq
  rw [←eq]
  have over : Physical.overlay (S.actual F z.1 z.2) (fun _ => none) = S.actual F z.1 z.2 := rfl
  rw [over] at rr
  change nextCost D seed (rows fit F) (e.past fit mixed qs z.1 z.2) q =
    ((S.query q).run (S.actual F z.1 z.2)).2.2 at tc
  rw [past_eq hn pos fit mixed x qs T i] at tc
  change _≤(nextCost D seed (rows fit F) (recentPast hn fit mixed x qs T) q).toReal
  rw [tc,ENNReal.toReal_natCast]
  exact_mod_cast rr

theorem cost_bound [Nonempty (Candidate n β)] (completed : Completed fit mixed D seed F x qs)
    (halts : ∀T i,(epochAt hn pos T i).SeedHalts fit mixed qs D seed)
    {a b : ℝ} (ap : 0<a) (bp : 0<b) :
    mean (fun T => mean (value hn pos fit mixed D seed F x qs a b T)) ≤
      2*((totalCost D seed (rows fit F) (runPrefix fit mixed x qs n)).toReal/(n*a))+
      2*(mean (queryCost hn fit mixed D seed F x qs)/b) := by
  let C := cumulative D seed (rows fit F) fit mixed x qs
  let c := counts hn pos fit mixed D seed F x qs
  let tr := commonTrace hn fit mixed D seed F x qs
  have mono := monotone_prefix D seed (rows fit F) fit mixed x qs completed
  have positive (i : Candidate n β) : 0<occupied β (i.val-1) := by
    obtain ⟨lo,hi,dense⟩ := mem_candidates.mp i.property
    have := prefix_ge pos (i.val-1); omega
  have rc (T i) : (c T i).reads=(tr T).2.length := congrArg (fun y => y.2.length)
    (snapshot_bounds hn pos fit mixed D seed F x qs completed T i).2.2
  have go := normalized_charge_pointwise (show 0<n by omega) (fun i : Candidate n β => β^i.val)
    (fun i => occupied β (i.val-1)) (fun _ => pow_pos (by omega) _) positive ap bp (increment C)
    (fun t => sub_nonneg.mpr (mono (Nat.sub_le t 1)))
    (fun T i => (c T i).epoch) (fun T i => (c T i).recent) (fun T i => (c T i).hits)
    (fun T => (tr T).2.length)
    (fun T i => (snapshot_bounds hn pos fit mixed D seed F x qs completed T i).1)
    (fun T i => (snapshot_bounds hn pos fit mixed D seed F x qs completed T i).2.1)
    (fun T => by
      change (∑i, ((c T i).hits:ℝ))≤((tr T).2.length:ℝ)
      rw [←Nat.cast_sum]
      exact_mod_cast sum_hits hn pos fit mixed D seed F x qs completed T)
  have avg : mean (fun T => ((tr T).2.length:ℝ))≤mean (queryCost hn fit mixed D seed F x qs) :=
    div_le_div_of_nonneg_right (sum_le_sum fun T _ => common_cost hn pos fit mixed D seed F x qs completed T
      (Classical.choice (inferInstance : Nonempty (Candidate n β))) (halts T _)) (by positivity)
  rw [total_increment,show C 0=0 from cumulative_zero ..,sub_zero,show C n=_ from cumulative_toReal ..] at go
  change mean (fun T => mean (fun i => charge a b _ (β^i.val) (occupied β (i.val-1))
    (c T i).epoch (c T i).recent (c T i).reads (c T i).hits))≤_
  simp_rw [rc]
  exact go.trans (add_le_add_left (mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_right avg bp.le) (by norm_num)) _)

end
end AmortizedBound.ActualCharge

/-! ## Conclusions -/

/-! Reduction of both dynamic lower bounds, at every universe size, to
the physical finite chronogram experiment. -/
namespace AmortizedBound.Conclusions
open Dynamic Parameters Filter MeasureTheory Real DisjointnessDraft.PhysicalProtocol
open scoped Topology
noncomputable section

theorem fourth_root (N : ℕ) : hardSize N ^ 4 ≤ N ∧ N < (hardSize N + 1)^4 := by
  have s := Nat.sqrt_le' N
  have t := Nat.sqrt_le' N.sqrt
  have u := Nat.lt_succ_sqrt' N
  have v := Nat.lt_succ_sqrt' N.sqrt
  have up : N.sqrt+1 ≤ (hardSize N+1)^2 := v
  have lower := Nat.pow_le_pow_left t 2
  have upper := Nat.pow_le_pow_left up 2
  rw [←pow_mul] at lower upper
  exact ⟨lower.trans s,u.trans_le upper⟩

theorem fourth_logs {N : ℕ} (h : 2≤hardSize N) :
    logb 2 (hardSize N) ≤ logb 2 N ∧ logb 2 N ≤ 8*logb 2 (hardSize N) := by
  let n := hardSize N
  have n2 : 2≤n := h
  have np : (0:ℝ)<n := by exact_mod_cast (by omega : 0<n)
  have nN : n≤N := (Nat.sqrt_le_self _).trans (Nat.sqrt_le_self _)
  have Np : (0:ℝ)<N := by exact_mod_cast (by omega : 0<N)
  have cap : N ≤ n^8 := by
    have sq : n+1 ≤ n^2 := by nlinarith
    calc N ≤ (n+1)^4 := (fourth_root N).2.le
         _ ≤ (n^2)^4 := Nat.pow_le_pow_left sq 4
         _ = n^8 := by ring
  have cap' := logb_le_logb_of_le (b:=2) (by norm_num) Np (by exact_mod_cast cap : (N:ℝ)≤(n:ℝ)^8)
  rw [logb_pow] at cap'
  exact ⟨logb_le_logb_of_le (by norm_num) np (by exact_mod_cast nN),by simpa [n] using cap'⟩

/-- Pointwise numerical resources consumed by a physical chronogram. -/
structure Regime (n w : ℕ) (a b : ℝ) : Prop where
  nLarge : 2 ≤ n
  positive : 1 ≤ a ∧ 1 ≤ b
  dyadic : 2 ≤ base a w
  chosen : 0 < epochs n a w
  mass : (n:ℝ)^(-1/2:ℝ) ≤ (dyadicRate a w)^(cutoff b (epochs n a w))/64
  tail : ∀ i ∈ candidates (depth n (base a w)),
    let s : ℝ := (base a w:ℝ)^i
    let e := ⌊64*a*s⌋₊
    let p := dyadicRate a w
    exp (-(p*e)/3) ≤ p^(cutoff b (epochs n a w))*(2:ℝ)^(-√(n:ℝ))
  messages : ∀ i ∈ candidates (depth n (base a w)),
    let β := base a w
    let s := β^i
    let e := ⌊64*a*s⌋₊
    let l := ⌊64*a*occupied β (i-1)⌋₊
    let cap := ⌊2*dyadicRate a w*e⌋₊
    let h := sampleExponent a w
    let r := cutoff b (epochs n a w)
    ((adviceBits w e l+1:ℕ):ℝ)≤(n:ℝ)^(5/4:ℝ) ∧
    ((packetBits w l cap+h*r:ℕ):ℝ)≤(s:ℝ)/200 ∧
    (replyBits w ⌊32*b⌋₊:ℝ)≤(logb 2 n)^3

theorem eventual_regime {f : Filter ℕ} {w : ℕ→ℕ} {a b : ℕ→ℝ}
    (fast : Fast f a (fun n => (w n:ℝ)) b) : ∀ᶠ n : ℕ in f, Regime n (w n) (a n) (b n) := by
  have grow := (tendsto_rpow_atTop (by norm_num : (0:ℝ)<1/4)).comp tendsto_natCast_atTop_atTop
  filter_upwards [fast.positive,growing_product fast 2,good_count fast,relative_tail fast,encoded_budgets fast,
    normalizer fast (by norm_num : (0:ℝ)<1/4), (eventually_ge_atTop 2).filter_mono fast.large,
    (grow.eventually_ge_atTop 64).filter_mono fast.large] with n ab aw ct tail msg gamma n2 big
  have np : (0:ℝ)<n := by exact_mod_cast (by omega : 0<n)
  have lg : 0<logb 2 n := logb_pos (by norm_num) (by exact_mod_cast (by omega : 1<n))
  refine ⟨n2,ab,base_two aw,?_,?_,tail,msg⟩
  · by_contra! z
    have z0 : epochs n (a n) (w n)=0 := Nat.eq_zero_of_le_zero z
    rw [z0] at ct; simp at ct; linarith [ct.1]
  · apply (le_div_iff₀ (by norm_num : (0:ℝ)<64)).mpr
    refine le_trans ?_ gamma
    have p := mul_le_mul_of_nonneg_right big (rpow_nonneg np.le (-1/2:ℝ))
    change 64*(n:ℝ)^(-1/2:ℝ) ≤ (n:ℝ)^(1/4:ℝ)*(n:ℝ)^(-1/2:ℝ) at p
    rw [←rpow_add np] at p
    convert p using 1 <;> ring_nf

def Single (N w : ℕ) (a b : ℝ) : Prop := ∃ (Ω : Type) (_ : MeasurableSpace Ω)
    (μ : Measure Ω) (_ : IsProbabilityMeasure μ) (D : DataStructure N w Ω),
    Correct μ D (hardFamilies N) (singleHistories N) ∧ PrefixBudgets μ D a b

def Mixed (N w : ℕ) (a b : ℝ) : Prop := b=2*a ∧ ∃ (Ω : Type) (_ : MeasurableSpace Ω)
    (μ : Measure Ω) (_ : IsProbabilityMeasure μ) (D : DataStructure N w Ω),
    Correct μ D (hardFamilies N) legal ∧ interleavedWork μ D ≤ ENNReal.ofReal ((hardSize N:ℝ)*a)

/-- The finite operational interface. It forwards the costs and correctness
of the actual machine on the fixed hard experiment, at its own physical word
width and universe size. -/
def NoFastMachine : Prop := ∀ᶠ n : ℕ in atTop, ∀ (N w : ℕ) (a b : ℝ),
  hardSize N=n → Regime n w a b → (Single N w a b ∨ Mixed N w a b) → False

/-- Diagonalize counterexamples at arbitrary universe sizes and index the
resulting filter by *distinct* hard sizes. This preserves varying machines
and word widths even when multiple universes have the same fourth root. -/
private theorem diagonal (Bad : ℕ → ℝ → Prop)
    (freq : ∀ u : ℝ, 0<u → ∃ᶠ N : ℕ in atTop, Bad N u) :
    ∃ (f : Filter ℕ) (N : ℕ → ℕ) (δ : ℕ → ℝ),
      f.NeBot ∧ f ≤ atTop ∧ Tendsto N f atTop ∧ Tendsto δ f (𝓝 0) ∧
      ∀ᶠ n : ℕ in f, 0<δ n ∧ hardSize (N n)=n ∧ Bad (N n) (δ n) := by
  classical
  have each (j : ℕ) : ∃ N : ℕ, j^4 ≤ N ∧ Bad N (1/((j:ℝ)+1)) :=
    frequently_atTop.mp (freq _ (by positivity)) (j^4)
  choose raw hraw bad using each
  have hi (j : ℕ) : j≤hardSize (raw j) := by
    apply Nat.le_sqrt'.mpr
    apply Nat.le_sqrt'.mpr
    rw [←pow_mul]; exact hraw j
  obtain ⟨φ,hφ,hm⟩ := strictMono_subseq_of_id_le hi
  let m := (fun j => hardSize (raw j)) ∘ φ
  let index := Function.invFun m
  have left : ∀ j, index (m j)=j := Function.leftInverse_invFun hm.injective
  let N := fun n => raw (φ (index n))
  let δ := fun n => 1/((φ (index n):ℝ)+1)
  let f := Filter.map m atTop
  have top : Tendsto N f atTop := by
    rw [show f=Filter.map m atTop from rfl,tendsto_map'_iff]
    have le (j : ℕ) : m j ≤ (N ∘ m) j := by
      simp only [N,Function.comp_apply,left]; exact (Nat.sqrt_le_self _).trans (Nat.sqrt_le_self _)
    exact tendsto_atTop_mono le hm.tendsto_atTop
  refine ⟨f,N,δ,inferInstance,hm.tendsto_atTop,top,?_,?_⟩
  · rw [show f=Filter.map m atTop from rfl,tendsto_map'_iff]
    simpa [Function.comp_def,δ,left] using tendsto_one_div_add_atTop_nhds_zero_nat.comp hφ.tendsto_atTop
  · change ∀ᶠ j : ℕ in atTop, 0<δ (m j) ∧ hardSize (N (m j))=m j ∧ Bad (N (m j)) (δ (m j))
    exact Eventually.of_forall fun j => by simp only [δ,N,left]; exact ⟨by positivity,rfl,bad _⟩

private theorem chooseEventually {X : Type*} [Inhabited X] {f : Filter ℕ} {P : ℕ → X → Prop}
    (ex : ∀ᶠ n : ℕ in f, ∃ x, P n x) : ∃ x : ℕ → X, ∀ᶠ n : ℕ in f, P n (x n) := by
  classical
  let pick (n : ℕ) := if h : ∃ x, P n x then h.choose else default
  exact ⟨pick,ex.mono fun n ok => by simpa [pick,ok] using ok.choose_spec⟩

private theorem scale_word {f : Filter ℕ} {N W : ℕ→ℕ} {lo hi : ℝ}
    (large : f≤atTop) (lp : 0<lo) (hp : 0<hi)
    (root : ∀ᶠ n : ℕ in f, hardSize (N n)=n) (word : ∀ᶠ n : ℕ in f, wordSize lo hi (N n) (W n)) :
    ∃ c C : ℝ, 0<c ∧ 0<C ∧ ∀ᶠ n : ℕ in f,
      c*logb 2 n ≤ W n ∧ (W n:ℝ)≤C*logb 2 n := by
  refine ⟨lo,8*hi,lp,by positivity,?_⟩
  filter_upwards [root,word,(eventually_ge_atTop 2).filter_mono large] with n eq w n2
  have logs := fourth_logs (N:=N n) (by omega)
  rw [eq] at logs
  exact ⟨(mul_le_mul_of_nonneg_left logs.1 lp.le).trans w.1,w.2.trans
    ((mul_le_mul_of_nonneg_left logs.2 hp.le).trans_eq (by ring))⟩

private theorem scale_update {f : Filter ℕ} {N : ℕ→ℕ} {tu : ℕ→ℝ}
    (large : f≤atTop) (grows : Tendsto N f atTop) (sub : Subpolynomial tu)
    (root : ∀ᶠ n : ℕ in f, hardSize (N n)=n) (e : ℝ) (ep : 0<e) :
    ∀ᶠ n : ℕ in f, tu (N n) ≤ (n:ℝ)^e := by
  filter_upwards [grows.eventually (sub (e/8) (by positivity)),root,
    (eventually_ge_atTop 2).filter_mono large] with n aa root n2
  have upper := (fourth_root (N n)).2.le
  rw [root] at upper
  have ns : n+1≤n^2 := by nlinarith
  have cap : N n ≤ n^8 := upper.trans ((Nat.pow_le_pow_left ns 4).trans_eq (by ring))
  have nn : 0≤(n:ℝ) := Nat.cast_nonneg _
  calc _ ≤ ((N n):ℝ)^(e/8) := aa
       _ ≤ ((n:ℝ)^8)^(e/8) := Real.rpow_le_rpow (Nat.cast_nonneg _) (by exact_mod_cast cap) (by positivity)
       _ = _ := by rw [←Real.rpow_natCast_mul nn]; push_cast; congr 1; ring

theorem query_tradeoff (physical : NoFastMachine) : QueryTradeoff := by
  intro lo hi lp lh
  by_contra fails
  let Bad (N : ℕ) (u : ℝ) := ∃ z : (ℕ×ℝ)×ℝ, 1≤z.2 ∧ z.2≤(N:ℝ)^u ∧
    wordSize lo hi N z.1.1 ∧ 0≤z.1.2 ∧ Single N z.1.1 z.2 z.1.2 ∧ z.1.2 < u*ratio N z.1.1 z.2
  have freq (u : ℝ) (up : 0<u) : ∃ᶠ N : ℕ in atTop, Bad N u := by
    by_contra notBad
    apply fails
    refine ⟨u,up,fun tu unit sub => ?_⟩
    filter_upwards [not_frequently.mp notBad,unit,sub u up] with N good one cap
    intro w word tq tq0 Ω m μ prob D ok costs
    apply le_of_not_gt
    intro tooSmall
    exact good ⟨((w,tq),tu N),one,cap,word,tq0,⟨Ω,m,μ,prob,D,ok,costs⟩,tooSmall⟩
  obtain ⟨f,N,δ,proper,large,grows,tiny,base⟩ := diagonal Bad freq
  haveI : f.NeBot := proper
  obtain ⟨z,chosen⟩ := chooseEventually (base.mono fun n h => h.2.2)
  let W n := (z n).1.1
  let q n := (z n).1.2
  let a n := (z n).2
  have root := base.mono (fun n h => h.2.1)
  have words := scale_word (W:=W) large lp (lp.trans_le lh) root (chosen.mono fun n h => h.2.2.1)
  have update (e : ℝ) (ep : 0<e) : ∀ᶠ n : ℕ in f, a n ≤ (n:ℝ)^e := by
    filter_upwards [chosen,root,base.mono (fun n h => h.1),
      tiny.eventually (Iio_mem_nhds (show 0<e/8 by positivity)),
      (eventually_ge_atTop 2).filter_mono large] with n alg rt dpos dsmall n2
    have upper := (fourth_root (N n)).2.le
    rw [rt] at upper
    have ns : n+1≤n^2 := by nlinarith
    have cap : N n ≤ n^8 := upper.trans ((Nat.pow_le_pow_left ns 4).trans_eq (by ring))
    have n1 : (1:ℝ) ≤ n := by exact_mod_cast (by omega : 1≤n)
    have d8 : δ n < e/8 := dsmall
    calc a n ≤ ((N n):ℝ)^(δ n) := alg.2.1
      _ ≤ ((n:ℝ)^8)^(δ n) := Real.rpow_le_rpow (Nat.cast_nonneg _) (by exact_mod_cast cap) dpos.le
      _ = (n:ℝ)^((8:ℕ)*δ n) := (Real.rpow_natCast_mul (Nat.cast_nonneg _) 8 (δ n)).symm
      _ ≤ (n:ℝ)^e := Real.rpow_le_rpow_of_exponent_le n1 (by push_cast; linarith)
  have scale : PhysicalScale f a (fun n => (W n:ℝ)) :=
    ⟨large,chosen.mono fun n h => h.1,update,words⟩
  have small (ε : ℝ) (ep : 0<ε) : ∀ᶠ n : ℕ in f, q n≤ε*(logb 2 n/logb 2 (a n*(W n)))^2 := by
    filter_upwards [chosen,base,scale.growing 2, tiny.eventually (Iio_mem_nhds (show 0<ε/64 by positivity)),
      (eventually_ge_atTop 2).filter_mono large] with n alg zδ aw dsmall n2
    have logs := fourth_logs (N:=N n) (by omega)
    rw [zδ.2.1] at logs
    let den := logb 2 (a n*(W n))
    have dpos : 0<den := by have := logprod_ge aw; dsimp [den]; linarith
    have nn : 0 ≤ logb 2 n := logb_nonneg (by norm_num) (by exact_mod_cast (by omega : 1≤n))
    have Nn : 0≤logb 2 (N n) := nn.trans logs.1
    have rat : logb 2 (N n)/den ≤ 8*(logb 2 n/den) :=
      (div_le_div_of_nonneg_right logs.2 dpos.le).trans_eq (by ring)
    have sq := pow_le_pow_left₀ (div_nonneg Nn dpos.le) rat 2
    have coeff : δ n≤ε/64 := le_of_lt dsmall
    have u := mul_le_mul coeff sq (sq_nonneg _) (by positivity)
    have bad : q n<δ n*(logb 2 (N n)/den)^2 := alg.2.2.2.2.2
    exact bad.le.trans (u.trans_eq (by ring))
  have fast := fast_single scale small
  obtain ⟨n,spec,reg,rootN,algo⟩ := (physical.filter_mono large |>.and
    ((eventual_regime fast).and (root.and chosen))).exists
  apply spec (N n) (W n) (a n) (max 1 (q n)) rootN reg
  obtain ⟨Ω,m,μ,iμ,D,ok,costs⟩ := algo.2.2.2.2.1
  exact Or.inl ⟨Ω,m,μ,iμ,D,ok,costs.updates,fun F hf xs hx i =>
    (costs.query F hf xs hx i).trans (ENNReal.ofReal_le_ofReal (le_max_right ..))⟩

private theorem scaled_total {N n : ℕ} (root : hardSize N=n) (n2 : 2≤n) (log2n : 2≤logb 2 n) :
    totalScale N ≤ 64*(logb 2 n/logb 2 (logb 2 n))^2 := by
  have L := fourth_logs (N:=N) (by omega)
  rw [root] at L
  let x := logb 2 n
  let y := logb 2 N
  have x2 : 2≤x := log2n
  have xy : x≤y := L.1
  have lpos : 0<logb 2 x := logb_pos (by norm_num) (by linarith)
  have lm := logb_le_logb_of_le (b:=2) (by norm_num) (by linarith : 0<x) xy
  have rat : y/logb 2 y ≤ 8*(x/logb 2 x) :=
    calc y/logb 2 y ≤ y/logb 2 x := div_le_div_of_nonneg_left (by linarith) lpos lm
         _ ≤ (8*x)/logb 2 x := div_le_div_of_nonneg_right L.2 lpos.le
         _ = _ := by ring
  have sq := pow_le_pow_left₀ (div_nonneg (by linarith : 0≤y) (lpos.trans_le lm).le) rat 2
  change (y/logb 2 y)^2 ≤ 64*(x/logb 2 x)^2
  exact sq.trans_eq (by ring)

theorem total_work (physical : NoFastMachine) : TotalWorkBound := by
  intro lo hi lp lh
  by_contra fails
  let Bad (N : ℕ) (u : ℝ) := ∃ w : ℕ,
    wordSize lo hi N w ∧ ∃ (Ω : Type) (_ : MeasurableSpace Ω) (μ : Measure Ω)
      (_ : IsProbabilityMeasure μ) (D : DataStructure N w Ω), Correct μ D (hardFamilies N) legal ∧
        interleavedWork μ D < ENNReal.ofReal (u*hardSize N*totalScale N)
  have freq (u : ℝ) (up : 0<u) : ∃ᶠ N : ℕ in atTop, Bad N u := by
    by_contra noBad
    apply fails
    refine ⟨u,up,?_⟩
    filter_upwards [not_frequently.mp noBad] with N good
    intro w word Ω m μ prob D ok
    exact le_of_not_gt fun lt => good ⟨w,word,Ω,m,μ,prob,D,ok,lt⟩
  obtain ⟨f,N,δ,proper,large,grows,tiny,base⟩ := diagonal Bad freq
  haveI : f.NeBot := proper
  obtain ⟨W,chosen⟩ := chooseEventually (base.mono fun n h => h.2.2)
  let τ n := δ n*totalScale (N n)
  let a n := max 1 (τ n)
  have root := base.mono (fun n h => h.2.1)
  have words := scale_word (W:=W) large lp (lp.trans_le lh) root (chosen.mono fun n h => h.1)
  have small (ε : ℝ) (ep : 0<ε) : ∀ᶠ n : ℕ in f,
      τ n ≤ ε*(logb 2 n/logb 2 (logb 2 n))^2 := by
    filter_upwards [base, tiny.eventually (Iio_mem_nhds (show 0<ε/64 by positivity)),
      (eventually_ge_atTop 2).filter_mono large,
      (DisjointnessFoundations.Tradeoff.log_tends.eventually_ge_atTop 2).filter_mono large] with n op ds n2 L
    have sc := scaled_total op.2.1 n2 L
    have ds' : δ n≤ε/64 := le_of_lt ds
    have h := mul_le_mul ds' sc (show 0≤totalScale (N n) from sq_nonneg _) (by positivity)
    exact h.trans_eq (by ring)
  have fast := fast_total large words small
  obtain ⟨n,spec,reg,rootN,algo⟩ := (physical.filter_mono large |>.and
    ((eventual_regime fast).and (root.and chosen))).exists
  apply spec (N n) (W n) (a n) (2*a n) rootN reg
  obtain ⟨Ω,m,μ,iμ,D,ok,work⟩ := algo.2
  refine Or.inr ⟨rfl,Ω,m,μ,iμ,D,ok,work.le.trans (ENNReal.ofReal_le_ofReal ?_)⟩
  have le := mul_le_mul_of_nonneg_left (le_max_right 1 (τ n)) (Nat.cast_nonneg (α:=ℝ) (hardSize (N n)))
  dsimp [τ,a] at *
  nlinarith only [le]

end
end AmortizedBound.Conclusions

/-! ## HardLaw -/

namespace AmortizedBound.Dynamic.Epoch
open DisjointnessFoundations HardIndependence HardDistribution MeasureTheory Finset
open scoped ENNReal
open Classical
noncomputable section

variable {n s N w : ℕ} {Ω : Type} (e : Epoch n s)

instance : Fintype e.Out := by unfold Out; infer_instance
instance : MeasurableSpace e.Out := by unfold Out; infer_instance
instance : MeasurableSingletonClass e.Out := by unfold Out; infer_instance
instance [Nonempty (Fin n)] : Nonempty e.Out := by unfold Out; infer_instance

/-- Restricting an independent uniform row to this epoch is a uniform block. -/
theorem block_uniform [Nonempty (Fin n)] :
    (unif (Row n)).map (fun row => row ∘ e.index) = unif (Fin s → Fin n) := by
  have split := uniform_split (A:=Fin n) e.index
  change (unif (Row n)).map (Prod.fst ∘ (splitCoordinates (A:=Fin n) e.index)) = _
  rw [←Measure.map_map measurable_fst (measurable_of_finite _),split]
  simp

private theorem joint_mean {A B : Type} [Fintype A] [Fintype B] (f : A×B → ℝ) :
    mean f=mean (fun a => mean (fun b => f (a,b))) := mean_prod (fun a b => f (a,b))

theorem join_mean (f : Row n → ℝ) :
    mean (fun z : (Fin s → Fin n) × e.Out => f (e.join z.1 z.2))=mean f :=
  mean_equiv (splitCoordinates (A:=Fin n) e.index).symm f

/-- Condition on any row and average over the original product block law. -/
theorem yes_mass (hn : 2≤n) (row : Row n) :
    1/4 ≤ mean (fun z : (Fin s → Fin n) × e.Out => if ∀i,row i≠e.join z.1 z.2 i then 1 else 0) := by
  rw [e.join_mean (fun x => if ∀i,row i≠x i then 1 else 0)]
  have ev (x : Row n) : (∀i,row i≠x i) ↔ x∈avoiding row := by simp [avoiding_spec,ne_comm]
  simp_rw [ev]
  simpa [mean,Finset.sum_boole] using (disjoint_probability hn row).2

private theorem mono_mean {A : Type} [Fintype A] {f g : A→ℝ} (h : ∀a,f a≤g a) : mean f≤mean g :=
  div_le_div_of_nonneg_right (sum_le_sum fun a _ => h a) (by positivity)

theorem rare_mass (hn : 0<n) (row : Row n) :
    mean (fun z : (Fin s → Fin n) × e.Out =>
      if Communication.Game.overlaps (row ∘ e.index) z.1 then 1 else 0)≤(s:ℝ)/n := by
  letI : Nonempty (Fin n) := ⟨⟨0,hn⟩⟩
  rw [joint_mean]
  have cn (x : Fin s→Fin n) : mean (fun _o : e.Out => if Communication.Game.overlaps (row ∘ e.index) x then (1:ℝ) else 0) = _ := mean_const (α:=e.Out) _
  simp_rw [cn]
  let ind := fun (i : Fin s) (x : Fin s→Fin n) => if x i=row (e.index i) then (1:ℝ) else 0
  have up (x : Fin s→Fin n) : (if Communication.Game.overlaps (row ∘ e.index) x then (1:ℝ) else 0)≤∑i,ind i x := by
    split_ifs with h
    · obtain ⟨j,eq⟩ := h
      have h1 := single_le_sum (s:=univ) (f:=fun i => ind i x)
        (fun i _ => by dsimp [ind]; split_ifs <;> norm_num) (mem_univ j)
      simpa [ind,show x j=row (e.index j) from eq.symm] using h1
    · apply sum_nonneg; intro i _; dsimp [ind]; split_ifs <;> norm_num
  refine (mono_mean up).trans_eq ?_
  rw [mean_sum]
  have atom (i : Fin s) : mean (ind i)=1/n := by
    change mean (fun x : Fin s→Fin n => (fun y => if y=row (e.index i) then (1:ℝ) else 0) (x i))=_
    rw [mean_eval (β:=fun _ : Fin s => Fin n) i (fun y => if y=row (e.index i) then (1:ℝ) else 0)]
    simp [mean]
  simp [atom,div_eq_mul_inv]

variable (fit : n*n≤N) (mixed : Bool) (qs : Fin n→Fin N) (D : DataStructure N w Ω) (seed : Ω)

/-- The physical replay yields the actual fixed-history answer on every hard
input, with the replay length bounded by that query's actual probe cost. -/
theorem snapshot_truth (halts : e.SeedHalts fit mixed qs D seed) :
    ∃ k, ∀ (F : Fin N→Row n) (x : Fin s→Fin n) (o : e.Out) (q : Fin N),
      let S := e.snapshot fit mixed qs D seed k
      let past := e.past fit mixed qs x o
      let rows := fun j => rowSet fit (F j)
      (S.truth F x o q).1=lastReport D seed rows (past++[.inr q]) ∧
        ((S.truth F x o q).2.length:ℝ≥0∞)≤nextCost D seed rows past q := by
  obtain ⟨k,all⟩ := e.snapshot_query fit mixed qs D seed halts
  refine ⟨k,?_⟩; intro F x o q
  let S := e.snapshot fit mixed qs D seed k
  have realRun := all F x o q
  obtain ⟨ret,len⟩ := Simulation.Physical.replay_correct (S.actual F x o) (S.query q) (fun _ => none)
  have id : Simulation.Physical.overlay (S.actual F x o) (fun _ => none)=S.actual F x o := rfl
  rw [id] at ret len
  exact ⟨ret.trans realRun.1.symm,realRun.2.symm ▸ (by exact_mod_cast len)⟩

/-- Any accepted collision in the block is a genuine error on the selected
query in its original history, including all preceding operations. -/
theorem genuine_error (k E L cap fuel h r : ℕ) (F : Fin N→Row n) (x : Fin s→Fin n) (o : e.Out) (q : Fin N)
    (coins : Protocol.Coins w h r)
    (correctReplay : ((e.snapshot fit mixed qs D seed k).truth F x o q).1 =
      lastReport D seed (fun j => rowSet fit (F j)) (e.past fit mixed qs x o++[.inr q]))
    (accepted : ((e.snapshot fit mixed qs D seed k).game E L cap fuel h r).accepted q (F,x,o,coins)=true)
    (collision : Communication.Game.overlaps ((F q) ∘ e.index) x) :
    lastReport D seed (fun j => rowSet fit (F j)) (e.past fit mixed qs x o++[.inr q]) ≠
      some (answer (fun j => rowSet fit (F j)) (e.past fit mixed qs x o) q) := by
  let S := e.snapshot fit mixed qs D seed k
  obtain ⟨yes,out,j,eq⟩ := S.accepted_collision E L cap fuel h r F x o q coins accepted collision
  have fails : ¬∀i, F q i≠e.join x o i := fun good => good (e.index j) (eq.trans (e.join_inside x o j).symm)
  have filter := e.filtered_answer fit mixed qs F x o q
  change e.outsideOK (F q) o=true at out
  rw [out, Bool.and_true, decide_eq_false fails] at filter
  rw [←correctReplay,yes,filter]; decide

end
end AmortizedBound.Dynamic.Epoch

/-! ## FixedQuality -/

namespace AmortizedBound
open MeasureTheory DisjointnessDraft.PhysicalProtocol DisjointnessFoundations
open DisjointnessFoundations.FiniteSampling DisjointnessFoundations.HardDistribution
open Real Finset Classical
noncomputable section

namespace Protocol.Snapshot
variable {m n s w : ℕ} {W O : Type} (S : Protocol.Snapshot m n s w W O)

/-- Each summand is charged at its individual mean-cost scale. -/
def load (a b : ℝ) (later k : ℕ) (F : Protocol.Rows m W) (x : Protocol.Block n s) (o : O) (q : Fin m) :=
  let log := (S.truth F x o q).2
  let d := (Simulation.Physical.needed (S.early F x o) log).card
  S.epochCost F x o/(2*a*s) + S.laterCost F x o/(2*a*later) + log.length/b + d/(b/k)

theorem load_good {a b : ℝ} {later k : ℕ} (ap : 0<a) (bp : 0<b) (sp : 0<s) (lp : 0<later) (kp : 0<k)
    (F : Protocol.Rows m W) (x : Protocol.Block n s) (o : O) (q : Fin m)
    (small : S.load a b later k F x o q ≤ 32) :
    S.bounded ⌊64*a*s⌋₊ ⌊64*a*later⌋₊ F x o ∧ (S.truth F x o q).2.length≤⌊32*b⌋₊ ∧
    (Simulation.Physical.needed (S.early F x o) (S.truth F x o q).2).card≤Parameters.cutoff b k := by
  let c := S.epochCost F x o
  let l := S.laterCost F x o
  let u := (S.truth F x o q).2.length
  let d := (Simulation.Physical.needed (S.early F x o) (S.truth F x o q).2).card
  have z1 : 0≤(c:ℝ)/(2*a*s) := by positivity
  have z2 : 0≤(l:ℝ)/(2*a*later) := by positivity
  have z3 : 0≤(u:ℝ)/b := by positivity
  have z4 : 0≤(d:ℝ)/(b/k) := by positivity
  change (c:ℝ)/(2*a*s)+l/(2*a*later)+u/b+d/(b/k)≤32 at small
  have c1 := (div_le_iff₀ (show 0<2*a*s by positivity)).mp (show (c:ℝ)/(2*a*s)≤32 by linarith)
  have l1 := (div_le_iff₀ (show 0<2*a*later by positivity)).mp (show (l:ℝ)/(2*a*later)≤32 by linarith)
  have u1 := (div_le_iff₀ bp).mp (show (u:ℝ)/b≤32 by linarith)
  have d1 := (div_le_iff₀ (show 0<b/k by positivity)).mp (show (d:ℝ)/(b/k)≤32 by linarith)
  refine ⟨⟨Nat.le_floor (by linarith only [c1]),Nat.le_floor (by linarith only [l1])⟩,Nat.le_floor u1,?_⟩
  change d ≤ ⌈32*b/k⌉₊
  have d2 : (d:ℝ)≤32*b/k := by simpa [mul_div_assoc] using d1
  exact_mod_cast d2.trans (Nat.le_ceil _)

theorem private_nonneg (rate : SamplingRate) (E L fuel h r : ℕ)
    (F : Protocol.Rows m W) (x : Protocol.Block n s) (o : O) (q : Fin m) :
    0≤S.privateYes rate E L fuel h r F x o q := by
  unfold privateYes
  rw [←Simulation.prob_private]
  exact ENNReal.toReal_nonneg

/-- A linear form of the four abort tests. It can be averaged on the
unaltered input and tape distributions, although the individual tests are
correlated with the truth value. -/
theorem linear_accept (rate : SamplingRate) {a b : ℝ} {later k h : ℕ}
    (dyadic : rate.p=(1/2:ℝ)^h) (ap : 0<a) (bp : 0<b) (sp : 0<s) (lp : 0<later) (kp : 0<k)
    (F : Protocol.Rows m W) (x : Protocol.Block n s) (o : O) (q : Fin m)
    (yes wrong : Prop) [Decidable yes] [Decidable wrong]
    (usable : yes → ¬wrong → S.outsideDisjoint (F q) o=true ∧ (S.truth F x o q).1=some true)
    (tail : exp (-(rate.p*⌊64*a*s⌋₊)/3) ≤ rate.p^(Parameters.cutoff b k)/4) :
    (3/4:ℝ)*rate.p^(Parameters.cutoff b k)*
      ((if yes then 1 else 0)-(if wrong then 1 else 0)-S.load a b later k F x o q/32) ≤
      S.privateYes rate ⌊64*a*s⌋₊ ⌊64*a*later⌋₊ ⌊32*b⌋₊ h (Parameters.cutoff b k) F x o q := by
  let c := S.load a b later k F x o q
  let γ := rate.p^(Parameters.cutoff b k)
  have gp : 0≤γ := pow_nonneg rate.positive.le _
  have cn : 0≤c := by dsimp [c,load]; positivity
  have pp := S.private_nonneg rate ⌊64*a*s⌋₊ ⌊64*a*later⌋₊ ⌊32*b⌋₊ h (Parameters.cutoff b k) F x o q
  change (3/4:ℝ)*γ*((if yes then 1 else 0)-(if wrong then 1 else 0)-c/32) ≤ _
  by_cases go : yes ∧ ¬wrong ∧ c≤32
  · obtain ⟨hy,hw,hc⟩ := go
    obtain ⟨bound,len,hit⟩ := S.load_good ap bp sp lp kp F x o q hc
    obtain ⟨out,rep⟩ := usable hy hw
    have lower := S.private_lower rate _ _ ⌊32*b⌋₊ h _ dyadic F x o q ⟨bound,out,rep,len,hit⟩
    have pos : 0≤3/4*γ := by positivity
    simp only [if_pos hy,if_neg hw,sub_zero]
    calc 3/4*γ*(1-c/32) ≤ 3/4*γ*1 := mul_le_mul_of_nonneg_left (by linarith) pos
         _ ≤ _ := by change γ-_≤_ at lower; change _≤γ/4 at tail; linarith only [lower,tail]
  · have lhs : (if yes then (1:ℝ) else 0)-(if wrong then 1 else 0)-c/32≤0 := by
      by_cases hy : yes <;> by_cases hw : wrong <;> simp_all <;> linarith
    exact (mul_nonpos_of_nonneg_of_nonpos (by positivity) lhs).trans pp

end Protocol.Snapshot
end
end AmortizedBound

/-! ## GameBound -/

namespace AmortizedBound.GameBound
open Conclusions Parameters MeasureTheory DisjointnessFoundations.HardIndependence
open DisjointnessFoundations.FiniteSampling Simulation.Physical Simulation Filter Real
open Classical
noncomputable section

def rate (a : ℝ) (w : ℕ) : SamplingRate where
  p := dyadicRate a w
  positive := by unfold dyadicRate; positivity
  le_one := pow_le_one₀ (by norm_num) (by norm_num)

variable {N n s w : ℕ} {W O : Type}
variable [Fintype W] [MeasurableSpace W] [MeasurableSingletonClass W]
  [Fintype O] [MeasurableSpace O] [MeasurableSingletonClass O] [Nonempty O]

/-- Both inequalities pertain to one and the same protocol with the original
uniform inputs, independent sample mask, and independent fair padding. -/
def Good (S : Protocol.Snapshot N n s w W O) (a b : ℝ) (later : ℕ) :=
  let p := rate a w
  let h := sampleExponent a w
  let r := cutoff b (epochs n a w)
  let early := ⌊64*a*s⌋₊
  let G := S.game early ⌊64*a*later⌋₊ ⌊2*p.p*early⌋₊ ⌊32*b⌋₊ h r
  let ν := privateLaw p (2^w) (h*r)
  let ρ := Communication.acceptance G (unif O) ν
  p.p^r/32≤ρ ∧ G.jointError (unif O) ν/ρ≤(s:ℝ)/(64*n)

theorem excludes :
    ∀ᶠ n : ℕ in atTop, ∀ (N w : ℕ) (a b : ℝ) (i : ℕ), n^4≤N →
    Regime n w a b → i∈candidates (depth n (base a w)) →
    ∀ (W O : Type) [Fintype W] [MeasurableSpace W] [MeasurableSingletonClass W] [Nonempty W]
      [Fintype O] [MeasurableSpace O] [MeasurableSingletonClass O] [Nonempty O]
      (S : Protocol.Snapshot N n ((base a w)^i) w W O),
      (unif W).map S.block=unif (Protocol.Block n ((base a w)^i)) →
      ¬Good S a b (occupied (base a w) (i-1)) := by
  filter_upwards [Protocol.Snapshot.fixed_snapshot] with n fixed
  intro N w a b i card reg chosen W O _ _ _ _ _ _ _ _ S balanced good
  let β := base a w
  let p := rate a w
  let h := sampleExponent a w
  let r := cutoff b (epochs n a w)
  let s := β^i
  let later := occupied β (i-1)
  let E := ⌊64*a*s⌋₊
  let L := ⌊64*a*later⌋₊
  let cap := ⌊2*p.p*E⌋₊
  let G := S.game E L cap ⌊32*b⌋₊ h r
  let ν := privateLaw p (2^w) (h*r)
  let ρ := Communication.acceptance G (unif O) ν
  change p.p^r/32≤ρ ∧ G.jointError (unif O) ν/ρ≤(s:ℝ)/(64*n) at good
  have up := (candidate_bounds reg.dyadic chosen).2.1
  have lo : (n:ℝ)^(2/3:ℝ)/3≤s := by simpa [s,β,Nat.cast_pow] using candidate_size reg.dyadic chosen
  obtain ⟨adv,pkt,rep⟩ := reg.messages i chosen
  have gm := reg.mass
  have hp : 0≤p.p^r := pow_nonneg p.positive.le _
  change (n:ℝ)^(-1/2:ℝ)≤p.p^r/64 at gm
  apply (not_lt_of_ge good.2)
  apply fixed N s w E L ⌊32*b⌋₊ h r W O S p lo (by dsimp [s,β]; omega) card balanced adv pkt rep
  linarith only [gm,hp,good.1]

end
end AmortizedBound.GameBound

/-! ## Reindex -/

namespace AmortizedBound.Dynamic.Epoch
open DisjointnessFoundations HardDistribution Finset Classical
noncomputable section
variable {n s N w : ℕ} {Ω : Type} (e : Epoch n s)

private theorem rounds_other (fit : n*n≤N) (mixed : Bool) (x : Row n) (qs qs' : Fin n→Fin N)
    (ts : List (Fin n)) (agree : ∀j ∈ ts,qs j=qs' j) :
    rounds fit mixed x qs ts=rounds fit mixed x qs' ts := by
  unfold rounds
  induction ts with
  | nil => rfl
  | cons t ts ih => simp [agree t (by simp),ih (fun j hj => agree j (by simp [hj]))]

theorem snapshot_other (fit : n*n≤N) (mixed : Bool) (qs qs' : Fin n→Fin N)
    (D : DataStructure N w Ω) (seed : Ω) (fuel : ℕ) (agree : ∀j,j≠e.selected → qs j=qs' j) :
    e.snapshot fit mixed qs D seed fuel=e.snapshot fit mixed qs' D seed fuel := by
  have before (t : Fin n) (ht : t∈e.before++e.middle++e.after) : t≠e.selected := by
    rw [e.parts,List.mem_take_iff_getElem] at ht
    obtain ⟨k,lt,eq⟩ := ht
    have val := congrArg Fin.val eq
    simp at val
    intro he; subst t; omega
  have old : e.oldOps fit mixed qs=e.oldOps fit mixed qs' := by
    funext o; apply rounds_other; intro j hj; exact agree j (before j (by simp [hj]))
  have mid : e.epochOps fit mixed qs=e.epochOps fit mixed qs' := by
    funext x o; apply rounds_other; intro j hj; exact agree j (before j (by simp [hj]))
  have tail : e.recentOps fit mixed qs=e.recentOps fit mixed qs' := by
    funext x o; unfold recentOps; congr 1
    apply rounds_other; intro j hj; exact agree j (before j (by simp [hj]))
  have ew : e.epochWrites fit mixed qs D seed=e.epochWrites fit mixed qs' D seed := by
    funext F x o; simp only [epochWrites,preState,old,mid]
  have lw : e.recentWrites fit mixed qs D seed=e.recentWrites fit mixed qs' D seed := by
    funext F x o; simp only [recentWrites,midState,preState,old,mid,tail]
  simp only [snapshot,ew,lw,preState,midState,lastState,old,mid,tail]

theorem swap_mean {A B : Type*} [Fintype A] [Fintype B] (g : A→B→ℝ) :
    mean (fun x=>mean (g x))=mean (fun y=>mean (fun x=>g x y)) := by
  simp only [mean,←Finset.sum_div,div_div]; rw [Finset.sum_comm,mul_comm]

private theorem mean_pair' {A B : Type*} [Fintype A] [Fintype B] (f : A×B→ℝ) :
    mean f=mean (fun a=>mean (fun b=>f (a,b))) := mean_prod (fun a b=>f (a,b))

private theorem mean_replace {Q : Type} [Fintype Q] [Nonempty Q] (t : Fin n)
    (g : (Fin n→Q)→Q→ℝ) (other : ∀qs qs' q,(∀j,j≠t→qs j=qs' j)→g qs q=g qs' q) :
    mean (fun qs => mean (g qs)) = mean (fun qs => g qs (qs t)) := by
  let eqv := Equiv.piSplitAt t (fun _ : Fin n => Q)
  have split (f : (Fin n→Q)→ℝ) : mean f=mean (fun pair => f (eqv.symm pair)) := (mean_equiv eqv.symm f).symm
  rw [split (fun qs => mean (g qs)),split (fun qs => g qs (qs t)),mean_pair',mean_pair']
  have at_t (a : Q) (o) : eqv.symm (a,o) t=a := by
    exact congrArg Prod.fst (eqv.apply_symm_apply (a,o))
  have off (a b : Q) (o) (q : Q) : g (eqv.symm (a,o)) q=g (eqv.symm (b,o)) q := by
    apply other
    intro j hj
    exact (congrFun (congrArg Prod.snd (eqv.apply_symm_apply (a,o))) ⟨j,hj⟩).trans
      (congrFun (congrArg Prod.snd (eqv.apply_symm_apply (b,o))) ⟨j,hj⟩).symm
  let a₀ : Q := Classical.choice inferInstance
  have same (a : Q) (o) (q : Q) := off a a₀ o q
  simp_rw [at_t]
  have fn (a : Q) (o) : g (eqv.symm (a,o))=g (eqv.symm (a₀,o)) := funext fun q=>same a o q
  calc _ = mean (fun _a : Q => mean (fun o => mean (g (eqv.symm (a₀,o))))) :=
         congrArg mean (funext fun a => congrArg mean (funext fun o => congrArg mean (fn a o)))
       _ = _ := mean_const _
       _ = _ := swap_mean (fun o q => g (eqv.symm (a₀,o)) q)
       _ = _ := by congr 1; funext a; congr 1; funext o; exact (same a o a).symm

/-- Retain all hard-input randomness when the selected query is freshly
sampled after the other public query indices are fixed. -/
theorem reindex (hn : 0<N)
    (g : (Fin n→Fin N)→Fin N→(Fin N→Row n)→(Fin s→Fin n)→e.Out→ℝ)
    (other : ∀qs qs' q F x o,(∀j,j≠e.selected→qs j=qs' j)→g qs q F x o=g qs' q F x o) :
    mean (fun qs => mean (fun v : Protocol.Snapshot.Input N n s (Row n) e.Out =>
      g qs v.1 v.2.1 v.2.2.1 v.2.2.2)) =
    mean (fun z : Input n N => let p := splitCoordinates e.index z.2.1
      g z.2.2 (z.2.2 e.selected) z.1 p.1 p.2) := by
  letI : Nonempty (Fin N) := ⟨⟨0,hn⟩⟩
  have inner (qs q F) : mean (fun p : (Fin s→Fin n)×e.Out => g qs q F p.1 p.2)=
      mean (fun x : Row n => let p:=splitCoordinates e.index x; g qs q F p.1 p.2) :=
    (mean_equiv (splitCoordinates (A:=Fin n) e.index) _).symm
  rw [mean_pair' (fun z : Input n N => _)]
  simp_rw [mean_pair' (fun v : Protocol.Snapshot.Input N n s (Row n) e.Out => _)]
  simp_rw [mean_pair' (fun v : (Fin N→Row n)×((Fin s→Fin n)×e.Out) => _),inner]
  simp_rw [mean_pair' (fun v : Row n×(Fin n→Fin N) => _)]
  let G := fun qs q F (x : Row n) => g qs q F ((splitCoordinates e.index) x).1 ((splitCoordinates e.index) x).2
  have step1 (qs) : mean (fun q=>mean (fun F=>mean (G qs q F))) =
      mean (fun F=>mean (fun x=>mean (fun q=>G qs q F x))) := by
    rw [swap_mean (fun q F=>mean (G qs q F))]
    exact congrArg mean (funext fun F=>swap_mean (fun q x=>G qs q F x))
  have step2 (F) : mean (fun qs=>mean (fun x=>mean (fun q=>G qs q F x))) =
      mean (fun x=>mean (fun qs=>G qs (qs e.selected) F x)) := by
    rw [swap_mean (fun qs x=>mean (fun q=>G qs q F x))]
    exact congrArg mean (funext fun x=>mean_replace e.selected (fun qs q=>G qs q F x)
      (fun qs qs' q h=>other qs qs' q _ _ _ h))
  calc _ = mean (fun qs=>mean (fun F=>mean (fun x=>mean (fun q=>G qs q F x)))) :=
         congrArg mean (funext step1)
       _ = mean (fun F=>mean (fun qs=>mean (fun x=>mean (fun q=>G qs q F x)))) :=
         swap_mean (fun qs F=>mean (fun x=>mean (fun q=>G qs q F x)))
       _ = _ := congrArg mean (funext step2)

end
end AmortizedBound.Dynamic.Epoch

/-! ## PublicTapes -/

/-! Countable public randomness for a finite collection of dynamic histories.
Only costs and reported answers require measurability in the original tape space.
A representative with the same observations carries the original physical traces. -/
namespace AmortizedBound.PublicTapes
open MeasureTheory Filter Dynamic
open scoped ENNReal
noncomputable section
open Classical

variable {Ω K : Type} [MeasurableSpace Ω] [MeasurableSpace K]
    [Countable K] [MeasurableSingletonClass K]
variable (μ : Measure Ω) [IsProbabilityMeasure μ]
variable (profile : Ω → K) (good : Ω → Prop) (hg : ∀ᵐ a ∂μ, good a)

/-- Representatives are good for every profile, including profiles of zero mass. -/
def rep (k : K) : Ω :=
  if h : ∃ a, good a ∧ profile a = k then Classical.choose h else hg.exists.choose

omit [MeasurableSpace K] [Countable K] [MeasurableSingletonClass K] in
theorem rep_good (k : K) : good (rep μ profile good hg k) := by
  unfold rep
  split <;> rename_i h
  · exact h.choose_spec.1
  · exact hg.exists.choose_spec

omit [MeasurableSpace K] [Countable K] [MeasurableSingletonClass K] in
theorem rep_profile {a : Ω} (ha : good a) :
    profile (rep μ profile good hg (profile a)) = profile a := by
  have h : ∃ a', good a' ∧ profile a' = profile a := ⟨a, ha, rfl⟩
  rw [rep, dif_pos h]
  exact h.choose_spec.2

omit [Countable K] [MeasurableSingletonClass K] in
theorem map_probability (hm : Measurable profile) : IsProbabilityMeasure (μ.map profile) :=
  MeasureTheory.isProbabilityMeasure_map hm.aemeasurable

/-- Every nonnegative quantity determined by the observations has the same
expectation on countably many good, original tapes. -/
theorem lintegral_rep (hm : Measurable profile) (f : Ω → ℝ≥0∞)
    (determined : ∀ a b, profile a = profile b → f a = f b) :
    (∫⁻ k, f (rep μ profile good hg k) ∂μ.map profile) = ∫⁻ a, f a ∂μ := by
  rw [lintegral_map (measurable_of_countable _) hm]
  apply lintegral_congr_ae
  filter_upwards [hg] with a ha
  exact determined _ _ (rep_profile μ profile good hg ha)

/-- The law of any event determined by the observations is preserved. -/
theorem measure_rep (hm : Measurable profile) (p : Ω → Prop)
    (determined : ∀ a b, profile a = profile b → (p a ↔ p b)) :
    (μ.map profile) {k | p (rep μ profile good hg k)} = μ {a | p a} := by
  rw [Measure.map_apply hm (Set.to_countable _).measurableSet]
  apply measure_congr
  filter_upwards [hg] with a ha
  exact propext (determined _ _ (rep_profile μ profile good hg ha))

/-- A valid run cost has a countable code, with zero reserved for failure. -/
private def costValue : ℕ → ℝ≥0∞
  | 0 => ⊤
  | k+1 => k

private theorem costValue_inj : Function.Injective costValue := by
  intro i j h
  cases i <;> cases j <;> simp_all [costValue]

private theorem measurableCostCode {c : Ω → ℕ} {v : Ω → ℝ≥0∞}
    (hv : Measurable v) (hc : ∀ a, costValue (c a) = v a) : Measurable c := by
  apply measurable_to_countable'
  intro k
  convert hv (measurableSet_singleton (costValue k)) using 1
  ext a
  change c a = k ↔ v a = costValue k
  rw [← hc a, costValue_inj.eq_iff]

private def totalCode (D : DataStructure N w Ω) (a : Ω) (f : Family N) (h : List (Op N)) :=
  ((history D a f h).map (fun v => v.probes+1)).getD 0

omit [MeasurableSpace Ω] in
private theorem totalValue (D : DataStructure N w Ω) (a : Ω) (f : Family N) (h : List (Op N)) :
    costValue (totalCode D a f h) = totalCost D a f h := by
  cases he : history D a f h <;> simp [he,totalCode,totalCost,costValue]

private def queryCode (D : DataStructure N w Ω) (a : Ω) (f : Family N) (h : List (Op N)) (q : Fin N) :=
  ((history D a f h).bind (fun v => (operation D a h.length (.inr q) v.memory).map
    (fun r => r.trace.length+1))).getD 0

omit [MeasurableSpace Ω] in
private theorem queryValue (D : DataStructure N w Ω) (a : Ω) (f : Family N) (h : List (Op N)) (q : Fin N) :
    costValue (queryCode D a f h q) = nextCost D a f h q := by
  cases he : history D a f h with
  | none => simp [he,queryCode,nextCost,costValue]
  | some v => cases ho : operation D a h.length (.inr q) v.memory <;>
                simp [he,ho,queryCode,nextCost,costValue]

private theorem measurableFlag {p : Ω → Prop} [DecidablePred p] (h : MeasurableSet {a | p a}) :
    Measurable (fun a => decide (p a)) := by
  apply measurable_to_countable'
  intro b
  cases b
  · convert h.compl using 1
    ext a
    simp
  · convert h using 1
    ext a
    simp

/-- `I` indexes total-prefix costs and `J` indexes queries after a prefix. -/
structure Tests (N : ℕ) (I J : Type) where
  family : I → Family N
  ops : I → List (Op N)
  queryFamily : J → Family N
  prefixOps : J → List (Op N)
  query : J → Fin N

abbrev Profile (I J : Type) := (I → ℕ) × (J → ℕ × (Bool → Bool))

variable {I J : Type} [Fintype I] [Fintype J]
variable (T : Tests N I J) (D : DataStructure N w Ω)

def observations (a : Ω) : Profile I J :=
  (fun i => totalCode D a (T.family i) (T.ops i), fun j =>
    (queryCode D a (T.queryFamily j) (T.prefixOps j) (T.query j), fun b =>
      decide (lastReport D a (T.queryFamily j) (T.prefixOps j ++ [.inr (T.query j)]) = some b)))

variable {families : Family N → Prop} {histories : List (Op N) → Prop}

structure Valid (T : Tests N I J) (families : Family N → Prop) (histories : List (Op N) → Prop) : Prop where
  family : ∀ i, families (T.family i)
  ops : ∀ i, histories (T.ops i)
  queryFamily : ∀ j, families (T.queryFamily j)
  queryHistory : ∀ j, histories (T.prefixOps j ++ [.inr (T.query j)])

omit [IsProbabilityMeasure μ] [Fintype I] [Fintype J] in
theorem measurable_observations (C : Correct μ D families histories) (V : Valid T families histories) :
    Measurable (observations T D) := by
  apply Measurable.prodMk
  · apply measurable_pi_lambda
    intro i
    exact measurableCostCode (C.measurableCost _ (V.family i) _ (V.ops i)) (fun a => totalValue D a _ _)
  · apply measurable_pi_lambda
    intro j
    apply Measurable.prodMk
    · exact measurableCostCode (C.measurableQuery _ (V.queryFamily j) _ _ (V.queryHistory j))
        (fun a => queryValue D a _ _ _)
    · apply measurable_pi_lambda
      intro b
      exact measurableFlag (C.measurableReport _ (V.queryFamily j) _ _ b (V.queryHistory j))

omit [MeasurableSpace Ω] [Fintype I] [Fintype J] in
theorem same_total {a b : Ω} (h : observations T D a = observations T D b) (i : I) :
    totalCost D a (T.family i) (T.ops i) = totalCost D b (T.family i) (T.ops i) := by
  simpa only [observations,totalValue] using congrArg (fun k : Profile I J => costValue (k.1 i)) h

omit [MeasurableSpace Ω] [Fintype I] [Fintype J] in
theorem same_query {a b : Ω} (h : observations T D a = observations T D b) (j : J) :
    nextCost D a (T.queryFamily j) (T.prefixOps j) (T.query j) =
      nextCost D b (T.queryFamily j) (T.prefixOps j) (T.query j) := by
  exact (queryValue D a _ _ _).symm.trans ((congrArg (fun k : Profile I J => costValue (k.2 j).1) h).trans
    (queryValue D b _ _ _))

omit [MeasurableSpace Ω] [Fintype I] [Fintype J] in
theorem same_report {a b : Ω} (h : observations T D a = observations T D b) (j : J) :
    lastReport D a (T.queryFamily j) (T.prefixOps j ++ [.inr (T.query j)]) =
      lastReport D b (T.queryFamily j) (T.prefixOps j ++ [.inr (T.query j)]) := by
  have E (r : Bool) := congrArg (fun k : Profile I J => (k.2 j).2 r) h
  change ∀ r : Bool, decide (_ = some r) = decide (_ = some r) at E
  cases e₁ : lastReport D a (T.queryFamily j) (T.prefixOps j ++ [.inr (T.query j)]) <;>
    cases e₂ : lastReport D b (T.queryFamily j) (T.prefixOps j ++ [.inr (T.query j)]) <;>
    simp_all

omit [IsProbabilityMeasure μ] in
theorem simultaneous_termination (C : Correct μ D families histories) (V : Valid T families histories) :
    ∀ᵐ a ∂μ, (∀ i, (history D a (T.family i) (T.ops i)).isSome) ∧
      ∀ j, (history D a (T.queryFamily j) (T.prefixOps j ++ [.inr (T.query j)])).isSome := by
  apply Filter.Eventually.and
  · exact ae_all_iff.mpr fun i => C.terminates _ (V.family i) _ (V.ops i)
  · exact ae_all_iff.mpr fun j => C.terminates _ (V.queryFamily j) _ (V.queryHistory j)

/-- A single original tape terminates on all allowed histories. Families are
finite and the set of finite histories is countable. -/
def Halts (D : DataStructure N w Ω) (families : Family N → Prop)
    (histories : List (Op N) → Prop) (a : Ω) :=
  ∀ f, families f → ∀ h, histories h → (history D a f h).isSome

omit [IsProbabilityMeasure μ] in
theorem halts_ae (C : Correct μ D families histories) :
    ∀ᵐ a ∂μ, Halts D families histories a := by
  apply ae_all_iff.mpr
  intro f
  by_cases hf : families f
  · have h : ∀ᵐ a ∂μ, ∀ ops, histories ops → (history D a f ops).isSome := by
      apply ae_all_iff.mpr
      intro ops
      by_cases hh : histories ops
      · filter_upwards [C.terminates f hf ops hh] with a ha
        exact fun _ => ha
      · exact ae_of_all _ fun _ h => (hh h).elim
    exact h.mono fun _ ha _ => ha
  · exact ae_of_all _ fun _ h => (hf h).elim

/-- A code describes an original, simultaneously terminating tape. -/
def representative (C : Correct μ D families histories) (k : Profile I J) : Ω :=
  rep μ (observations T D) (Halts D families histories) (halts_ae μ D C) k

omit [Fintype I] [Fintype J] in
theorem representative_halts (C : Correct μ D families histories) (k : Profile I J) :
    Halts D families histories (representative μ T D C k) :=
  rep_good μ _ _ _ _

def law : Measure (Profile I J) := μ.map (observations T D)

omit [Fintype I] [Fintype J] in
theorem law_probability (C : Correct μ D families histories) (V : Valid T families histories) :
    IsProbabilityMeasure (law μ T D) :=
  map_probability μ _ (measurable_observations μ T D C V)

theorem expected_total (C : Correct μ D families histories) (V : Valid T families histories) (i : I) :
    (∫⁻ k, totalCost D (representative μ T D C k) (T.family i) (T.ops i) ∂law μ T D) =
      ∫⁻ a, totalCost D a (T.family i) (T.ops i) ∂μ :=
  lintegral_rep μ _ _ _ (measurable_observations μ T D C V) _ (fun _ _ h => same_total T D h i)

theorem expected_query (C : Correct μ D families histories) (V : Valid T families histories) (j : J) :
    (∫⁻ k, nextCost D (representative μ T D C k) (T.queryFamily j) (T.prefixOps j) (T.query j) ∂law μ T D) =
      ∫⁻ a, nextCost D a (T.queryFamily j) (T.prefixOps j) (T.query j) ∂μ :=
  lintegral_rep μ _ _ _ (measurable_observations μ T D C V) _ (fun _ _ h => same_query T D h j)

theorem report_error (C : Correct μ D families histories) (V : Valid T families histories) (j : J) :
    law μ T D {k | lastReport D (representative μ T D C k) (T.queryFamily j)
      (T.prefixOps j ++ [.inr (T.query j)]) ≠ some (answer (T.queryFamily j) (T.prefixOps j) (T.query j))}
      ≤ Dynamic.error := by
  refine (measure_rep μ _ _ _ (measurable_observations μ T D C V)
    (fun a => lastReport D a (T.queryFamily j) (T.prefixOps j ++ [.inr (T.query j)]) ≠
      some (answer (T.queryFamily j) (T.prefixOps j) (T.query j))) ?_).le.trans ?_
  · intro a b hab
    dsimp only
    rw [same_report T D hab j]
  · exact C.perQuery _ (V.queryFamily j) _ _ (V.queryHistory j)

/-- All lists of operations up to the indicated horizon have a finite index. -/
abbrev HistoryCode (N horizon : ℕ) := Σ k : Fin (horizon+1), Fin k.val → Op N

def decode (k : HistoryCode N horizon) : List (Op N) := List.ofFn k.2

def encode (ops : List (Op N)) (h : ops.length ≤ horizon) : HistoryCode N horizon :=
  ⟨⟨ops.length, by omega⟩, ops.get⟩

@[simp] theorem decode_encode (ops : List (Op N)) (h : ops.length ≤ horizon) :
    decode (encode ops h) = ops := List.ofFn_get ops

abbrev Totals (N horizon : ℕ) (families : Family N → Prop) (histories : List (Op N) → Prop) :=
  {z : Family N × HistoryCode N horizon // families z.1 ∧ histories (decode z.2)}

abbrev Queries (N horizon : ℕ) (families : Family N → Prop) (histories : List (Op N) → Prop) :=
  {z : (Family N × HistoryCode N horizon) × Fin N //
    families z.1.1 ∧ histories (decode z.1.2 ++ [.inr z.2])}

def bounded (N horizon : ℕ) (families : Family N → Prop) (histories : List (Op N) → Prop) :
    Tests N (Totals N horizon families histories) (Queries N horizon families histories) where
  family z := z.1.1
  ops z := decode z.1.2
  queryFamily z := z.1.1.1
  prefixOps z := decode z.1.1.2
  query z := z.1.2

theorem bounded_valid (N horizon : ℕ) (families : Family N → Prop) (histories : List (Op N) → Prop) :
    Valid (bounded N horizon families histories) families histories :=
  ⟨fun z => z.2.1,fun z => z.2.2,fun z => z.2.1,fun z => z.2.2⟩

def totalIndex {f : Family N} (hf : families f) {ops : List (Op N)} (ho : histories ops)
    (hl : ops.length ≤ horizon) : Totals N horizon families histories :=
  ⟨(f,encode ops hl),hf,by simpa using ho⟩

def queryIndex {f : Family N} (hf : families f) {ops : List (Op N)} {q : Fin N}
    (ho : histories (ops ++ [.inr q])) (hl : ops.length ≤ horizon) : Queries N horizon families histories :=
  ⟨((f,encode ops hl),q),hf,by simpa using ho⟩

abbrev Tape (horizon : ℕ) (families : Family N → Prop) (histories : List (Op N) → Prop) :=
  Profile (Totals N horizon families histories) (Queries N horizon families histories)

/-- The induced law is a probability law on a countable discrete space.
Every function of a chosen original execution, including its trace, is now measurable. -/
def compressed (horizon : ℕ) (families : Family N → Prop) (histories : List (Op N) → Prop) :
    Measure (Tape horizon families histories) := law μ (bounded N horizon families histories) D

def original (horizon : ℕ) (C : Correct μ D families histories) (k : Tape horizon families histories) : Ω :=
  representative μ (bounded N horizon families histories) D C k

theorem compressed_probability (horizon : ℕ) (C : Correct μ D families histories) :
    IsProbabilityMeasure (compressed μ D horizon families histories) :=
  law_probability μ _ D C (bounded_valid ..)

theorem original_halts (horizon : ℕ) (C : Correct μ D families histories) (k : Tape horizon families histories) :
    Halts D families histories (original μ D horizon C k) :=
  representative_halts μ _ D C k

theorem compressed_total (horizon : ℕ) (C : Correct μ D families histories)
    {f : Family N} (hf : families f) {ops : List (Op N)} (ho : histories ops) (hl : ops.length ≤ horizon) :
    (∫⁻ k, totalCost D (original μ D horizon C k) f ops ∂compressed μ D horizon families histories) =
      ∫⁻ a, totalCost D a f ops ∂μ := by
  simpa only [totalIndex,bounded,decode_encode] using
    expected_total μ (bounded N horizon families histories) D C (bounded_valid ..) (totalIndex hf ho hl)

theorem compressed_query (horizon : ℕ) (C : Correct μ D families histories)
    {f : Family N} (hf : families f) {ops : List (Op N)} {q : Fin N}
    (ho : histories (ops ++ [.inr q])) (hl : ops.length ≤ horizon) :
    (∫⁻ k, nextCost D (original μ D horizon C k) f ops q ∂compressed μ D horizon families histories) =
      ∫⁻ a, nextCost D a f ops q ∂μ := by
  simpa only [queryIndex,bounded,decode_encode] using
    expected_query μ (bounded N horizon families histories) D C (bounded_valid ..) (queryIndex hf ho hl)

theorem compressed_error (horizon : ℕ) (C : Correct μ D families histories)
    {f : Family N} (hf : families f) {ops : List (Op N)} {q : Fin N}
    (ho : histories (ops ++ [.inr q])) (hl : ops.length ≤ horizon) :
    compressed μ D horizon families histories {k | lastReport D (original μ D horizon C k) f
      (ops ++ [.inr q]) ≠ some (answer f ops q)} ≤ Dynamic.error := by
  simpa only [queryIndex,bounded,decode_encode] using
    report_error μ (bounded N horizon families histories) D C (bounded_valid ..) (queryIndex hf ho hl)

end
end AmortizedBound.PublicTapes

/-! ## SpendingLimits -/

/-! Expected probe budgets for actual runs on the countable law of
representative tapes and the independent finite uniform hard input. -/
namespace AmortizedBound.SpendingLimits
open Dynamic PublicTapes Simulation Simulation.Accounting MeasureTheory Filter Finset
open DisjointnessFoundations.HardDistribution
open scoped ENNReal
open Classical
noncomputable section

def rows (fit : n*n≤N) (z : Input n N) : Family N := fun q => rowSet fit (z.1 q)

theorem family_ok (fit : n*n≤N) (eq : n=hardSize N) (z : Input n N) : hardFamilies N (rows fit z) :=
  fun q => (rowSet_card fit (z.1 q)).trans eq

def work (D : DataStructure N w Ω) (seed : Ω) (fit : n*n≤N) (mixed : Bool) (z : Input n N) :=
  (totalCost D seed (rows fit z) (runPrefix fit mixed z.2.1 z.2.2 n)).toReal

def reads (D : DataStructure N w Ω) (seed : Ω) (fit : n*n≤N) (mixed : Bool) (hn : 2≤n)
    (z : Input n N) (T : Time n) :=
  (nextCost D seed (rows fit z) (throughUpdate fit mixed z.2.1 z.2.2 (timeIndex hn T))
    (z.2.2 (timeIndex hn T))).toReal

def Budget {K : Type} [MeasurableSpace K] (ν : Measure K) (seed : K→Ω) (D : DataStructure N w Ω)
    (fit : n*n≤N) (mixed : Bool) (hn : 2≤n) (a b : ℝ) : Prop :=
  (∀ z, Integrable (fun k => work D (seed k) fit mixed z) ν) ∧
  (∀ z, Integrable (fun k => mean (reads D (seed k) fit mixed hn z)) ν) ∧
  mean (fun z => ∫ k, work D (seed k) fit mixed z ∂ν) ≤ n*a ∧
  mean (fun z => ∫ k, mean (reads D (seed k) fit mixed hn z) ∂ν) ≤ b

theorem mean_mono {α : Type*} [Fintype α] {f g : α→ℝ} (h : ∀x,f x ≤ g x) : mean f≤mean g :=
  div_le_div_of_nonneg_right (sum_le_sum (fun x _ => h x)) (by positivity)

theorem integrable_mean {I K : Type*} [Fintype I] [MeasurableSpace K] (ν : Measure K)
    (v : K→I→ℝ) (ok : ∀ i, Integrable (fun k => v k i) ν) :
    Integrable (fun k => mean (v k)) ν :=
  (integrable_finset_sum univ (fun i _ => ok i)).div_const _

theorem integral_mean {I K : Type*} [Fintype I] [MeasurableSpace K] (ν : Measure K)
    (v : K→I→ℝ) (ok : ∀ i, Integrable (fun k => v k i) ν) :
    (∫ k, mean (v k) ∂ν) = mean (fun i => ∫ k,v k i ∂ν) := by
  simp only [mean,integral_div,integral_finset_sum _ (fun i _ => ok i)]

theorem aggregate {K : Type} [MeasurableSpace K] (ν : Measure K) (seed : K→Ω) (D : DataStructure N w Ω)
    (fit : n*n≤N) (mixed : Bool) (hn : 2≤n) {a b : ℝ} (h : Budget ν seed D fit mixed hn a b) :
    Integrable (fun k => mean (work D (seed k) fit mixed)) ν ∧
    Integrable (fun k => mean (fun z => mean (reads D (seed k) fit mixed hn z))) ν ∧
    (∫ k,mean (work D (seed k) fit mixed) ∂ν) ≤ n*a ∧
    (∫ k,mean (fun z => mean (reads D (seed k) fit mixed hn z)) ∂ν) ≤ b := by
  obtain ⟨hw,hq,tw,tq⟩ := h
  exact ⟨integrable_mean ν _ hw,integrable_mean ν _ hq,(integral_mean ν _ hw).le.trans tw,
    (integral_mean ν _ hq).le.trans tq⟩

def elements (fit : n*n≤N) (x : Row n) (t : ℕ) : List (Fin N) :=
  ((List.finRange n).take t).map (fun j => address fit j (x j))

theorem distinct (fit : n*n≤N) (x : Row n) (t : ℕ) : (elements fit x t).Nodup :=
  List.Nodup.map (fun j k e => congrArg Prod.fst (@address_injective n N fit (j,x j) (k,x k) e)) (List.nodup_finRange n).take

theorem update_only (fit : n*n≤N) (x : Row n) (qs : Fin n→Fin N) (t : ℕ) :
    runPrefix fit false x qs t=(elements fit x t).map Sum.inl := Epoch.single_rounds fit qs x _

theorem updates_legal (xs : List (Fin N)) (hx : xs.Nodup) : singleHistories N (xs.map Sum.inl) :=
  ⟨by simpa [legal,insertions,List.filterMap_map] using hx,⟨xs,Or.inl rfl⟩⟩

theorem prefix_legal (xs : List (Fin N)) (hx : xs.Nodup) (q : Fin N) :
    singleHistories N (xs.map Sum.inl ++ [.inr q]) :=
  ⟨by simpa [legal,insertions,List.filterMap_map,List.filterMap_append] using hx,⟨xs,Or.inr ⟨q,rfl⟩⟩⟩

theorem update_list (fit : n*n≤N) (x : Row n) (qs : Fin n→Fin N) (t : Fin n) :
    throughUpdate fit false x qs t=(elements fit x (t.val+1)).map Sum.inl := by
  simpa [update_only] using end_round fit false x qs t

theorem full_schedule (fit : n*n≤N) (x : Row n) (qs : Fin n→Fin N) :
    runPrefix fit true x qs n = schedule fit x qs := by simp [runPrefix,Epoch.rounds,schedule,List.take_of_length_le (show (List.finRange n).length≤n by simp)]

private theorem real_integral {K : Type} [MeasurableSpace K] [Countable K] [MeasurableSingletonClass K]
    (ν : Measure K) (g : K→ℝ≥0∞) {c : ℝ} (cp : 0≤c) (cap : (∫⁻ k,g k ∂ν)≤ENNReal.ofReal c) :
    Integrable (fun k => (g k).toReal) ν ∧ (∫ k,(g k).toReal ∂ν)≤c := by
  have meas : AEMeasurable g ν := (measurable_of_countable g).aemeasurable
  have fin := cap.trans_lt ENNReal.ofReal_lt_top
  refine ⟨integrable_toReal_of_lintegral_ne_top meas fin.ne,?_⟩
  rw [integral_toReal meas (ae_lt_top (measurable_of_countable g) fin.ne)]
  simpa [ENNReal.toReal_ofReal cp] using ENNReal.toReal_mono ENNReal.ofReal_ne_top cap

theorem single {n N w : ℕ} (eq : n=hardSize N) (fit : n*n≤N) (hn : 2≤n)
    [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ] (D : DataStructure N w Ω)
    (C : Correct μ D (hardFamilies N) (singleHistories N)) {a b : ℝ} (ap : 0≤a) (bp : 0≤b)
    (cost : PrefixBudgets μ D a b) :
    Budget (compressed μ D (2*n) (hardFamilies N) (singleHistories N))
      (original μ D (2*n) C) D fit false hn a b := by
  have npos : 0<n := by omega
  have Npos : 0<N := by nlinarith
  letI : Nonempty (Fin N) := ⟨⟨0,Npos⟩⟩
  letI : Nonempty (Fin n) := ⟨⟨0,npos⟩⟩
  letI : Nonempty (Time n) := (times_nonempty n).to_subtype
  let ν := compressed μ D (2*n) (hardFamilies N) (singleHistories N)
  let seed := original μ D (2*n) C
  have allWork (z : Input n N) : Integrable (fun k => work D (seed k) fit false z) ν ∧
      (∫ k,work D (seed k) fit false z ∂ν)≤n*a := by
    let xs := elements fit z.2.1 n
    have eqx := update_only fit z.2.1 z.2.2 n
    have len : xs.length=n := by simp [xs,elements]
    have valid := updates_legal xs (distinct ..)
    have cap := compressed_total μ D (2*n) C (family_ok fit eq z) valid (by simp [len]; omega)
    have cb := cost.updates _ (family_ok fit eq z) xs (distinct ..)
    rw [len,←ENNReal.ofReal_natCast n,←ENNReal.ofReal_mul (Nat.cast_nonneg _)] at cb
    exact real_integral ν _ (by positivity) (by dsimp [ν,seed,work]; rw [eqx]; exact cap.le.trans cb)
  have allQuery (z : Input n N) (T : Time n) : Integrable (fun k => reads D (seed k) fit false hn z T) ν ∧
      (∫ k,reads D (seed k) fit false hn z T ∂ν)≤b := by
    let t := timeIndex hn T
    let xs := elements fit z.2.1 (t.val+1)
    have eqx := update_list fit z.2.1 z.2.2 t
    have len : (xs.map (Sum.inl : Fin N→Op N)).length≤2*n := by simp [xs,elements]; omega
    have valid := prefix_legal xs (distinct ..) (z.2.2 t)
    have cap := compressed_query μ D (2*n) C (family_ok fit eq z) valid len
    have cb := cost.query _ (family_ok fit eq z) xs (distinct ..) (z.2.2 t)
    apply real_integral ν _ bp
    change (∫⁻ k,nextCost D (seed k) _ (throughUpdate fit false z.2.1 z.2.2 t) (z.2.2 t) ∂ν)≤_
    rw [eqx]
    exact cap.le.trans cb
  refine ⟨fun z => (allWork z).1,fun z => integrable_mean ν _ (fun T => (allQuery z T).1),
    (mean_mono fun z => (allWork z).2).trans_eq (mean_const _),?_⟩
  refine (mean_mono fun z => ?_).trans_eq (mean_const b)
  rw [integral_mean ν _ (fun T => (allQuery z T).1)]
  exact (mean_mono fun T => (allQuery z T).2).trans_eq (mean_const _)

theorem mixed {n N w : ℕ} (eq : n=hardSize N) (fit : n*n≤N) (hn : 2≤n)
    [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ] (D : DataStructure N w Ω)
    (C : Correct μ D (hardFamilies N) legal) {a : ℝ} (ap : 0≤a)
    (cost : interleavedWork μ D ≤ ENNReal.ofReal ((n:ℝ)*a)) :
    Budget (compressed μ D (2*n) (hardFamilies N) legal)
      (original μ D (2*n) C) D fit true hn a (2*a) := by
  subst n
  let n := hardSize N
  have np : 0<n := by dsimp [n]; omega
  have Np : 0<N := by nlinarith
  letI : Nonempty (Fin N) := ⟨⟨0,Np⟩⟩
  letI : Nonempty (Fin (hardSize N)) := ⟨⟨0,np⟩⟩
  let ν := compressed μ D (2*n) (hardFamilies N) legal
  let seed := original μ D (2*n) C
  let f (z : Input (hardSize N) N) (k : Tape (2*n) (hardFamilies N) legal) :=
    totalCost D (seed k) (rows fit z) (runPrefix fit true z.2.1 z.2.2 n)
  let g (z : Input (hardSize N) N) := ∫⁻ k,f z k ∂ν
  let card := Fintype.card (Input (hardSize N) N)
  have cardE : (card:ℝ≥0∞)≠0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  have integrated (z : Input (hardSize N) N) : g z =
      ∫⁻ seed, totalCost D seed (rows fit z) (schedule fit z.2.1 z.2.2) ∂μ := by
    obtain ⟨len,leg⟩ := schedule_properties fit z.2.1 z.2.2
    dsimp only [g,f,n]
    rw [full_schedule]
    apply compressed_total μ D (2*n) C (family_ok fit rfl z) leg len.le
  have cap : (∑ z,g z)/(card:ℝ≥0∞) ≤ ENNReal.ofReal ((n:ℝ)*a) := by
    simp_rw [integrated]
    exact cost
  have capSum := (ENNReal.div_le_iff cardE (ENNReal.natCast_ne_top _)).mp cap
  have bound_ne : ENNReal.ofReal ((n:ℝ)*a)*(card:ℝ≥0∞)≠⊤ :=
    ENNReal.mul_ne_top ENNReal.ofReal_ne_top (ENNReal.natCast_ne_top _)
  have finite (z) : g z≠⊤ := ((single_le_sum (f:=g) (fun _ _ => zero_le _) (mem_univ z)).trans capSum |>.trans_lt bound_ne.lt_top).ne
  have gmeas (z) : AEMeasurable (f z) ν := (measurable_of_countable _).aemeasurable
  have wi (z) : Integrable (fun k => work D (seed k) fit true z) ν :=
    integrable_toReal_of_lintegral_ne_top (gmeas z) (finite z)
  have integral (z) : (∫k, work D (seed k) fit true z ∂ν)=(g z).toReal :=
    integral_toReal (gmeas z) (ae_lt_top (measurable_of_countable _) (finite z))
  have wcap : mean (fun z => ∫ k,work D (seed k) fit true z ∂ν)≤n*a := by
    simp_rw [integral,mean]
    have rcap := ENNReal.toReal_mono ENNReal.ofReal_ne_top cap
    rw [ENNReal.toReal_div,ENNReal.toReal_sum (fun z _ => finite z),
      ENNReal.toReal_natCast,ENNReal.toReal_ofReal (by positivity)] at rcap
    exact rcap
  have finish (z : Input (hardSize N) N) (k : Tape (2*n) (hardFamilies N) legal) :
      ∃ last, history D (seed k) (rows fit z) (runPrefix fit true z.2.1 z.2.2 n)=some last := by
    rw [full_schedule]
    exact Option.isSome_iff_exists.mp (original_halts μ D (2*n) C k _ (family_ok fit rfl z)
      _ (schedule_properties fit z.2.1 z.2.2).2)
  have point (z k) : mean (reads D (seed k) fit true hn z) ≤ (2/n)*work D (seed k) fit true z :=
    interleaved_query_mean fit hn z.2.1 z.2.2 D (seed k) _ (finish z k)
  have nonneg (z k) : 0≤mean (reads D (seed k) fit true hn z) :=
    div_nonneg (sum_nonneg (fun _ _ => ENNReal.toReal_nonneg)) (Nat.cast_nonneg _)
  have qi (z) : Integrable (fun k => mean (reads D (seed k) fit true hn z)) ν :=
    ((wi z).const_mul (2/n)).mono' (measurable_of_countable _).aestronglyMeasurable
      (ae_of_all _ (fun k => by rw [Real.norm_eq_abs,abs_of_nonneg (nonneg z k)]; exact point z k))
  refine ⟨wi,qi,wcap,?_⟩
  have qbound (z) : (∫k, mean (reads D (seed k) fit true hn z) ∂ν) ≤
      (2/n)*(∫ k,work D (seed k) fit true z ∂ν) := by
    rw [←integral_const_mul]
    exact integral_mono (qi z) ((wi z).const_mul _) (point z)
  have bound := mean_mono qbound
  have eq : mean (fun z => (2/(n:ℝ))*(∫ k,work D (seed k) fit true z ∂ν))=
      (2/n)*mean (fun z => ∫ k,work D (seed k) fit true z ∂ν) := by
    simp [mean,mul_sum,←mul_div_assoc]
  rw [eq] at bound
  have npos : 0<(n:ℝ) := by exact_mod_cast np
  exact bound.trans ((mul_le_mul_of_nonneg_left wcap (by positivity : 0≤2/(n:ℝ))).trans_eq
    (by field_simp; ring))

end
end AmortizedBound.SpendingLimits

/-! ## PublicScore -/

/-! Selecting a public index and tape in the physical experiment. Each public
choice retains the full uniform distribution of its own finite input space. -/
namespace AmortizedBound.PublicScore
open DisjointnessFoundations.HardDistribution MeasureTheory Finset
open Classical
noncomputable section

def mark (p : Prop) : ℝ := if p then 1 else 0

variable {A Ω : Type} [Fintype A] [MeasurableSpace Ω]

theorem mean_mono {f g : A → ℝ} (h : ∀ x, f x ≤ g x) : mean f ≤ mean g :=
  div_le_div_of_nonneg_right (sum_le_sum fun i _ => h i) (by positivity)

theorem mean_sub (f g : A → ℝ) : mean (fun i => f i-g i)=mean f-mean g := by
  simp only [mean,sum_sub_distrib,sub_div]

theorem mean_mul (c : ℝ) (f : A → ℝ) : mean (fun i => c*f i)=c*mean f := by
  simp only [mean,←mul_sum,mul_div_assoc]

theorem mean_div (f : A → ℝ) (c : ℝ) : mean (fun i => f i/c)=mean f/c := by
  simp only [mean,←sum_div,div_div]
  ring

theorem mean_integrable (μ : Measure Ω) (f : A → Ω → ℝ) (hi : ∀ i, Integrable (f i) μ) :
    Integrable (fun ω => mean (fun i => f i ω)) μ :=
  (integrable_finset_sum univ (fun i _ => hi i)).div_const _

theorem integral_mean (μ : Measure Ω) (f : A → Ω → ℝ) (hi : ∀ i, Integrable (f i) μ) :
    (∫ ω, mean (fun i => f i ω) ∂μ)=mean (fun i => ∫ ω, f i ω ∂μ) := by
  unfold mean
  rw [integral_div,integral_finset_sum univ (fun i _ => hi i)]

theorem exists_le_mean [Nonempty A] (f : A → ℝ) : ∃ i, f i ≤ mean f := by
  obtain ⟨i,_,h⟩ := exists_min_image univ f univ_nonempty
  exact ⟨i,(mean_const (α:=A) (f i)).symm.le.trans (mean_mono fun x => h x (mem_univ x))⟩

variable [Countable Ω] [MeasurableSingletonClass Ω]
variable (μ : Measure Ω) [IsProbabilityMeasure μ]

theorem integrable_bounded (f : Ω→ℝ) (u : ℝ) (h : ∀a, 0≤f a ∧ f a≤u) : Integrable f μ := by
  apply Integrable.mono' (integrable_const u) (measurable_of_countable f).aestronglyMeasurable
  exact ae_of_all _ fun a => by simpa [Real.norm_eq_abs, abs_of_nonneg (h a).1] using (h a).2

private theorem mark_integrable (s : Set Ω) : Integrable (fun a => mark (a∈s)) μ := by
  apply integrable_bounded μ _ 1
  intro a
  unfold mark
  split <;> norm_num

omit [IsProbabilityMeasure μ] in
private theorem mark_integral (s : Set Ω) :
    (∫a, mark (a∈s) ∂μ)= μ.real s := by
  change (∫a, s.indicator (fun _ => (1:ℝ)) a ∂μ)=_
  rw [integral_indicator (Set.to_countable _).measurableSet,setIntegral_const,smul_eq_mul,mul_one]

/-- The clean mass and the collision mass refer to the uniform input for
each public index. The bound on the normalized load is a single joint
average over indices, inputs and tapes. -/
theorem select {J : Type} [Fintype J] [Nonempty J] (I : J → Type)
    [∀ j, Fintype (I j)] [∀ j, Nonempty (I j)]
    (n γ : ℝ) (size : J→ℝ) (hn : 0<n) (hg : 0<γ) (sizes : ∀j,0<size j)
    (clean hit : (j : J) → I j → Prop) (wrong : (j : J) → I j → Set Ω)
    (load acc err : (j : J) → I j → Ω → ℝ)
    (loadInt : ∀ j i, Integrable (load j i) μ)
    (accInt : ∀ j i, Integrable (acc j i) μ)
    (errInt : ∀ j i, Integrable (err j i) μ)
    (errNonneg : ∀ j i a, 0≤err j i a)
    (linear : ∀ j i a, 3/4*γ*(mark (clean j i)-mark (a∈wrong j i)-load j i a/32)≤acc j i a)
    (localized : ∀ j i a, err j i a ≤ if hit j i ∧ a∈wrong j i then γ else 0)
    (accuracy : ∀ j i, μ.real (wrong j i) ≤ 1/4096)
    (yes : ∀ j, 1/4≤mean (fun i => mark (clean j i)))
    (rare : ∀ j, mean (fun i => mark (hit j i))≤size j/n)
    (budget : mean (fun j => mean (fun i => ∫a, load j i a ∂μ))≤4) :
    ∃ j a, γ/32≤mean (fun i => acc j i a) ∧
      mean (fun i => err j i a)/mean (fun i => acc j i a)≤size j/(64*n) := by
  obtain ⟨j,hj⟩ := exists_le_mean (fun j => mean (fun i => ∫a, load j i a ∂μ))
  have small := hj.trans budget
  have massPoint (i : I j) :
      3/4*γ*(mark (clean j i)-μ.real (wrong j i)-(∫a,load j i a ∂μ)/32) ≤ ∫a,acc j i a ∂μ := by
    have m := mark_integrable μ (wrong j i)
    have v : Integrable (fun a => mark (clean j i)-mark (a∈wrong j i)) μ :=
      (integrable_const (mark (clean j i))).sub m
    have v' := (loadInt j i).div_const 32
    have z := integral_mono ((v.sub v').const_mul (3/4*γ)) (accInt j i) (linear j i)
    change (∫a,3/4*γ*(mark (clean j i)-mark (a∈wrong j i)-load j i a/32) ∂μ)≤_ at z
    rw [integral_const_mul,integral_sub v v',integral_sub (integrable_const _) m,integral_const,
      measureReal_univ_eq_one,one_smul,mark_integral,integral_div] at z
    exact z
  have av := mean_mono massPoint
  rw [mean_mul,mean_sub,mean_sub,mean_div] at av
  have ac : mean (fun i => μ.real (wrong j i))≤1/4096 :=
    (mean_mono fun i => accuracy j i).trans_eq (mean_const _)
  have high : γ/16 ≤ ∫a, mean (fun i => acc j i a) ∂μ := by
    rw [integral_mean μ _ (accInt j)]
    have c : 1/4-1/4096-4/32 ≤ mean (fun i => mark (clean j i))-mean (fun i => μ.real (wrong j i))-
        mean (fun i => ∫a,load j i a ∂μ)/32 := by linarith only [yes j,ac,small]
    have b := (mul_le_mul_of_nonneg_left c (show 0≤3/4*γ by positivity)).trans av
    nlinarith only [b,hg]
  have errPoint (i : I j) : (∫a,err j i a ∂μ) ≤ γ*(1/4096)*mark (hit j i) := by
    by_cases hit' : hit j i
    · have k : ∀ a, err j i a ≤ γ*mark (a∈wrong j i) := by
        intro a
        simpa [mark,hit',mul_ite] using localized j i a
      have h := integral_mono (errInt j i) ((mark_integrable μ (wrong j i)).const_mul γ) k
      rw [integral_const_mul,mark_integral] at h
      simpa [mark,hit'] using h.trans (mul_le_mul_of_nonneg_left (accuracy j i) hg.le)
    · have z := integral_mono (errInt j i) (integrable_const (0:ℝ)) (fun a => by simpa [hit'] using localized j i a)
      simpa [mark,hit'] using z
  have er := mean_mono errPoint
  rw [mean_mul] at er
  have upper := er.trans (mul_le_mul_of_nonneg_left (rare j) (show 0 ≤ γ*(1/4096) by positivity))
  have low : (∫a, n/size j*mean (fun i => err j i a) ∂μ)≤γ/4096 := by
    rw [integral_const_mul,integral_mean μ _ (errInt j)]
    convert mul_le_mul_of_nonneg_left upper (div_nonneg hn.le (sizes j).le) using 1
    field_simp [(sizes j).ne',hn.ne']
    ring
  have nonnegative (a : Ω) : 0≤mean (fun i => err j i a) :=
    (mean_const (α:=I j) 0).symm.le.trans (mean_mono fun i => errNonneg j i a)
  obtain ⟨a,ha⟩ := Simulation.fixed_public μ (fun a => mean (fun i => acc j i a))
    (fun a => mean (fun i => err j i a)) (fun _ => size j) n γ hn hg
    (fun _ => sizes j) nonnegative (mean_integrable μ _ (accInt j))
    ((mean_integrable μ _ (errInt j)).const_mul _) high low
  exact ⟨j,a,ha⟩

end
end AmortizedBound.PublicScore

/-! ## LoadBound -/

namespace AmortizedBound.LoadBound
open DisjointnessFoundations.HardDistribution MeasureTheory Finset Classical
noncomputable section

private theorem point_le_scaled {A : Type} [Fintype A] [Nonempty A] (f : A→ℝ)
    (nn : ∀i,0≤f i) (i : A) : f i≤Fintype.card A*mean f := by
  have p : (Fintype.card A:ℝ)≠0 := by positivity
  have eq : (Fintype.card A:ℝ)*mean f=∑j,f j := by unfold mean; field_simp
  rw [eq]; exact single_le_sum (fun j _ => nn j) (mem_univ i)

/-- From the pointwise accounting and two expected budgets, recover each
individual load's integrability and the single joint expectation bound. -/
theorem of_accounting {J Ω : Type} [Fintype J] [Nonempty J] (I : J→Type)
    [∀j,Fintype (I j)] [∀j,Nonempty (I j)] [MeasurableSpace Ω] [Countable Ω] [MeasurableSingletonClass Ω]
    (μ : Measure Ω) (n : ℕ) (a b : ℝ) (np : 0<n) (ap : 0<a) (bp : 0<b)
    (load : (j : J) → I j → Ω → ℝ) (nn : ∀j i z,0≤load j i z)
    (work query : Ω→ℝ) (wi : Integrable work μ) (qi : Integrable query μ)
    (wc : (∫ z,work z ∂μ)≤n*a) (qc : (∫ z,query z ∂μ)≤b)
    (cap : ∀z,mean (fun j=>mean (fun i=>load j i z)) ≤ 2*(work z/(n*a))+2*(query z/b)) :
    (∀j i, Integrable (load j i) μ) ∧ mean (fun j=>mean (fun i=>∫z,load j i z ∂μ))≤4 := by
  let total := fun z=>mean (fun j=>mean (fun i=>load j i z))
  let dom := fun z=>2*(work z/(n*a))+2*(query z/b)
  have di : Integrable dom μ := ((wi.div_const _).const_mul _).add ((qi.div_const _).const_mul _)
  have nonneg (j z) : 0≤mean (fun i=>load j i z) := div_nonneg (sum_nonneg fun i _=>nn j i z) (by positivity)
  have integ (j : J) (i : I j) : Integrable (load j i) μ := by
    apply Integrable.mono' ((di.const_mul (Fintype.card J:ℝ)).const_mul (Fintype.card (I j):ℝ))
      (measurable_of_countable _).aestronglyMeasurable
    apply ae_of_all; intro z
    rw [Real.norm_eq_abs,abs_of_nonneg (nn j i z)]
    refine (point_le_scaled _ (fun v=>nn j v z) i).trans (mul_le_mul_of_nonneg_left ?_ (by positivity))
    refine (point_le_scaled (fun j=>mean (fun i=>load j i z)) (fun v=>nonneg v z) j).trans ?_
    exact mul_le_mul_of_nonneg_left (cap z) (by positivity)
  have ii (j : J) := PublicScore.mean_integrable μ (load j) (integ j)
  have ti : Integrable total μ := PublicScore.mean_integrable μ _ ii
  have bound := Simulation.Accounting.normalized_charge_expectation μ ap bp np work query total wi qi ti
    (ae_of_all _ cap) wc qc
  change (∫z,mean (fun j=>mean (fun i=>load j i z)) ∂μ)≤4 at bound
  rw [PublicScore.integral_mean μ _ ii] at bound
  simp_rw [PublicScore.integral_mean μ _ (integ _)] at bound
  exact ⟨integ,bound⟩

end
end AmortizedBound.LoadBound

/-! ## JointCharge -/

namespace AmortizedBound.JointCharge
open DisjointnessFoundations HardDistribution Finset MeasureTheory Classical
open Dynamic Simulation.Accounting ActualCharge
noncomputable section

abbrev Public (n N β : ℕ) := Time n × Candidate n β × (Fin n→Fin N)

variable {n β N w : ℕ} {Ω : Type} (hn : 2≤n) (pos : 1≤β) (fit : n*n≤N) (mixed : Bool)
    (D : DataStructure N w Ω) (seed : Ω)

abbrev Inputs (j : Public n N β) :=
  Protocol.Snapshot.Input N n (β^j.2.1.val) (Row n) (epochAt hn pos j.1 j.2.1).Out

def load (a b : ℝ) (j : Public n N β) (u : Inputs hn pos j) :=
  (snap hn pos fit mixed D seed j.2.2 j.1 j.2.1).load a b (Parameters.occupied β (j.2.1.val-1))
    (Fintype.card (Candidate n β)) u.2.1 u.2.2.1 u.2.2.2 u.1

theorem load_reindex (a b : ℝ) (T : Time n) (i : Candidate n β) :
    mean (fun qs : Fin n→Fin N => mean (load hn pos fit mixed D seed a b (T,i,qs))) =
      mean (fun z : Input n N => value hn pos fit mixed D seed z.1 z.2.1 z.2.2 a b T i) := by
  let e := epochAt hn pos T i
  let g := fun qs q F x o => (snap hn pos fit mixed D seed qs T i).load a b
    (Parameters.occupied β (i.val-1)) (Fintype.card (Candidate n β)) F x o q
  have indep : ∀qs qs' q F x o,(∀j,j≠e.selected→qs j=qs' j)→g qs q F x o=g qs' q F x o := by
    intro qs qs' q F x o hs
    change (e.snapshot fit mixed qs D seed _).load .. = (e.snapshot fit mixed qs' D seed _).load ..
    rw [e.snapshot_other fit mixed qs qs' D seed (Epoch.fuel D seed n) hs]
  exact e.reindex (by nlinarith : 0<N) g indep

theorem halting (eq : n=hardSize N)
    (good : PublicTapes.Halts D (hardFamilies N) (if mixed then legal else singleHistories N) seed) :
    (∀z : Input n N, Completed fit mixed D seed z.1 z.2.1 z.2.2) ∧
    (∀(T : Time n) (i : Candidate n β) (qs : Fin n→Fin N),
      (epochAt hn pos T i).SeedHalts fit mixed qs D seed) := by
  constructor
  · intro z
    apply Option.isSome_iff_exists.mp
    apply good _ (SpendingLimits.family_ok fit eq z)
    cases mixed with
    | true =>
      rw [SpendingLimits.full_schedule]
      exact (schedule_properties ..).2
    | false =>
      rw [SpendingLimits.update_only]
      exact SpendingLimits.updates_legal _ (SpendingLimits.distinct ..)
  · intro T i qs F x o q
    let e := epochAt hn pos T i
    apply good _ (fun j => (rowSet_card fit (F j)).trans eq)
    cases mixed with
    | true => exact e.selected_legal fit true qs x o q
    | false => exact e.selected_single fit qs x o q

private theorem average_add_scaled {I : Type} [Fintype I] (a b : ℝ) (f g : I→ℝ) :
    mean (fun z => 2*(f z/a)+2*(g z/b))=2*(mean f/a)+2*(mean g/b) := by
  simp only [mean,sum_add_distrib,←mul_sum,←sum_div,add_div]
  ring

/-- All three public finite choices and the dependent protocol input have
their actual uniform laws; the selected query index on the right belongs to
the original full hard input. -/
theorem joint_load [Nonempty (Candidate n β)] (eq : n=hardSize N)
    (good : PublicTapes.Halts D (hardFamilies N) (if mixed then legal else singleHistories N) seed)
    {a b : ℝ} (ap : 0<a) (bp : 0<b) :
    mean (fun j : Public n N β => mean (load hn pos fit mixed D seed a b j)) ≤
      2*(mean (SpendingLimits.work D seed fit mixed)/(n*a))+
      2*(mean (fun z => mean (SpendingLimits.reads D seed fit mixed hn z))/b) := by
  obtain ⟨fin,allHalt⟩ := halting hn pos fit mixed D seed eq good
  let vals := fun (T : Time n) (i : Candidate n β) (z : Input n N) =>
    value hn pos fit mixed D seed z.1 z.2.1 z.2.2 a b T i
  let totals := fun z : Input n N => mean (fun T => mean (fun i => vals T i z))
  have point (z : Input n N) : totals z ≤ 2*(SpendingLimits.work D seed fit mixed z/(n*a))+
      2*(mean (SpendingLimits.reads D seed fit mixed hn z)/b) :=
    cost_bound hn pos fit mixed D seed z.1 z.2.1 z.2.2 (fin z) (fun T i => allHalt T i z.2.2) ap bp
  have inner (T : Time n) : mean (fun p : Candidate n β × (Fin n→Fin N) =>
      mean (load hn pos fit mixed D seed a b (T,p)))=mean (fun z => mean (fun i => vals T i z)) := by
    rw [mean_prod (fun i qs => mean (load hn pos fit mixed D seed a b (T,i,qs)))]
    simp_rw [load_reindex hn pos fit mixed D seed a b T]
    exact Epoch.swap_mean (vals T)
  have outer := mean_prod (fun T (p : Candidate n β × (Fin n→Fin N)) =>
      mean (load hn pos fit mixed D seed a b (T,p)))
  change mean (fun j : Public n N β => mean (load hn pos fit mixed D seed a b j))=_ at outer
  rw [outer]
  simp_rw [inner]
  rw [Epoch.swap_mean (fun T z => mean (fun i => vals T i z))]
  exact (SpendingLimits.mean_mono point).trans_eq
    (average_add_scaled (n*a) b _ _)

end
end AmortizedBound.JointCharge

/-! ## BudgetBridge -/

namespace AmortizedBound.BudgetBridge
open Dynamic PublicTapes Parameters Conclusions MeasureTheory
open DisjointnessFoundations.HardDistribution Simulation.Accounting
open Classical
noncomputable section

private theorem nonnegative {m n s w : ℕ} {W O : Type} (S : Protocol.Snapshot m n s w W O)
    (a b : ℝ) (ap : 0<a) (bp : 0<b) (later k : ℕ) (F : Protocol.Rows m W) (x : Protocol.Block n s)
    (o : O) (q : Fin m) : 0≤S.load a b later k F x o q := by unfold Protocol.Snapshot.load; positivity

/-- The physical simulation on the compressed original tape has all required
finite first moments. Its normalized load has total mean at most four. -/
theorem physical {N n w : ℕ} {a b : ℝ} {Ω : Type} [MeasurableSpace Ω]
    (fit : n*n≤N) (mixed : Bool) (eq : n=hardSize N) (reg : Regime n w a b)
    (μ : Measure Ω) [IsProbabilityMeasure μ] (D : DataStructure N w Ω)
    (C : Correct μ D (hardFamilies N) (if mixed then legal else singleHistories N))
    (budget : SpendingLimits.Budget (compressed μ D (2*n) (hardFamilies N) (if mixed then legal else singleHistories N))
      (original μ D (2*n) C) D fit mixed reg.nLarge a b) :
    let β := base a w
    let hb : 1≤β := (by have := reg.dyadic; omega)
    let seed := original μ D (2*n) C
    let ν := compressed μ D (2*n) (hardFamilies N) (if mixed then legal else singleHistories N)
    let load := fun (j : JointCharge.Public n N β) (z : JointCharge.Inputs reg.nLarge hb j) k =>
      JointCharge.load reg.nLarge hb fit mixed D (seed k) a b j z
    (∀j z,Integrable (load j z) ν) ∧ mean (fun j=>mean (fun z=>∫k,load j z k ∂ν))≤4 := by
  intro β hb seed ν load
  letI : Nonempty (Fin n) := ⟨⟨0,by have := reg.nLarge; omega⟩⟩
  letI : Nonempty (Fin N) := ⟨⟨0,by have := reg.nLarge; nlinarith⟩⟩
  letI : Nonempty (Time n) := (times_nonempty n).to_subtype
  have kp := reg.chosen
  letI : Nonempty (Candidate n β) := Finset.Nonempty.to_subtype (Finset.card_pos.mp kp)
  letI : ∀j : JointCharge.Public n N β, Nonempty (JointCharge.Inputs reg.nLarge hb j) := fun _ => inferInstance
  have ap : 0<a := lt_of_lt_of_le zero_lt_one reg.positive.1
  have bp : 0<b := lt_of_lt_of_le zero_lt_one reg.positive.2
  obtain ⟨wi,qi,wc,qc⟩ := SpendingLimits.aggregate ν seed D fit mixed reg.nLarge budget
  refine LoadBound.of_accounting (JointCharge.Inputs reg.nLarge hb) ν n a b (by have := reg.nLarge; omega)
    ap bp load ?_ _ _ wi qi wc qc ?_
  · intro j z k; exact nonnegative _ a b ap bp _ _ _ _ _ _
  · intro k; exact JointCharge.joint_load reg.nLarge hb fit mixed D (seed k) eq (original_halts μ D (2*n) C k) ap bp

end
end AmortizedBound.BudgetBridge

/-! ## SnapshotWitness -/

/-! A time, candidate epoch and tape whose actual word-probe simulation
has large acceptance and small conditional collision probability. -/
namespace AmortizedBound.SnapshotWitness
open Dynamic Parameters Conclusions Simulation Simulation.Accounting
open DisjointnessFoundations DisjointnessFoundations.FiniteSampling DisjointnessFoundations.HardDistribution
open MeasureTheory Real Finset Classical
noncomputable section

local instance (e : Epoch n s) : Nonempty e.Out := ⟨fun t => t.1⟩

abbrev Public (n β N : ℕ) := Time n × Candidate n β × (Fin n → Fin N)

def epoch (hn : 2≤n) (hb : 1≤β) (j : Public n β N) :=
  candidateEpoch hb (timeIndex hn j.1) (by rw [timeIndex_label]; exact (mem_Icc.mp j.1.property).1) j.2.1

abbrev Inputs (hn : 2≤n) (hb : 1≤β) (j : Public n β N) :=
  Protocol.Snapshot.Input N n (β^j.2.1.val) (Row n) (epoch hn hb j).Out

section
variable {Ω : Type} (hn : 2≤n) (hb : 1≤β) (fit : n*n≤N) (mixed : Bool)
    (D : DataStructure N w Ω) (seed : Ω)

def snapshot (j : Public n β N) :=
  (epoch hn hb j).snapshot fit mixed j.2.2 D seed (Epoch.fuel D seed n)

def load (a b : ℝ) (j : Public n β N) (z : Inputs hn hb j) :=
  (snapshot hn hb fit mixed D seed j).load a b (occupied β (j.2.1.val-1))
    (Fintype.card (Candidate n β)) z.2.1 z.2.2.1 z.2.2.2 z.1

abbrev rate := GameBound.rate

def accept (a b : ℝ) (j : Public n β N) (z : Inputs hn hb j) :=
  (snapshot hn hb fit mixed D seed j).privateYes (rate a w) ⌊64*a*(β^j.2.1.val:ℕ)⌋₊
    ⌊64*a*occupied β (j.2.1.val-1)⌋₊ ⌊32*b⌋₊ (sampleExponent a w)
    (cutoff b (Fintype.card (Candidate n β))) z.2.1 z.2.2.1 z.2.2.2 z.1

def hit (j : Public n β N) (z : Inputs hn hb j) :=
  Communication.Game.overlaps ((z.2.1 z.1) ∘ (epoch hn hb j).index) z.2.2.1

def joint (a b : ℝ) (j : Public n β N) (z : Inputs hn hb j) : ℝ :=
  if hit hn hb j z then accept hn hb fit mixed D seed a b j z else 0

def clean (j : Public n β N) (z : Inputs hn hb j) :=
  ∀t, z.2.1 z.1 t ≠ (epoch hn hb j).join z.2.2.1 z.2.2.2 t

def family (j : Public n β N) (z : Inputs hn hb j) : Family N := fun i => rowSet fit (z.2.1 i)

def past (j : Public n β N) (z : Inputs hn hb j) :=
  (epoch hn hb j).past fit mixed j.2.2 z.2.2.1 z.2.2.2

def wrong (j : Public n β N) (z : Inputs hn hb j) :=
  lastReport D seed (family hn hb fit j z) (past hn hb fit mixed j z ++ [.inr z.1]) ≠
    some (answer (family hn hb fit j z) (past hn hb fit mixed j z) z.1)

abbrev Allowed (N : ℕ) (mixed : Bool) : List (Op N)→Prop := if mixed then legal else singleHistories N

theorem valid (j : Public n β N) (z : Inputs hn hb j) :
    Allowed N mixed (past hn hb fit mixed j z ++ [.inr z.1]) := by
  cases mixed with
  | true => exact (epoch hn hb j).selected_legal fit true j.2.2 _ _ _
  | false => exact (epoch hn hb j).selected_single fit j.2.2 _ _ _

theorem past_short (j : Public n β N) (z : Inputs hn hb j) : (past hn hb fit mixed j z).length≤2*n := by
  unfold past
  rw [Epoch.selected_ordinal]
  have lt := (epoch hn hb j).selected.isLt
  cases mixed <;> simp [Epoch.stepCount] <;> omega

theorem family_valid (eq : n=hardSize N) (j : Public n β N) (z : Inputs hn hb j) :
    hardFamilies N (family hn hb fit j z) := fun _ => (rowSet_card fit _).trans eq

private theorem mean_pair {A B : Type} [Fintype A] [Fintype B] (f : A×B→ℝ) :
    mean f=mean (fun a=>mean (fun b=>f (a,b))) := mean_prod (fun a b=>f (a,b))

theorem yes_mass [Nonempty (Fin N)] (j : Public n β N) :
    1/4≤mean (fun z : Inputs hn hb j => PublicScore.mark (clean hn hb j z)) := by
  letI : Nonempty (Fin n) := ⟨⟨0,by omega⟩⟩
  rw [mean_pair]
  apply (mean_const (α:=Fin N) (1/4)).symm.le.trans
  apply PublicScore.mean_mono
  intro q
  rw [mean_pair]
  apply (mean_const (α:=Fin N→Row n) (1/4)).symm.le.trans
  apply PublicScore.mean_mono
  intro F
  refine ((epoch hn hb j).yes_mass hn (F q)).trans_eq ?_
  congr 1
  funext z
  by_cases c : ∀i,F q i ≠ (epoch hn hb j).join z.1 z.2 i <;> simp [PublicScore.mark,clean,c]

theorem hit_mass [Nonempty (Fin N)] (j : Public n β N) :
    mean (fun z : Inputs hn hb j => PublicScore.mark (hit hn hb j z)) ≤ (β^j.2.1.val:ℕ)/(n:ℝ) := by
  letI : Nonempty (Fin n) := ⟨⟨0,by omega⟩⟩
  rw [mean_pair,←mean_const (α:=Fin N) ((β^j.2.1.val:ℕ)/(n:ℝ))]
  apply PublicScore.mean_mono
  intro q
  rw [mean_pair,←mean_const (α:=Fin N→Row n) ((β^j.2.1.val:ℕ)/(n:ℝ))]
  apply PublicScore.mean_mono
  intro F
  exact (epoch hn hb j).rare_mass (by omega) (F q)

theorem report (eq : n=hardSize N) (halts : PublicTapes.Halts D (hardFamilies N) (Allowed N mixed) seed)
    (j : Public n β N) (z : Inputs hn hb j) :
    ((snapshot hn hb fit mixed D seed j).truth z.2.1 z.2.2.1 z.2.2.2 z.1).1=
      lastReport D seed (family hn hb fit j z) (past hn hb fit mixed j z ++ [.inr z.1]) := by
  let e := epoch hn hb j
  let S := snapshot hn hb fit mixed D seed j
  have sh : e.SeedHalts fit mixed j.2.2 D seed := fun F x o q =>
    halts _ (family_valid hn hb fit eq j (q,F,x,o)) _ (valid hn hb fit mixed j (q,F,x,o))
  have actual := e.snapshot_query_common fit mixed j.2.2 D seed sh z.2.1 z.2.2.1 z.2.2.2 z.1
  have v := (Physical.replay_correct (S.actual z.2.1 z.2.2.1 z.2.2.2) (S.query z.1) (fun _=>none)).1
  have ov : Physical.overlay (S.actual z.2.1 z.2.2.1 z.2.2.2) (fun _=>none)=S.actual z.2.1 z.2.2.1 z.2.2.2 := rfl
  rw [ov] at v
  exact v.trans actual.1.symm

theorem usable (eq : n=hardSize N) (halts : PublicTapes.Halts D (hardFamilies N) (Allowed N mixed) seed)
    (j : Public n β N) (z : Inputs hn hb j) (yes : clean hn hb j z) (ok : ¬wrong hn hb fit mixed D seed j z) :
    (snapshot hn hb fit mixed D seed j).outsideDisjoint (z.2.1 z.1) z.2.2.2=true ∧
    ((snapshot hn hb fit mixed D seed j).truth z.2.1 z.2.2.1 z.2.2.2 z.1).1=some true := by
  let e := epoch hn hb j
  have rel := e.filtered_answer fit mixed j.2.2 z.2.1 z.2.2.1 z.2.2.2 z.1
  have full : ∀t,z.2.1 z.1 t ≠ e.join z.2.2.1 z.2.2.2 t := yes
  rw [decide_eq_true full,Bool.and_eq_true] at rel
  refine ⟨rel.2,?_⟩
  rw [report hn hb fit mixed D seed eq halts]
  exact (not_ne_iff.mp ok).trans (congrArg some rel.1)

theorem local_error (eq : n=hardSize N) (halts : PublicTapes.Halts D (hardFamilies N) (Allowed N mixed) seed)
    (a b : ℝ) (j : Public n β N) (z : Inputs hn hb j) :
    joint hn hb fit mixed D seed a b j z ≤
      if hit hn hb j z ∧ wrong hn hb fit mixed D seed j z then
        (rate a w).p^(cutoff b (Fintype.card (Candidate n β))) else 0 := by
  let S := snapshot hn hb fit mixed D seed j
  by_cases h : hit hn hb j z
  · by_cases fail : wrong hn hb fit mixed D seed j z
    · simp only [joint,if_pos h,if_pos (And.intro h fail)]
      exact S.private_upper _ _ _ _ _ _ rfl _ _ _ _
    · simp only [joint,if_pos h,fail,and_false,if_false]
      unfold accept
      rw [Protocol.Snapshot.private_exact]
      split
      · rename_i elig
        have filt := (epoch hn hb j).filtered_answer fit mixed j.2.2 z.2.1 z.2.2.1 z.2.2.2 z.1
        have out := elig.2.1
        change (epoch hn hb j).outsideOK (z.2.1 z.1) z.2.2.2=true at out
        obtain ⟨k,coincide⟩ := h
        have no : ¬(∀t,z.2.1 z.1 t ≠ (epoch hn hb j).join z.2.2.1 z.2.2.2 t) := fun ok =>
          ok ((epoch hn hb j).index k) (coincide.trans ((epoch hn hb j).join_inside _ _ k).symm)
        rw [out,Bool.and_true,decide_eq_false no] at filt
        have reported := (report hn hb fit mixed D seed eq halts j z).symm.trans elig.2.2.1
        exfalso
        apply fail
        unfold wrong
        rw [reported]
        rw [show answer (family hn hb fit j z) (past hn hb fit mixed j z) z.1=false from filt]; decide
      · exact le_rfl
  · simp [joint,h]

private theorem small_tail {n β : ℕ} (b2 : 2≤β) (i : Candidate n β) :
    (2:ℝ)^(-√(n:ℝ)) ≤ 1/4 := by
  have floor := (candidate_bounds b2 i.property).2.1
  have ip := (mem_candidates.mp i.property).1
  have two : 2≤β^i.val := b2.trans (by simpa using Nat.pow_le_pow_right (by omega : 0<β) ip)
  have n4 : (4:ℝ)≤n := by exact_mod_cast (by omega : 4≤n)
  have sq : 2≤√(n:ℝ) := (Real.le_sqrt (by norm_num) (by positivity)).mpr (by linarith)
  have h := Real.rpow_le_rpow_of_exponent_le (by norm_num : 1≤(2:ℝ)) (neg_le_neg sq)
  norm_num at h ⊢
  exact h

end

set_option maxHeartbeats 1800000 in
theorem select {n N w : ℕ} {Ω : Type} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (D : DataStructure N w Ω) (mixed : Bool)
    (eq : n=hardSize N) (fit : n*n≤N) {a b : ℝ} (reg : Regime n w a b)
    (C : Correct μ D (hardFamilies N) (Allowed N mixed)) :
    let hn := reg.nLarge
    let hb : 1≤base a w := (by have := reg.dyadic; omega)
    let ν := PublicTapes.compressed μ D (2*n) (hardFamilies N) (Allowed N mixed)
    let seed := PublicTapes.original μ D (2*n) C
    (∀ (j : Public n (base a w) N) (z : Inputs hn hb j),
      Integrable (fun k => load hn hb fit mixed D (seed k) a b j z) ν) →
    mean (fun j : Public n (base a w) N =>
      mean (fun z : Inputs hn hb j => ∫k,load hn hb fit mixed D (seed k) a b j z ∂ν)) ≤ 4 →
    ∃ (j : Public n (base a w) N) (k : PublicTapes.Tape (2*n) (hardFamilies N) (Allowed N mixed)), GameBound.Good
      (snapshot hn hb fit mixed D (seed k) j) a b (occupied (base a w) (j.2.1.val-1)) := by
  intro hn hb ν seed integ budget
  let β := base a w
  let J := Public n β N
  let I := Inputs (N:=N) hn hb
  let K := PublicTapes.Tape (2*n) (hardFamilies N) (Allowed N mixed)
  let kcount := Fintype.card (Candidate n β)
  let γ := (rate a w).p^(cutoff b kcount)
  have kk : kcount=epochs n a w := Fintype.card_coe _
  have nn : 0<n := by have := reg.nLarge; omega
  have Nn : 0<N := by nlinarith
  letI : Nonempty (Fin n) := ⟨⟨0,nn⟩⟩
  letI : Nonempty (Fin N) := ⟨⟨0,Nn⟩⟩
  letI : Nonempty (Candidate n β) := (Finset.card_pos.mp reg.chosen).to_subtype
  letI : IsProbabilityMeasure ν := PublicTapes.compressed_probability μ D _ C
  have hg : 0<γ := pow_pos (rate a w).positive _
  have kp : 0<kcount := kk ▸ reg.chosen
  have ap : 0<a := by linarith only [reg.positive.1]
  have bp : 0<b := by linarith only [reg.positive.2]
  have sz (j : J) : 0<β^j.2.1.val := pow_pos (by omega : 0<β) _
  have lp (j : J) : 0<occupied β (j.2.1.val-1) := by
    have h := mem_candidates.mp j.2.1.property
    exact lt_of_lt_of_le (by omega) (prefix_ge hb _)
  let loss (j : J) (z : I j) (k : K) := load hn hb fit mixed D (seed k) a b j z
  let α (j : J) (z : I j) (k : K) := accept hn hb fit mixed D (seed k) a b j z
  let ε (j : J) (z : I j) (k : K) := joint hn hb fit mixed D (seed k) a b j z
  let E (j : J) (z : I j) := {k : K | wrong hn hb fit mixed D (seed k) j z}
  have halt (k : K) := PublicTapes.original_halts μ D (2*n) C k
  have privateRange (j : J) (z : I j) (k : K) : 0≤α j z k ∧ α j z k≤γ := by
    let S := snapshot hn hb fit mixed D (seed k) j
    exact ⟨S.private_nonneg _ _ _ _ _ _ _ _ _ _, S.private_upper _ _ _ _ _ _ rfl _ _ _ _⟩
  have errorRange (j : J) (z : I j) (k : K) : 0≤ε j z k ∧ ε j z k≤γ := by
    by_cases h : hit hn hb j z
    · simpa only [ε,joint,if_pos h] using privateRange j z k
    · simp only [ε,joint,if_neg h]; exact ⟨le_rfl,hg.le⟩
  have quality (j : J) (z : I j) (k : K) :
      3/4*γ*(PublicScore.mark (clean hn hb j z)-PublicScore.mark (k∈E j z)-loss j z k/32)≤α j z k := by
    let S := snapshot hn hb fit mixed D (seed k) j
    apply S.linear_accept (rate a w) rfl ap bp (sz j) (lp j) kp z.2.1 z.2.2.1 z.2.2.2 z.1
      (clean hn hb j z) (k∈E j z) (usable hn hb fit mixed D (seed k) eq (halt k) j z)
    have tail := reg.tail j.2.1.val j.2.1.property
    have shrink := mul_le_mul_of_nonneg_left (small_tail reg.dyadic j.2.1) hg.le
    change _ ≤ γ/4
    apply le_trans _ (show γ*(2:ℝ)^(-√(n:ℝ))≤γ/4 by linarith only [shrink])
    simpa only [γ,kk,rate,GameBound.rate,β,Nat.cast_pow] using tail
  have accuracy (j : J) (z : I j) : ν.real (E j z)≤1/4096 := by
    have err := PublicTapes.compressed_error μ D (2*n) C (family_valid hn hb fit eq j z)
      (valid hn hb fit mixed j z) (past_short hn hb fit mixed j z)
    have bound := ENNReal.toReal_mono (show Dynamic.error≠⊤ by norm_num [Dynamic.error]) err
    simpa [ν,E,seed,wrong,Measure.real,Dynamic.error] using bound
  obtain ⟨j,k,h⟩ := PublicScore.select ν I n γ (fun j => (β^j.2.1.val : ℕ)) (by exact_mod_cast nn) hg
    (fun j => by change (0:ℝ) < ((β^j.2.1.val:ℕ):ℝ); exact_mod_cast sz j) (clean hn hb) (hit hn hb) E loss α ε integ
    (fun j z => PublicScore.integrable_bounded ν _ γ (privateRange j z))
    (fun j z => PublicScore.integrable_bounded ν _ γ (errorRange j z))
    (fun j z k => (errorRange j z k).1) quality
    (fun j z k => local_error hn hb fit mixed D (seed k) eq (halt k) a b j z)
    accuracy (yes_mass hn hb) (hit_mass hn hb) budget
  refine ⟨j,k,?_⟩
  let S := snapshot hn hb fit mixed D (seed k) j
  let r := cutoff b (epochs n a w)
  let early := ⌊64*a*(β^j.2.1.val:ℕ)⌋₊
  let later := ⌊64*a*occupied β (j.2.1.val-1)⌋₊
  let hgt := sampleExponent a w
  dsimp only [GameBound.Good]
  rw [S.average_error (rate a w) early later ⌊32*b⌋₊ hgt r,S.average_acceptance (rate a w) early later ⌊32*b⌋₊ hgt r]
  simpa only [γ,α,ε,accept,joint,hit,r,←kk,S,early,later,hgt,β,kcount] using h

end
end AmortizedBound.SnapshotWitness

/-! ## MainResults -/

namespace AmortizedBound
open Dynamic Parameters Conclusions GameBound MeasureTheory Filter
open DisjointnessFoundations.HardIndependence
open Classical
noncomputable section

/-- A correct machine within the finite fast-regime budgets supplies one
actual public snapshot meeting both protocol guarantees on its original inputs. -/
theorem physical_witness {n N w : ℕ} {a b : ℝ} {Ω : Type} [MeasurableSpace Ω]
    (reg : Regime n w a b) (eq : n=hardSize N) (fit : n*n≤N) (mixed : Bool)
    (μ : Measure Ω) [IsProbabilityMeasure μ] (D : DataStructure N w Ω)
    (C : Correct μ D (hardFamilies N) (SnapshotWitness.Allowed N mixed))
    (budget : SpendingLimits.Budget (PublicTapes.compressed μ D (2*n) (hardFamilies N) (SnapshotWitness.Allowed N mixed))
      (PublicTapes.original μ D (2*n) C) D fit mixed reg.nLarge a b) :
    let hb : 1≤base a w := (by have := reg.dyadic; omega)
    ∃ (j : SnapshotWitness.Public n (base a w) N) (seed : Ω),
    haveI : Nonempty (Fin n) := ⟨⟨0,by have := reg.nLarge; omega⟩⟩
    Good (SnapshotWitness.snapshot reg.nLarge hb fit mixed D seed j) a b
      (occupied (base a w) (j.2.1.val-1)) := by
  intro hb
  letI : Nonempty (Fin n) := ⟨⟨0,by have := reg.nLarge; omega⟩⟩
  obtain ⟨integ,load⟩ := BudgetBridge.physical fit mixed eq reg μ D C budget
  obtain ⟨j,k,quality⟩ := SnapshotWitness.select μ D mixed eq fit reg C integ load
  exact ⟨j,PublicTapes.original μ D (2*n) C k,quality⟩

/-- The verified finite protocol contradicts its communication lower bound
once the hard universe is sufficiently large. -/
theorem no_fast_machine : NoFastMachine := by
  unfold NoFastMachine
  filter_upwards [GameBound.excludes] with n impossible
  intro N w a b heq reg alleged
  have fit : n*n≤N := heq ▸ active_fits N
  have size : n^4≤N := heq ▸ (fourth_root N).1
  have nn : 0<n := lt_of_lt_of_le (by decide : 0<2) reg.nLarge
  letI : Nonempty (Fin n) := ⟨⟨0,nn⟩⟩
  have hb : 1≤base a w := by have := reg.dyadic; omega
  have ap : 0≤a := zero_le_one.trans reg.positive.1
  have bp : 0≤b := zero_le_one.trans reg.positive.2
  have contradiction (mixed : Bool) (Ω : Type) [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
      (D : DataStructure N w Ω) (C : Correct μ D (hardFamilies N) (SnapshotWitness.Allowed N mixed))
      (budget : SpendingLimits.Budget (PublicTapes.compressed μ D (2*n) (hardFamilies N) (SnapshotWitness.Allowed N mixed))
        (PublicTapes.original μ D (2*n) C) D fit mixed reg.nLarge a b) : False := by
    obtain ⟨j,k,good⟩ := physical_witness reg heq.symm fit mixed μ D C budget
    let e := SnapshotWitness.epoch reg.nLarge hb j
    let S := SnapshotWitness.snapshot reg.nLarge hb fit mixed D k j
    exact impossible N w a b j.2.1.val size reg j.2.1.property (Row n) e.Out S e.block_uniform good
  rcases alleged with single | mixed
  · obtain ⟨Ω,m,μ,prob,D,C,cost⟩ := single
    exact contradiction false Ω μ D C (SpendingLimits.single heq.symm fit reg.nLarge μ D C ap bp cost)
  · obtain ⟨rfl,Ω,m,μ,prob,D,C,cost⟩ := mixed
    apply contradiction true Ω μ D C
    apply SpendingLimits.mixed heq.symm fit reg.nLarge μ D C ap
    simpa only [heq] using cost

/-- Total expected work on the fixed alternating hard distribution. -/
theorem total_work : Dynamic.TotalWorkBound := Conclusions.total_work no_fast_machine

/-- Amortized insertion cost and expected cost of a single subsequent query. -/
theorem query_tradeoff : Dynamic.QueryTradeoff := Conclusions.query_tradeoff no_fast_machine

end
end AmortizedBound

/-! ## GraphReductions -/

/-! Graph reductions and the maximum-cost consequence of the dynamic lower bounds. -/
namespace AmortizedBound.GraphReductions
open Dynamic MeasureTheory Filter Real
open DisjointnessDraft.Applications Graphs
open DisjointnessFoundations CellProbe QueryNormalization
open scoped ENNReal
noncomputable section
open Classical

/-- The last assertion of the single-query trade-off, including its quantifiers
over randomized machines and expected costs. -/
theorem maximum_of_query (bound : QueryTradeoff) (lo hi : ℝ) (lp : 0<lo) (lh : lo≤hi) :
    ∃ c : ℝ, 0<c ∧ ∀ tu : ℕ→ℝ, (∀ᶠ N : ℕ in atTop, 1≤tu N) → Subpolynomial tu → ∀ᶠ N : ℕ in atTop, ∀ w, wordSize lo hi N w → ∀ tq : ℝ, 0≤tq →
      ∀ (Ω : Type) [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ] (D : DataStructure N w Ω),
      Correct μ D (hardFamilies N) (singleHistories N) → PrefixBudgets μ D (tu N) tq →
      c*totalScale N ≤ max (tu N) tq := by
  obtain ⟨d,dp,lbu⟩ := bound lo hi lp lh
  refine ⟨min 1 (d/16),lt_min (by norm_num) (by positivity),fun tu one sub => ?_⟩
  filter_upwards [lbu tu one sub,one,Tradeoff.log_tends.eventually_ge_atTop (max (max 2 hi) (2/lo))] with N bound unit lg
  intro w ww tq tq0 Ω _ μ _ D ok costs
  let L := logb 2 N
  let l := logb 2 L
  have L2 : 2 ≤ L := ((le_max_left ..).trans (le_max_left ..)).trans lg
  have hiL : hi≤L := ((le_max_right ..).trans (le_max_left ..)).trans lg
  have low := (div_le_iff₀ lp).mp ((le_max_right ..).trans lg)
  have w2 : (2:ℝ)≤w := by linarith only [low,ww.1]
  have l1 : 1≤l := by simpa [l] using logb_le_logb_of_le (b:=2) (by norm_num) (by norm_num : (0:ℝ)<2) L2
  have r0 : 0≤L/l := by positivity
  change min 1 (d/16)*(L/l)^2 ≤ max (tu N) tq
  by_cases big : L^2≤tu N
  · have r : L/l≤L := (div_le_iff₀ (by linarith)).mpr (by nlinarith only [mul_le_mul_of_nonneg_left l1 (show 0≤L by linarith)])
    exact (mul_le_mul_of_nonneg_right (min_le_left ..) (sq_nonneg _) |>.trans_eq (one_mul _)).trans
      ((pow_le_pow_left₀ r0 r 2).trans (big.trans (le_max_left ..)))
  · let x := logb 2 (tu N*w)
    have aw : 2≤tu N*w := w2.trans (by simpa using mul_le_mul_of_nonneg_right unit (Nat.cast_nonneg w))
    have xp : 0<x := logb_pos (by norm_num) (by linarith)
    have ws : (w:ℝ) ≤ L^2 := by
      have z : (w:ℝ)≤hi*L := ww.2
      nlinarith only [z,mul_le_mul_of_nonneg_right hiL (show 0≤L by linarith)]
    have pow : tu N*w ≤ L^4 := (mul_le_mul (le_of_not_ge big) ws (Nat.cast_nonneg _) (sq_nonneg _)).trans_eq (by ring)
    have u := logb_le_logb_of_le (b:=2) (by norm_num) (by linarith : 0<tu N*w) pow
    rw [logb_pow] at u
    change x≤(↑(4:ℕ):ℝ)*l at u
    norm_num at u
    have rr : L/l ≤ 4*(L/x) := by
      rw [mul_div_assoc',div_le_div_iff₀ (by linarith : 0<l) xp]
      nlinarith only [mul_le_mul_of_nonneg_left u (show 0≤L by linarith)]
    have comp := mul_le_mul_of_nonneg_left (pow_le_pow_left₀ r0 rr 2) (show 0≤d/16 by positivity)
    have less := mul_le_mul_of_nonneg_right (min_le_right 1 (d/16)) (sq_nonneg (L/l))
    have given : d*(L/x)^2≤tq := bound w ww tq tq0 Ω μ D ok costs
    exact less.trans ((comp.trans_eq (by ring)).trans (given.trans (le_max_right ..)))

/-- Use two fibers of N vertices, one target, and exactly p isolated vertices. -/
abbrev Vertex (N p : ℕ) := Fin N ⊕ Fin N ⊕ Option (Fin p)
def row (q : Fin N) : Vertex N p := Sum.inl q
def col (x : Fin N) : Vertex N p := Sum.inr (Sum.inl x)
def sink : Vertex N p := Sum.inr (Sum.inr none)
def role : Vertex N p → Graphs.V (Fin N) (Fin N)
  | .inl q => .row q
  | .inr (.inl x) => .col x
  | .inr (.inr none) => .target
  | .inr (.inr (some _)) => .source

theorem vertices (N p : ℕ) : Fintype.card (Vertex N p)=2*N+1+p := by simp [Vertex]; omega

theorem padding (V : ℕ) (pos : 0<V) : let N := (V-1)/2; let p := V-(2*N+1)
    Fintype.card (Vertex N p)=V ∧ p≤1 := by
  dsimp only; rw [vertices]; omega

def incidence (f : Family N) (q x : Fin N) := x∈ f q

def directed (f : Family N) (X : Fin N→Prop) (a b : Vertex N p) := base (incidence f) X (role a) (role b)
def active (X : Fin N→Prop) : Vertex N p → Prop
  | .inr (.inl x) => X x
  | .inr (.inr (some _)) => False
  | _ => True
def fixedGraph (f : Family N) (a b : Vertex N p) := sym (base (incidence f) (fun _ => True)) (role a) (role b)
def induced (f : Family N) (X : Fin N→Prop) (a b : Vertex N p) := fixedGraph f a b ∧ active X a ∧ active X b

def triangleGraph (f : Family N) (X : Fin N→Prop) (selected : Option (Fin N)) (a b : Vertex N p) :=
  sym (directed f X) a b ∨ ∃ q, selected=some q ∧ ((a=row q ∧ b=sink) ∨ (a=sink ∧ b=row q))

private theorem walk_map {A B : Type} {G : A→A→Prop} {H : B→B→Prop} (r : A→B)
    (p : ∀ a b,G a b → H (r a) (r b)) {a b k} (w : Walk G a k b) : Walk H (r a) k (r b) := by
  induction w with
  | nil => exact .nil _
  | cons h _ ih => exact .cons (p _ _ h) ih

theorem directed_hit (f : Family N) (X : Fin N→Prop) (q : Fin N) :
    reach (directed (p:=p) f X) (row q) sink ↔ Hit (incidence f) X q := by
  constructor
  · rintro ⟨d,w⟩
    exact (reach_iff ..).mp ⟨d,walk_map role (fun _ _ e => e) w⟩
  · rintro ⟨x,h,m⟩
    exact ⟨2,.cons (b:=col x) h (.cons (b:=sink) m (.nil _))⟩

theorem induced_role (f : Family N) (X : Fin N→Prop) (a b : Vertex N p) :
    induced f X a b ↔ enabled (incidence f) X (role a) (role b) := by
  rcases a with a|a|(_|a) <;> rcases b with b|b|(_|b) <;>
    simp [induced,fixedGraph,active,role,sym,base,enabled]

theorem connectivity_hit (f : Family N) (X : Fin N→Prop) (q : Fin N) :
    reach (induced (p:=p) f X) (row q) sink ↔ Hit (incidence f) X q := by
  constructor
  · rintro ⟨d,w⟩
    exact (subgraph_iff ..).mp ⟨d,walk_map role (fun a b e => (induced_role f X a b).mp e) w⟩
  · rintro ⟨x,h,m⟩
    exact ⟨2,.cons (b:=col x) ((induced_role ..).mpr ⟨h,m⟩) (.cons (b:=sink) ((induced_role ..).mpr m) (.nil _))⟩

theorem triangle_hit (f : Family N) (X : Fin N→Prop) (q : Fin N) :
    (∃ a b c : Vertex N p, triangleGraph f X (some q) a b ∧ triangleGraph f X (some q) b c ∧
      triangleGraph f X (some q) c a) ↔ Hit (incidence f) X q := by
  constructor
  · rintro ⟨a,b,c,ab,bc,ca⟩
    have proj {a b : Vertex N p} (h : triangleGraph f X (some q) a b) :
        GraphVariants.triEdge (incidence f) X q (role a) (role b) := by
      rcases h with h|⟨r,he,edges⟩
      · exact Or.inl h
      · cases he
        rcases edges with ⟨rfl,rfl⟩|⟨rfl,rfl⟩
        · exact Or.inr (Or.inl ⟨rfl,rfl⟩)
        · exact Or.inr (Or.inr ⟨rfl,rfl⟩)
    exact (GraphVariants.triangle_iff ..).mp ⟨role a,role b,role c,proj ab,proj bc,proj ca⟩
  · rintro ⟨x,h,m⟩
    exact ⟨row q,col x,sink,Or.inl (Or.inl h),Or.inl (Or.inl m),Or.inr ⟨q,rfl,Or.inr ⟨rfl,rfl⟩⟩⟩

inductive EdgeEdit (V : Type) where
  | insert (a b : V)
  | erase (a b : V)
  deriving DecidableEq

def triUpdate (x : Fin N) : EdgeEdit (Vertex N p) := .insert (col x) sink
def triSelect (q : Fin N) : EdgeEdit (Vertex N p) := .insert sink (row q)
def triClear (q : Fin N) : EdgeEdit (Vertex N p) := .erase sink (row q)
def triOps : Op N → List (EdgeEdit (Vertex N p) ⊕ Unit)
  | .inl x => [.inl (triUpdate x)]
  | .inr q => [.inl (triSelect q), .inr (), .inl (triClear q)]

theorem triangle_counts (fit : n*n≤N) (x : Row n) (qs : Fin n → Fin N) :
    let graph := (schedule fit x qs).flatMap (triOps (p:=p))
    (graph.filter Sum.isLeft).length=3*n ∧ (graph.filter Sum.isRight).length=n := by
  intro graph
  have lengths (ts : List (Fin n)) :
      let ops := (ts.flatMap fun t => ([.inl (address fit t (x t)),.inr (qs t)] : List (Op N))).flatMap (triOps (p:=p))
      (ops.filter Sum.isLeft).length=3*ts.length ∧ (ops.filter Sum.isRight).length=ts.length := by
    induction ts with
    | nil => simp
    | cons t ts ih => dsimp only at *; simp [triOps,List.filter] at *; omega
  simpa only [graph,schedule,List.length_finRange] using lengths (List.finRange n)

inductive Incremental where | reachability | connectivity deriving DecidableEq

structure Configuration (V : Type) where
  edge : V→V→Prop
  enabled : V→Prop

inductive Change (V : Type)
  | insert (a b : V)
  | activate (a : V)
  deriving DecidableEq

def config (k : Incremental) (f : Family N) (X : Fin N→Prop) : Configuration (Vertex N p) :=
  match k with
  | .reachability => ⟨directed f X,fun _ => True⟩
  | .connectivity => ⟨fixedGraph f,active X⟩

def graphStep {V : Type} (g : Configuration V) : Change V → Configuration V
  | .insert a b => {g with edge := fun u v => g.edge u v ∨ (u=a ∧ v=b)}
  | .activate a => {g with enabled := fun v => g.enabled v ∨ v=a}

def update (k : Incremental) (x : Fin N) : Change (Vertex N p) := match k with
  | .reachability => .insert (col x) sink
  | .connectivity => .activate (col x)

theorem step_correct (k : Incremental) (f : Family N) (X : Fin N→Prop) (x : Fin N) :
    graphStep (config (p:=p) k f X) (update k x)=config k f (fun y => X y ∨ y=x) := by
  cases k <;> simp only [graphStep,config,update]
  · congr 1; funext u v; apply propext
    rcases u with u|u|(_|u) <;> rcases v with v|v|(_|v) <;> simp [directed,role,base,col,sink]
  · congr 1; funext v; apply propext
    rcases v with v|v|(_|v) <;> simp [active,col]

def graphReport {V : Type} (k : Incremental) (g : Configuration V) (q : V×V) : Prop :=
  match k with
  | .reachability => reach g.edge q.1 q.2
  | .connectivity => g.enabled q.1 ∧ g.enabled q.2 ∧ reach (fun u v => g.edge u v ∧ g.enabled u ∧ g.enabled v) q.1 q.2

theorem report_correct (k : Incremental) (f : Family N) (h : List (Op N)) (q : Fin N) :
    decide (graphReport k (config (p:=p) k f (fun x => x∈insertions h)) (row q,sink))=!(answer f h q) := by
  have eq : decide (Hit (incidence f) (fun x => x∈insertions h) q)=!(answer f h q) := by
    apply Bool.eq_iff_iff.mpr
    simp [Hit,incidence,answer]; tauto
  rw [←eq]
  apply decide_eq_decide.mpr
  cases k with
  | reachability => exact directed_hit ..
  | connectivity => simpa [graphReport,config,active,row,sink,induced] using connectivity_hit (p:=p) f (fun x => x∈insertions h) q

/-- The target operation changes no memory outside its actual sequence of
word probes. Relabeling both input and the reported Boolean preserves every
address, content, probe count, and public operation position. -/
def targetOp (k : Incremental) : Op N → Change (Vertex N p) ⊕ (Vertex N p×Vertex N p) :=
  Sum.map (update k) (fun q => (row q,sink))

abbrev GraphMachine (N p w : ℕ) (Ω : Type) :=
  Machine w (Configuration (Vertex N p)) (Change (Vertex N p)) (Vertex N p×Vertex N p) Ω

def flipStep (f : S→Step (Word w) S) (s : S) : Step (Word w) S := match f s with
  | .done b => .done (!b)
  | .read a k => .read a k
  | .write a v k => .write a v k

def flipResult (r : Result w) : Result w := {r with report := !r.report}

def source (k : Incremental) (D : GraphMachine N p w Ω) : DataStructure N w Ω where
  State := D.State
  init coin f := D.init coin (config k f (fun _ => False))
  start coin t op := D.start coin t (targetOp k op)
  step := flipStep D.step

theorem execute_flip (f : S→Step (Word w) S) (fuel : ℕ) (s : S) (mem : Memory w) :
    execute (flipStep f) fuel s mem=(execute f fuel s mem).map flipResult := by
  induction fuel generalizing s mem with
  | zero => cases h : f s <;> simp [execute,flipStep,h,flipResult]
  | succ n ih =>
    cases h : f s with
    | done b => simp [execute,flipStep,h,flipResult]
    | read a k =>
      rw [execute,show flipStep f s=.read a k by simp [flipStep,h], execute,h]
      simp only []
      rw [ih]
      cases execute f n (k (mem a)) mem <;> rfl
    | write a v k =>
      rw [execute,show flipStep f s=.write a v k by simp [flipStep,h], execute,h]
      simp only []
      rw [ih]
      cases execute f n k (Function.update mem a v) <;> rfl

private theorem finish_map (v : ℕ→Option A) (f : A→B) :
    finish (fun n => (v n).map f)=(finish v).map f := by
  classical
  unfold finish
  simp only [Option.isSome_map']
  split <;> rfl

theorem operation_map (k : Incremental) (D : GraphMachine N p w Ω) (coin t op mem) :
    operation (source k D) coin t op mem=(operation D coin t (targetOp k op) mem).map flipResult := by
  unfold operation
  simp only [source,execute_flip,finish_map]

def flipHistory (h : History w) : History w := {h with lastReport := h.lastReport.map Bool.not}

theorem advance_map (k : Incremental) (D : GraphMachine N p w Ω) (coin t op) (h : History w) :
    advance (source k D) coin t op (flipHistory h)=
      (advance D coin t (targetOp k op) h).map flipHistory := by
  cases op <;> simp only [advance,flipHistory,operation_map]
  all_goals cases operation D coin t (targetOp k _) h.memory <;> rfl

theorem run_map (k : Incremental) (D : GraphMachine N p w Ω) (coin t) (h : History w) (ops : List (Op N)) :
    runFrom (source k D) coin t (flipHistory h) ops =
      (runFrom D coin t h (ops.map (targetOp k))).map flipHistory := by
  induction ops generalizing t h with
  | nil => rfl
  | cons op ops ih =>
    simp only [runFrom,List.map_cons,advance_map]
    cases advance D coin t (targetOp k op) h <;> simp [ih]

theorem history_map (k : Incremental) (D : GraphMachine N p w Ω) (coin f ops) :
    history (source k D) coin f ops=(history D coin (config k f (fun _ => False)) (ops.map (targetOp k))).map flipHistory := by
  unfold history
  simp only [source]
  cases D.init coin (config k f (fun _ => False)) with
  | none => rfl
  | some mem => exact run_map k D coin 0 ⟨mem,0,none⟩ ops

theorem cost_map (k : Incremental) (D : GraphMachine N p w Ω) (coin f ops) :
    totalCost (source k D) coin f ops=totalCost D coin (config k f (fun _ => False)) (ops.map (targetOp k)) := by
  simp [totalCost,history_map,flipHistory,Option.map_map,Function.comp_def]

theorem query_map (k : Incremental) (D : GraphMachine N p w Ω) (coin f ops q) :
    nextCost (source k D) coin f ops q=nextCost D coin (config k f (fun _ => False)) (ops.map (targetOp k)) (row q,sink) := by
  simp only [nextCost,history_map]
  cases history D coin (config k f (fun _ => False)) (ops.map (targetOp k)) with
  | none => rfl
  | some h =>
    simp only [Option.map_some,Option.bind_some,flipHistory,operation_map,List.length_map]
    change ((Option.map _ (Option.map _ (operation D coin ops.length (.inr (row q,sink)) h.memory))).getD _) = _
    change ((Option.map _ (Option.map _ (operation D coin ops.length (.inr (row q,sink)) h.memory))).getD _) = ((operation D coin ops.length (.inr (row q,sink)) h.memory).map _).getD _
    cases operation D coin ops.length (.inr (row q,sink)) h.memory <;> rfl

abbrev Trace (N p : ℕ) := List (Change (Vertex N p) ⊕ (Vertex N p×Vertex N p))

def stateAfter (g : Configuration V') (ops : List (Change V' ⊕ (V'×V'))) :=
  ops.foldl (fun g op => op.elim (graphStep g) (fun _ => g)) g

theorem state_history (k : Incremental) (f : Family N) (ops : List (Op N)) :
    stateAfter (config (p:=p) k f (fun _ => False)) (ops.map (targetOp k)) =
      config k f (fun x => x∈insertions ops) := by
  induction ops using List.reverseRecOn with
  | nil => simp [stateAfter,insertions]
  | append_singleton h op ih =>
    cases op with
    | inl x =>
      simp only [stateAfter,List.map_append,List.map_singleton,List.foldl_append,List.foldl_cons,List.foldl_nil,
        targetOp,Sum.map_inl,Sum.elim_inl] at *
      rw [ih,step_correct]; congr 1; funext y; apply propext
      simp [insertions,List.filterMap_append]
    | inr q =>
      simpa [stateAfter,targetOp,insertions,List.filterMap_append,List.foldl_append] using ih

theorem last_report_map (k : Incremental) (D : GraphMachine N p w Ω) (coin f ops) :
    lastReport (source k D) coin f ops=(lastReport D coin (config k f (fun _ => False))
      (ops.map (targetOp k))).map Bool.not := by
  simp only [lastReport,history_map]
  cases history D coin (config k f (fun _ => False)) (ops.map (targetOp k)) <;> rfl

/-- Correctness and measurability on the graph histories in the reduction.
The answer in the last field is computed from the target's actual graph
after applying every edge insertion or activation. -/
structure GraphCorrect [MeasurableSpace Ω] (μ : Measure Ω) (D : GraphMachine N p w Ω)
    (k : Incremental) (H : List (Op N)→Prop) : Prop where
  terminates : ∀ f, hardFamilies N f → ∀ h, H h →
    ∀ᵐ coin ∂μ,(history D coin (config k f (fun _ => False)) (h.map (targetOp k))).isSome
  measurableCost : ∀ f, hardFamilies N f → ∀ h,H h → Measurable
    (fun coin => totalCost D coin (config k f (fun _ => False)) (h.map (targetOp k)))
  measurableQuery : ∀ f, hardFamilies N f → ∀ h q,H (h++[.inr q]) → Measurable
    (fun coin => nextCost D coin (config k f (fun _ => False)) (h.map (targetOp k)) (row q,sink))
  measurableReport : ∀ f, hardFamilies N f → ∀ h q b,H (h++[.inr q]) → MeasurableSet
    {coin | lastReport D coin (config k f (fun _ => False)) ((h++[.inr q]).map (targetOp k))=some b}
  error : ∀ f, hardFamilies N f → ∀ h q,H (h++[.inr q]) →
    let g := config k f (fun _ => False)
    μ {coin | lastReport D coin g ((h++[.inr q]).map (targetOp k)) ≠
      some (decide (graphReport k (stateAfter g (h.map (targetOp k))) (row q,sink)))} ≤ Dynamic.error

private theorem flip_iff {s : Option Bool} {b : Bool} : s.map Bool.not=some b ↔ s=some (!b) := by
  cases s with | none => simp | some a => cases a <;> cases b <;> decide

theorem correct_source [MeasurableSpace Ω] (μ : Measure Ω) (D : GraphMachine N p w Ω)
    (k : Incremental) (H : List (Op N)→Prop) (h : GraphCorrect μ D k H) :
    Correct μ (source k D) (hardFamilies N) H where
  terminates f hf xs hx := by simp only [history_map,Option.isSome_map']; exact h.terminates f hf xs hx
  measurableCost f hf xs hx := by simp only [cost_map]; exact h.measurableCost f hf xs hx
  measurableQuery f hf xs q hx := by simp only [query_map]; exact h.measurableQuery f hf xs q hx
  measurableReport f hf xs q b hx := by simp only [last_report_map,flip_iff]; exact h.measurableReport f hf xs q (!b) hx
  perQuery f hf xs q hx := by
    simp only [last_report_map,ne_eq,flip_iff]
    simpa only [ne_eq] using (by simpa only [state_history,report_correct] using h.error f hf xs q hx)

structure UpdateQueryCost [MeasurableSpace Ω] (μ : Measure Ω) (D : GraphMachine N p w Ω)
    (k : Incremental) (tu tq : ℝ) : Prop where
  updates : ∀ f, hardFamilies N f → ∀ xs : List (Fin N), xs.Nodup →
    (∫⁻ coin,totalCost D coin (config k f (fun _ => False)) (xs.map (fun x => .inl (update k x))) ∂μ)
      ≤ xs.length * ENNReal.ofReal tu
  query : ∀ f, hardFamilies N f → ∀ xs : List (Fin N), xs.Nodup → ∀ q : Fin N,
    (∫⁻ coin,nextCost D coin (config k f (fun _ => False)) (xs.map (fun x => .inl (update k x))) (row q,sink) ∂μ)
      ≤ ENNReal.ofReal tq

theorem cost_source [MeasurableSpace Ω] (μ : Measure Ω) (D : GraphMachine N p w Ω)
    (k : Incremental) (tu tq : ℝ) (cost : UpdateQueryCost μ D k tu tq) : PrefixBudgets μ (source k D) tu tq where
  updates f hf xs hx := by simpa only [cost_map,List.map_map,Function.comp_def,targetOp,Sum.map_inl] using cost.updates f hf xs hx
  query f hf xs hx q := by simpa only [query_map,List.map_map,Function.comp_def,targetOp,Sum.map_inl] using cost.query f hf xs hx q

/-- Expected work on the pushforward of the fixed Disjointness hard
distribution under the literal one-graph-operation-per-source-operation map. -/
def graphWork [MeasurableSpace Ω] (μ : Measure Ω) (D : GraphMachine N p w Ω) (k : Incremental) :=
  let n := hardSize N
  (∑ z : Input n N, ∫⁻ coin,totalCost D coin (config k (fun q => rowSet (active_fits N) (z.1 q)) (fun _ => False))
    ((schedule (active_fits N) z.2.1 z.2.2).map (targetOp k)) ∂μ) / Fintype.card (Input n N)

theorem work_source [MeasurableSpace Ω] (μ : Measure Ω) (D : GraphMachine N p w Ω) (k : Incremental) :
    interleavedWork μ (source k D)=graphWork μ D k := by simp only [interleavedWork,graphWork,cost_map]

def graphSize (N p : ℕ) := 2*N+1+p

theorem eventual_vertices (P : ℕ→ℕ→Prop) (h : ∀ᶠ N : ℕ in atTop, ∀p≤1,P N p) :
    ∀ᶠ V : ℕ in atTop, P ((V-1)/2) (V-(2*((V-1)/2)+1)) := by
  obtain ⟨M,hh⟩ := eventually_atTop.mp h
  exact eventually_atTop.mpr ⟨2*M+1,fun V v => hh _ (by omega) _ (by omega)⟩

theorem size_limits {N p : ℕ} (N3 : 3≤N) (pad : p≤1) :
    N ≤ graphSize N p ∧ graphSize N p ≤ N^2 ∧
    logb 2 N ≤ logb 2 (graphSize N p) ∧ logb 2 (graphSize N p) ≤ 2*logb 2 N := by
  have low : N≤graphSize N p := by unfold graphSize; omega
  have high : graphSize N p≤N^2 := by unfold graphSize; nlinarith
  have np : (0:ℝ)<N := by exact_mod_cast (by omega : 0<N)
  have vp : (0:ℝ)<graphSize N p := by exact_mod_cast (by omega : 0<graphSize N p)
  have bound := logb_le_logb_of_le (b:=2) (by norm_num) vp (by exact_mod_cast high : (graphSize N p:ℝ)≤(N:ℝ)^2)
  rw [logb_pow] at bound
  exact ⟨low,high,logb_le_logb_of_le (by norm_num) np (by exact_mod_cast low),by simpa using bound⟩

theorem root_limit {N p : ℕ} (root : 1≤hardSize N) (pad : p≤1) :
    (graphSize N p:ℝ)^(1/4:ℝ) ≤ 4*hardSize N := by
  let n := hardSize N
  have n1 : 1≤n := root
  have high : N<(n+1)^4 := (Conclusions.fourth_root N).2
  have g : graphSize N p ≤ (4*n)^4 := by
    have h := Nat.pow_le_pow_left (show n+1≤2*n by omega) 4
    unfold graphSize; nlinarith [show 1≤n^4 from Nat.one_le_pow _ _ n1]
  have h := rpow_le_rpow (Nat.cast_nonneg (graphSize N p)) (by exact_mod_cast g : (graphSize N p:ℝ)≤(4*(n:ℝ))^4)
    (by norm_num : (0:ℝ)≤1/4)
  rw [←Real.rpow_natCast_mul (by positivity)] at h
  simpa using h

theorem scale_limit {N p : ℕ} (N3 : 3≤N) (pad : p≤1) (lg : 2≤logb 2 N) :
    totalScale (graphSize N p) ≤ 4*totalScale N := by
  obtain ⟨_,_,low,high⟩ := size_limits N3 pad
  let x := logb 2 N
  let y := logb 2 (graphSize N p)
  have x2 : 2≤x := lg
  have xy : x≤y := low
  have lpos : 0<logb 2 x := logb_pos (by norm_num) (by linarith)
  have lm := logb_le_logb_of_le (b:=2) (by norm_num) (by linarith : 0<x) xy
  have rat : y/logb 2 y ≤ 2*(x/logb 2 x) :=
    calc y/logb 2 y ≤ y/logb 2 x := div_le_div_of_nonneg_left (by linarith) lpos lm
         _ ≤ (2*x)/logb 2 x := div_le_div_of_nonneg_right high lpos.le
         _ = _ := by ring
  exact (pow_le_pow_left₀ (div_nonneg (by linarith : 0≤y) (lpos.trans_le lm).le) rat 2).trans_eq (by unfold totalScale; dsimp [x]; ring)

private theorem width {lo hi : ℝ} (lp : 0<lo) (hp : 0<hi) {N p w : ℕ}
    (N3 : 3≤N) (pad : p≤1) (ww : wordSize lo hi (graphSize N p) w) : wordSize lo (2*hi) N w := by
  obtain ⟨_,_,low,high⟩ := size_limits N3 pad
  exact ⟨(mul_le_mul_of_nonneg_left low lp.le).trans ww.1,ww.2.trans
    ((mul_le_mul_of_nonneg_left high hp.le).trans_eq (by ring))⟩

/-- Both incremental graph problems inherit the total-work theorem on their
fixed distributions, with the total expressed in the actual number of vertices. -/
theorem incremental_total (bound : TotalWorkBound) (lo hi : ℝ) (lp : 0<lo) (lh : lo≤hi) :
    ∃ c : ℝ, 0<c ∧ ∀ᶠ N : ℕ in atTop, ∀ p≤1, ∀ w, wordSize lo hi (graphSize N p) w →
      ∀ (k : Incremental) (Ω : Type) [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
        (D : GraphMachine N p w Ω), GraphCorrect μ D k legal →
      ENNReal.ofReal (c*(graphSize N p:ℝ)^(1/4:ℝ)*totalScale (graphSize N p)) ≤ graphWork μ D k := by
  have hp := lp.trans_le lh
  obtain ⟨d,dp,lb⟩ := bound lo (2*hi) lp (by linarith)
  refine ⟨d/16,by positivity,?_⟩
  filter_upwards [lb,eventually_ge_atTop 16,Tradeoff.log_tends.eventually_ge_atTop 2] with N bound N16 lg
  intro p pad w ww k Ω _ μ _ D ok
  have lower := bound w (width lp hp (by omega) pad ww) Ω μ (source k D) (correct_source μ D k legal ok)
  rw [work_source] at lower
  have hn : 1≤hardSize N := by
    apply Nat.le_sqrt'.mpr
    apply Nat.le_sqrt'.mpr
    norm_num; omega
  have rp := root_limit hn pad
  have sc := scale_limit (by omega : 3≤N) pad lg
  have product := mul_le_mul rp sc (by exact sq_nonneg _) (by positivity)
  apply le_trans (ENNReal.ofReal_le_ofReal ?_) lower
  nlinarith only [mul_le_mul_of_nonneg_left product dp.le]

private theorem grow_size (p : ℕ) : Tendsto (fun N => graphSize N p) atTop atTop :=
  tendsto_atTop_mono (fun N => by change N≤2*N+1+p; omega) tendsto_id

theorem incremental_query_at_padding (bound : QueryTradeoff) {p : ℕ} (pad : p≤1)
    (lo hi : ℝ) (lp : 0<lo) (lh : lo≤hi) :
    ∃ c : ℝ, 0<c ∧ ∀ tu : ℕ→ℝ, (∀ᶠ V : ℕ in atTop, 1≤tu V) → Subpolynomial tu →
    ∀ᶠ N : ℕ in atTop, ∀ w, wordSize lo hi (graphSize N p) w → ∀ tq : ℝ, 0≤tq →
      ∀ (k : Incremental) (Ω : Type) [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
        (D : GraphMachine N p w Ω), GraphCorrect μ D k (singleHistories N) → UpdateQueryCost μ D k (tu (graphSize N p)) tq →
      c*ratio (graphSize N p) w (tu (graphSize N p)) ≤ tq := by
  have hp := lp.trans_le lh
  obtain ⟨d,dp,lbu⟩ := bound lo (2*hi) lp (by linarith)
  refine ⟨d/4,by positivity,fun tu unit sub => ?_⟩
  let a N := tu (graphSize N p)
  have one : ∀ᶠ N : ℕ in atTop,1≤a N := (grow_size p).eventually unit
  have small : Subpolynomial a := by
    intro e ep
    filter_upwards [(grow_size p).eventually (sub (e/2) (by positivity)), eventually_ge_atTop 3] with N cap n3
    have top := (size_limits n3 pad).2.1
    have pow := Real.rpow_le_rpow (Nat.cast_nonneg (graphSize N p)) (by exact_mod_cast top : (graphSize N p:ℝ)≤(N:ℝ)^2)
      (show 0≤e/2 by positivity)
    rw [←Real.rpow_natCast_mul (Nat.cast_nonneg N),show (↑(2:ℕ):ℝ)*(e/2)=e by push_cast;ring] at pow
    exact cap.trans pow
  filter_upwards [lbu a one small,one,eventually_ge_atTop 3,Tradeoff.log_tends.eventually_ge_atTop (2/lo)] with N bound a1 n3 big
  intro w ww tq tq0 k Ω _ μ _ D ok costs
  have w' := width lp hp n3 pad ww
  have val := bound w w' tq tq0 Ω μ (source k D) (correct_source μ D k _ ok) (cost_source μ D k _ _ costs)
  have h := (div_le_iff₀ lp).mp big
  have w2 : (2:ℝ)≤w := by linarith only [h,w'.1]
  have aw : 2≤a N*w := w2.trans (by simpa using mul_le_mul_of_nonneg_right a1 (Nat.cast_nonneg w))
  have xp : 0<logb 2 (a N*w) := logb_pos (by norm_num) (by linarith)
  have low := (size_limits n3 pad).2.2
  have nn : 0≤logb 2 N := logb_nonneg (by norm_num) (by exact_mod_cast (by omega : 1≤N))
  have r : logb 2 (graphSize N p)/logb 2 (a N*w) ≤ 2*(logb 2 N/logb 2 (a N*w)) :=
    (div_le_div_of_nonneg_right low.2 xp.le).trans_eq (by ring)
  have sq := mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (div_nonneg (nn.trans low.1) xp.le) r 2) dp.le
  change d/4*(logb 2 (graphSize N p)/logb 2 (a N*w))^2 ≤ tq
  change d*(logb 2 N/logb 2 (a N*w))^2≤tq at val
  nlinarith only [sq,val]

/-- The one-operation encodings send exactly n updates and n queries. -/
theorem incremental_counts (fit : n*n≤N) (x : Row n) (qs : Fin n→Fin N) (k : Incremental) :
    let ops := (schedule fit x qs).map (targetOp (p:=p) k)
    (ops.filter Sum.isLeft).length=n ∧ (ops.filter Sum.isRight).length=n := by
  intro ops
  have counts (ts : List (Fin n)) :
      let list := (ts.flatMap fun t => ([.inl (address fit t (x t)),.inr (qs t)] : List (Op N))).map (targetOp (p:=p) k)
      (list.filter Sum.isLeft).length=ts.length ∧ (list.filter Sum.isRight).length=ts.length := by
    induction ts with
    | nil => simp
    | cons t ts ih => dsimp only at *; simp [targetOp,List.filter] at *; omega
  simpa only [ops,schedule,List.length_finRange] using counts (List.finRange n)

theorem root_lower (N p : ℕ) : (hardSize N:ℝ) ≤ (graphSize N p:ℝ)^(1/4:ℝ) := by
  have h : hardSize N^4≤graphSize N p := (Conclusions.fourth_root N).1.trans (by unfold graphSize; omega)
  have pow := rpow_le_rpow (pow_nonneg (Nat.cast_nonneg (hardSize N)) 4)
    (by exact_mod_cast h : (hardSize N:ℝ)^4 ≤ (graphSize N p:ℝ)) (by norm_num : (0:ℝ)≤1/4)
  rw [←Real.rpow_natCast_mul (Nat.cast_nonneg _)] at pow
  simpa using pow

/-- Whenever the cost of the fixed sequence is at most u updates times tu
plus q queries times tq, its per-operation maximum inherits the lower bound.
This arithmetic applies to the triangle schedule as well (three updates per
source round). -/
theorem maximum_from_graph_work {N p : ℕ} {c tu tq : ℝ} (cp : 0<c) (u : ℕ) (np : 0<hardSize N)
    (work : ℝ≥0∞)
    (lb : ENNReal.ofReal (c*(graphSize N p:ℝ)^(1/4:ℝ)*totalScale (graphSize N p))≤work)
    (ub : work≤ENNReal.ofReal ((hardSize N:ℝ)*((u:ℝ)*tu+tq)))
    (ut : 0≤tu) (qt : 0≤tq) :
    c/((u:ℝ)+1)*totalScale (graphSize N p) ≤ max tu tq := by
  have upper := ENNReal.toReal_mono ENNReal.ofReal_ne_top (lb.trans ub)
  have s0 : 0≤totalScale (graphSize N p) := sq_nonneg _
  rw [ENNReal.toReal_ofReal (by positivity),ENNReal.toReal_ofReal (by positivity)] at upper
  have a := mul_le_mul_of_nonneg_right (root_lower N p) (mul_nonneg cp.le s0)
  have nn : 0<(hardSize N:ℝ) := by exact_mod_cast np
  have workBound : (hardSize N:ℝ)*(c*totalScale (graphSize N p)) ≤ (hardSize N:ℝ)*((u:ℝ)*tu+tq) := by
    nlinarith only [upper,a]
  have avg := (mul_le_mul_left nn).mp workBound
  have comb := mul_le_mul_of_nonneg_left (le_max_left tu tq) (Nat.cast_nonneg (α:=ℝ) u)
  rw [div_mul_eq_mul_div,(div_le_iff₀ (by positivity))]
  nlinarith only [avg,comb,le_max_right tu tq]

theorem graph_work_budget {N p w : ℕ} (np : 0<hardSize N) [MeasurableSpace Ω] (μ : Measure Ω)
    (D : GraphMachine N p w Ω) (k : Incremental) {tu tq : ℝ}
    (upper : ∀ z : Input (hardSize N) N,
      (∫⁻ coin,totalCost D coin (config k (fun q => rowSet (active_fits N) (z.1 q)) (fun _ => False))
        ((schedule (active_fits N) z.2.1 z.2.2).map (targetOp k)) ∂μ) ≤
          ENNReal.ofReal ((hardSize N:ℝ)*(tu+tq))) :
    graphWork μ D k ≤ ENNReal.ofReal ((hardSize N:ℝ)*(tu+tq)) := by
  have hh : hardSize N≤N := (Nat.sqrt_le_self _).trans (Nat.sqrt_le_self _)
  letI : Nonempty (Fin N) := ⟨⟨0,by omega⟩⟩
  letI : Nonempty (Fin (hardSize N)) := ⟨⟨0,np⟩⟩
  unfold graphWork
  apply (ENNReal.div_le_iff (Nat.cast_ne_zero.mpr Fintype.card_ne_zero) (ENNReal.natCast_ne_top _)).mpr
  exact (Finset.sum_le_sum (fun z _ => upper z)).trans_eq (by simp [mul_comm])

/-- A single constant handles odd and even numbers of graph vertices. -/
theorem incremental_query (bound : QueryTradeoff) (lo hi : ℝ) (lp : 0<lo) (lh : lo≤hi) :
    ∃ c : ℝ, 0<c ∧ ∀ tu : ℕ→ℝ, (∀ᶠ V : ℕ in atTop, 1≤tu V) → Subpolynomial tu →
    ∀ᶠ N : ℕ in atTop, ∀p≤1, ∀w, wordSize lo hi (graphSize N p) w → ∀tq : ℝ, 0≤tq →
      ∀ (k : Incremental) (Ω : Type) [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
        (D : GraphMachine N p w Ω), GraphCorrect μ D k (singleHistories N) → UpdateQueryCost μ D k (tu (graphSize N p)) tq →
      c*ratio (graphSize N p) w (tu (graphSize N p))≤tq := by
  obtain ⟨c,cp,even⟩ := incremental_query_at_padding bound (Nat.zero_le 1) lo hi lp lh
  obtain ⟨d,dp,odd⟩ := incremental_query_at_padding bound (le_refl 1) lo hi lp lh
  refine ⟨min c d,lt_min cp dp,fun tu unit sub => ?_⟩
  filter_upwards [even tu unit sub,odd tu unit sub] with N e o
  intro p pad w ww tq tq0 k Ω _ μ _ D ok costs
  by_cases z : p=0
  · subst p
    exact (mul_le_mul_of_nonneg_right (min_le_left c d) (sq_nonneg _)).trans (e w ww tq tq0 k Ω μ D ok costs)
  · have one : p=1 := by omega
    subst p
    exact (mul_le_mul_of_nonneg_right (min_le_right c d) (sq_nonneg _)).trans (o w ww tq tq0 k Ω μ D ok costs)

end
end AmortizedBound.GraphReductions

/-! ## TriangleReduction -/

/-! Sequential execution of the three physical operations comprising one
source query in the undirected triangle reduction. -/
namespace AmortizedBound.TriangleReduction
open Dynamic DisjointnessFoundations CellProbe QueryNormalization
open Classical
noncomputable section

inductive Calls (S : Type) : ℕ→Type where
  | ret (b : Bool) : Calls S 0
  | call {k : ℕ} (st : S) (next : Bool→Calls S k) : Calls S (k+1)

abbrev Control (S : Type) := Sigma (Calls S)

def step (act : S→Step W S) (p : Control S) : Step W (Control S) :=
  match p with
  | Sigma.mk _ (Calls.ret b) => .done b
  | Sigma.mk (k+1) (Calls.call s next) => match act s with
    | .done b => step act ⟨k,next b⟩
    | .read a f => .read a fun v => ⟨k+1,.call (f v) next⟩
    | .write a v s' => .write a v ⟨k+1,.call s' next⟩
termination_by p.1

theorem same_step (act : S→Step (Word w) S) (fuel : ℕ) {s t : S} (same : act s=act t) (m : Memory w) :
    execute act fuel s m=execute act fuel t m := by
  conv_lhs => rw [execute,same]
  conv_rhs => rw [execute]

def prepend (first : Result w) (last : Result w) : Result w :=
  {last with trace := first.trace++last.trace}

theorem run_call (act : S→Step (Word w) S) {s : S} (next : Bool→Calls S k)
    (t u : ℕ) (mem : Memory w) {r v : Result w} (first : execute act t s mem=some r)
    (rest : execute (step act) u ⟨k,next r.report⟩ r.memory=some v) :
    execute (step act) (t+u) ⟨k+1,.call s next⟩ mem=some (prepend r v) := by
  induction t generalizing s mem r with
  | zero =>
    cases hs : act s with
    | done b =>
      simp [execute,hs] at first; subst r
      rw [Nat.zero_add,same_step _ _ (show step act ⟨k+1,.call s next⟩=step act ⟨k,next b⟩ by rw [step,hs])]
      simpa [prepend] using rest
    | read | write => simp [execute,hs] at first
  | succ t ih =>
    cases hs : act s with
    | done b =>
      simp [execute,hs] at first; subst r
      rw [same_step _ _ (show step act ⟨k+1,.call s next⟩=step act ⟨k,next b⟩ by rw [step,hs])]
      simpa [prepend] using execute_mono (step act) (show u≤t+1+u by omega) _ _ rest
    | read a f =>
      rw [execute,hs] at first
      obtain ⟨r',hr,rfl⟩ := Option.map_eq_some_iff.mp first
      have h := ih (s:=f (mem a)) mem hr rest
      rw [show t+1+u=t+u+1 by omega,execute,step,hs]
      simp only [h,Option.map_some]; rfl
    | write a val st =>
      rw [execute,hs] at first
      obtain ⟨r',hr,rfl⟩ := Option.map_eq_some_iff.mp first
      have h := ih (s:=st) (Function.update mem a val) hr rest
      rw [show t+1+u=t+u+1 by omega,execute,step,hs]
      simp only [h,Option.map_some]; rfl

def sequence (D : Machine w F U Q Ω) (seed : Ω) (t : ℕ) (insert : U) (test : Q) (erase : U) : Control D.State :=
  ⟨3,.call (D.start seed t (.inl insert)) fun _ =>
    .call (D.start seed (t+1) (.inr test)) fun answer =>
    .call (D.start seed (t+2) (.inl erase)) fun _ => .ret (!answer)⟩

/-- The report comes from the middle operation, with the memory after
cleanup and every read and write from all three operations in its true order. -/
theorem sequence_exec (D : Machine w F U Q Ω) (seed : Ω) (t : ℕ) (insert : U) (test : Q) (erase : U)
    (m : Memory w) {u v z : Result w}
    (hi : operation D seed t (.inl insert) m=some u)
    (hq : operation D seed (t+1) (.inr test) u.memory=some v)
    (hd : operation D seed (t+2) (.inl erase) v.memory=some z) :
    ∃ fuel, execute (step D.step) fuel (sequence D seed t insert test erase) m =
      some ⟨!v.report,z.memory,u.trace++v.trace++z.trace⟩ := by
  obtain ⟨n1,h1⟩ := Execution.finish_witness _ hi
  obtain ⟨n2,h2⟩ := Execution.finish_witness _ hq
  obtain ⟨n3,h3⟩ := Execution.finish_witness _ hd
  let ret : Bool→Calls D.State 0 := fun _ => .ret (!v.report)
  have done : execute (step D.step) 0 ⟨0,ret z.report⟩ z.memory=some ⟨!v.report,z.memory,[]⟩ := by
    simp [ret,execute,step]
  have last := run_call D.step ret n3 0 v.memory h3 done
  let cleanup : Bool→Calls D.State 1 := fun answer =>
    .call (D.start seed (t+2) (.inl erase)) (fun _ => .ret (!answer))
  have testRun := run_call D.step cleanup n2 (n3+0) u.memory h2 last
  let testCall : Bool→Calls D.State 2 := fun _ => .call (D.start seed (t+1) (.inr test)) cleanup
  have first := run_call D.step testCall n1 (n2+(n3+0)) m h1 testRun
  exact ⟨_,by simpa [sequence,testCall,cleanup,ret,prepend,List.append_assoc] using first⟩
/-- Target words and addresses occupy a proper initial segment of the
simulator's words. The next address is available for its insertion count. -/
def reserve (ww : w<v) : Word v := ⟨2^w,Nat.pow_lt_pow_right (by decide : 1<2) ww⟩
def widen (ww : w<v) (a : Word w) : Word v := Fin.castLE (Nat.pow_le_pow_right (by decide) ww.le) a
def narrow (a : Word v) : Word w := ⟨a.val % 2^w,Nat.mod_lt _ (by positivity)⟩
@[simp] theorem narrow_widen (ww : w<v) (a : Word w) : narrow (widen ww a)=a :=
  Fin.ext (Nat.mod_eq_of_lt a.isLt)

theorem separate (ww : w<v) (a : Word w) : widen ww a≠reserve ww :=
  fun h => (Nat.ne_of_lt a.isLt) (congrArg Fin.val h)

def Encode (ww : w<v) (wide : Memory v) (m : Memory w) (count : ℕ) :=
  (∀a,narrow (wide (widen ww a))=m a) ∧ (wide (reserve ww)).val=count

def initial (ww : w<v) (m : Memory w) : Memory v := fun a =>
  if h : a.val<2^w then widen ww (m ⟨a.val,h⟩) else 0

theorem initialized (ww : w<v) (m : Memory w) : Encode ww (initial ww m) m 0 := by
  constructor
  · intro a
    have lt : (widen ww a).val<2^w := a.isLt
    simp [initial,lt]
    rfl
  · simp [initial,reserve]

theorem encode_write (ww : w<v) (mem : Memory v) (m : Memory w) (c) (rep : Encode ww mem m c)
    (a value : Word w) :
    Encode ww (Function.update mem (widen ww a) (widen ww value)) (Function.update m a value) c := by
  constructor
  · intro b; by_cases eq : b=a
    · subst b; simp
    · have ne : widen ww b≠widen ww a := fun h => eq (Fin.ext (congrArg (fun z : Word v => z.val) h))
      simp [Function.update_of_ne eq,Function.update_of_ne ne,rep.1]
  · rw [Function.update_of_ne (Ne.symm (separate ww a))]; exact rep.2

theorem encode_count (ww : w<v) (mem : Memory v) (m : Memory w) (c) (rep : Encode ww mem m c)
    (c' : Word v) : Encode ww (Function.update mem (reserve ww) c') m c'.val :=
  ⟨fun a => by rw [Function.update_of_ne (separate ww a)]; exact rep.1 a,by simp⟩

def liftStep (ww : w<v) (act : S→Step (Word w) S) (s : S) : Step (Word v) S :=
  match act s with
  | .done b => .done b
  | .read a k => .read (widen ww a) fun val => k (narrow val)
  | .write a val k => .write (widen ww a) (widen ww val) k

theorem lift_exec (ww : w<v) (act : S→Step (Word w) S) (fuel : ℕ) (s : S)
    (mem : Memory v) (m : Memory w) (c) (rep : Encode ww mem m c) {r : Result w}
    (h : execute act fuel s m=some r) :
    ∃v',execute (liftStep ww act) fuel s mem=some v' ∧ Encode ww v'.memory r.memory c ∧
      v'.report=r.report ∧ v'.trace.length=r.trace.length := by
  induction fuel generalizing s mem m r with
  | zero =>
    cases hs : act s <;> simp [execute,hs] at h
    subst r
    exact ⟨⟨_,mem,[]⟩,by simp [execute,liftStep,hs],rep,rfl,rfl⟩
  | succ n ih =>
    cases hs : act s with
    | done b =>
      simp [execute,hs] at h; subst r
      exact ⟨⟨_,mem,[]⟩,by simp [execute,liftStep,hs],rep,rfl,rfl⟩
    | read a k =>
      rw [execute,hs] at h
      obtain ⟨r',hr,rfl⟩ := Option.map_eq_some_iff.mp h
      obtain ⟨v',hv,ok,rb,rc⟩ := ih (k (m a)) mem m rep hr
      refine ⟨withProbe (.read (widen ww a) (mem (widen ww a))) v',?_,ok,rb,?_⟩
      · simp [execute,liftStep,hs,rep.1,hv]
      · simp [withProbe,rc]
    | write a value k =>
      rw [execute,hs] at h
      obtain ⟨r',hr,rfl⟩ := Option.map_eq_some_iff.mp h
      obtain ⟨v',hv,ok,rb,rc⟩ := ih k _ _ (encode_write ww mem m c rep a value) hr
      refine ⟨withProbe (.write (widen ww a) (widen ww value)) v',?_,ok,rb,?_⟩
      · simp [execute,liftStep,hs,hv]
      · simp [withProbe,rc]

/-- The simulator reads or overwrites the count word separately from all
the graph machine's addresses. -/
inductive Wrapper (W S : Type) where
  | run (s : S)
  | readCount (next : W→Wrapper W S)
  | writeCount (value : W) (next : Wrapper W S)

def wrapperStep (addr : W) (inner : S→Step W S) : Wrapper W S→Step W (Wrapper W S)
  | .run s => match inner s with
    | .done b => .done b
    | .read a k => .read a fun v => .run (k v)
    | .write a v k => .write a v (.run k)
  | .readCount f => .read addr f
  | .writeCount v next => .write addr v next

theorem wrapper_run (addr : Word w) (inner : S→Step (Word w) S) (k : ℕ) (s : S) (m : Memory w) :
    execute (wrapperStep addr inner) k (.run s) m=execute inner k s m := by
  induction k generalizing s m with
  | zero => cases hs : inner s <;> simp [execute,wrapperStep,hs]
  | succ n ih =>
    cases hs : inner s <;> conv_lhs => rw [execute,wrapperStep,hs]
    all_goals conv_rhs => rw [execute,hs]
    all_goals first | rfl | simp only [ih]

def one (D : Machine w F U Q Ω) (seed : Ω) (j : ℕ) (op : U ⊕ Q) : Control D.State :=
  ⟨1,.call (D.start seed j op) fun b => .ret b⟩

theorem one_exec (D : Machine w F U Q Ω) (seed : Ω) (j : ℕ) (op : U ⊕ Q) (m : Memory w)
    {r : Result w} (ran : operation D seed j op m=some r) :
    ∃ k,execute (step D.step) k (one D seed j op) m=some r := by
  obtain ⟨k,hk⟩ := Execution.finish_witness _ ran
  have tail : execute (step D.step) 0 ⟨0,Calls.ret r.report⟩ r.memory=some ⟨r.report,r.memory,[]⟩ := by
    simp [execute,step]
  have h := run_call D.step (fun b => .ret b) k 0 m hk tail
  cases r; exact ⟨k,by simpa [one,prepend] using h⟩

def clock (t c : ℕ) := 3*t-2*c

def source (ww : w<v) (D : Machine w F U Q Ω) (graph : Family N→F) (ins : Fin N→U)
    (select clear : Fin N→U) (test : Q) : DataStructure N v Ω where
  State := Wrapper (Word v) (Control D.State)
  init seed f := (D.init seed (graph f)).map (initial ww)
  start seed t op := .readCount fun c => match op with
    | .inl x => .writeCount (c+1) (.run (one D seed (clock t c.val) (.inl (ins x))))
    | .inr q => .run (sequence D seed (clock t c.val) (select q) test (clear q))
  step := wrapperStep (reserve ww) (liftStep ww (step D.step))

theorem clock_history (ops : List (Op N)) (block : Op N→List G)
    (ins : ∀x,(block (.inl x)).length=1) (ask : ∀q,(block (.inr q)).length=3) :
    (ops.flatMap block).length=clock ops.length (insertions ops).length := by
  induction ops with
  | nil => rfl
  | cons op ops ih =>
    have lim : (insertions ops).length≤ops.length := List.length_filterMap_le ..
    cases op <;> simp [List.flatMap_cons,insertions,List.length_append,ins,ask,clock] at * <;> omega

variable {N v w : ℕ} {F U Q Ω : Type} (ww : w<v) (D : Machine w F U Q Ω) (graph : Family N→F)
    (ins select clear : Fin N→U) (test : Q)

def block : Op N→List (U ⊕ Q)
  | .inl x => [.inl (ins x)]
  | .inr q => [.inl (select q),.inr test,.inl (clear q)]

def countStep : Op N→ℕ
  | .inl _ => 1
  | .inr _ => 0

def blockResult (seed : Ω) (j : ℕ) (m : Memory w) : Op N→Option (Result w)
  | .inl x => operation D seed j (.inl (ins x)) m
  | .inr q => do
    let u ← operation D seed j (.inl (select q)) m
    let v ← operation D seed (j+1) (.inr test) u.memory
    let z ← operation D seed (j+2) (.inl (clear q)) v.memory
    return ⟨!v.report,z.memory,u.trace++v.trace++z.trace⟩

theorem source_operation (seed : Ω) (t c : ℕ) (op : Op N) (m : Memory w) (mem : Memory v)
    (rep : Encode ww mem m c) (room : c+countStep op<2^v) {r : Result w}
    (ran : blockResult D ins select clear test seed (clock t c) m op=some r) :
    ∃ z, operation (source ww D graph ins select clear test) seed t op mem=some z ∧
      Encode ww z.memory r.memory (c+countStep op) ∧ z.report=r.report ∧
      z.trace.length=r.trace.length+(1+countStep op) := by
  let addr := reserve ww
  let act := liftStep ww (step D.step)
  have cc : (mem addr).val=c := rep.2
  cases op with
  | inl x =>
    have raw := one_exec D seed (clock t c) (.inl (ins x)) m ran
    obtain ⟨k,hk⟩ := raw
    let ct := mem addr + 1
    have eq : ct.val=c+1 := by
      have wide : 1<2^v := Nat.one_lt_pow (by omega) (by decide)
      change ((mem addr).val+(1%2^v))%2^v=c+1
      rw [Nat.mod_eq_of_lt wide,cc,Nat.mod_eq_of_lt (show c+1<2^v from room)]
    let mem' := Function.update mem addr ct
    have rep' : Encode ww mem' m (c+1) := eq ▸ encode_count ww mem m c rep ct
    obtain ⟨z,hz,repz,b,sz⟩ := lift_exec ww (step D.step) k _ mem' m (c+1) rep' hk
    let extra := withProbe (.read addr (mem addr)) (withProbe (.write addr ct) z)
    refine ⟨extra,operation_of_fuel (fuel:=k+2) _ ?_,repz,b,?_⟩
    · change execute (wrapperStep addr act) (k+2) (.readCount _) mem=some extra
      rw [execute,wrapperStep]
      change (execute (wrapperStep addr act) (k+1) (.writeCount ct (.run (one D seed (clock t (mem addr).val) (.inl (ins x))))) mem).map _=_
      rw [execute,wrapperStep]
      change ((execute (wrapperStep addr act) k (.run _) mem').map _).map _=_
      rw [wrapper_run,cc,hz]; rfl
    · simp [extra,withProbe,sz,countStep]
  | inr q =>
    obtain ⟨u,hu,rest⟩ := Option.bind_eq_some_iff.mp ran
    obtain ⟨v',hv,rest'⟩ := Option.bind_eq_some_iff.mp rest
    obtain ⟨z',hz',heq⟩ := Option.bind_eq_some_iff.mp rest'
    cases Option.some.inj heq
    obtain ⟨k,hk⟩ := sequence_exec D seed (clock t c) (select q) test (clear q) m hu hv hz'
    obtain ⟨z,hz,repz,b,sz⟩ := lift_exec ww (step D.step) k _ mem m c rep hk
    let extra := withProbe (.read addr (mem addr)) z
    refine ⟨extra,operation_of_fuel (fuel:=k+1) _ ?_,by simpa [countStep] using repz,b,?_⟩
    · change execute (wrapperStep addr act) (k+1) (.readCount _) mem=some extra
      rw [execute,wrapperStep]
      change (execute (wrapperStep addr act) k (.run (sequence D seed (clock t (mem addr).val) _ _ _)) mem).map _=_
      rw [wrapper_run,cc,hz]; rfl
    · simp [extra,withProbe,sz,countStep]

theorem block_result (seed : Ω) (t : ℕ) (h : History w) (op : Op N) {z : History w}
    (ran : runFrom D seed t h (block ins select clear test op)=some z) :
    ∃ r, blockResult D ins select clear test seed t h.memory op=some r ∧
      z.memory=r.memory ∧ z.probes=h.probes+r.trace.length := by
  cases op with
  | inl x =>
    cases hi : operation D seed t (.inl (ins x)) h.memory with
    | none => simp [block,runFrom,advance,hi] at ran
    | some u =>
      simp [block,runFrom,advance,hi] at ran; cases ran
      exact ⟨u,hi,rfl,rfl⟩
  | inr q =>
    cases hi : operation D seed t (.inl (select q)) h.memory with
    | none => simp [block,runFrom,advance,hi] at ran
    | some u =>
      cases hq : operation D seed (t+1) (.inr test) u.memory with
      | none => simp [block,runFrom,advance,hi,hq] at ran
      | some v' =>
        cases hd : operation D seed (t+2) (.inl (clear q)) v'.memory with
        | none => simp [block,runFrom,advance,hi,hq,hd] at ran
        | some z' =>
          simp [block,runFrom,advance,hi,hq,hd] at ran; cases ran
          exact ⟨⟨!v'.report,z'.memory,u.trace++v'.trace++z'.trace⟩,by simp [blockResult,hi,hq,hd],rfl,by simp [Nat.add_assoc]⟩

theorem history_append (D : Machine w F U Q Ω) (seed : Ω) (f : F) (p q : List (U ⊕ Q)) :
    history D seed f (p++q)=(history D seed f p).bind (fun h => runFrom D seed p.length h q) := by
  simp [history,runFrom_append,Option.bind_assoc]

theorem clock_block (ops : List (Op N)) :
    (ops.flatMap (block ins select clear test)).length=clock ops.length (insertions ops).length :=
  clock_history ops _ (by intro; rfl) (by intro; rfl)

theorem count_bound (ops : List (Op N)) (leg : legal ops) : (insertions ops).length≤N := by
  rw [←List.toFinset_card_of_nodup leg]
  exact (Finset.card_le_univ _).trans_eq (Fintype.card_fin N)

theorem prefix_legal (ops : List (Op N)) (op : Op N) (leg : legal (ops++[op])) : legal ops := by
  change (insertions (ops++[op])).Nodup at leg
  simp only [insertions,List.filterMap_append,List.nodup_append] at leg
  exact leg.1

theorem count_snoc (ops : List (Op N)) (op : Op N) :
    (insertions (ops++[op])).length=(insertions ops).length+countStep op := by
  cases op <;> simp [insertions,List.filterMap_append,countStep]

theorem histories (space : N<2^v) (seed : Ω) (f : Family N) (ops : List (Op N)) (leg : legal ops)
    {target : History w} (ok : history D seed (graph f) (ops.flatMap (block ins select clear test))=some target) :
    ∃ h,history (source ww D graph ins select clear test) seed f ops=some h ∧
      Encode ww h.memory target.memory (insertions ops).length ∧
      h.probes=target.probes+ops.length+(insertions ops).length := by
  induction ops using List.reverseRecOn generalizing target with
  | nil =>
    cases hi : D.init seed (graph f) with
    | none => simp [history,hi] at ok
    | some m =>
      simp [history,hi,runFrom] at ok; cases ok
      exact ⟨⟨initial ww m,0,none⟩,by simp [source,history,hi,runFrom],initialized ww m,rfl⟩
  | append_singleton ops op ih =>
    let blocks := ops.flatMap (block ins select clear test)
    have hx : history D seed (graph f) (blocks++block ins select clear test op)=some target := by
      simpa [blocks,List.flatMap_append] using ok
    rw [history_append] at hx
    obtain ⟨p,hp,tail⟩ := Option.bind_eq_some_iff.mp hx
    obtain ⟨h,haveH,rep,cost⟩ := ih (prefix_legal ops op leg) hp
    obtain ⟨r,rr,rm,rc⟩ := block_result D ins select clear test seed blocks.length p op tail
    have room := (count_bound _ leg).trans_lt space
    rw [count_snoc] at room
    have eql : blocks.length=clock ops.length (insertions ops).length := clock_block ins select clear test ops
    rw [eql] at rr
    obtain ⟨z,opok,repz,_,zc⟩ := source_operation ww D graph ins select clear test seed ops.length
      (insertions ops).length op p.memory h.memory rep room rr
    let next : History v := ⟨z.memory,h.probes+z.trace.length,op.elim (fun _ => none) (fun _ => some z.report)⟩
    refine ⟨next,?_,?_,?_⟩
    · rw [history_snoc,haveH]; simp [advance,opok,next]
    · rw [rm,count_snoc]; exact repz
    · dsimp [next]; rw [count_snoc,List.length_append]; simp only [List.length_cons,List.length_nil]
      omega

theorem source_halts (space : N<2^v) (seed : Ω) (f : Family N) (ops : List (Op N)) (leg : legal ops)
    (ok : (history D seed (graph f) (ops.flatMap (block ins select clear test))).isSome) :
    (history (source ww D graph ins select clear test) seed f ops).isSome := by
  obtain ⟨p,hp⟩ := Option.isSome_iff_exists.mp ok
  obtain ⟨h,hh,_⟩ := histories ww D graph ins select clear test space seed f ops leg hp
  simp [hh]

theorem total_good (space : N<2^v) (seed : Ω) (f : Family N) (ops : List (Op N)) (leg : legal ops)
    (ok : (history D seed (graph f) (ops.flatMap (block ins select clear test))).isSome) :
    totalCost (source ww D graph ins select clear test) seed f ops =
    totalCost D seed (graph f) (ops.flatMap (block ins select clear test))+ops.length+(insertions ops).length := by
  obtain ⟨p,hp⟩ := Option.isSome_iff_exists.mp ok
  obtain ⟨h,hh,_,counts⟩ := histories ww D graph ins select clear test space seed f ops leg hp
  simp [totalCost,hp,hh,counts]

/-- At any fixed source query, identify the physical middle graph query
and include every probe made by the following selector deletion. -/
theorem query_good (space : N<2^v) (seed : Ω) (f : Family N) (ops : List (Op N))
    (leg : legal ops) (q : Fin N)
    (ok : (history D seed (graph f) ((ops++[(Sum.inr q : Op N)]).flatMap (block ins select clear test))).isSome) :
    let S := source ww D graph ins select clear test
    let base := ops.flatMap (block ins select clear test)
    lastReport S seed f (ops++[(Sum.inr q : Op N)]) =
      (lastReport D seed (graph f) (base++[.inl (select q),.inr test])).map Bool.not ∧
    nextCost S seed f ops q =
      totalCost D seed (graph f) ((ops++[(Sum.inr q : Op N)]).flatMap (block ins select clear test)) -
        totalCost D seed (graph f) base + 1 := by
  intro S base
  obtain ⟨target,full⟩ := Option.isSome_iff_exists.mp ok
  have done : history D seed (graph f) (base++block ins select clear test (.inr q))=some target := by
    simpa [base,List.flatMap_append] using full
  rw [history_append] at done
  obtain ⟨p,hp,tail⟩ := Option.bind_eq_some_iff.mp done
  obtain ⟨r,rr,_,rc⟩ := block_result D ins select clear test seed base.length p (.inr q) tail
  obtain ⟨u,hu,rem⟩ := Option.bind_eq_some_iff.mp rr
  obtain ⟨v',hv,rem'⟩ := Option.bind_eq_some_iff.mp rem
  obtain ⟨z',hz',rval⟩ := Option.bind_eq_some_iff.mp rem'
  have report : r.report = !v'.report := congrArg Result.report (Option.some.inj rval).symm
  obtain ⟨h,hh,rep,_⟩ := histories ww D graph ins select clear test space seed f ops leg hp
  have eq : base.length=clock ops.length (insertions ops).length := clock_block ins select clear test ops
  rw [eq] at rr
  obtain ⟨z,zok,_,rb,zc⟩ := source_operation ww D graph ins select clear test seed ops.length _ (.inr q)
    p.memory h.memory rep (by simpa [countStep] using (count_bound ops leg).trans_lt space) rr
  have actual : history D seed (graph f) (base++[.inl (select q),.inr test]) =
      some ⟨v'.memory,p.probes+u.trace.length+v'.trace.length,some v'.report⟩ := by
    rw [history_append,hp]
    simp [runFrom,advance,hu,hv]
  change history S seed f ops=some h at hh
  change operation S seed ops.length (.inr q) h.memory=some z at zok
  constructor
  · simp [lastReport,history_snoc,hh,advance,zok,rb,report,actual]
  · unfold nextCost totalCost
    rw [hh,hp,full]
    simp [zok,zc,countStep,rc]

theorem report_good (space : N<2^v) (seed : Ω) (f : Family N) (ops : List (Op N)) (leg : legal ops)
    (q : Fin N) (ok : (history D seed (graph f) ((ops++[(Sum.inr q : Op N)]).flatMap (block ins select clear test))).isSome) :
    lastReport (source ww D graph ins select clear test) seed f (ops++[(Sum.inr q : Op N)]) =
      (lastReport D seed (graph f) (ops.flatMap (block ins select clear test)++[.inl (select q),.inr test])).map Bool.not :=
  (query_good ww D graph ins select clear test space seed f ops leg q ok).1

theorem next_good (space : N<2^v) (seed : Ω) (f : Family N) (ops : List (Op N)) (leg : legal ops)
    (q : Fin N) (ok : (history D seed (graph f) ((ops++[(Sum.inr q : Op N)]).flatMap (block ins select clear test))).isSome) :
    nextCost (source ww D graph ins select clear test) seed f ops q =
      totalCost D seed (graph f) ((ops++[(Sum.inr q : Op N)]).flatMap (block ins select clear test)) -
      totalCost D seed (graph f) (ops.flatMap (block ins select clear test)) + 1 :=
  (query_good ww D graph ins select clear test space seed f ops leg q ok).2

end
end AmortizedBound.TriangleReduction

/-! ## TriangleGraph -/

namespace AmortizedBound.TriangleGraph
open Dynamic GraphReductions DisjointnessFoundations DisjointnessDraft.Applications
open Graphs Classical MeasureTheory
noncomputable section
variable {V : Type}

abbrev Edges (V : Type) := V→V→Prop
abbrev Target (N p w : ℕ) (Ω : Type) := Machine w (Edges (Vertex N p)) (EdgeEdit (Vertex N p)) Unit Ω
def startGraph (f : Family N) : Edges (Vertex N p) := triangleGraph f (fun _=>False) none
def present (G : Edges V) := ∃a b c,G a b ∧ G b c ∧ G c a

def pair (a b u v : V) := (u=a ∧ v=b) ∨ (u=b ∧ v=a)
def applyEdit (G : Edges V) : EdgeEdit V → Edges V
  | .insert a b => fun u v=>G u v ∨ pair a b u v
  | .erase a b => fun u v=>G u v ∧ ¬pair a b u v
def step (G : Edges V) (op : EdgeEdit V ⊕ Unit) := op.elim (applyEdit G) (fun _=>G)
def after (G : Edges V) (ops : List (EdgeEdit V ⊕ Unit)) := ops.foldl step G

def validOp (G : Edges V) : EdgeEdit V ⊕ Unit → Prop
  | .inl (.insert a b) => a≠b ∧ ¬G a b
  | .inl (.erase a b) => a≠b ∧ G a b
  | .inr _ => True
def ValidHistory (G : Edges V) : List (EdgeEdit V ⊕ Unit) → Prop
  | [] => True
  | op::ops => validOp G op ∧ ValidHistory (step G op) ops

theorem valid_append (G : Edges V) (left right : List (EdgeEdit V⊕Unit)) :
    ValidHistory G (left++right) ↔ ValidHistory G left ∧ ValidHistory (after G left) right := by
  induction left generalizing G with
  | nil => simp [ValidHistory,after]
  | cons a l ih => simp [ValidHistory,ih,after,and_assoc]

theorem put_update (f : Family N) (X : Fin N→Prop) (x : Fin N) :
    applyEdit (triangleGraph (p:=p) f X none) (triUpdate x)=triangleGraph f (fun y=>X y ∨ y=x) none := by
  funext u v; apply propext
  rcases u with u|u|(_|u) <;> rcases v with v|v|(_|v) <;>
    simp [applyEdit,triUpdate,triangleGraph,directed,pair,sym,base,role,col,row,sink]

theorem put_select (f : Family N) (X : Fin N→Prop) (q : Fin N) :
    applyEdit (triangleGraph (p:=p) f X none) (triSelect q)=triangleGraph f X (some q) := by
  funext u v; apply propext
  simp [applyEdit,triSelect,triangleGraph,pair,or_comm]

theorem put_clear (f : Family N) (X : Fin N→Prop) (q : Fin N) :
    applyEdit (triangleGraph (p:=p) f X (some q)) (triClear q)=triangleGraph f X none := by
  funext u v; apply propext
  rcases u with u|u|(_|u) <;> rcases v with v|v|(_|v) <;>
    simp [applyEdit,triClear,triangleGraph,directed,pair,sym,base,role,col,row,sink]

theorem after_expansion (f : Family N) (h : List (Op N)) :
    after (startGraph (p:=p) f) (h.flatMap triOps)=triangleGraph f (fun x=>x∈insertions h) none := by
  induction h using List.reverseRecOn with
  | nil => simp [startGraph,insertions,after]
  | append_singleton l op ih =>
    simp only [List.flatMap_append,List.flatMap_singleton,after,List.foldl_append] at *
    rw [ih]; cases op with
    | inl x =>
      simp only [triOps,List.foldl_cons,List.foldl_nil,step,Sum.elim_inl,put_update]
      have eq : (fun y=>y∈insertions l ∨ y=x)=(fun y=>y∈insertions (l++[.inl x])) := by
        funext y; apply propext; simp [insertions,List.filterMap_append]
      rw [eq]
    | inr q => simp [triOps,step,put_select,put_clear,insertions,List.filterMap_append]

theorem true_answer (f : Family N) (h : List (Op N)) (q : Fin N) :
    decide (present (after (startGraph (p:=p) f) (h.flatMap triOps++[.inl (triSelect q)])))=!(answer f h q) := by
  have state := after_expansion (p:=p) f h
  simp only [after,List.foldl_append,List.foldl_cons,List.foldl_nil,step,Sum.elim_inl] at state ⊢
  rw [state,put_select]
  have equiv : present (triangleGraph (p:=p) f (fun x=>x∈insertions h) (some q)) ↔ Hit (incidence f) (fun x=>x∈insertions h) q :=
    triangle_hit f (fun x=>x∈insertions h) q
  rw [propext equiv]
  apply Bool.eq_iff_iff.mpr
  simp [Hit,incidence,answer]; tauto

theorem valid_block (f : Family N) (X : Fin N→Prop) (op : Op N)
    (fresh : ∀x,op=.inl x→¬X x) :
    ValidHistory (triangleGraph (p:=p) f X none) (triOps op) := by
  cases op with
  | inl x =>
    simp [ValidHistory,validOp,triOps,triUpdate,triangleGraph,directed,sym,role,base,col,sink,fresh x rfl]
  | inr q =>
    simp only [ValidHistory,validOp,triOps,step,Sum.elim_inl,Sum.elim_inr,put_select,put_clear]
    simp [triSelect,triClear,triangleGraph,directed,sym,role,base,row,sink]

theorem legal_expansion (f : Family N) (h : List (Op N)) (ok : legal h) :
    ValidHistory (startGraph (p:=p) f) (h.flatMap triOps) := by
  induction h using List.reverseRecOn with
  | nil => trivial
  | append_singleton l op ih =>
    rw [List.flatMap_append,List.flatMap_singleton,valid_append,after_expansion]
    have ins : insertions (l++[op])=insertions l++insertions [op] := by simp [insertions,List.filterMap_append]
    unfold legal at ok; rw [ins,List.nodup_append] at ok
    refine ⟨ih ok.1,valid_block _ _ _ ?_⟩
    rintro x rfl hx
    exact ok.2.2 hx (by simp [insertions])

theorem legal_middle (f : Family N) (h : List (Op N)) (q : Fin N) (ok : legal h) :
    ValidHistory (startGraph (p:=p) f) (h.flatMap triOps++[.inl (triSelect q),.inr ()]) := by
  rw [valid_append,after_expansion]
  refine ⟨legal_expansion f h ok,?_⟩
  simp [ValidHistory,validOp,step,triSelect,triangleGraph,directed,sym,role,base,row,sink]

def Simple (G : Edges V) : Prop := Symmetric G ∧ Irreflexive G

theorem start_simple (f : Family N) : Simple (startGraph (p:=p) f) := by
  constructor
  · intro u v uv
    change triangleGraph f (fun _=>False) none u v at uv
    simpa [startGraph,triangleGraph,sym,or_comm] using uv
  · intro u; rcases u with u|u|(_|u) <;> simp [startGraph,triangleGraph,directed,sym,role,base]

structure Correct {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω) (D : Target N p w Ω) : Prop where
  terminates : ∀ G, Simple G → ∀ ops, ValidHistory G ops → ∀ᵐ a ∂μ, (history D a G ops).isSome
  measurableCost : ∀ G, Simple G → ∀ ops, ValidHistory G ops → Measurable (fun a => totalCost D a G ops)
  measurableReport : ∀ G, Simple G → ∀ h b, ValidHistory G (h++[.inr ()]) →
    MeasurableSet {a | lastReport D a G (h++[.inr ()])=some b}
  perQuery : ∀ G, Simple G → ∀ h, ValidHistory G (h++[.inr ()]) →
    μ {a | lastReport D a G (h++[.inr ()]) ≠ some (decide (present (after G h)))}≤Dynamic.error

end
end AmortizedBound.TriangleGraph

/-! ## GraphGeometry -/

/-! Walk depth, acyclicity, and actual edge bounds on the hard graphs. -/
namespace AmortizedBound.GraphGeometry
open GraphReductions Dynamic Finset Real
open DisjointnessDraft.Applications Graphs
open Classical
noncomputable section

def level : Vertex N p → ℕ
  | .inl _ => 0
  | .inr (.inl _) => 1
  | .inr (.inr none) => 2
  | .inr (.inr (some _)) => 0

theorem step_level {f : Family N} {X : Fin N→Prop} {u v : Vertex N p} (e : directed f X u v) :
    level v=level u+1 := by
  rcases u with u|u|(_|u) <;> rcases v with v|v|(_|v) <;> simp_all [level,directed,role,base]

theorem walk_level {f : Family N} {X : Fin N→Prop} {u v : Vertex N p} {d : ℕ}
    (w : Walk (directed f X) u d v) : level v=level u+d := by
  induction w with
  | nil => omega
  | cons h _ ih => have e := step_level h; omega

theorem directed_depth {f : Family N} {X : Fin N→Prop} {u v : Vertex N p} {d : ℕ}
    (w : Walk (directed f X) u d v) : d≤2 := by
  have upper : level v≤2 := by rcases v with v|v|(_|v) <;> norm_num [level]
  have := walk_level w
  omega

theorem acyclic {f : Family N} {X : Fin N→Prop} {u : Vertex N p} {d : ℕ}
    (w : Walk (directed f X) u d u) : d=0 := by have := walk_level w; omega

/-- Directed pairs are counted even when the graph represents undirected
edges, so the same upper bound also bounds the number of undirected edges. -/
def arcs {V : Type} [Fintype V] (G : V→V→Prop) : Finset (V×V) := univ.filter (fun z => G z.1 z.2)

def incidencePairs (f : Family N) : Finset (Vertex N p × Vertex N p) :=
  univ.biUnion (fun q => (f q).image (fun x => (row q,col x)))

def sinkPairs (N p : ℕ) : Finset (Vertex N p × Vertex N p) := univ.image (fun x => (col x,sink))

theorem incidence_count (f : Family N) (hf : hardFamilies N f) :
    (incidencePairs (p:=p) f).card ≤ N*hardSize N := by
  unfold incidencePairs
  simpa using Finset.card_biUnion_le_card_mul (univ : Finset (Fin N)) (fun q => (f q).image
    (fun x => (row (p:=p) q,col x))) (hardSize N) (fun q _ => card_image_le.trans (hf q).le)

theorem directed_count (f : Family N) (hf : hardFamilies N f) (X : Fin N→Prop) :
    (arcs (directed (p:=p) f X)).card ≤ N*hardSize N+N := by
  have sub : arcs (directed (p:=p) f X) ⊆ incidencePairs f ∪ sinkPairs N p := by
    rintro ⟨a,b⟩ hz
    have edge := (mem_filter.mp hz).2
    rcases a with a|a|(_|a) <;> rcases b with b|b|(_|b) <;> simp_all [directed,role,base,incidence]
    · exact Or.inl (mem_biUnion.mpr ⟨a,mem_univ _,mem_image.mpr ⟨b,edge,rfl⟩⟩)
    · exact Or.inr (mem_image.mpr ⟨a,mem_univ _,rfl⟩)
  have links : (sinkPairs N p).card ≤ N := by
    unfold sinkPairs
    simpa using (card_image_le (s:=univ) (f:=fun x : Fin N => (col (p:=p) x,sink)))
  exact (card_le_card sub).trans ((card_union_le ..).trans (Nat.add_le_add (incidence_count f hf) links))

private theorem sym_count {V : Type} [Fintype V] (G : V→V→Prop) :
    (arcs (sym G)).card ≤ 2*(arcs G).card := by
  have sub : arcs (sym G) ⊆ arcs G ∪ (arcs G).image Prod.swap := by
    rintro ⟨a,b⟩ h
    obtain h|h := (mem_filter.mp h).2
    · exact mem_union_left _ (mem_filter.mpr ⟨mem_univ _,h⟩)
    · exact mem_union_right _ (mem_image.mpr ⟨(b,a),mem_filter.mpr ⟨mem_univ _,h⟩,rfl⟩)
  exact (card_le_card sub).trans ((card_union_le ..).trans (by
    have h := card_image_le (s:=arcs G) (f:=Prod.swap); omega))

theorem fixed_count (f : Family N) (hf : hardFamilies N f) :
    (arcs (fixedGraph (p:=p) f)).card ≤ 2*(N*hardSize N+N) :=
  (sym_count (directed f (fun _ => True))).trans (Nat.mul_le_mul_left 2 (directed_count f hf _))

theorem triangle_count (f : Family N) (hf : hardFamilies N f) (X : Fin N→Prop) (sel : Option (Fin N)) :
    (arcs (triangleGraph (p:=p) f X sel)).card ≤ 2*(N*hardSize N+N)+2 := by
  have basic := (sym_count (directed (p:=p) f X)).trans (Nat.mul_le_mul_left 2 (directed_count f hf X))
  cases sel with
  | none => simp [arcs,triangleGraph] at basic ⊢; omega
  | some q =>
    let extra : Finset (Vertex N p × Vertex N p) := {(row q,sink),(sink,row q)}
    have sub : arcs (triangleGraph f X (some q)) ⊆ arcs (sym (directed f X)) ∪ extra := by
      rintro ⟨a,b⟩ h
      obtain e|⟨r,eq,e⟩ := (mem_filter.mp h).2
      · exact mem_union_left _ (mem_filter.mpr ⟨mem_univ _,e⟩)
      · cases eq
        apply mem_union_right
        rcases e with ⟨rfl,rfl⟩|⟨rfl,rfl⟩ <;> simp [extra]
    have e2 : extra.card≤2 := Finset.card_le_two
    exact (card_le_card sub).trans ((card_union_le ..).trans (Nat.add_le_add basic e2))

theorem sparse {N p : ℕ} (N1 : 1≤N) :
    ((2*(N*hardSize N+N)+2:ℕ):ℝ) ≤ 6*(graphSize N p:ℝ)^(5/4:ℝ) := by
  let V := graphSize N p
  have natural : N≤V := by unfold V graphSize; omega
  have NV : (N:ℝ)≤V := by exact_mod_cast natural
  have VP : (1:ℝ)≤V := by exact_mod_cast (show 1≤V by omega)
  have vpos : 0<(V:ℝ) := by linarith
  have root : (hardSize N:ℝ)≤(V:ℝ)^(1/4:ℝ) := root_lower N p
  have root1 := Real.one_le_rpow VP (by norm_num : (0:ℝ)≤1/4)
  have c1 := mul_le_mul NV root (Nat.cast_nonneg _) (Nat.cast_nonneg _)
  have c2 := mul_le_mul_of_nonneg_left root1 (Nat.cast_nonneg (α:=ℝ) V)
  have eq : (V:ℝ)*(V:ℝ)^(1/4:ℝ)=(V:ℝ)^(5/4:ℝ) := by rw [mul_comm,←rpow_add_one vpos.ne']; norm_num
  change ((2*(N*hardSize N+N)+2:ℕ):ℝ) ≤ 6*(V:ℝ)^(5/4:ℝ)
  rw [←eq]; push_cast
  nlinarith only [c1,c2,NV,VP]

end
end AmortizedBound.GraphGeometry

/-! ## GraphCorollaries -/

/-! Consequences of the unconditional dynamic lower bounds for every
sufficiently large graph size, including both parities. -/
namespace AmortizedBound.GraphCorollaries
open GraphReductions Dynamic Filter Real MeasureTheory
open scoped ENNReal
noncomputable section

def side (V : ℕ) := (V-1)/2
def extra (V : ℕ) := V-(2*side V+1)

theorem exact_vertices {V : ℕ} (v : 0<V) : graphSize (side V) (extra V)=V := by
  simp only [graphSize,extra,side]; omega

theorem disjointness_maximum (lo hi : ℝ) (lp : 0<lo) (lh : lo≤hi) :
    ∃ c : ℝ, 0<c ∧ ∀ tu : ℕ→ℝ, (∀ᶠ N : ℕ in atTop, 1≤tu N) → Subpolynomial tu → ∀ᶠ N : ℕ in atTop, ∀ w, wordSize lo hi N w → ∀ tq : ℝ, 0≤tq →
      ∀ (Ω : Type) [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ] (D : DataStructure N w Ω),
      Correct μ D (hardFamilies N) (singleHistories N) → PrefixBudgets μ D (tu N) tq →
      c*totalScale N ≤ max (tu N) tq :=
  maximum_of_query AmortizedBound.query_tradeoff lo hi lp lh

theorem total_work (lo hi : ℝ) (lp : 0<lo) (lh : lo≤hi) :
    ∃ c : ℝ, 0<c ∧ ∀ᶠ V : ℕ in atTop, ∀w, wordSize lo hi V w →
      ∀ (k : Incremental) (Ω : Type) [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
        (D : GraphMachine (side V) (extra V) w Ω), GraphCorrect μ D k legal →
      ENNReal.ofReal (c*(V:ℝ)^(1/4:ℝ)*totalScale V)≤graphWork μ D k := by
  obtain ⟨c,cp,h⟩ := incremental_total AmortizedBound.total_work lo hi lp lh
  refine ⟨c,cp,?_⟩
  have allV := eventual_vertices _ h
  filter_upwards [allV,eventually_ge_atTop 1] with V lower vp
  have eq := exact_vertices vp
  change graphSize ((V-1)/2) (V-(2*((V-1)/2)+1))=V at eq
  simpa only [eq] using lower

theorem query_tradeoff (lo hi : ℝ) (lp : 0<lo) (lh : lo≤hi) :
    ∃ c : ℝ, 0<c ∧ ∀ tu : ℕ→ℝ, (∀ᶠ V : ℕ in atTop,1≤tu V) → Subpolynomial tu → ∀ᶠ V : ℕ in atTop, ∀w, wordSize lo hi V w → ∀ tq : ℝ,0≤tq →
      ∀ (k : Incremental) (Ω : Type) [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
        (D : GraphMachine (side V) (extra V) w Ω), GraphCorrect μ D k (singleHistories (side V)) →
        UpdateQueryCost μ D k (tu V) tq → c*ratio V w (tu V)≤tq := by
  obtain ⟨c,cp,h⟩ := incremental_query AmortizedBound.query_tradeoff lo hi lp lh
  refine ⟨c,cp,fun tu unit sub => ?_⟩
  have allV := eventual_vertices _ (h tu unit sub)
  filter_upwards [allV,eventually_ge_atTop 1] with V lower vp
  have eq := exact_vertices vp
  change graphSize ((V-1)/2) (V-(2*((V-1)/2)+1))=V at eq
  simpa only [eq] using lower

theorem maximum (lo hi : ℝ) (lp : 0<lo) (lh : lo≤hi) :
    ∃ c : ℝ, 0<c ∧ ∀ᶠ V : ℕ in atTop, ∀w, wordSize lo hi V w →
      ∀ (k : Incremental) (Ω : Type) [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
        (D : GraphMachine (side V) (extra V) w Ω), GraphCorrect μ D k legal →
      ∀tu tq : ℝ, 0≤tu → 0≤tq →
      (∀ z : Input (hardSize (side V)) (side V),
        (∫⁻ coin,totalCost D coin (config k (fun q => rowSet (active_fits _) (z.1 q)) (fun _=>False))
          ((schedule (active_fits _) z.2.1 z.2.2).map (targetOp k)) ∂μ) ≤
          ENNReal.ofReal ((hardSize (side V):ℝ)*(tu+tq))) →
      c*totalScale V ≤ max tu tq := by
  obtain ⟨d,dp,lb⟩ := total_work lo hi lp lh
  refine ⟨d/2,by positivity,?_⟩
  filter_upwards [lb,eventually_ge_atTop 33] with V low large
  intro w ww k Ω _ μ _ D valid tu tq ut qt cost
  have npos : 0<hardSize (side V) := by
    apply Nat.le_sqrt'.mpr
    apply Nat.le_sqrt'.mpr
    unfold side; norm_num; omega
  have eq := exact_vertices (by omega : 0<V)
  have h := low w ww k Ω μ D valid
  have ub := graph_work_budget npos μ D k cost
  have fin := maximum_from_graph_work (N:=side V) (p:=extra V) (tu:=tu) (tq:=tq) dp 1 npos (graphWork μ D k) (by rw [eq]; exact h) (by simpa using ub) ut qt
  norm_num [eq] at fin ⊢; exact fin

end
end AmortizedBound.GraphCorollaries

/-! ## TriangleCorollary -/

/-! Changing the physical word size for the triangle reduction, and absorbing
its count-word probes into the asymptotic bound in the actual vertex count. -/
namespace AmortizedBound.TriangleCorollary
open Dynamic GraphReductions MeasureTheory Filter Real DisjointnessFoundations
open scoped ENNReal
open Classical
noncomputable section

def width (N w : ℕ) := w + ⌈logb 2 N⌉₊ + 2

theorem place (N w : ℕ) (np : 0<N) : w<width N w ∧ N<2^width N w := by
  constructor
  · dsimp [width]; omega
  · have hp : (0:ℝ)<N := by exact_mod_cast np
    have h : logb 2 N < (width N w:ℝ) := by
      have floor := Nat.le_ceil (logb 2 N)
      simp only [width,Nat.cast_add,Nat.cast_ofNat]
      linarith [Nat.cast_nonneg (α:=ℝ) w]
    have b := rpow_lt_rpow_of_exponent_lt (by norm_num : (1:ℝ)<2) h
    rw [rpow_logb (by norm_num) (by norm_num) hp,rpow_natCast] at b
    exact_mod_cast b

theorem word_bounds {lo hi : ℝ} (lp : 0<lo) (hp : 0<hi) {N p w : ℕ} (n3 : 3≤N)
    (pad : p≤1) (lg : 2≤logb 2 N) (ww : wordSize lo hi (graphSize N p) w) :
    wordSize lo (2*hi+3) N (width N w) := by
  obtain ⟨_,_,l,u⟩ := size_limits n3 pad
  have low := (mul_le_mul_of_nonneg_left l lp.le).trans ww.1
  have high := ww.2.trans (mul_le_mul_of_nonneg_left u hp.le)
  have add := Nat.ceil_lt_add_one (show 0≤logb 2 N by linarith)
  unfold width wordSize
  push_cast
  exact ⟨by linarith [Nat.cast_nonneg (α:=ℝ) ⌈logb 2 (N:ℝ)⌉₊],by nlinarith⟩

theorem overhead (d : ℝ) (dp : 0<d) : ∀ᶠ N : ℕ in atTop, 6≤d*totalScale N := by
  let A := 6/d+1
  have Ap : 0<A := by dsimp [A]; positivity
  have ep : 0<log 2/A := by positivity
  have sub := Tradeoff.log_tends.eventually (Real.isLittleO_log_id_atTop.bound ep)
  filter_upwards [sub,Tradeoff.log_tends.eventually_ge_atTop 2] with N h low
  let x := logb 2 N
  have x2 : 2≤x := low
  have xp : 0<x := by linarith
  have lpos : 0<logb 2 x := logb_pos (by norm_num) (by linarith)
  change ‖log x‖ ≤ log 2/A*‖x‖ at h
  rw [Real.norm_eq_abs,abs_of_nonneg (Real.log_nonneg (by linarith)),Real.norm_eq_abs,abs_of_nonneg xp.le] at h
  have l2 : 0<log 2 := log_pos (by norm_num)
  have upper : logb 2 x ≤ x/A := (div_le_iff₀ l2).mpr (h.trans_eq (by ring))
  have comp : A≤x/logb 2 x := (le_div_iff₀ lpos).mpr
    (by simpa only [mul_comm] using (le_div_iff₀ Ap).mp upper)
  have one : 1≤A := by dsimp [A]; linarith [div_pos (by norm_num : (0:ℝ)<6) dp]
  have square : A≤(x/logb 2 x)^2 := comp.trans (by nlinarith only [one.trans comp,sq_nonneg (x/logb 2 x-1)])
  have z := mul_le_mul_of_nonneg_left square dp.le
  have formal : d*A=6+d := by dsimp [A]; field_simp
  change 6≤d*(x/logb 2 x)^2
  rw [formal] at z
  exact (le_add_of_nonneg_right dp.le).trans z

theorem absorb {d : ℝ} (dp : 0<d) {N p : ℕ} (N3 : 3≤N) (pad : p≤1)
    (root : 1≤hardSize N) (lg : 2≤logb 2 N) (large : 6≤d*totalScale N)
    {work : ℝ≥0∞} (charged : ENNReal.ofReal (d*hardSize N*totalScale N)≤work+3*hardSize N) :
    ENNReal.ofReal ((d/32)*(graphSize N p:ℝ)^(1/4:ℝ)*totalScale (graphSize N p)) ≤ work := by
  by_cases top : work=⊤
  · simp [top]
  have h := ENNReal.toReal_mono (show work+3*hardSize N≠⊤ by finiteness) charged
  have nn : 0≤totalScale N := sq_nonneg _
  have vn : 0≤totalScale (graphSize N p) := sq_nonneg _
  have src : 0≤d*hardSize N*totalScale N := by positivity
  rw [ENNReal.toReal_ofReal src,ENNReal.toReal_add top (by finiteness),ENNReal.toReal_mul] at h
  simp only [ENNReal.toReal_ofNat,ENNReal.toReal_natCast] at h
  have rent := mul_le_mul_of_nonneg_right large (Nat.cast_nonneg (α:=ℝ) (hardSize N))
  have gain := mul_le_mul (root_limit root pad) (scale_limit N3 pad lg) vn (by positivity)
  have lower := mul_le_mul_of_nonneg_left gain (show 0≤d/32 by positivity)
  apply (ENNReal.ofReal_le_ofReal ?_).trans_eq (ENNReal.ofReal_toReal top)
  nlinarith only [rent,h,lower]

/-- Reindexing public tapes leaves every physical trace unchanged at its chosen tape. -/
def reindex (f : K→Ω) (D : Machine w F U Q Ω) : Machine w F U Q K :=
  ⟨D.State,fun k => D.init (f k),fun k => D.start (f k),D.step⟩

theorem run_reindex (f : K→Ω) (D : Machine w F U Q Ω) (k t s ops) :
    runFrom (reindex f D) k t s ops=runFrom D (f k) t s ops := by
  induction ops generalizing t s with
  | nil => rfl
  | cons op ops ih =>
    simp only [runFrom]
    exact congrArg ((advance D (f k) t op s).bind) (funext fun v => ih (t+1) v)

theorem history_reindex (f : K→Ω) (D : Machine w F U Q Ω) (k fam ops) :
    history (reindex f D) k fam ops=history D (f k) fam ops := by
  simp only [history,reindex]
  exact congrArg ((D.init (f k) fam).bind) (funext fun m => run_reindex f D k 0 ⟨m,0,none⟩ ops)

theorem total_reindex (f : K→Ω) (D : Machine w F U Q Ω) (k fam ops) :
    totalCost (reindex f D) k fam ops=totalCost D (f k) fam ops := by simp only [totalCost,history_reindex]

theorem report_reindex (f : K→Ω) (D : Machine w F U Q Ω) (k fam ops) :
    lastReport (reindex f D) k fam ops=lastReport D (f k) fam ops := by simp only [lastReport,history_reindex]

theorem halt_iff (D : Machine w F U Q Ω) (k fam ops) :
    (history D k fam ops).isSome ↔ totalCost D k fam ops≠⊤ := by
  cases h : history D k fam ops <;> simp [totalCost,h]

theorem next_delta (D : Machine w F U Q Ω) (k fam ops q) (done : (history D k fam (ops++[.inr q])).isSome) :
    nextCost D k fam ops q=totalCost D k fam (ops++[.inr q])-totalCost D k fam ops := by
  simp only [totalCost,nextCost,history_snoc] at done ⊢
  cases h : history D k fam ops with
  | none => simp [h] at done
  | some st =>
    cases z : operation D k ops.length (.inr q) st.memory with
    | none => simp [h,advance,z] at done
    | some r => simp [h,advance,z,add_comm]

open TriangleGraph
variable {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (D : Target N p w Ω) (C : TriangleGraph.Correct μ D)

abbrev HistCases (N : ℕ) := {z : Family N × List (Op N) // legal z.2}
def goodTape (a : Ω) := ∀ z : HistCases N, (history D a (startGraph z.1.1) (z.1.2.flatMap triOps)).isSome

include C in
omit [IsProbabilityMeasure μ] in
theorem good_ae : ∀ᵐ a ∂μ, goodTape D a := ae_all_iff.mpr fun z =>
  C.terminates _ (start_simple _) _ (legal_expansion _ _ z.2)

include C in
omit [IsProbabilityMeasure μ] in
theorem good_measurable : MeasurableSet {a | goodTape D a} := by
  unfold goodTape
  simp only [Set.setOf_forall]
  refine MeasurableSet.iInter fun z => ?_
  have m := C.measurableCost _ (start_simple z.1.1) _ (legal_expansion _ _ z.2)
  simpa only [halt_iff] using (m (measurableSet_singleton (⊤:ℝ≥0∞))).compl

def chooseTape (a : Ω) : Ω := if goodTape D a then a else (good_ae μ D C).exists.choose

theorem choose_measurable : Measurable (chooseTape μ D C) :=
  Measurable.ite (good_measurable μ D C) measurable_id measurable_const

theorem choose_ae : ∀ᵐ a ∂μ,chooseTape μ D C a=a :=
  (good_ae μ D C).mono fun _ ha => if_pos ha

theorem choose_good (a : Ω) : goodTape D (chooseTape μ D C a) := by
  unfold chooseTape
  split <;> rename_i h
  · exact h
  · exact (good_ae μ D C).exists.choose_spec

private theorem blocks : TriangleReduction.block (triUpdate (p:=p)) triSelect triClear ()=triOps (N:=N) := by
  funext x
  cases x <;> rfl

def simulation : DataStructure N (width N w) Ω :=
  reindex (chooseTape μ D C) (TriangleReduction.source (v:=width N w) (by unfold width; omega) D
    startGraph triUpdate triSelect triClear ())

theorem halts (np : 0<N) (a : Ω) (f : Family N) (ops : List (Op N)) (ok : legal ops) :
    (history (simulation μ D C) a f ops).isSome := by
  unfold simulation
  rw [history_reindex]
  apply TriangleReduction.source_halts _ _ _ _ _ _ _ (place N w np).2 _ _ _ ok
  rw [blocks]
  exact choose_good μ D C a ⟨(f,ops),ok⟩

theorem total (np : 0<N) (a : Ω) (f : Family N) (ops : List (Op N)) (ok : legal ops) :
    totalCost (simulation μ D C) a f ops=
    totalCost D (chooseTape μ D C a) (startGraph f) (ops.flatMap triOps)+ops.length+(insertions ops).length := by
  unfold simulation
  rw [total_reindex, TriangleReduction.total_good _ _ _ _ _ _ _ (place N w np).2 _ _ _ ok]
  · rw [blocks]
  · rw [blocks]; exact choose_good μ D C a ⟨(f,ops),ok⟩

theorem measurable_total (np : 0<N) (f : Family N) (ops : List (Op N)) (ok : legal ops) :
    Measurable (fun a=>totalCost (simulation μ D C) a f ops) := by
  simp_rw [total μ D C np _ _ _ ok]
  exact (((C.measurableCost _ (start_simple f) _ (legal_expansion f ops ok)).comp (choose_measurable μ D C)).add_const _).add_const _

def work : ℝ≥0∞ :=
  let n := hardSize N
  (∑ z : Input n N, ∫⁻ a,totalCost D a (startGraph (fun q=>rowSet (active_fits N) (z.1 q)))
    ((schedule (active_fits N) z.2.1 z.2.2).flatMap triOps) ∂μ) / Fintype.card (Input n N)

theorem work_source (np : 0<N) : interleavedWork μ (simulation μ D C) = work μ D+3*hardSize N := by
  let n := hardSize N
  let c (z : Input n N) (a : Ω) := totalCost D a (startGraph (fun q=>rowSet (active_fits N) (z.1 q)))
    ((schedule (active_fits N) z.2.1 z.2.2).flatMap triOps)
  let s (z : Input n N) (a : Ω) := totalCost (simulation μ D C) a (fun q=>rowSet (active_fits N) (z.1 q))
    (schedule (active_fits N) z.2.1 z.2.2)
  have point (z : Input n N) : ∀ᵐ a ∂μ, s z a=c z a+3*n := by
    filter_upwards [choose_ae μ D C] with a ha
    obtain ⟨len,leg⟩ := schedule_properties (active_fits N) z.2.1 z.2.2
    have ins : (insertions (schedule (active_fits N) z.2.1 z.2.2)).length=n := by
      let go (xs : List (Fin n)) := xs.flatMap fun i => ([.inl (address (active_fits N) i (z.2.1 i)),.inr (z.2.2 i)] : List (Op N))
      have size (xs : List (Fin n)) : (insertions (go xs)).length=xs.length := by
        induction xs with
        | nil => rfl
        | cons t xs ih => simpa [go,insertions,List.filterMap_append] using congrArg Nat.succ ih
      simpa [go,schedule] using size (List.finRange n)
    simp only [s,c,total μ D C np _ _ _ leg,ha,len,ins,Nat.cast_mul,Nat.cast_ofNat]
    ring
  have integral (z : Input n N) : (∫⁻ a,s z a ∂μ) = (∫⁻ a,c z a ∂μ)+3*n := by
    rw [lintegral_congr_ae (point z),lintegral_add_right _ measurable_const,lintegral_const,measure_univ,mul_one]
  letI : Nonempty (Fin N) := ⟨⟨0,np⟩⟩
  haveI : Nonempty (Input n N) := ⟨(fun _=>id,id,fun _=>Classical.choice inferInstance)⟩
  have card : (Fintype.card (Input n N) : ℝ≥0∞)≠0 := by exact_mod_cast Fintype.card_ne_zero
  change (∑ z : Input n N, ∫⁻ a,s z a ∂μ) / Fintype.card (Input n N)=
    (∑ z : Input n N, ∫⁻ a,c z a ∂μ) / Fintype.card (Input n N)+3*n
  simp_rw [integral]
  rw [Finset.sum_add_distrib,ENNReal.add_div]
  congr 1
  simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul]
  rw [mul_comm,ENNReal.mul_div_cancel_right card (by finiteness)]

private theorem prefix_ok (ops : List (Op N)) (q : Fin N) : legal (ops++[.inr q]) ↔ legal ops := by
  simp [legal,insertions,List.filterMap_append]

theorem report (np : 0<N) (a : Ω) (f : Family N) (ops : List (Op N)) (q : Fin N) (ok : legal ops) :
    lastReport (simulation μ D C) a f (ops++[.inr q]) =
    (lastReport D (chooseTape μ D C a) (startGraph f) (ops.flatMap triOps++[.inl (triSelect q),.inr ()])).map Bool.not := by
  unfold simulation
  rw [report_reindex,TriangleReduction.report_good _ _ _ _ _ _ _ (place N w np).2 _ _ _ ok q]
  · rw [blocks]
  · rw [blocks]; exact choose_good μ D C a ⟨(f,ops++[.inr q]),(prefix_ok ops q).mpr ok⟩

private theorem flip (z : Option Bool) (b : Bool) : z.map Bool.not=some b ↔ z=some (!b) := by
  cases z with | none => simp | some x => cases x <;> cases b <;> decide

theorem correct_simulation (np : 0<N) :
    Dynamic.Correct μ (simulation μ D C) (hardFamilies N) legal where
  terminates f _ ops ok := ae_of_all μ (fun a => halts μ D C np a f ops ok)
  measurableCost f _ ops ok := measurable_total μ D C np f ops ok
  measurableQuery f _ ops q ok := by
    have m := measurable_total μ D C np f (ops++[.inr q]) ok
    have e := measurable_total μ D C np f ops ((prefix_ok ops q).mp ok)
    simp_rw [next_delta _ _ _ _ _ (halts μ D C np _ f (ops++[.inr q]) ok)]
    exact m.sub e
  measurableReport f _ ops q b ok := by
    have pre := (prefix_ok ops q).mp ok
    have legalGraph := legal_middle (p:=p) f ops q pre
    have measurableReport := C.measurableReport _ (start_simple f) (ops.flatMap triOps++[.inl (triSelect q)]) (!b)
      (by simpa only [List.append_assoc,List.singleton_append] using legalGraph)
    simp_rw [report μ D C np _ f ops q pre,flip]
    exact (choose_measurable μ D C) (by simpa only [List.append_assoc,List.singleton_append] using measurableReport)
  perQuery f _ ops q ok := by
    have pre := (prefix_ok ops q).mp ok
    have legalGraph := legal_middle (p:=p) f ops q pre
    have risk := C.perQuery _ (start_simple f) (ops.flatMap triOps++[.inl (triSelect q)])
      (by simpa only [List.append_assoc,List.singleton_append] using legalGraph)
    simp only [true_answer,List.append_assoc,List.singleton_append] at risk
    refine (measure_congr ?_).le.trans risk
    filter_upwards [choose_ae μ D C] with a ha
    apply propext
    change (lastReport (simulation μ D C) a f (ops++[.inr q]) ≠ some (answer f ops q)) ↔ _
    rw [report μ D C np a f ops q pre,ha]
    exact not_congr (flip _ _)

theorem triangle_total (lo hi : ℝ) (lp : 0<lo) (lh : lo≤hi) :
    ∃ c : ℝ, 0<c ∧ ∀ᶠ N : ℕ in atTop, ∀ p≤1, ∀ w, wordSize lo hi (graphSize N p) w →
      ∀ (Ω : Type) [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ] (D : Target N p w Ω),
      TriangleGraph.Correct μ D →
      ENNReal.ofReal (c*(graphSize N p:ℝ)^(1/4:ℝ)*totalScale (graphSize N p)) ≤ work μ D := by
  obtain ⟨d,dp,lower⟩ := AmortizedBound.total_work lo (2*hi+3) lp (by linarith)
  refine ⟨d/32,by positivity,?_⟩
  filter_upwards [lower,overhead d dp,eventually_ge_atTop 16,Tradeoff.log_tends.eventually_ge_atTop 2]
    with N lb large N16 lg
  intro p pad w ww Ω _ μ _ D C
  have pos : 0<N := by omega
  have hh : 1≤hardSize N := by apply Nat.le_sqrt'.mpr; apply Nat.le_sqrt'.mpr; norm_num; omega
  have widths := word_bounds lp (lp.trans_le lh) (by omega : 3≤N) pad lg ww
  have h := lb (width N w) widths Ω μ (simulation μ D C) (correct_simulation μ D C pos)
  rw [work_source μ D C pos] at h
  exact absorb dp (by omega) pad hh lg large h

/-- Every sufficiently large number of vertices is realized, with at most
one isolated padding vertex. The distribution uses three edge edits and
one test per insertion/query pair. -/
theorem triangle_vertices (lo hi : ℝ) (lp : 0<lo) (lh : lo≤hi) :
    ∃ c : ℝ, 0<c ∧ ∀ᶠ V : ℕ in atTop,
      let N := (V-1)/2
      let p := V-(2*N+1)
      ∀ w, wordSize lo hi V w →
      ∀ (Ω : Type) [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ] (D : Target N p w Ω),
      TriangleGraph.Correct μ D →
      ENNReal.ofReal (c*(V:ℝ)^(1/4:ℝ)*totalScale V) ≤ work μ D := by
  obtain ⟨c,cp,h⟩ := triangle_total lo hi lp lh
  refine ⟨c,cp,?_⟩
  filter_upwards [eventual_vertices _ h,eventually_ge_atTop 1] with V bound pos
  have eq : graphSize ((V-1)/2) (V-(2*((V-1)/2)+1))=V := by unfold graphSize; omega
  rw [eq] at bound
  exact bound

/-- Post-preprocessing time bounds on every fixed simple-graph edit and
test sequence, including each selector insertion and deletion. -/
def Budget (tu tq : ℝ) : Prop := ∀ (G : Edges (Vertex N p)), Simple G →
  ∀ ops, ValidHistory G ops →
    (∫⁻ a,totalCost D a G ops ∂μ) ≤
      ENNReal.ofReal (((ops.filter Sum.isLeft).length:ℝ)*tu+((ops.filter Sum.isRight).length:ℝ)*tq)

omit [IsProbabilityMeasure μ] in
theorem work_budget {tu tq : ℝ} (np : 0<N) (B : Budget μ D tu tq) :
    work μ D ≤ ENNReal.ofReal ((hardSize N:ℝ)*(3*tu+tq)) := by
  let n := hardSize N
  letI : Nonempty (Fin N) := ⟨⟨0,np⟩⟩
  letI : Nonempty (Input n N) := ⟨(fun _=>id,id,fun _=>Classical.choice inferInstance)⟩
  let g (z : Input n N) := startGraph (p:=p) (fun q=>rowSet (active_fits N) (z.1 q))
  let h (z : Input n N) := schedule (active_fits N) z.2.1 z.2.2
  have point (z : Input n N) : (∫⁻ a,totalCost D a (g z) ((h z).flatMap triOps) ∂μ) ≤
      ENNReal.ofReal ((n:ℝ)*(3*tu+tq)) := by
    have upper := B (g z) (start_simple _) ((h z).flatMap triOps)
      (legal_expansion _ (h z) (schedule_properties (active_fits N) z.2.1 z.2.2).2)
    dsimp only [h] at upper
    obtain ⟨u,q⟩ := triangle_counts (p:=p) (active_fits N) z.2.1 z.2.2
    rw [u,q,Nat.cast_mul,Nat.cast_ofNat] at upper
    exact upper.trans_eq (congrArg ENNReal.ofReal (by dsimp only [n]; ring))
  unfold work
  apply (ENNReal.div_le_iff (Nat.cast_ne_zero.mpr Fintype.card_ne_zero) (ENNReal.natCast_ne_top _)).mpr
  exact (Finset.sum_le_sum (fun z _ => point z)).trans_eq (by simp [n,mul_comm])

theorem maximum_vertices (lo hi : ℝ) (lp : 0<lo) (lh : lo≤hi) :
    ∃ c : ℝ, 0<c ∧ ∀ᶠ V : ℕ in atTop,
      let N := (V-1)/2
      let p := V-(2*N+1)
      ∀ w, wordSize lo hi V w →
      ∀ (Ω : Type) [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ] (D : Target N p w Ω),
        TriangleGraph.Correct μ D → ∀tu tq : ℝ, 0≤tu → 0≤tq → Budget μ D tu tq →
        c*totalScale V ≤ max tu tq := by
  obtain ⟨c,cp,h⟩ := triangle_vertices lo hi lp lh
  refine ⟨c/4,by positivity,?_⟩
  filter_upwards [h,eventually_ge_atTop 33] with V lower big
  intro N p w ww Ω _ μ _ D ok tu tq ut qt cost
  have exactSize : graphSize N p=V := by unfold graphSize; dsimp [N,p]; omega
  have np : 0<hardSize N := by apply Nat.le_sqrt'.mpr; apply Nat.le_sqrt'.mpr; dsimp [N]; omega
  have ub := work_budget μ D (by dsimp [N]; omega) cost
  have lb := lower w ww Ω μ D ok
  have out := maximum_from_graph_work (N:=N) (p:=p) cp 3 np (work μ D) (by rwa [exactSize]) (by simpa using ub) ut qt
  norm_num [exactSize] at out ⊢
  exact out

end
end AmortizedBound.TriangleCorollary
