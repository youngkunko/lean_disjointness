import DisjointnessDraft.Fresh

/-! Moving a fixed-length sequence of legal target updates to source
preprocessing. The *contents* of the sequence may depend on every input set.
Post-setup random tape indices are shifted by exactly the number of operations. -/
namespace DisjointnessDraft.Preload
open DisjointnessFoundations CellProbe InputReduction MeasureTheory
open scoped ENNReal
noncomputable section
open Classical
variable {n w : ℕ} {F E Q C Ω : Type}

structure Map (n : ℕ) (F E Q : Type) where
  initial : Family n → F
  setup : Family n → List E
  length : ℕ
  fixed : ∀ f, (setup f).length=length
  insert : Fin n → E
  ask : Fin n → Q
  negate : Bool

variable (A : Map n F E Q) (D : DataStructure w F E Q C) (R : RandomTape Ω C)

def atFamily (f : Family n) : Padding.Embedding (Family n) (Fin n) (Fin n) F E Q :=
  ⟨A.initial,A.insert,A.ask,A.setup f⟩

def body : DataStructure w (Family n) (Fin n) (Fin n) (ℕ × Ω) where
  UState := D.UState
  QState := D.QState
  preprocess coin f := ProtocolRun.afterPrefix D R coin.2 (A.initial f) (A.setup f)
  startUpdate coin x := D.startUpdate (R.insertion (A.length+coin.1) coin.2) (A.insert x)
  updateStep := D.updateStep
  startQuery coin q := D.startQuery (R.query coin.2) (A.ask q)
  queryStep := D.queryStep

theorem inserts (a : Ω) (j : ℕ) (m : Memory w) (xs : List (Fin n)) :
    insertAll (body A D R) (Padding.tape Ω) a j m xs =
    insertAll D R a (A.length+j) m (xs.map A.insert) := by
  induction xs generalizing j m with
  | nil => rfl
  | cons x xs ih =>
    simp only [insertAll,List.map_cons]
    change (insertOne D (R.insertion (A.length+j) a) (A.insert x) m).bind _ = _
    cases insertOne D (R.insertion (A.length+j) a) (A.insert x) m with
    | none => rfl
    | some z => obtain ⟨mid,c⟩ := z; simp [ih,Nat.add_assoc]

theorem local_prefix (a : Ω) (f : Family n) (xs : List (Fin n)) :
    prefixRun (body A D R) (Padding.tape Ω) a f xs=
    prefixRun (Padding.pullback (atFamily A f) D R) (Padding.tape Ω) a f xs := by
  unfold prefixRun
  rw [inserts,Padding.insertAll_pullback]
  change insertAll D R a (A.length+0) _ _=insertAll D R a ((A.setup f).length+0) _ _
  rw [A.fixed]; rfl

theorem final (tu : ℝ≥0∞) (h : WorstUpdate D R tu) (a : Ω) (f : Family n) (xs : List (Fin n)) (q : Fin n) :
    finalRun (body A D R) (Padding.tape Ω) a f xs q =
    finalRun D R a (A.initial f) (A.setup f++xs.map A.insert) (A.ask q) := by
  apply Eq.trans _ (Padding.final_compare (atFamily A f) D R h a f xs q)
  unfold finalRun; rw [local_prefix]; rfl

theorem worst (tu : ℝ≥0∞) (h : WorstUpdate D R tu) : WorstUpdate (body A D R) (Padding.tape Ω) tu := by
  intro a f xs
  obtain ⟨m,c,run,paid⟩ := Padding.worst_pullback (atFamily A f) D R h a f xs
  refine ⟨m,c,(local_prefix A D R a f xs).trans run,fun x => ?_⟩
  have hh := paid x
  change cost (insertOne D (R.insertion ((A.setup f).length+xs.length) a) (A.insert x) m)≤_ at hh
  rw [A.fixed] at hh
  exact hh

def flip (neg : Bool) : Translation (Family n) (Fin n) (Fin n) (Family n) (Fin n) (Fin n) :=
  ⟨id,id,id,neg⟩

def algorithm (tu : ℕ) := mapped (flip A.negate) (body A (UpdateCutoff.machine D tu) R)

theorem pays_of_worst {F' E' Q' C' : Type} (S : DataStructure w F' E' Q' C') (T : RandomTape Ω C')
    (B : ℕ) (paid : WorstUpdate S T B) (a : Ω) (f : F') (xs : List E') : SingleSelector.Pays S T B a f xs := by
  intro p e s _
  obtain ⟨m,c,pre,b⟩ := paid a f p
  have h := b e
  cases eq : insertOne S (T.insertion p.length a) e m with
  | none => simp [eq,cost] at h
  | some v =>
    obtain ⟨m',d⟩ := v
    refine ⟨m,c,m',d,pre,eq,?_⟩
    rw [eq] at h; exact_mod_cast (show (d:ℝ≥0∞)≤B from h)

theorem coupled (tu : ℕ) (a : Ω) (f : Family n) (xs : List (Fin n)) (q : Fin n)
    (paid : SingleSelector.Pays D R tu a (A.initial f) (A.setup f++xs.map A.insert)) :
    finalRun (algorithm A D R tu) (Padding.tape Ω) a f xs q =
    (finalRun D R a (A.initial f) (A.setup f++xs.map A.insert) (A.ask q)).map
      (fun z => (out A.negate z.1,z.2)) := by
  rw [algorithm,InputReduction.final_eq]
  simp only [flip,List.map_id_fun,id_eq]
  rw [final A _ R _ (UpdateCutoff.worst D R tu)]
  have h := SingleSelector.agrees D R tu a _ _ paid
  unfold finalRun
  rw [h]
  rfl

variable [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]

structure Guarantees (tu : ℕ) (tq : ℝ) : Prop where
  pays : ∀ a f (xs : List (Fin n)), xs.Nodup → SingleSelector.Pays D R tu a (A.initial f) (A.setup f++xs.map A.insert)
  answer : ∀ a f (xs : List (Fin n)) q, xs.Nodup →
    (finalRun D R a (A.initial f) (A.setup f++xs.map A.insert) (A.ask q)).map Prod.fst =
      some (out A.negate (DisjointnessDraft.answer f xs q))
  measurable : ∀ f (xs : List (Fin n)) q, xs.Nodup → Measurable (fun a => cost (finalRun D R a (A.initial f) (A.setup f++xs.map A.insert) (A.ask q)))
  query : ∀ f (xs : List (Fin n)) q, xs.Nodup → (∫⁻ a, cost (finalRun D R a (A.initial f) (A.setup f++xs.map A.insert) (A.ask q)) ∂μ) ≤ ENNReal.ofReal tq

omit [IsProbabilityMeasure μ] in
theorem transfer [IsProbabilityMeasure μ] (tu : ℕ) (tq : ℝ) (h : Guarantees A D R μ tu tq) :
    Fresh.OnFresh μ (algorithm A D R tu) (Padding.tape Ω) tu tq := by
  have costeq a f (xs : List (Fin n)) q (fresh : xs.Nodup) : cost (finalRun (algorithm A D R tu) (Padding.tape Ω) a f xs q) =
      cost (finalRun D R a (A.initial f) (A.setup f++xs.map A.insert) (A.ask q)) := by
    rw [coupled A D R tu a f xs q (h.pays a f xs fresh)]
    cases finalRun D R a _ _ _ <;> rfl
  refine ⟨fun a f xs _ => pays_of_worst _ _ _ (InputReduction.worst _ _ _ _ (worst A _ R _ (UpdateCutoff.worst D R tu))) a f xs,?_,?_,?_⟩
  · intro a f xs q fresh
    rw [coupled A D R tu a f xs q (h.pays a f xs fresh)]
    have yes := h.answer a f xs q fresh
    cases eq : finalRun D R a (A.initial f) (A.setup f++xs.map A.insert) (A.ask q) with
    | none => simp [eq] at yes
    | some z =>
      obtain ⟨b,c⟩ := z
      simp only [eq,Option.map_some,Option.some.injEq] at yes
      have val : b = out A.negate (DisjointnessDraft.answer f xs q) := Option.some.inj yes
      change some (out A.negate b) = _
      rw [val]
      cases nflag : A.negate <;> simp [out,nflag]
  · intro f xs q fresh; simpa only [fun a => costeq a f xs q fresh] using h.measurable f xs q fresh
  · intro f xs q fresh; simp only [fun a => costeq a f xs q fresh]; exact h.query f xs q fresh

end
end DisjointnessDraft.Preload
