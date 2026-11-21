import DisjointnessDraft.Streaming.Machine
import DisjointnessFoundations.AdaptiveTraceComparison
import DisjointnessDraft.Streaming.Storage
import DisjointnessDraft.Streaming.Size

/-! A physical deterministic word-memory matcher and a worst-case total bound for
every finite prefix, including malformed streams and arbitrarily many repetitions. -/
namespace DisjointnessDraft.Streaming.Storage
open DisjointnessFoundations CellProbe WordProgram WordImage QueryNormalization Simulation
noncomputable section
open Classical
abbrev Layout (n m w : ℕ) := WordImage.Layout (Addr n m) (Val n) w

private def addrCode : Addr n m → Unit ⊕ Unit ⊕ Fin n ⊕ Fin n ⊕ (Fin m × Fin n)
  | .tag => .inl ()
  | .head => .inr (.inl ())
  | .next x => .inr (.inr (.inl x))
  | .seen x => .inr (.inr (.inr (.inl x)))
  | .entry q j => .inr (.inr (.inr (.inr (q,j))))

private def valCode : Val n → (Fin 4) ⊕ (Option (Fin n)) ⊕ Bool
  | .tag .first => .inl 0 | .tag .live => .inl 1
  | .tag (.closed false) => .inl 2 | .tag (.closed true) => .inl 3
  | .ptr p => .inr (.inl p) | .bit b => .inr (.inr b)

theorem space (n m : ℕ) : Fintype.card (Addr n m) ≤ m*n+2*n+2 ∧ Fintype.card (Val n) ≤ n+7 := by
  have ad : Function.Injective (@addrCode n m) := by
    intro x y eq; cases x <;> cases y <;> simp_all [addrCode]
  have va : Function.Injective (@valCode n) := by
    let inv : (Fin 4 ⊕ (Option (Fin n)) ⊕ Bool) → Val n := fun v =>
      match v with
      | .inl i => if i=0 then .tag .first else if i=1 then .tag .live else .tag (.closed (decide (i=3)))
      | .inr (.inl p) => .ptr p
      | .inr (.inr b) => .bit b
    apply Function.LeftInverse.injective (g:=inv)
    intro v; cases v with
    | tag t => cases t with
      | first | live => rfl
      | closed b => cases b <;> rfl
    | ptr | bit => rfl
  constructor
  · simpa [add_assoc,add_left_comm,add_comm,two_mul] using (Fintype.card_le_of_injective _ ad)
  · simpa [add_assoc,add_left_comm,add_comm] using (Fintype.card_le_of_injective _ va)

theorem layout_exists (n m w : ℕ) (room : m*n+2*n+7≤2^w) : Nonempty (Layout n m w) := by
  obtain ⟨a,b⟩ := space n m
  have ac : Fintype.card (Addr n m)≤Fintype.card (Word w) := by simp [Word]; omega
  have vc : Fintype.card (Val n)≤Fintype.card (Word w) := by simp [Word]; omega
  exact ⟨(Function.Embedding.nonempty_of_card_le ac).some,(Function.Embedding.nonempty_of_card_le vc).some,default⟩

def reconstruct (r : Expr n m) (q : Fin m) : Finset (Fin n) :=
  Finset.univ.filter (fun x => !(r.rmatch (word [x] q)))

theorem reconstruct_expression (f : Fin m → Finset (Fin n)) : reconstruct (expression f)=f := by
  ext q a
  simp only [reconstruct,Finset.mem_filter,Finset.mem_univ,true_and,Bool.not_eq_true']
  have h : (expression f).rmatch (word [a] q) = true ↔ a ∉ f q := by
    simp [RegularExpression.rmatch_iff_matches',reduction]
  cases eq : (expression f).rmatch (word [a] q) <;> simp_all

def rwStep (L : Layout n m w) : P n m Bool → Step (Word w) (P n m Bool)
  | .pure b => .done b
  | .read a k => .read (L.addr a) (fun v => k (Function.invFun L.value v))
  | .write a v k => .write (L.addr a) (L.value v) k

theorem forget_step (L : Layout n m w) : forgetReport (rwStep L) = (codec L).updateStep := by
  funext p; cases p <;> rfl

theorem report_run (L : Layout n m w) (p : P n m Bool) (mem : Addr n m → Val n) :
    let pair := p.run mem
    QueryNormalization.run (rwStep L) pair.2.2 p (image L mem) = some (pair.1,pair.2.2) := by
  induction p generalizing mem with
  | pure b => rfl
  | read a k ih =>
    change QueryNormalization.run _ (1+_) _ _ = _
    rw [Nat.add_comm,QueryNormalization.run,rwStep]
    simp only [image_at,Function.leftInverse_invFun L.value.injective]
    rw [Function.leftInverse_invFun L.value.injective (mem a),ih]
    change some (_, _+1) = some (_,1+_)
    simp [Program.run,Nat.add_comm]
  | write a v k ih =>
    change QueryNormalization.run _ (1+_) _ _ = _
    rw [Nat.add_comm,QueryNormalization.run,rwStep]
    dsimp only
    rw [image_update,ih]
    change some (_, _+1) = some (_,1+_)
    simp [Program.run,Nat.add_comm]

def matcher (L : Layout n n w) : Engine n n w Unit where
  State := P n n Bool
  preprocess _ r := image L (words (reconstruct r) .first [])
  start _ c := operation c
  step := rwStep L

def fixedTape : RandomTape Unit Unit := ⟨fun _ => (),fun _ _ => (), fun _ => ()⟩

def potential (s : Store n) := if s.1=.live then 2*s.2.length else 0

theorem charge (f : Fin m → Finset (Fin n)) (s : Store n) (x : Symbol n m) (h : valid s) :
    probes s x + potential (nextState f s x) ≤ 8+potential s := by
  rcases s with ⟨p,xs⟩
  cases p <;> cases x with
  | none => simp_all [valid,probes,potential,nextState] <;> omega
  | some a => cases a with
    | inl j => by_cases j∈xs <;> simp_all [valid,probes,potential,nextState,push] <;> omega
    | inr q => simp [probes,potential,nextState]

private theorem one (L : Layout n n w) (f : Family n) (s : Store n) (c : Symbol n n) (v : valid s) :
    let t := nextState f s c
    insertOne (process (matcher L)) () c (image L (words f s.1 s.2)) =
      some (image L (words f t.1 t.2),probes s c) := by
  have run := WordImage.update_exact L (operation c) (words f s.1 s.2)
  rw [operation_run _ _ _ v] at run
  unfold insertOne
  apply finish_eq_some _ (fun le h => updateRun_mono _ le _ _ h)
  change updateRun (forgetReport (rwStep L)) _ _ _=_
  rwa [forget_step]

private theorem one_report (L : Layout n n w) (f : Family n) (s : Store n) (c : Symbol n n) (v : valid s) :
    let t := nextState f s c
    finish (fun fuel => result (Simulation.run (process (matcher L)).queryStep
      (image L (words f s.1 s.2)) fuel ((process (matcher L)).startQuery () c))) =
      some (accepted (parser t),probes s c) := by
  have h := report_run L (operation c) (words f s.1 s.2)
  rw [operation_run _ _ _ v] at h
  apply finish_eq_some _ _ ((final_symbol (matcher L) () c _ _).trans h)
  intro a b val le ok
  obtain ⟨z,hz,_⟩ := Option.map_eq_some_iff.mp ok
  rw [VerifiedEpoch.run_stable _ _ a _ z hz b ((VerifiedEpoch.run_length_le _ _ _ _).trans le)]
  exact ok

private theorem suffix (L : Layout n n w) (f : Family n) (s : Store n) (ts : List (Symbol n n))
    (offset : ℕ) (v : valid s) :
    ∃ t : Store n, ∃ cost : ℕ, valid t ∧ parser t = consume f (parser s) ts ∧
      cost+potential t≤8*ts.length+potential s ∧
      insertAll (process (matcher L)) fixedTape () offset (image L (words f s.1 s.2)) ts =
        some (image L (words f t.1 t.2),cost) := by
  induction ts generalizing s offset with
  | nil => exact ⟨s,0,v,rfl,by simp,rfl⟩
  | cons x ts ih =>
    obtain ⟨vt,interp⟩ := valid_next f s x v
    obtain ⟨t,c,ok,re,bound,exec⟩ := ih (nextState f s x) (offset+1) vt
    refine ⟨t,probes s x+c,ok,?_,?_,?_⟩
    · simpa only [consume,List.foldl_cons,←interp] using re
    · have h := charge f s x v
      simp only [List.length_cons,Nat.mul_add,Nat.mul_one]
      omega
    · change (insertOne (process (matcher L)) () x _).bind _ = _
      rw [one _ _ _ _ v]
      simp [exec]

private theorem prefix_result (L : Layout n n w) (f : Family n) (ts : List (Symbol n n)) :
    ∃ s : Store n, ∃ c≤8*ts.length, valid s ∧ parser s=consume f .first ts ∧
      prefixRun (process (matcher L)) fixedTape () f ts = some (image L (words f s.1 s.2),c) := by
  obtain ⟨s,c,v,st,b,exec⟩ := suffix L f (.first,[]) ts 0 (by simp [valid])
  refine ⟨s,c,?_,v,st,?_⟩
  · simp [potential] at b; omega
  · simpa only [prefixRun,process,matcher,fixedTape,reconstruct_expression] using exec

/-- The physical matcher answers the prefix ending at each symbol correctly.
The total cost of all reports and memory changes is at most 8 probes per symbol
amortized on every stream. -/
theorem upper (L : Layout n n w) :
    ZeroError (process (matcher L)) fixedTape reports ∧
    ∀ (f : Family n) (ts : List (Symbol n n)), ∃ c≤8*ts.length, ∃ mem,
      prefixRun (process (matcher L)) fixedTape () f ts = some (mem,c) := by
  constructor
  · intro seed f ts x
    obtain ⟨s,c,_,ok,st,run⟩ := prefix_result L f ts
    simp only [finalRun,run,Option.bind_eq_bind,Option.some_bind]
    change (finish (fun fuel => result (Simulation.run _ _ fuel _))).map Prod.fst = _
    rw [one_report L f s x ok]
    apply congrArg some
    apply Bool.eq_iff_iff.mpr
    rw [(valid_next f s x ok).2,st]
    have hu : consume f .first (ts++[x]) = advance f (consume f .first ts) x := by simp [consume,List.foldl_append]
    change accepted (advance f (consume f .first ts) x) = true ↔ _
    rw [←hu]
    rw [parser_correct]
    exact (RegularExpression.rmatch_iff_matches' _ _).symm
  · intro f ts
    obtain ⟨s,c,b,_,_,h⟩ := prefix_result L f ts
    exact ⟨c,b,_,h⟩

end
end DisjointnessDraft.Streaming.Storage
