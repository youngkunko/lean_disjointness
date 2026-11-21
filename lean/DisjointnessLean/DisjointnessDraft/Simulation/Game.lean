import DisjointnessDraft.Simulation.Tables
import DisjointnessDraft.Information.ProtocolConditioning
import DisjointnessFoundations.QueryTraceInterpreter

/-! The Merlin/Bob/Alice simulation of the new manuscript. The verifier
inspects every changed address in the received trace, allowing an unsampled
cell if its simulated value happens to equal its final value. -/
namespace DisjointnessDraft.PhysicalProtocol
open DisjointnessFoundations Simulation Description
open Information (Layer)
open Classical
noncomputable section

abbrev Log (w : ℕ) := List (Cell w × Cell w)
abbrev Families (m : ℕ) (W : Type) := Fin m → W

def touched (writes : Log w) : Finset (Cell w) := (writes.map Prod.fst).toFinset

@[simp] theorem mem_touched (ws : Log w) (a : Cell w) : a∈touched ws ↔ Written ws a := by
  simp [touched,Written,List.mem_map]

/-- A fixed epoch on a fixed data-structure random tape. Its older memory is
computable from the indexed family and outside updates alone. The logs below
are the actual chronological writes produced on each input. -/
structure Snapshot (m N s w ecap lcap : ℕ) (W O : Type) where
  State : Type
  block : W → Layer N s
  old : Families m W → O → Cell w → Cell w
  epoch : Families m W → Layer N s → O → Log w
  later : Families m W → Layer N s → O → Log w
  epoch_length : ∀ F X o,(epoch F X o).length ≤ ecap
  later_length : ∀ F X o,(later F X o).length ≤ lcap
  start : Fin m → State
  step : State → QueryStep (Cell w) (Cell w) State

namespace Snapshot
variable {m N s w ecap lcap : ℕ} {W O : Type} (S : Snapshot m N s w ecap lcap W O)
abbrev F := Families m W

def truth (f : F (m:=m) (W:=W)) (x : Layer N s) (o : O) :=
  applyWrites (applyWrites (S.old f o) (S.epoch f x o)) (S.later f x o)
def early (f : F (m:=m) (W:=W)) (x : Layer N s) (o : O) :=
  touched (S.epoch f x o) \ touched (S.later f x o)
def recent (f : F (m:=m) (W:=W)) (x : Layer N s) (o : O) := touched (S.later f x o)

def advice (f : F (m:=m) (W:=W)) (x : Layer N s) (o : O) : Advice w ecap lcap := by
  have ec : (S.early f x o).card≤ecap :=
    (Finset.card_le_card Finset.sdiff_subset).trans ((List.toFinset_card_le _).trans
      ((List.length_map _).le.trans (S.epoch_length f x o)))
  have lc : (S.recent f x o).card≤lcap :=
    (List.toFinset_card_le _).trans ((List.length_map _).le.trans (S.later_length f x o))
  exact (table _ (S.truth f x o) ec,table _ (S.truth f x o) lc)

def sim (f : F (m:=m) (W:=W)) (o : O) (packet : Table w capacity) (a : Cell w) : Cell w :=
  (packet.val a).getD (S.old f o a)

def reply (limit fuel : ℕ) (f : F (m:=m) (W:=W)) (o : O) (p : Packet w lcap limit) (q : Fin m) :
    TraceCode w fuel := match p with
  | none => encodeTrace w fuel ⟨[],none⟩
  | some tab => encodeTrace w fuel (run S.step (S.sim f o tab) fuel (S.start q))

def verifies (p : Packet w lcap limit) (v : TraceCode w fuel) (u : Advice w ecap lcap) : Bool := by
  let trace := decodeTrace w fuel v
  exact decide (p.isSome ∧ trace.answer=some true ∧ ∀ pair∈trace.probes, ∀ a,
    listed u pair.1=some a → pair.2=a)

def game (limit fuel : ℕ) :
    Information.Game m N s W O (Cell w→Bool) (Advice w ecap lcap) (Packet w lcap limit) (TraceCode w fuel) :=
  ⟨S.block,S.advice,fun u r => send u r limit,S.reply limit fuel,verifies⟩

def touchedBits (f : Families m W) (x : Layer N s) (o : O) (bits : Cell w → Bool) :=
  (S.early f x o).filter (fun a => bits a)

theorem listed_advice (f : Families m W) (x : Layer N s) (o : O) (a : Cell w) :
    listed (S.advice f x o) a =
      if a∈S.recent f x o ∨ a∈S.early f x o then some (S.truth f x o a) else none := by
  by_cases h : a∈S.recent f x o <;> by_cases h' : a∈S.early f x o <;>
    simp [listed,advice,table_val,h,h']

theorem sim_value (f : Families m W) (x : Layer N s) (o : O) (bits : Cell w → Bool)
    (tab : Table w (lcap+limit)) (sent : send (S.advice f x o) bits limit = some tab) (a : Cell w) :
    S.sim f o tab a = if a∈S.recent f x o ∨ a∈S.touchedBits f x o bits then S.truth f x o a else S.old f o a := by
  simp only [send] at sent
  split at sent
  · cases sent
    simp only [sim,table_val]
    change (if a ∈ domain (S.advice f x o).2.val ∪ sampled (S.advice f x o).1 bits then
      some ((listed (S.advice f x o) a).getD 0) else none).getD _ = _
    simp only [listed_advice,advice,table_domain,sampled,Finset.mem_union,Finset.mem_filter,touchedBits]
    by_cases l : a∈S.recent f x o <;> by_cases e : a∈S.early f x o <;> cases bit : bits a <;> simp_all [listed,table_val]
  · contradiction

theorem intact (f : Families m W) (x : Layer N s) (o : O) (a : Cell w)
    (outside : ¬(a∈S.recent f x o ∨ a∈S.early f x o)) : S.truth f x o a = S.old f o a := by
  have l : ¬ Written (S.later f x o) a := by simpa [recent] using fun h => outside (Or.inl h)
  have e : ¬ Written (S.epoch f x o) a := by
    intro h; apply outside; right
    simpa [early,l] using h
  rw [truth,applyWrites_of_unwritten _ _ _ l,applyWrites_of_unwritten _ _ _ e]

def actual (fuel : ℕ) (f : Families m W) (x : Layer N s) (o : O) (q : Fin m) :=
  run S.step (S.truth f x o) fuel (S.start q)

def required (fuel : ℕ) (f : Families m W) (x : Layer N s) (o : O) (q : Fin m) :=
  S.early f x o ∩ touched (S.actual fuel f x o q).probes

theorem verified (f : Families m W) (x : Layer N s) (o : O) (q : Fin m) (bits : Cell w→Bool)
    (limit fuel : ℕ) (accepts : (S.game limit fuel).accepted q (f,x,o,bits)=true) :
    (S.actual fuel f x o q).answer=some true := by
  let p := send (S.advice f x o) bits limit
  change verifies p (S.reply limit fuel f o p q) (S.advice f x o) = true at accepts
  cases sent : p with
  | none => simp [sent,verifies] at accepts
  | some tab =>
    rw [sent] at accepts
    simp only [reply,verifies,decode_encode _ _ _ (probe_budget ..),Option.isSome_some,
      decide_eq_true_eq,true_and] at accepts
    let simulated := run S.step (S.sim f o tab) fuel (S.start q)
    have same : simulated = S.actual fuel f x o q := by
      by_contra bad
      obtain ⟨before,a,as,bs,hist,_,diff⟩ := first_difference S.step (S.sim f o tab) (S.truth f x o) fuel (S.start q) bad
      by_cases changed : a∈S.recent f x o ∨ a∈S.early f x o
      · exact diff (accepts.2 (a,S.sim f o tab a) (by simp [hist]) _ (by simp [S.listed_advice,changed]))
      · rw [S.sim_value _ _ _ _ _ sent,S.intact _ _ _ _ changed] at diff
        rcases not_or.mp changed with ⟨l,e⟩
        simp [l,e,touchedBits] at diff
    rw [←same]; exact accepts.1

theorem sound (limit fuel : ℕ)
    (correct : ∀ (f : Families m W) x o q, (S.actual fuel f x o q).answer=some true →
      Disjoint (S.block (f q)).val x.val) : (S.game limit fuel).Sound := by
  rintro q ⟨f,x,o,r⟩ h
  exact correct f x o q (S.verified f x o q r limit fuel h)

theorem success (f : Families m W) (x : Layer N s) (o : O) (q : Fin m) (bits : Cell w→Bool)
    (limit fuel : ℕ) (short : (S.touchedBits f x o bits).card≤limit)
    (cover : ∀ a∈S.required fuel f x o q,bits a=true) (yes : (S.actual fuel f x o q).answer=some true) :
    (S.game limit fuel).accepted q (f,x,o,bits)=true := by
  have sample : sampled (S.advice f x o).1 bits = S.touchedBits f x o bits := by simp [advice,sampled,touchedBits]
  have ex : ∃ t, send (S.advice f x o) bits limit = some t := by
    simp [send,sample,short]
  obtain ⟨t,sent⟩ := ex
  let simulated := run S.step (S.sim f o t) fuel (S.start q)
  have same : S.actual fuel f x o q=simulated := by
    by_contra bad
    obtain ⟨before,a,as,bs,hist,_,diff⟩ := first_difference S.step (S.truth f x o) (S.sim f o t) fuel (S.start q) bad
    rw [S.sim_value _ _ _ _ _ sent] at diff
    by_cases l : a∈S.recent f x o
    · simp [l] at diff
    by_cases e : a∈S.early f x o
    · have hit : a ∈ touched (S.actual fuel f x o q).probes := (mem_touched _ _).mpr ⟨S.truth f x o a,by simp [actual,hist]⟩
      have bit := cover a (Finset.mem_inter.mpr ⟨e,hit⟩)
      simp [touchedBits,e,bit] at diff
    · simp [l,e,touchedBits,S.intact f x o a (by simp [l,e])] at diff
  change verifies (send (S.advice f x o) bits limit) (S.reply limit fuel f o (send (S.advice f x o) bits limit) q) (S.advice f x o)=true
  rw [sent]
  simp only [reply,verifies,decode_encode _ _ _ (probe_budget ..),Option.isSome_some,decide_eq_true_eq,true_and]
  change simulated.answer=some true ∧ ∀ y∈simulated.probes, ∀ a, listed (S.advice f x o) y.1=some a → y.2=a
  rw [←same]
  refine ⟨yes,?_⟩
  intro entry h a ha
  rw [listed_advice] at ha
  split at ha
  · injection ha with hv
    simpa [←hv] using recorded_word S.step (S.truth f x o) fuel (S.start q) entry h
  · contradiction

end Snapshot
end
end DisjointnessDraft.PhysicalProtocol
