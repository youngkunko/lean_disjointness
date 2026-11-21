import DisjointnessDraft.Native.Operational

/-! The three possible outputs of the printed protocol, including verified
intersections as well as verified disjoint answers and an explicit failure. -/
namespace DisjointnessDraft.PhysicalProtocol.Snapshot
open DisjointnessFoundations Description Simulation
noncomputable section
open Classical

def output (p : Packet w lc limit) (v : TraceCode w fuel) (u : Advice w ec lc) : Option Bool :=
  let t := decodeTrace w fuel v
  if p.isSome ∧ ∀ pair∈t.probes, ∀ a,listed u pair.1=some a → pair.2=a then t.answer else none

theorem positive {w lc limit fuel ec : ℕ} (p : Packet w lc limit) (v : TraceCode w fuel) (u : Advice w ec lc) :
    output p v u=some true ↔ verifies p v u=true := by
  simp only [output,verifies,decide_eq_true_eq]
  split <;> rename_i h
  · exact ⟨fun a => ⟨h.1,a,h.2⟩,fun a => a.2.1⟩
  · simp only [reduceCtorEq,false_iff]; tauto

variable {m N s w ec lc : ℕ} {W O : Type} (S : Snapshot m N s w ec lc W O)

theorem output_trace (f : Families m W) (x : Information.Layer N s) (o : O) (q : Fin m)
    (bits : Cell w → Bool) (limit fuel : ℕ) {b : Bool}
    (ok : let p := send (S.advice f x o) bits limit
          output p (S.reply limit fuel f o p q) (S.advice f x o)=some b) :
    (S.actual fuel f x o q).answer=some b := by
  let p := send (S.advice f x o) bits limit
  change output p (S.reply limit fuel f o p q) (S.advice f x o)=some b at ok
  cases sent : p with
  | none => simp [sent,output] at ok
  | some tab =>
    rw [sent] at ok
    simp only [reply,output,decode_encode _ _ _ (probe_budget ..),Option.isSome_some,true_and] at ok
    split at ok
    · rename_i content
      let st := run S.step (S.sim f o tab) fuel (S.start q)
      have same : st=S.actual fuel f x o q := by
        by_contra bad
        obtain ⟨before,a,as,bs,hist,_,diff⟩ := first_difference S.step (S.sim f o tab) (S.truth f x o) fuel (S.start q) bad
        by_cases changed : a∈S.recent f x o ∨ a∈S.early f x o
        · exact diff (content (a,S.sim f o tab a) (by simp [hist]) _ (by simp [S.listed_advice,changed]))
        · rw [S.sim_value _ _ _ _ _ sent,S.intact _ _ _ _ changed] at diff
          rcases not_or.mp changed with ⟨l,e⟩; simp [l,e,touchedBits] at diff
      rw [←same]; exact ok
    · contradiction

end
end DisjointnessDraft.PhysicalProtocol.Snapshot

namespace DisjointnessDraft.Native
open DisjointnessFoundations CellProbe VerifiedEpoch PhysicalProtocol
open scoped ENNReal
noncomputable section
open Classical
variable {ℓ g n w tu : ℕ} {Ω C : Type}

theorem verified_bit (fit : occupied ℓ g≤n) (hg : 2≤g) (D : Machine n w C) (R : RandomTape Ω C)
    (a : Ω) (hu : WorstUpdate D R (tu:ℝ≥0∞)) (hz : FreshCorrect D R)
    (i : Fin ℓ) (F : Fin n → Whole ℓ g) (b : Block ℓ g i) (o : Outside g i) (q : Fin n)
    (bits : Cell w → Bool) (limit fuel : ℕ) (out : Bool)
    (ok : let S := snapshot fit hg D R hu a i
          let p := send (S.advice F b o) bits limit
          Snapshot.output p (S.reply limit fuel F o p q) (S.advice F b o)=some out) :
    answer (rows fit F) (updates fit (join i b o)) q=out := by
  have yes := (snapshot fit hg D R hu a i).output_trace F b o q bits limit fuel ok
  rw [snap_trace] at yes
  let z : Draw n ℓ g := (q,F,join i b o)
  let k := reads fit D R a z
  have h := exact_trace fit D R hu hz a z
  dsimp only at h
  change (trace fit D R a z fuel).answer=some out at yes
  have eq : trace fit D R a z (max k fuel)=trace fit D R a z fuel :=
    run_stable _ _ _ _ out yes _ ((run_length_le ..).trans (le_max_right _ _))
  have eq' : trace fit D R a z (max k fuel)=trace fit D R a z k :=
    run_stable _ _ _ _ _ h.1 _ (h.2.le.trans (le_max_left _ _))
  rw [←eq,eq',h.1] at yes; exact Option.some.inj yes

end
end DisjointnessDraft.Native
