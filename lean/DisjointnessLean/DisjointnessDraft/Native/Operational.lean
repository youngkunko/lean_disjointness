import DisjointnessDraft.Simulation.Game
import DisjointnessDraft.Native.Tape
import DisjointnessDraft.Native.EpochGeometry

namespace DisjointnessDraft.Native
open DisjointnessFoundations CellProbe HardDistribution ProtocolRun VerifiedEpoch PhysicalProtocol
open scoped ENNReal BigOperators
noncomputable section
open Classical

variable {ℓ g n w tu : ℕ} {Ω C : Type}
variable (fit : occupied ℓ g≤n) (hg : 2≤g) (D : Machine n w C) (R : RandomTape Ω C)
    (hu : WorstUpdate D R (tu:ℝ≥0∞)) (a : Ω)

def snapshot (i : Fin ℓ) : Snapshot n (blockSize ℓ g i) (epochSize g i) w
    (epochSize g i*tu) (2*epochSize g i*tu / g^2) (Whole ℓ g) (Outside g i) where
  State := D.QState
  block := fun y => y i
  old F o := oldMemory fit D R a F (join i (Classical.choice (layer_nonempty (Nat.zero_lt_of_lt i.isLt) (by omega) i)) o) i
  epoch F b o := epochLog fit D R a F (join i b o) i
  later F b o := recentLog fit D R a F (join i b o) i
  epoch_length F b o := (log_lengths fit D R a hu F (join i b o) i).1
  later_length F b o := by
    apply (log_lengths fit D R a hu F (join i b o) i).2.trans
    apply (Nat.le_div_iff_mul_le (pow_pos (by omega : 0<g) _)).mpr
    have h := Nat.mul_le_mul_right tu (after_small fit hg (join i b o) i)
    simpa only [Nat.mul_right_comm] using h
  start q := D.startQuery (R.query a) q
  step := D.queryStep

local notation "snap" => snapshot fit hg D R hu a

theorem snap_truth (i : Fin ℓ) (F : Fin n → Whole ℓ g) (b : Block ℓ g i) (o : Outside g i) :
    (snap i).truth F b o = afterPrefix D R a (rows fit F) (updates fit (join i b o)) := by
  unfold Snapshot.truth
  change Simulation.applyWrites (Simulation.applyWrites (oldMemory fit D R a F (join i _ o) i) _) _=_
  rw [old_independent fit D R a F i _ b o]
  exact physical_final fit D R a hu F (join i b o) i

theorem snap_trace (i : Fin ℓ) (F : Fin n → Whole ℓ g) (b : Block ℓ g i) (o : Outside g i) (q : Fin n) (k : ℕ) :
    (snap i).actual k F b o q = trace fit D R a (q,F,join i b o) k := by
  unfold Snapshot.actual; rw [snap_truth]; rfl

theorem verified_whole (hz : FreshCorrect D R) (i : Fin ℓ) (F : Fin n → Whole ℓ g) (b : Block ℓ g i)
    (o : Outside g i) (q : Fin n) (limit fuel : ℕ) (r : PhysicalProtocol.Cell w → Bool)
    (yes : ((snap i).game limit fuel).accepted q (F,b,o,r)=true) :
    answer (rows fit F) (updates fit (join i b o)) q=true := by
  have h := (snap i).verified F b o q r limit fuel yes
  rw [snap_trace] at h
  let z : Draw n ℓ g := (q,F,join i b o)
  let k := reads fit D R a z
  have done := exact_trace fit D R hu hz a z
  dsimp only at done
  change (trace fit D R a z fuel).answer=some true at h
  let maxFuel := max k fuel
  have eq1 : trace fit D R a z maxFuel=trace fit D R a z fuel :=
    run_stable _ _ fuel _ true h maxFuel ((run_length_le ..).trans (le_max_right _ _))
  have eq2 : trace fit D R a z maxFuel=trace fit D R a z k :=
    run_stable _ _ k _ _ done.1 maxFuel (done.2.le.trans (le_max_left _ _))
  rw [←eq1,eq2,done.1] at h
  exact Option.some.inj h

theorem game_sound (hz : FreshCorrect D R) (i : Fin ℓ) (limit fuel : ℕ) :
    ((snap i).game limit fuel).Sound := by
  rintro q ⟨F,b,o,r⟩ yes
  have h := (correct fit F (join i b o) q).mp (verified_whole fit hg D R hu a hz i F b o q limit fuel r yes)
  simpa only [join_same] using h i

theorem under_cap (hz : FreshCorrect D R) (i : Fin ℓ) (F : Fin n → Whole ℓ g) (b : Block ℓ g i)
    (o : Outside g i) (q : Fin n) (fuel : ℕ) (ok : reads fit D R a (q,F,join i b o)≤fuel) :
    ((snap i).actual fuel F b o q).answer = some (answer (rows fit F) (updates fit (join i b o)) q) := by
  let z : Draw n ℓ g := (q,F,join i b o)
  have h := exact_trace fit D R hu hz a z
  dsimp only at h
  have eq : trace fit D R a z fuel=trace fit D R a z (reads fit D R a z) :=
    run_stable _ _ _ _ _ h.1 fuel (h.2.le.trans ok)
  rw [snap_trace]; exact eq ▸ h.1

end
end DisjointnessDraft.Native
