import DisjointnessDraft.Transfer.Scripts
import DisjointnessDraft.Streaming.BitMachine

/-! Word-address embedding and one disjoint clock cell. A transaction on the
target modifies exactly the represented target memory. Phase III executes
the same transaction with temporary writes and a read-only source query. -/
namespace DisjointnessDraft.Transfer.Compiler
open DisjointnessFoundations CellProbe WordProgram WordImage QueryNormalization
open Streaming.Binary (stepWord memory_and_cost bit_report)
noncomputable section
open Classical

structure Layout (w v : ℕ) where
  cell : Word w ↪ Word v
  clock : Word v
  away : ∀ a,clock ≠ cell a

def layout (w v : ℕ) (hv : w<v) : Layout w v where
  cell := Fin.castLEEmb (Nat.pow_le_pow_right (by decide) hv.le)
  clock := ⟨2^w,Nat.pow_lt_pow_right (by decide) hv⟩
  away := by intro a eq; have bad := congrArg Fin.val eq; change 2^w=a.val at bad; omega

def stamp (v j : ℕ) : Word v := ⟨j % 2^v,Nat.mod_lt _ (by positivity)⟩

def underlying (L : Layout w v) : WordImage.Layout (Word w) (Word w) v := ⟨L.cell,L.cell,0⟩

def image (L : Layout w v) (j : ℕ) (mem : Memory w) : Memory v :=
  Function.update (WordImage.image (underlying L) mem) L.clock (stamp v j)

theorem read_cell (L : Layout w v) (j : ℕ) (mem : Memory w) (a : Word w) :
    image L j mem (L.cell a)=L.cell (mem a) := by
  rw [image,Function.update_of_ne (L.away a).symm]
  exact WordImage.image_at (underlying L) _ _

theorem write_cell (L : Layout w v) (j : ℕ) (mem : Memory w) (a u : Word w) :
    Function.update (image L j mem) (L.cell a) (L.cell u)=image L j (Function.update mem a u) := by
  unfold image
  rw [Function.update_comm (L.away a)]
  rw [←WordImage.image_update (underlying L)]
  rfl

theorem write_clock (L : Layout w v) (j k : ℕ) (mem : Memory w) :
    Function.update (image L j mem) L.clock (stamp v k)=image L k mem := by simp [image]

def liftWord (L : Layout w v) : Op w X → Op v X
  | .pure x => .pure x
  | .read a k => .read (L.cell a) (fun u => liftWord L (k (Function.invFun L.cell u)))
  | .write a u p => .write (L.cell a) (L.cell u) (liftWord L p)

theorem lift_run (L : Layout w v) (p : Op w X) (j : ℕ) (mem : Memory w) :
    (liftWord L p).run (image L j mem) =
      let z := p.run mem
      (z.1,image L j z.2.1,z.2.2) := by
  induction p generalizing mem with
  | pure _ => rfl
  | read a k ih => simp [liftWord,Program.run,read_cell,Function.leftInverse_invFun L.cell.injective (mem a),ih]
  | write a u k ih => simp [liftWord,Program.run,write_cell,ih]

variable (L : Layout w v) (S : Schedule n F U Q A) (D : Target F U Q A w Ω)

def updateProgram (a : Ω) (x : Fin n) : Op v Bool := do
  let j ← Program.load L.clock
  let _ ← liftWord L (script D a j.val ((S.insert x).map Sum.inl))
  Program.store L.clock (stamp v (j.val+(S.insert x).length))
  pure false

def finalProgram (a : Ω) (q : Fin n) : Op v Bool := do
  let j ← Program.load L.clock
  let out ← liftWord L (script D a j.val (S.finish q))
  pure (S.decode q out)

def machine : Machine n v Ω where
  UState := Op v Bool
  QState := Op v Bool × Local v
  preprocess a f := image L 0 (D.init a (S.initial f))
  startUpdate := updateProgram L S D
  updateStep := Streaming.forgetReport stepWord
  startQuery a q := (finalProgram L S D a q,fun _ => none)
  queryStep := compile stepWord

def tape (Ω : Type) : RandomTape Ω Ω := ⟨id,fun _ => id,id⟩

theorem update_eq (a : Ω) (x : Fin n) (mem : Memory w) (j : ℕ) (fits : j<2^v) :
    let z := (script D a j ((S.insert x).map Sum.inl)).run mem
    insertOne (machine L S D) a x (image L j mem) =
      some (image L (j+(S.insert x).length) z.2.1,z.2.2+2) := by
  have read : image L j mem L.clock=stamp v j := by simp [image]
  have len : (stamp v j).val=j := Nat.mod_eq_of_lt fits
  have run := memory_and_cost (updateProgram L S D a x) (image L j mem)
  have ex := finish_eq_some _ (fun le ok => updateRun_mono _ le _ _ ok) run
  unfold insertOne
  change finish (fun k => updateRun (Streaming.forgetReport stepWord) k (updateProgram L S D a x) _) = _
  rw [ex]
  simp [updateProgram,Program.run_bind,read,len,lift_run,write_clock,Nat.add_comm,Nat.add_assoc]; omega

theorem final_eq (a : Ω) (q : Fin n) (mem : Memory w) (j : ℕ) (fits : j<2^v) :
    let z := (script D a j (S.finish q)).run mem
    let ds := machine L S D
    finish (fun fuel => result (Simulation.run ds.queryStep (image L j mem) fuel (ds.startQuery a q))) =
      some (S.decode q z.1,z.2.2+1) := by
  have read : image L j mem L.clock=stamp v j := by simp [image]
  have len : (stamp v j).val=j := Nat.mod_eq_of_lt fits
  have rr := bit_report (finalProgram L S D a q) (image L j mem)
  let op := finalProgram L S D a q
  let ran := op.run (image L j mem)
  have done : result (Simulation.run (machine L S D).queryStep (image L j mem) ran.2.2 ((machine L S D).startQuery a q)) =
      some (ran.1,ran.2.2) := (QueryNormalization.correct _ _ _ _ (fun _ => none)).trans rr
  let kernel := fun k => result (Simulation.run (machine L S D).queryStep (image L j mem) k ((machine L S D).startQuery a q))
  have stable {low high : ℕ} {z : Bool × ℕ} (hh : low ≤ high) (ok : kernel low=some z) : kernel high=some z := by
    obtain ⟨bit,hb,_⟩ := Option.map_eq_some_iff.mp ok
    unfold kernel
    rw [VerifiedEpoch.run_stable (machine L S D).queryStep (image L j mem) low ((machine L S D).startQuery a q) bit hb high
      ((VerifiedEpoch.run_length_le _ _ _ _).trans hh)]
    exact ok
  have ex := finish_eq_some kernel stable done
  change finish kernel=_
  rw [ex]
  simp [op,ran,finalProgram,Program.run_bind,read,len,lift_run,Nat.add_comm]

end
end DisjointnessDraft.Transfer.Compiler
