import DisjointnessFoundations.FiniteProbePrograms

namespace DisjointnessFoundations.WordProgram

open CellProbe Simulation

variable {A W R : Type} {w : ℕ} [DecidableEq A]

structure Codec (A W : Type) (w : ℕ) where
  live : A → Prop
  addr : A → Word w
  inject : Set.InjOn addr {a | live a}
  encode : W → Word w
  decode : Word w → W

namespace Codec

variable (c : Codec A W w)

def represents (mem : A → W) (physical : Memory w) : Prop :=
  ∀ a, c.live a → c.decode (physical (c.addr a)) = mem a

def valid (c : Codec A W w) (p : Program A W R) (mem : A → W) : Prop :=
  match p with
  | .pure _ => True
  | .read a k => c.live a ∧ valid c (k (mem a)) mem
  | .write a v k => c.live a ∧ c.decode (c.encode v) = v ∧ valid c k (Function.update mem a v)

def readOnly (c : Codec A W w) (p : Program A W R) (mem : A → W) : Prop :=
  match p with
  | .pure _ => True
  | .read a k => c.live a ∧ readOnly c (k (mem a)) mem
  | .write .. => False

def updateStep : Program A W R → UpdateStep (Word w) (Program A W R)
  | .pure _ => .done
  | .read a k => .read (c.addr a) (k ∘ c.decode)
  | .write a v k => .write (c.addr a) (c.encode v) k

def queryStep : Program A W Bool → QueryStep (Word w) (Word w) (Program A W Bool)
  | .pure b => .done b
  | .read a k => .read (c.addr a) (k ∘ c.decode)
  | .write .. => .done false

theorem write_represents {mem : A → W} {physical : Memory w} (rep : c.represents mem physical)
    {a : A} {v : W} (live : c.live a) (fits : c.decode (c.encode v)=v) :
    c.represents (Function.update mem a v) (Function.update physical (c.addr a) (c.encode v)) := by
  intro j hj
  by_cases h : j=a
  · subst j; simp [fits]
  · have hp : c.addr j ≠ c.addr a := fun e => h (c.inject hj live e)
    simp [Function.update_of_ne hp,Function.update_of_ne h,rep j hj]

theorem compile_update (p : Program A W R) (mem : A → W) (physical : Memory w)
    (rep : c.represents mem physical) (ok : c.valid p mem) :
    let out := p.run mem
    ∃ m, updateRun c.updateStep out.2.2 p physical = some (m,out.2.2) ∧ c.represents out.2.1 m := by
  induction p generalizing mem physical with
  | pure x => exact ⟨physical,rfl,rep⟩
  | read a k ih =>
    obtain ⟨m,h,rep'⟩ := ih (mem a) mem physical rep ok.2
    refine ⟨m,?_,rep'⟩
    simp only [Program.run]
    rw [Nat.add_comm 1,updateRun,updateStep]
    simp only [Function.comp_apply,rep a ok.1,h]
    rfl
  | write a v k ih =>
    obtain ⟨m,h,rep'⟩ := ih _ _ (c.write_represents rep ok.1 ok.2.1) ok.2.2
    refine ⟨m,?_,rep'⟩
    simp only [Program.run]
    rw [Nat.add_comm 1,updateRun,updateStep]
    simp only [h]
    rfl

theorem compile_query (p : Program A W Bool) (mem : A → W) (physical : Memory w)
    (rep : c.represents mem physical) (ok : c.readOnly p mem) :
    let result := p.run mem
    let t := Simulation.run c.queryStep physical result.2.2 p
    t.answer=some result.1 ∧ t.probes.length=result.2.2 := by
  induction p generalizing mem physical with
  | pure x => exact ⟨rfl,rfl⟩
  | read a k ih =>
    obtain ⟨ans,len⟩ := ih (mem a) mem physical rep ok.2
    simp only [Program.run]
    rw [Nat.add_comm 1,Simulation.run,queryStep]
    simp [Function.comp_def,rep a ok.1,Transcript.prepend,ans,len]
  | write a v k ih => exact False.elim ok

end Codec
end DisjointnessFoundations.WordProgram
