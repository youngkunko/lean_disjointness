import DisjointnessFoundations.ProbeMachineInterface
import Mathlib.Tactic.Ring
import Mathlib.Algebra.Group.Int.Defs
import Mathlib.Data.List.Count

namespace DisjointnessFoundations.WordProgram

inductive Program (A W : Type) (R : Type) : Type where
  | pure (x : R)
  | read (a : A) (cont : W → Program A W R)
  | write (a : A) (v : W) (cont : Program A W R)

namespace Program
variable {A W R S : Type}

protected def bind (p : Program A W R) (f : R → Program A W S) : Program A W S :=
  match p with
  | .pure x => f x
  | .read a k => .read a (fun v => (k v).bind f)
  | .write a v k => .write a v (k.bind f)

instance : Monad (Program A W) where
  pure := Program.pure
  bind := Program.bind

def load (a : A) : Program A W W := .read a .pure

def store (a : A) (v : W) : Program A W Unit := .write a v (.pure ())

def run [DecidableEq A] (p : Program A W R) (mem : A → W) : R × (A → W) × ℕ :=
  match p with
  | .pure x => (x,mem,0)
  | .read a k =>
    let o := (k (mem a)).run mem
    (o.1,o.2.1,1+o.2.2)
  | .write a v k =>
    let o := k.run (Function.update mem a v)
    (o.1,o.2.1,1+o.2.2)

@[simp] theorem run_pure [DecidableEq A] (x : R) (mem : A → W) :
    (pure x : Program A W R).run mem = (x,mem,0) := rfl

@[simp] theorem run_load [DecidableEq A] (a : A) (mem : A → W) :
    (load a).run mem = (mem a,mem,1) := rfl

@[simp] theorem run_store [DecidableEq A] (a : A) (v : W) (mem : A → W) :
    (store a v).run mem = ((),Function.update mem a v,1) := rfl

theorem run_bind [DecidableEq A] (p : Program A W R) (f : R → Program A W S) (mem : A → W) :
    (p >>= f).run mem =
    let a := p.run mem
    let b := (f a.1).run a.2.1
    (b.1,b.2.1,a.2.2+b.2.2) := by
  change (p.bind f).run mem = _
  induction p generalizing mem with
  | pure x => simp [Program.bind,run]
  | read a k ih => simp [Program.bind,run,ih,Nat.add_assoc]
  | write a v k ih => simp [Program.bind,run,ih,Nat.add_assoc]

def loads (as : List A) : Program A W (List W) :=
  match as with
  | [] => pure []
  | a :: tail => do
    let v ← load a
    let vs ← loads tail
    pure (v :: vs)

@[simp] theorem run_loads [DecidableEq A] (as : List A) (mem : A → W) :
    (loads as).run mem = (as.map mem,mem,as.length) := by
  induction as with
  | nil => rfl
  | cons a as ih => simp [loads,run_bind,ih,Nat.add_comm]

def addEach (as : List A) (d : ℤ) : Program A ℤ Unit :=
  match as with
  | [] => pure ()
  | a :: tail => do
    let n ← load a
    store a (n+d)
    addEach tail d

@[simp] theorem run_addEach [DecidableEq A] (as : List A) (d : ℤ) (mem : A → ℤ) :
    (addEach as d).run mem = ((),fun k => mem k+(as.count k:ℤ)*d,2*as.length) := by
  induction as generalizing mem with
  | nil => simp [addEach]
  | cons a as ih =>
    simp only [addEach,run_bind,run_load,run_store,ih,Prod.mk.injEq, true_and]
    constructor
    · funext k
      by_cases h : a=k
      · subst k; simp [List.count_cons]; ring
      · simp [List.count_cons,h,Ne.symm h]
    · simp only [List.length_cons]; omega

end Program
end DisjointnessFoundations.WordProgram
