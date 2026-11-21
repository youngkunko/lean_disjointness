import DisjointnessDraft.Transfer.Operational

/-! A tape-independent controller uses its own word array to compute target
operation arguments and the final decoder. Auxiliary reads and writes cost
one probe each. The physical word has one additional address bit. -/
namespace DisjointnessDraft.Transfer.Auxiliary
open DisjointnessFoundations CellProbe WordProgram Compiler Classical
noncomputable section
abbrev Addr (w : ℕ) := Word w ⊕ Word w
abbrev Virtual (w : ℕ) (X : Type) := Program (Addr w) (Word w) X
def joint (target aux : Memory w) : Addr w → Word w := Sum.elim target aux
def words (w : ℕ) : WordImage.Layout (Addr w) (Word w) (w+1) where
  addr := (Fintype.equivFinOfCardEq (show Fintype.card (Addr w)=2^(w+1) by
    simp [Addr,Word,pow_succ]; omega)).toEmbedding
  value := Fin.castLEEmb (Nat.pow_le_pow_right (by decide) (Nat.le_succ w))
  blank := 0
def encode (p : Virtual w X) : Op (w+1) X :=
  match p with
  | .pure x => .pure x
  | .read a k => .read ((words w).addr a) (fun u => encode (k (Function.invFun (words w).value u)))
  | .write a u k => .write ((words w).addr a) ((words w).value u) (encode k)

theorem encoded_run (p : Virtual w X) (mem : Addr w → Word w) :
    (encode p).run (WordImage.image (words w) mem)=
    let z := p.run mem
    (z.1,WordImage.image (words w) z.2.1,z.2.2) := by
  induction p generalizing mem with
  | pure x => rfl
  | read a k ih =>
    simp [encode,Program.run,WordImage.image_at,Function.leftInverse_invFun (words w).value.injective (mem a),ih]
  | write a u k ih =>
    simp [encode,Program.run,WordImage.image_update,ih]

def targetOp (p : Op w X) : Virtual w X := match p with
  | .pure x => .pure x
  | .read a k => .read (.inl a) fun v => targetOp (k v)
  | .write a u k => .write (.inl a) u (targetOp k)
def auxOp (p : Op w X) : Virtual w X := match p with
  | .pure x => .pure x
  | .read a k => .read (.inr a) fun v => auxOp (k v)
  | .write a u k => .write (.inr a) u (auxOp k)

private theorem write_left (m a : Memory w) (i v : Word w) :
    Function.update (joint m a) (.inl i) v=joint (Function.update m i v) a := by
  funext x; rcases x with x|x <;> by_cases eq : x=i <;> simp [joint,Function.update,eq]
private theorem write_right (m a : Memory w) (i v : Word w) :
    Function.update (joint m a) (.inr i) v=joint m (Function.update a i v) := by
  funext x; rcases x with x|x <;> by_cases eq : x=i <;> simp [joint,Function.update,eq]

theorem target_run (p : Op w X) (m a : Memory w) :
    (targetOp p).run (joint m a)=let z:=p.run m; (z.1,joint z.2.1 a,z.2.2) := by
  induction p generalizing m with
  | pure x => rfl
  | read i k ih => simp [targetOp,Program.run,show joint m a (.inl i)=m i from rfl,ih]
  | write i v k ih => simp [targetOp,Program.run,write_left,ih]
theorem aux_run (p : Op w X) (m a : Memory w) :
    (auxOp p).run (joint m a)=let z:=p.run a; (z.1,joint m z.2.1,z.2.2) := by
  induction p generalizing a with
  | pure x => rfl
  | read i k ih => simp [auxOp,Program.run,show joint m a (.inr i)=a i from rfl,ih]
  | write i v k ih => simp [auxOp,Program.run,write_right,ih]

structure Controller (n w : ℕ) (F U Q A : Type) where
  initial : Family n → F
  auxiliary : Family n → Memory w
  insert : Fin n → Op w (ℕ × List U)
  finish : Fin n → Op w (ℕ × List (Instr U Q) × (List A → Bool))

variable (C : Controller n w F U Q A) (D : Compiler.Target F U Q A w Ω)
def update (a : Ω) (x : Fin n) : Op (w+1) Bool := encode do
  let s ← auxOp (C.insert x)
  let _ ← targetOp (script D a s.1 (s.2.map Sum.inl))
  pure false
def query (a : Ω) (q : Fin n) : Op (w+1) Bool := encode do
  let s ← auxOp (C.finish q)
  let out ← targetOp (script D a s.1 s.2.1)
  pure (s.2.2 out)

@[simp] private theorem pure_virtual (x : X) (m : Addr w → Word w) :
    (pure x : Virtual w X).run m=(x,m,0) := rfl

def image (m aux : Memory w) := WordImage.image (words w) (joint m aux)

theorem update_run (a : Ω) (x : Fin n) (m aux : Memory w) :
    (update C D a x).run (image m aux)=
    let s := (C.insert x).run aux
    let z := (script D a s.1.1 (s.1.2.map Sum.inl)).run m
    (false,image z.2.1 s.2.1,s.2.2+z.2.2) := by
  simp [update,image,encoded_run,Program.run_bind,aux_run,target_run]
theorem query_run (a : Ω) (q : Fin n) (m aux : Memory w) :
    (query C D a q).run (image m aux)=
    let s := (C.finish q).run aux
    let z := (script D a s.1.1 s.1.2.1).run m
    (s.1.2.2 z.1,image z.2.1 s.2.1,s.2.2+z.2.2) := by
  simp [query,image,encoded_run,Program.run_bind,aux_run,target_run]

/-- A final source query can choose auxiliary addresses after observing a
target report. Each target call supplies its operation ordinal. -/
inductive QueryProgram (w : ℕ) (U Q A : Type) where
  | done (answer : Bool)
  | read (address : Word w) (next : Word w → QueryProgram w U Q A)
  | write (address value : Word w) (next : QueryProgram w U Q A)
  | call (ordinal : ℕ) (op : Instr U Q) (next : Option A → QueryProgram w U Q A)

namespace QueryProgram

structure Outcome (w : ℕ) (U Q : Type) where
  answer : Bool
  auxiliary : Memory w
  operations : List (Instr U Q)
  probes : ℕ
  ordinalsCorrect : Prop

def report (spec : F → List (Instr U Q) → Q → A) (f : F) (h : List (Instr U Q)) :
    Instr U Q → Option A
  | .inl _ => none
  | .inr q => some (spec f h q)

/-- Replay the controller with a target-answer function. This mathematical
replay describes its path and cost but is never run by the physical machine. -/
def inspect (spec : F → List (Instr U Q) → Q → A) (f : F)
    (p : QueryProgram w U Q A) (h : List (Instr U Q)) (aux : Memory w) : Outcome w U Q :=
  match p with
  | .done b => ⟨b,aux,[],0,True⟩
  | .read i k =>
      let v := inspect spec f (k (aux i)) h aux
      {v with probes := v.probes+1}
  | .write i x k =>
      let v := inspect spec f k h (Function.update aux i x)
      {v with probes := v.probes+1}
  | .call idx op k =>
      let v := inspect spec f (k (report spec f h op)) (h++[op]) aux
      {v with operations := op::v.operations, ordinalsCorrect := idx=h.length ∧ v.ordinalsCorrect}

private def pad (b : Bool) : ℕ → Virtual w Bool
  | 0 => .pure b
  | n+1 => .read (.inr 0) fun _ => pad b n

private theorem pad_run (b : Bool) (n : ℕ) (m : Addr w → Word w) :
    (pad b n).run m=(b,m,n) := by
  induction n with
  | zero => rfl
  | succ n ih => simp [pad,Program.run,ih,Nat.add_comm]

/-- Auxiliary reads after termination fill the remaining budget. Consequently
the auxiliary cost is measurable even if distinct legal reports use distinct
numbers of useful probes. -/
def physical (D : Compiler.Target F U Q A w Ω) (a : Ω) (p : QueryProgram w U Q A)
    (remaining : ℕ) : Virtual w Bool :=
  match p with
  | .done b => pad b remaining
  | .read i k => .read (.inr i) fun x => physical D a (k x) (remaining-1)
  | .write i x k => .write (.inr i) x (physical D a k (remaining-1))
  | .call i op k => do
      let v ← targetOp (targetStep D a i op)
      physical D a (k v) remaining

def observedAnswer (D : Compiler.Target F U Q A w Ω) (a : Ω) (f : F)
    (h : List (Instr U Q)) (q : Q) : A :=
  ((D.query a h.length q).run (observed D a f h).2.1).1

private theorem step_report (D : Compiler.Target F U Q A w Ω) (a : Ω) (f : F)
    (h : List (Instr U Q)) (op : Instr U Q) :
    ((targetStep D a h.length op).run (observed D a f h).2.1).1 =
      report (observedAnswer D a) f h op := by
  cases op <;> simp [report,targetStep,Program.run_bind,observedAnswer]

theorem physical_run (D : Compiler.Target F U Q A w Ω) (a : Ω) (f : F)
    (p : QueryProgram w U Q A) (h : List (Instr U Q)) (aux : Memory w) (budget : ℕ)
    (indices : (inspect (observedAnswer D a) f p h aux).ordinalsCorrect)
    (bound : (inspect (observedAnswer D a) f p h aux).probes≤budget) :
    let v := inspect (observedAnswer D a) f p h aux
    (physical D a p budget).run (joint (observed D a f h).2.1 aux) =
      (v.answer,joint (observed D a f (h++v.operations)).2.1 v.auxiliary,
        budget+total D a f h v.operations) := by
  induction p generalizing h aux budget with
  | done b => simp [physical,pad_run,inspect,total]
  | read i k ih =>
    cases budget with
    | zero => simp [inspect] at bound
    | succ n =>
      have hb : (inspect (observedAnswer D a) f (k (aux i)) h aux).probes≤n :=
        Nat.le_of_succ_le_succ bound
      have rest := ih (aux i) h aux n indices hb
      simp [physical,Program.run,show joint (observed D a f h).2.1 aux (.inr i)=aux i from rfl,
        rest,inspect,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm]
  | write i x k ih =>
    cases budget with
    | zero => simp [inspect] at bound
    | succ n =>
      have hb : (inspect (observedAnswer D a) f k h (Function.update aux i x)).probes≤n :=
        Nat.le_of_succ_le_succ bound
      have rest := ih h (Function.update aux i x) n indices hb
      simp [physical,Program.run,write_right,rest,inspect,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm]
  | call idx op k ih =>
    obtain ⟨rfl,tail⟩ := indices
    have rest := ih (report (observedAnswer D a) f h op) (h++[op]) aux budget tail bound
    simp only [physical,Program.run_bind,target_run,step_report,←next_memory,rest,inspect,total,
      List.append_assoc,List.singleton_append]
    simp [expense,Nat.add_assoc,Nat.add_left_comm,Nat.add_comm]

end QueryProgram

end
end DisjointnessDraft.Transfer.Auxiliary
