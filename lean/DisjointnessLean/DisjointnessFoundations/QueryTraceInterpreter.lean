import Std

namespace DisjointnessFoundations.Simulation

variable {Addr Word State : Type}

inductive QueryStep (Addr Word State : Type) where
  | done (answer : Bool)
  | read (address : Addr) (resume : Word → State)

structure Transcript (Addr Word : Type) where
  probes : List (Addr × Word)
  answer : Option Bool

def Transcript.prepend (a : Addr) (w : Word) (t : Transcript Addr Word) :
    Transcript Addr Word := ⟨(a,w)::t.probes, t.answer⟩

def run (step : State → QueryStep Addr Word State) (mem : Addr → Word) :
    Nat → State → Transcript Addr Word
  | 0, s => match step s with
    | .done b => ⟨[],some b⟩
    | .read _ _ => ⟨[],none⟩
  | n+1, s => match step s with
    | .done b => ⟨[],some b⟩
    | .read a resume => (run step mem n (resume (mem a))).prepend a (mem a)

theorem probe_budget (step : State → QueryStep Addr Word State) (mem : Addr → Word)
    (fuel : Nat) (s : State) : (run step mem fuel s).probes.length ≤ fuel := by
  induction fuel generalizing s with
  | zero => cases h : step s <;> simp [run,h]
  | succ n ih =>
    cases h : step s with
    | done b => simp [run,h]
    | read a k => simpa [run,h,Transcript.prepend] using Nat.succ_le_succ (ih (k (mem a)))

theorem recorded_word (step : State → QueryStep Addr Word State) (mem : Addr → Word)
    (fuel : Nat) (s : State) :
    ∀ entry ∈ (run step mem fuel s).probes, entry.2 = mem entry.1 := by
  induction fuel generalizing s with
  | zero => cases h : step s <;> simp [run,h]
  | succ n ih =>
    cases h : step s with
    | done b => simp [run,h]
    | read a k =>
      intro entry hm
      simp [run,h,Transcript.prepend] at hm
      rcases hm with rfl | hm
      · rfl
      · exact ih _ _ hm

theorem first_difference (step : State → QueryStep Addr Word State) (left right : Addr → Word)
    (fuel : Nat) (s : State) (hne : run step left fuel s ≠ run step right fuel s) :
    ∃ (pre : List (Addr × Word)) (a : Addr) (xs ys : List (Addr × Word)),
      (run step left fuel s).probes = pre ++ ((a,left a)::xs) ∧
      (run step right fuel s).probes = pre ++ ((a,right a)::ys) ∧ left a ≠ right a := by
  induction fuel generalizing s with
  | zero => cases h : step s <;> simp [run,h] at hne
  | succ n ih =>
    cases h : step s with
    | done b => simp [run,h] at hne
    | read a k =>
      by_cases same : left a = right a
      · have htail : run step left n (k (left a)) ≠ run step right n (k (left a)) := by
          intro e
          apply hne
          simp only [run,h]
          rw [e,same]
        obtain ⟨pre,b,xs,ys,l,r,ne⟩ := ih _ htail
        refine ⟨(a,left a)::pre,b,xs,ys,?_,?_,ne⟩
        · simp [run,h,Transcript.prepend,l]
        · simp [run,h,Transcript.prepend,←same,r]
      · exact ⟨[],a,(run step left n (k (left a))).probes,(run step right n (k (right a))).probes,by simp [run,h,Transcript.prepend],by simp [run,h,Transcript.prepend],same⟩

section Memory

variable [DecidableEq Addr]

def applyWrites : (Addr → Word) → List (Addr × Word) → Addr → Word
  | mem, [] => mem
  | mem, (a,v)::rest => applyWrites (fun x => if x=a then v else mem x) rest

def Written (writes : List (Addr × Word)) (a : Addr) : Prop :=
  ∃ w, (a,w) ∈ writes

theorem applyWrites_of_unwritten (mem : Addr → Word) (writes : List (Addr × Word))
    (a : Addr) (ha : ¬ Written writes a) : applyWrites mem writes a = mem a := by
  induction writes generalizing mem with
  | nil => rfl
  | cons p rest ih =>
    rcases p with ⟨b,v⟩
    have hn : ¬ Written rest a := fun ⟨u,hu⟩ => ha ⟨u,List.mem_cons_of_mem _ hu⟩
    have ne : a ≠ b := fun e => ha ⟨v,e ▸ List.mem_cons_self⟩
    rw [applyWrites,ih _ hn,if_neg ne]

def EpochCells (epoch later : List (Addr × Word)) (a : Addr) : Prop :=
  Written epoch a ∧ ¬ Written later a

end Memory
end DisjointnessFoundations.Simulation
