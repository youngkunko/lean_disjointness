import DisjointnessDraft.Streaming.Parser
import DisjointnessFoundations.LogicalWordLayout

/-! Separate word cells store the parser tag, the linked list of distinct
symbols, its membership flags, and the preprocessed incidence table. -/
namespace DisjointnessDraft.Streaming.Storage
open DisjointnessFoundations DisjointnessFoundations.WordProgram
open Program (load store run_bind run_load)
inductive Tag where
  | first | live | closed (answer : Bool)
  deriving DecidableEq, Fintype

inductive Addr (n m : ℕ) where
  | tag | head | next (j : Fin n) | seen (j : Fin n) | entry (q : Fin m) (j : Fin n)
  deriving DecidableEq, Fintype

inductive Val (n : ℕ) where
  | tag (v : Tag) | ptr (v : Option (Fin n)) | bit (v : Bool)
  deriving DecidableEq, Fintype

instance : Inhabited (Val n) := ⟨.ptr none⟩
abbrev Store (n : ℕ) := Tag × List (Fin n)
abbrev P (n m : ℕ) (α : Type) := Program (Addr n m) (Val n) α

@[simp] private theorem run_return {α : Type} (x : α) (mem : Addr n m → Val n) :
    (Pure.pure x : P n m α).run mem = (x,mem,0) := rfl

def links : List (Fin n) → Fin n → Option (Fin n)
  | [], _ => none
  | a::xs, x => if x=a then xs.head? else links xs x

def words (f : Fin m → Finset (Fin n)) (p : Tag) (xs : List (Fin n)) : Addr n m → Val n
  | .tag => .tag p
  | .head => .ptr xs.head?
  | .next a => .ptr (links xs a)
  | .seen a => .bit (decide (a ∈ xs))
  | .entry q a => .bit (decide (a ∈ f q))

def parser (s : Store n) : Parser n :=
  match s.1 with
  | .first => .first
  | .live => .live s.2
  | .closed b => .closed b

def nextState (f : Fin m → Finset (Fin n)) (s : Store n) (c : Symbol n m) : Store n :=
  match s.1,c with
  | .first,none => (.live,s.2)
  | .live,some (.inl j) => (.live,push j s.2)
  | .live,some (.inr q) => (.closed (decide (∀ a ∈ s.2,a ∉ f q)),s.2)
  | _,_ => (.closed false,s.2)

def valid (s : Store n) := s.2.Nodup ∧ (s.1=.first → s.2=[])

theorem valid_next (f : Fin m → Finset (Fin n)) (s : Store n) (c : Symbol n m) (h : valid s) :
    valid (nextState f s c) ∧ parser (nextState f s c)=advance f (parser s) c := by
  rcases s with ⟨p,xs⟩
  rcases h with ⟨nd,start⟩
  change xs.Nodup at nd
  cases p <;> cases c with
  | none => simp_all [valid,nextState,parser,advance]
  | some a => cases a with
    | inl j => by_cases mem : j∈xs <;> simp_all [valid,nextState,parser,advance,push]
    | inr q => simp_all [valid,nextState,parser,advance]

private theorem tag_update (f : Fin m → Finset (Fin n)) (old now : Tag) (xs : List (Fin n)) :
    Function.update (words f old xs) .tag (.tag now) = words f now xs := by
  funext a; cases a <;> simp [words,Function.update]

private theorem fresh_update (f : Fin m → Finset (Fin n)) (p : Tag) (xs : List (Fin n)) (j : Fin n) :
    Function.update
      (Function.update (Function.update (words f p xs) (.next j) (.ptr xs.head?)) (.seen j) (.bit true))
      .head (.ptr (some j)) = words f p (j::xs) := by
  funext a
  cases a with
  | tag | head | entry => simp [words,Function.update]
  | next a => by_cases e : a=j <;> simp [words,Function.update,links,e]
  | seen a => by_cases e : a=j <;> simp [words,Function.update,e]

def scan (q : Fin m) : ℕ → Option (Fin n) → P n m Bool
  | 0,_ | _+1,none => pure true
  | k+1,some x => do
    let v ← load (.entry q x)
    let ptr ← load (.next x)
    let b ← scan q k (match ptr with | .ptr a => a | _ => none)
    pure (b && decide (v = .bit false))

private theorem scan_run (f : Fin m → Finset (Fin n)) (p : Tag) (whole xs : List (Fin n)) (q : Fin m)
    (fuel : ℕ) (len : xs.length≤fuel) (chain : ∀ j∈xs, links whole j=links xs j) (nd : xs.Nodup) :
    (scan q fuel xs.head?).run (words f p whole) =
    (decide (∀ a∈xs,a∉ f q),words f p whole,2*xs.length) := by
  induction xs generalizing fuel with
  | nil => cases fuel <;> simp [scan]
  | cons x xs ih =>
    cases fuel with
    | zero => simp at len
    | succ k =>
      have fresh := (List.nodup_cons.mp nd).1
      have here : links whole x=xs.head? := by simpa [links] using chain x (by simp)
      have tail (a : Fin n) (ha : a∈xs) : links whole a=links xs a := by
        have ne : a≠x := fun e => fresh (e ▸ ha)
        simpa [links,ne] using chain a (by simp [ha])
      simp only [List.head?_cons,scan,run_bind,run_load,words,here]
      rw [ih k (by simpa using len) tail (List.nodup_cons.mp nd).2]
      (simp [Nat.mul_add,Nat.add_comm,Bool.and_comm]; omega)

def close (p : Tag) (b : Bool) : P n m Bool := do
  store .tag (.tag p)
  pure b

def operation (c : Symbol n m) : P n m Bool := do
  let tag ← load .tag
  match tag,c with
  | .tag .first,none => close .live false
  | .tag .live,some (.inl j) =>
    let v ← load (.seen j)
    if v = .bit true then pure false else do
      let old ← load .head
      store (.next j) old
      store (.seen j) (.bit true)
      store .head (.ptr (some j))
      pure false
  | .tag .live,some (.inr q) =>
    let head ← load .head
    let b ← scan q n (match head with | .ptr a => a | _ => none)
    close (.closed b) b
  | _,_ => close (.closed false) false

def probes (s : Store n) (c : Symbol n m) : ℕ :=
  match s.1,c with
  | .live,some (.inl j) => if j ∈ s.2 then 2 else 6
  | .live,some (.inr _) => 3+2*s.2.length
  | _,_ => 2

theorem operation_run (f : Fin m → Finset (Fin n)) (s : Store n) (c : Symbol n m) (ok : valid s) :
    (operation c).run (words f s.1 s.2) =
      let t := nextState f s c
      (accepted (parser t),words f t.1 t.2,probes s c) := by
  rcases s with ⟨p,xs⟩
  have nd : xs.Nodup := ok.1
  have len : xs.length≤n := by
    rw [←List.toFinset_card_of_nodup nd]
    simpa using Finset.card_le_univ xs.toFinset
  cases p <;> cases c with
  | none => simp [operation,run_bind,close,words,tag_update,nextState,parser,accepted,probes]
  | some sym => cases sym with
    | inl j =>
      by_cases h : j∈xs <;>
        simp [operation,run_bind,close,words,tag_update,fresh_update,nextState,parser,accepted,probes,push,h]
    | inr q =>
      have sc := scan_run f .live xs xs q n len (by simp) nd
      simp [operation,run_bind,close,words,tag_update,nextState,parser,accepted,probes,sc,Nat.add_comm] <;> omega

end DisjointnessDraft.Streaming.Storage
