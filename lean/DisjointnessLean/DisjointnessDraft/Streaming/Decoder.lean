import DisjointnessDraft.Streaming.Binary
import Mathlib.Data.Fintype.Card

/-! A one-block buffer for arbitrary binary streams, including partial and
invalid codewords. An invalid block rules out every future completion. -/
namespace DisjointnessDraft.Streaming.Binary
open Classical
noncomputable section
abbrev Partial (b : ℕ) := {xs : List Bool // xs.length<b}
abbrev Buffer (b : ℕ) := Option (Partial b)
def empty (hb : 0<b) : Buffer b := some ⟨[],hb⟩

def signature (v : Partial b) : Fin b × (Fin b → Bool) :=
  (⟨v.val.length,v.property⟩,fun i => v.val[i.val]?.getD false)
theorem signature_injective (b : ℕ) : Function.Injective (@signature b) := by
  rintro ⟨xs,hx⟩ ⟨ys,hy⟩ eq
  have len := congrArg (fun v : Fin b × (Fin b → Bool) => v.1.val) eq
  change xs.length=ys.length at len
  apply Subtype.ext
  apply List.ext_getElem len
  intro i ix iy
  have h := congrArg (fun v : Fin b × (Fin b → Bool) => v.2 ⟨i,ix.trans hx⟩) eq
  simpa [signature,List.getElem?_eq_getElem,ix,iy] using h
instance finitePart (b : ℕ) : Fintype (Partial b) := Fintype.ofInjective _ (signature_injective b)
theorem buffer_space (b : ℕ) : Fintype.card (Buffer b)≤b*2^b+1 := by
  have h := Fintype.card_le_of_injective _ (signature_injective b)
  simpa [Buffer] using Nat.add_le_add_right h 1

variable {α : Type}
def decode (C : Code α b) (xs : List Bool) : Option α :=
  if h : ∃ a,C.bits a=xs then some h.choose else none
theorem decoded (C : Code α b) (xs : List Bool) (a : α) (h : decode C xs=some a) : C.bits a=xs := by
  unfold decode at h; split at h
  · rename_i yes; cases h; exact yes.choose_spec
  · contradiction
theorem rejected (C : Code α b) (xs : List Bool) (h : decode C xs=none) : ∀ a,C.bits a≠xs := by
  intro a e; simp [decode,show ∃ v,C.bits v=xs from ⟨a,e⟩] at h

def advanceBit (C : Code α b) (hb : 0<b) (u : Buffer b) (x : Bool) : Buffer b × Option α :=
  match u with
  | none => (none,none)
  | some p =>
    let block := p.val++[x]
    if h : block.length<b then (some ⟨block,h⟩,none)
    else match decode C block with | none => (none,none) | some s => (empty hb,some s)

def Invariant (C : Code α b) (raw : List Bool) (source : List α) : Buffer b → Prop
  | none => ∀ more : List Bool,∀ ys : List α,raw++more≠ys.flatMap C.bits
  | some p => raw=source.flatMap C.bits ++ p.val

theorem strip (C : Code α b) (hb : 0<b) (source : List α) (tail : List Bool) (ts : List α)
    (eq : source.flatMap C.bits++tail=ts.flatMap C.bits) :
    ∃ rest, ts=source++rest ∧ tail=rest.flatMap C.bits := by
  induction source generalizing ts with
  | nil => exact ⟨ts,rfl,by simpa using eq⟩
  | cons x xs ih =>
    cases ts with
    | nil =>
      have z := congrArg List.length eq; simp [C.length] at z; omega
    | cons y ys =>
      simp only [List.flatMap_cons,List.append_assoc] at eq
      obtain ⟨head,rest⟩ := List.append_inj eq (by simp)
      have same : x=y := C.table.injective (List.ofFn_injective head)
      obtain ⟨r,hr,he⟩ := ih ys rest
      exact ⟨r,by simp [same,hr],he⟩

theorem advance_invariant (C : Code α b) (hb : 0<b) (raw : List Bool) (src : List α)
    (buf : Buffer b) (x : Bool) (h : Invariant C raw src buf) :
    let next := advanceBit C hb buf x
    Invariant C (raw++[x]) (src++next.2.toList) next.1 := by
  cases buf with
  | none =>
    change ∀ (more : List Bool) (ys : List α),(raw++[x])++more≠ys.flatMap C.bits
    intro more ys bad
    exact h (x::more) ys (by simpa using bad)
  | some p =>
    change raw=src.flatMap C.bits++p.val at h
    subst raw
    let block := p.val++[x]
    by_cases small : block.length<b
    · simp only [advanceBit,dif_pos (show (p.val++[x]).length<b from small),Invariant,Option.toList_none,List.append_nil,List.append_assoc]
    · have len : block.length=b := by have h := p.property; dsimp [block] at *; simp at *; omega
      cases dec : decode C block with
      | some a =>
        have code := decoded C block a dec
        simp only [advanceBit,show ¬(p.val++[x]).length<b from small,dif_neg,show decode C (p.val++[x])=some a from dec,
          empty,Invariant,Option.toList_some,List.flatMap_append,List.flatMap_cons,List.flatMap_nil,List.append_nil]
        simp [code,block]
      | none =>
        change let next := advanceBit C hb (some p) x; _
        simp only [advanceBit,show ¬(p.val++[x]).length<b from small,dif_neg,show decode C (p.val++[x])=none from dec,Invariant]
        intro more ys bad
        obtain ⟨rest,_,eq⟩ := strip C hb src (block++more) ys (by simpa [block] using bad)
        cases rest with
        | nil => have z := congrArg List.length eq; simp [len] at z; omega
        | cons a as =>
          have lh : block.length=(C.bits a).length := by rw [len,C.length]
          exact rejected C block dec a (List.append_inj eq lh).1.symm

theorem complete (C : Code α b) (hb : 0<b) (raw : List Bool) (src : List α)
    (buf : Buffer b) (h : Invariant C raw src buf) (ys : List α) :
    raw=ys.flatMap C.bits ↔ (∃ p : Partial b,buf=some p ∧ p.val=[]) ∧ src=ys := by
  cases buf with
  | none => simp only [reduceCtorEq,false_and,exists_false,and_false,false_and,iff_false]; simpa using h [] ys
  | some p =>
    change raw=src.flatMap C.bits++p.val at h; subst raw
    constructor
    · intro e
      obtain ⟨r,eq,z⟩ := strip C hb src p.val ys e
      cases r with
      | nil => simp_all
      | cons a as =>
        have len := congrArg List.length z
        simp only [List.flatMap_cons,List.length_append,C.length] at len
        have short := p.property; omega
    · rintro ⟨⟨r,eq,ep⟩,rfl⟩
      obtain rfl := Option.some.inj eq; simp [ep]

def aligned (u : Buffer b) := ∃ p : Partial b,u=some p ∧ p.val=[]
theorem next_aligned (C : Code α b) (hb : 0<b) (u : Buffer b) (x : Bool) :
    aligned (advanceBit C hb u x).1 ↔ (advanceBit C hb u x).2.isSome := by
  cases u with
  | none => simp [advanceBit,aligned]
  | some p =>
    by_cases short : (p.val++[x]).length<b
    · simp only [advanceBit,dif_pos short]; simp [aligned]
    · simp only [advanceBit,dif_neg short]
      cases decode C (p.val++[x]) <;> simp [empty,aligned]

end
end DisjointnessDraft.Streaming.Binary
