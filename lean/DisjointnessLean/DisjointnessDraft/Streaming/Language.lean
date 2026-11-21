import Mathlib.Computability.RegularExpressions
import Mathlib.Data.Fintype.Card
import Mathlib.Data.List.FinRange
import Mathlib.Tactic

/-! The actual union, concatenation and star expressions used in the streaming reduction.
A symbol is either the start marker, a data coordinate or a query selector. -/
namespace DisjointnessDraft.Streaming
open Computability RegularExpression
abbrev Symbol (n m : ℕ) := Option (Fin n ⊕ Fin m)
abbrev Expr (n m : ℕ) := RegularExpression (Symbol n m)
def marker : Symbol n m := none
def datum (j : Fin n) : Symbol n m := some (.inl j)
def selector (q : Fin m) : Symbol n m := some (.inr q)

def alternation {α : Type} : List (RegularExpression α) → RegularExpression α
  | [] => 0
  | [a] => a
  | a :: b :: xs => a + alternation (b :: xs)

theorem mem_alternation {α : Type} (xs : List (RegularExpression α)) (s : List α) :
    s ∈ (alternation xs).matches' ↔ ∃ e ∈ xs, s ∈ e.matches' := by
  induction xs with
  | nil => simp [alternation]
  | cons a xs ih => cases xs with
    | nil => simp [alternation]
    | cons b xs => simpa only [alternation, matches'_add, Language.mem_add, List.mem_cons,
        exists_eq_or_imp] using (or_congr Iff.rfl ih)

def allowed (s : Finset (Fin n)) := (List.finRange n).filter (· ∉ s)

def branch (s : Finset (Fin n)) (q : Fin m) : Expr n m :=
  match allowed s with
  | [] => char marker * char (selector q)
  | j :: js => char marker * ((alternation ((j :: js).map (fun a => char (datum a)))).star *
      char (selector q))

def expression (f : Fin m → Finset (Fin n)) : Expr n m :=
  alternation ((List.finRange m).map (fun q => branch (f q) q))

def word (xs : List (Fin n)) (q : Fin m) : List (Symbol n m) :=
  marker :: (xs.map datum ++ [selector q])

private theorem star_literals {α : Type} (letters : List α) (s : List α) :
    s ∈ (alternation (letters.map char)).star.matches' ↔ ∀ a ∈ s, a ∈ letters := by
  rw [matches'_star, Language.mem_kstar]
  constructor
  · rintro ⟨parts,rfl,h⟩ a ha
    obtain ⟨piece,mem,found⟩ := List.mem_flatten.mp ha
    obtain ⟨e,he,eq⟩ := (mem_alternation _ _).mp (h piece mem)
    obtain ⟨c,hc,rfl⟩ := List.mem_map.mp he
    change piece = [c] at eq
    subst piece
    simpa [List.mem_singleton.mp found] using hc
  · intro h
    refine ⟨s.map (fun a => [a]),?_,?_⟩
    · clear h
      induction s with
      | nil => rfl
      | cons a s ih => change a::s = a::_; exact congrArg (a :: ·) ih
    intro piece mem
    obtain ⟨a,ha,rfl⟩ := List.mem_map.mp mem
    exact (mem_alternation _ _).mpr ⟨char a,List.mem_map.mpr ⟨a,h a ha,rfl⟩,rfl⟩

private theorem only_data (allowed : List (Fin n)) (x : List (Symbol n m)) :
    (∀ a ∈ x, a ∈ allowed.map datum) ↔
      ∃ xs : List (Fin n), x = xs.map datum ∧ ∀ a ∈ xs, a ∈ allowed := by
  constructor
  · induction x with
    | nil => exact fun _ => ⟨[],rfl,by simp⟩
    | cons a x ih =>
      intro h
      obtain ⟨j,hj,rfl⟩ := List.mem_map.mp (h a (by simp))
      obtain ⟨xs,rfl,hx⟩ := ih (fun a ha => h a (by simp [ha]))
      exact ⟨j::xs,rfl,by simpa [hj] using hx⟩
  · rintro ⟨xs,rfl,h⟩ a ha
    obtain ⟨j,hj,rfl⟩ := List.mem_map.mp ha
    exact List.mem_map.mpr ⟨j,h j hj,rfl⟩

private theorem singleton_char {α : Type} (a : α) (s : List α) :
    s ∈ (char a).matches' ↔ s = [a] := Iff.rfl

theorem mem_branch (s : Finset (Fin n)) (q : Fin m) (text : List (Symbol n m)) :
    text ∈ (branch s q).matches' ↔
      ∃ xs : List (Fin n), text = word xs q ∧ ∀ a ∈ xs, a ∉ s := by
  have allow (j : Fin n) : j ∈ allowed s ↔ j ∉ s := by simp [allowed]
  cases h : allowed s with
  | nil =>
    have hall (j : Fin n) : j ∈ s := by by_contra hh; simpa [h] using (allow j).mpr hh
    simp only [branch,h,matches'_mul,Language.mem_mul,singleton_char,
      exists_eq_left]
    constructor
    · rintro rfl; exact ⟨[],rfl,by simp⟩
    · rintro ⟨xs,rfl,hx⟩
      cases xs with
      | nil => rfl
      | cons a t => exact False.elim (hx a (by simp) (hall a))
  | cons j js =>
    have mapped : ((j::js).map (fun a => (char (datum a) : Expr n m))) =
        ((j::js).map datum).map char := by simp
    simp only [branch,h,mapped,matches'_mul,Language.mem_mul,singleton_char,
      exists_eq_left,star_literals,only_data]
    constructor
    · rintro ⟨_,⟨middle,⟨xs,rfl,hx⟩,rfl⟩,rfl⟩
      exact ⟨xs,rfl,fun a ha => (allow a).mp (by simpa only [h] using hx a ha)⟩
    · rintro ⟨xs,rfl,hx⟩
      exact ⟨_,⟨_,⟨xs,rfl,fun a ha => h ▸ (allow a).mpr (hx a ha)⟩,rfl⟩,rfl⟩

/-- Characterizes *all* accepted texts, including the implicit rejection of malformed input. -/
theorem language (f : Fin m → Finset (Fin n)) (text : List (Symbol n m)) :
    text ∈ (expression f).matches' ↔
    ∃ (q : Fin m) (xs : List (Fin n)), text = word xs q ∧ ∀ a ∈ xs, a ∉ f q := by
  simp [expression,mem_alternation,mem_branch]

theorem word_injective {xs ys : List (Fin n)} {q r : Fin m} (h : word xs q = word ys r) :
    xs = ys ∧ q = r := by
  have e := List.cons.inj h |>.2
  have rr := congrArg List.reverse e
  simp only [List.reverse_append,List.reverse_cons,List.reverse_nil,List.nil_append,
    List.cons_append] at rr
  have eq : q = r := by simpa [selector] using (List.cons.inj rr).1
  subst r
  have mapEq : xs.map (@datum n m) = ys.map datum := List.append_cancel_right e
  exact ⟨List.map_injective_iff.mpr (fun _ _ a => by simpa [datum] using a) mapEq,rfl⟩

theorem reduction (f : Fin m → Finset (Fin n)) (xs : List (Fin n)) (q : Fin m) :
    word xs q ∈ (expression f).matches' ↔ ∀ a ∈ xs, a ∉ f q := by
  rw [language]
  constructor
  · rintro ⟨r,ys,h,hr⟩
    obtain ⟨rfl,rfl⟩ := word_injective h
    exact hr
  · exact fun h => ⟨q,xs,rfl,h⟩

end DisjointnessDraft.Streaming
