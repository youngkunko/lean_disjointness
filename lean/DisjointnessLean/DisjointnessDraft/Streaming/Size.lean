import DisjointnessDraft.Streaming.Language

/-! Size counts one syntax node for each literal and operator. The all-empty
set family realizes the maximum over inputs of a given square dimension. -/
namespace DisjointnessDraft.Streaming
open RegularExpression
def nodes {α : Type} : RegularExpression α → ℕ
  | .zero | .epsilon | .char _ => 1
  | .plus x y | .comp x y => nodes x + nodes y + 1
  | .star x => nodes x + 1

private theorem alt_size {α : Type} (r : RegularExpression α) (rs : List (RegularExpression α)) :
    nodes (alternation (r::rs)) = ((r::rs).map nodes).sum + rs.length := by
  induction rs generalizing r with
  | nil => simp [alternation]
  | cons a rs ih =>
    change nodes r + nodes (alternation (a::rs)) + 1 = _
    rw [ih]
    simp
    omega

private theorem literal_size (j : Fin n) (js : List (Fin n)) :
    nodes (alternation ((j::js).map (fun a => (char (datum a) : Expr n m)))) = 2*js.length+1 := by
  rw [List.map_cons,alt_size]
  simp [List.map_map,Function.comp_def,nodes]
  omega

theorem branch_size (s : Finset (Fin n)) (q : Fin m) :
    nodes (branch s q) ≤ 2*n+4 := by
  cases h : allowed s with
  | nil => simp [branch,h,nodes]
  | cons j js =>
    have len : (j::js).length ≤ n := by
      rw [←h]
      simpa [allowed] using List.length_filter_le (fun j : Fin n => decide (j ∉ s)) (List.finRange n)
    have e := literal_size (m:=m) j js
    simp only [branch,h]
    change 1+((nodes (alternation ((j::js).map (fun a => (char (datum a) : Expr n m))))+1)+1+1)+1 ≤ _
    rw [e]
    simp only [List.length_cons] at len
    omega

theorem empty_branch (hn : 0<n) (q : Fin m) :
    nodes (branch (∅ : Finset (Fin n)) q) = 2*n+4 := by
  have len : (allowed (∅ : Finset (Fin n))).length=n := by simp [allowed]
  cases h : allowed (∅ : Finset (Fin n)) with
  | nil => simp [h] at len; omega
  | cons j js =>
    rw [h,List.length_cons] at len
    simp only [branch,h]
    change 1+((nodes (alternation ((j::js).map (fun a => (char (datum a) : Expr n m))))+1)+1+1)+1 = _
    rw [literal_size]
    omega

private theorem sum_bound {α : Type} (xs : List α) (f : α → ℕ) (u : ℕ) (h : ∀ x, f x ≤ u) :
    (xs.map f).sum ≤ xs.length*u := by
  induction xs with
  | nil => simp
  | cons a xs ih => simpa [Nat.succ_mul,Nat.add_comm] using Nat.add_le_add (h a) ih

def maxLength (n : ℕ) := nodes (expression (fun _ : Fin n => (∅ : Finset (Fin n))))

theorem maximum (hn : 0<n) (f : Fin n → Finset (Fin n)) :
    nodes (expression f) ≤ maxLength n ∧ maxLength n + 1 = n*(2*n+5) := by
  have len : (List.finRange n).length=n := List.length_finRange
  cases h : List.finRange n with
  | nil => rw [h] at len; simp at len; omega
  | cons q qs =>
    rw [h,List.length_cons] at len
    simp only [expression,maxLength,h,List.map_cons,alt_size,List.length_map,List.map_map,List.sum_cons]
    have maxS := sum_bound qs (fun i => nodes (branch (f i) i)) (2*n+4) (fun i => branch_size (f i) i)
    have emp : (fun x : Fin n => nodes (branch (∅ : Finset (Fin n)) x)) = fun _ => 2*n+4 :=
      funext (empty_branch hn)
    simp only [Function.comp_def,empty_branch hn,emp,List.map_const',List.sum_replicate_nat]
    constructor
    · have first := branch_size (f q) q
      omega
    · nlinarith [congrArg (fun x : ℕ => x*(2*n+5)) len]

theorem quadratic (hn : 1≤n) : n^2 ≤ maxLength n ∧ maxLength n ≤ 7*n^2 := by
  have h := (maximum hn (fun _ : Fin n => (∅ : Finset (Fin n)))).2
  have needed := Nat.mul_le_mul_left n hn
  constructor <;> nlinarith

@[simp] theorem alphabet_card (n m : ℕ) : Fintype.card (Symbol n m) = n+m+1 := by
  simp [Symbol]

end DisjointnessDraft.Streaming
