import DisjointnessDraft.Streaming.Language

/-! The parser keeps the distinct data coordinates only until the first
selector. Each completed prefix is accepted exactly when the regex matches. -/
namespace DisjointnessDraft.Streaming
inductive Parser (n : ℕ) where
  | first
  | live (seen : List (Fin n))
  | closed (accepted : Bool)
  deriving DecidableEq

def push (x : Fin n) (xs : List (Fin n)) := if x ∈ xs then xs else x::xs

@[simp] theorem mem_push (a x : Fin n) (xs : List (Fin n)) :
    a ∈ push x xs ↔ a=x ∨ a∈xs := by
  by_cases hx : x ∈ xs
  · simp [push,hx]; exact fun h => h ▸ hx
  · simp [push,hx]

def advance (f : Fin m → Finset (Fin n)) : Parser n → Symbol n m → Parser n
  | .first, none => .live []
  | .live xs, some (.inl x) => .live (push x xs)
  | .live xs, some (.inr q) => .closed (decide (∀ x ∈ xs, x ∉ f q))
  | _, _ => .closed false

def accepted : Parser n → Bool
  | .closed b => b
  | _ => false

def consume (f : Fin m → Finset (Fin n)) (p : Parser n) (text : List (Symbol n m)) :=
  text.foldl (advance f) p

@[simp] theorem closed_suffix (f : Fin m → Finset (Fin n)) (b : Bool) (xs : List (Symbol n m)) :
    accepted (consume f (.closed b) xs) = true ↔ xs=[] ∧ b=true := by
  induction xs generalizing b with
  | nil => simp [consume,accepted]
  | cons x xs ih =>
    change accepted (consume f (.closed false) xs) = true ↔ _
    rw [ih]; simp

private theorem live_suffix (f : Fin m → Finset (Fin n)) (seen : List (Fin n)) (ts : List (Symbol n m)) :
    accepted (consume f (.live seen) ts) = true ↔
    ∃ (q : Fin m) (ys : List (Fin n)), ts = ys.map datum ++ [selector q] ∧
      (∀ a ∈ seen, a ∉ f q) ∧ ∀ a ∈ ys, a ∉ f q := by
  induction ts generalizing seen with
  | nil =>
    simp [consume,accepted]
  | cons t ts ih =>
    cases t with
    | none =>
      change accepted (consume f (.closed false) ts) = true ↔ _
      rw [closed_suffix]
      simp only [Bool.false_eq_true,and_false,false_iff]
      rintro ⟨q,_|⟨a,ys⟩,h,_⟩ <;> simp [datum,selector] at h
    | some sym => cases sym with
      | inl a =>
        change accepted (consume f (.live (push a seen)) ts) = true ↔ _
        rw [ih]
        constructor
        · rintro ⟨q,ys,h,hs,hy⟩
          exact ⟨q,a::ys,by simp [h,datum],fun x hx => hs x (by simp [hx]),
            by simpa [hs a (by simp)] using hy⟩
        · rintro ⟨q,_|⟨j,ys⟩,h,hs,hy⟩
          · simp [selector] at h
          · simp only [List.map_cons,List.cons_append,List.cons.injEq,datum,Option.some.injEq,
              Sum.inl.injEq] at h
            obtain ⟨rfl,rfl⟩ := h
            refine ⟨q,ys,rfl,?_,fun x hx => hy x (by simp [hx])⟩
            intro x hx
            rcases (mem_push _ _ _).mp hx with rfl | mem
            · exact hy _ (by simp)
            · exact hs _ mem
      | inr q =>
        change accepted (consume f (.closed _) ts) = true ↔ _
        rw [closed_suffix,decide_eq_true_eq]
        constructor
        · rintro ⟨rfl,hs⟩; exact ⟨q,[],rfl,hs,by simp⟩
        · rintro ⟨r,_|⟨j,ys⟩,h,hs,hy⟩
          · simp only [List.map_nil,List.nil_append,List.cons.injEq,selector,
              Option.some.injEq,Sum.inr.injEq] at h
            exact ⟨h.2,h.1 ▸ hs⟩
          · simp [datum] at h

theorem parser_correct (f : Fin m → Finset (Fin n)) (text : List (Symbol n m)) :
    accepted (consume f .first text) = true ↔ text ∈ (expression f).matches' := by
  rw [language]
  cases text with
  | nil => simp [consume,accepted,word]
  | cons x ts => cases x with
    | none =>
      change accepted (consume f (.live []) ts) = true ↔ _
      rw [live_suffix]
      simp [word,marker]
    | some x =>
      change accepted (consume f (.closed false) ts) = true ↔ _
      simp [word,marker]

end DisjointnessDraft.Streaming
