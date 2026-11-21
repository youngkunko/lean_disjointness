import DisjointnessDraft.Streaming.Size

/-! Replace each literal by a fixed-length binary word. Concatenation,
alternation and star preserve exactly the homomorphic image of the language. -/
namespace DisjointnessDraft.Streaming.Binary
open Computability RegularExpression
variable {α : Type}

def literal : List Bool → RegularExpression Bool
  | [] => 1
  | [x] => char x
  | x::y::tail => char x * literal (y::tail)

theorem mem_literal (xs ys : List Bool) : ys ∈ (literal xs).matches' ↔ ys=xs := by
  induction xs generalizing ys with
  | nil => simp [literal]
  | cons x xs ih => cases xs with
    | nil => exact Iff.rfl
    | cons y tail =>
      rw [literal,matches'_mul,Language.mem_mul]
      constructor
      · rintro ⟨p,hp,q,hq,rfl⟩
        change p=[x] at hp
        rw [hp,(ih q).mp hq]; rfl
      · rintro rfl; exact ⟨_,rfl,_,(ih _).mpr rfl,rfl⟩

def substitute (code : α → List Bool) : RegularExpression α → RegularExpression Bool
  | .zero => 0 | .epsilon => 1 | .char x => literal (code x)
  | .plus p q => substitute code p + substitute code q
  | .comp p q => substitute code p * substitute code q
  | .star p => (substitute code p).star

private theorem star_lift (code : α → List Bool) (P : RegularExpression α) (parts : List (List Bool))
    (h : ∀ l∈parts, ∃ t, t ∈ P.matches' ∧ t.flatMap code=l) :
    ∃ T : List (List α), (∀ t∈T, t∈P.matches') ∧ T.flatten.flatMap code=parts.flatten := by
  induction parts with
  | nil => exact ⟨[],by simp,rfl⟩
  | cons l ls ih =>
    obtain ⟨a,ha,ea⟩ := h l (by simp)
    obtain ⟨as,all,eas⟩ := ih (fun x hx => h x (by simp [hx]))
    exact ⟨a::as,List.forall_mem_cons.mpr ⟨ha,all⟩,by simp [ea,eas]⟩

theorem substitution (code : α → List Bool) (P : RegularExpression α) (bits : List Bool) :
    bits ∈ (substitute code P).matches' ↔
    ∃ source, source ∈ P.matches' ∧ source.flatMap code=bits := by
  induction P generalizing bits with
  | zero => simp [substitute,RegularExpression.zero_def]
  | epsilon => simp [substitute,RegularExpression.one_def]
  | char a =>
    rw [substitute,mem_literal]
    constructor
    · rintro rfl; exact ⟨[a],rfl,by simp⟩
    · rintro ⟨t,ht,rfl⟩; change t=[a] at ht; simp [ht]
  | plus p q ip iq =>
    simp only [substitute,plus_def,matches'_add,Language.mem_add,ip,iq]
    aesop
  | comp p q ip iq =>
    simp only [substitute,comp_def,matches'_mul,Language.mem_mul,ip,iq]
    constructor
    · rintro ⟨_,⟨a,ha,rfl⟩,_,⟨b,hb,rfl⟩,rfl⟩
      exact ⟨_,⟨a,ha,b,hb,rfl⟩,by simp⟩
    · rintro ⟨_,⟨a,ha,b,hb,rfl⟩,rfl⟩
      exact ⟨_,⟨a,ha,rfl⟩,_,⟨b,hb,rfl⟩,by simp⟩
  | star p ih =>
    simp only [substitute,matches'_star,Language.mem_kstar,ih]
    constructor
    · rintro ⟨parts,rfl,all⟩
      obtain ⟨T,ht,eq⟩ := star_lift code p parts all
      exact ⟨T.flatten,⟨T,rfl,ht⟩,eq⟩
    · rintro ⟨_,⟨T,rfl,all⟩,rfl⟩
      refine ⟨T.map (fun t => t.flatMap code),?_,?_⟩
      · induction T with
        | nil => rfl
        | cons a T ih => simp [ih (fun v hv => all v (by simp [hv]))]
      · intro u hu
        obtain ⟨t,ht,rfl⟩ := List.mem_map.mp hu
        exact ⟨t,all t ht,rfl⟩

structure Code (α : Type) (b : ℕ) where
  table : α ↪ (Fin b → Bool)

def Code.bits (C : Code α b) (a : α) := List.ofFn (C.table a)

@[simp] theorem Code.length (C : Code α b) (a : α) : (C.bits a).length=b := List.length_ofFn

theorem Code.encode_injective (C : Code α b) (pos : 0<b) : Function.Injective (List.flatMap C.bits) := by
  intro xs
  induction xs with
  | nil =>
    intro ys h
    cases ys with
    | nil => rfl
    | cons y ys => have z := congrArg List.length h; simp at z; omega
  | cons x xs ih =>
    intro ys h
    cases ys with
    | nil => have z := congrArg List.length h; simp at z; omega
    | cons y ys =>
      simp only [List.flatMap_cons] at h
      have lc : (C.bits x).length=(C.bits y).length := by simp
      obtain ⟨he,ht⟩ := List.append_inj h lc
      exact congrArg₂ List.cons (C.table.injective (List.ofFn_injective he)) (ih ht)

theorem Code.reduction (C : Code (Symbol n m) b) (pos : 0<b) (f : Fin m → Finset (Fin n))
    (xs : List (Fin n)) (q : Fin m) :
    (word xs q).flatMap C.bits ∈ (substitute C.bits (expression f)).matches' ↔ ∀ a ∈ xs,a∉f q := by
  rw [substitution,←Streaming.reduction]
  constructor
  · rintro ⟨t,ht,e⟩; exact C.encode_injective pos e ▸ ht
  · exact fun h => ⟨_,h,rfl⟩

theorem Code.incomplete (C : Code α b) (P : RegularExpression α) (bits : List Bool) (h : ¬ b ∣ bits.length) :
    bits ∉ (substitute C.bits P).matches' := by
  rintro mem
  obtain ⟨ts,_,rfl⟩ := (substitution _ _ _).mp mem
  apply h
  clear h mem ‹ts ∈ P.matches'›
  induction ts with
  | nil => simp
  | cons a ts ih => simp only [List.flatMap_cons,List.length_append,C.length]; exact dvd_add dvd_rfl ih

theorem exists_code (n m : ℕ) :
    Nonempty (Code (Symbol n m) (Nat.log2 (n+m+1)+1)) := by
  apply Nonempty.intro
  constructor
  apply Nonempty.some
  apply Function.Embedding.nonempty_of_card_le
  simpa using (Nat.le_of_lt (Nat.lt_log2_self (n:=n+m+1)))

theorem binary_size (C : Code α b) (pos : 0<b) (P : RegularExpression α) :
    nodes (substitute C.bits P) ≤ (2*b)*nodes P := by
  have lit' (a : α) : nodes (literal (C.bits a)) ≤ 2*b := by
    cases h : C.bits a with
    | nil => have len := C.length a; rw [h] at len; simp at len; omega
    | cons j js =>
      have len := C.length a
      rw [h,List.length_cons] at len
      cases js with
      | nil => simp [literal,nodes]; omega
      | cons k ks =>
        have sq : ∀ (q : Bool) (qs : List Bool), nodes (literal (q::qs))=2*qs.length+1 := by
          intro q qs; induction qs generalizing q with
          | nil => rfl
          | cons v vs ih =>
            change 1+nodes (literal (v::vs))+1=_
            rw [ih]
            simp; omega
        rw [sq]; omega
  induction P with
  | zero | epsilon => simpa [substitute,nodes] using (show 1≤2*b by omega)
  | char a => simpa [substitute,nodes] using lit' a
  | plus a d ia id | comp a d ia id =>
    change _+_+1≤2*b*(nodes a+nodes d+1)
    simp only [Nat.mul_add,Nat.mul_one]
    omega
  | star p ih => change _+1≤2*b*(nodes p+1); rw [Nat.mul_add,Nat.mul_one]; omega

end DisjointnessDraft.Streaming.Binary
