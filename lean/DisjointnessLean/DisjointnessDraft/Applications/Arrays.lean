import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Basic
import Mathlib.Data.List.Count
import Mathlib.Data.Fintype.Basic
import Mathlib.Algebra.BigOperators.Group.List.Basic
import Mathlib.Tactic.Ring

/-! Concrete array and finite-set reductions. The range-mode theorem handles
arbitrary ties; the Langerman test quantifies over every nonempty prefix. -/
namespace DisjointnessDraft.Applications.Arrays
open Classical
noncomputable section
variable {Q U : Type} [DecidableEq U]

def family (S : Q → Finset U) (X : Finset U) : Option Q → Finset U
  | none => X | some q => S q

omit [DecidableEq U] in
theorem disjoint_query [DecidableEq U] (S : Q → Finset U) (X : Finset U) (q : Q) :
    Disjoint (family S X (some q)) (family S X none) ↔ Disjoint (S q) X := Iff.rfl

def pagh (S : Q → Finset U) : List U → Set Q
  | [] => Set.univ
  | x::xs => pagh S xs ∩ {q | x∉S q}

omit [DecidableEq U] in
theorem pagh_query [DecidableEq U] (S : Q → Finset U) (xs : List U) (q : Q) :
    q∈pagh S xs ↔ ∀ x∈xs,x∉S q := by induction xs <;> simp_all [pagh,and_comm]

def bit (P : Prop) : ℕ := if P then 1 else 0

def matrix (S : Q → Finset U) (X : Finset U) (q i : Q) (x : U) := bit (x∈S i)+bit (x∈X)+bit (i=q)

theorem erickson (S : Q → Finset U) (X : Finset U) (q : Q) :
    (∀ i x,matrix S X q i x≤3) ∧ ((∃ i x,matrix S X q i x=3) ↔ ∃ x,x∈S q ∧ x∈X) := by
  constructor
  · intro i x; unfold matrix bit; split_ifs <;> decide
  · constructor
    · rintro ⟨i,x,h⟩; unfold matrix bit at h; split_ifs at h <;> try contradiction
      subst i; exact ⟨x,by assumption,by assumption⟩
    · rintro ⟨x,r,t⟩; exact ⟨q,x,by simp [matrix,bit,r,t]⟩

def chunk (S : Finset U) (xs : List U) := xs.filter (·∉S) ++ xs.filter (·∈S)

theorem chunk_count (S : Finset U) (xs : List U) (x : U) : (chunk S xs).count x=xs.count x := by
  induction xs with
  | nil => simp [chunk]
  | cons y ys ih =>
    by_cases h : y∈S <;> by_cases eq : y=x <;> simp_all [chunk,List.count_append,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm]

theorem mode_count (S X : Finset U) (x : U) (middle : List (List U))
    (perm : ∀ l∈middle,l.count x=1) :
    (S.toList ++ middle.flatten ++ X.toList).count x = middle.length+bit (x∈S)+bit (x∈X) := by
  have flat (ls : List (List U)) (p : ∀ l∈ls,l.count x=1) : ls.flatten.count x=ls.length := by
    induction ls with
    | nil => simp
    | cons l ls ih => simp [p l (by simp),ih (fun a h => p a (by simp [h])),Nat.add_comm]
  have one (A : Finset U) : A.toList.count x = bit (x∈A) := by
    by_cases h : x∈A
    · rw [List.count_eq_one_of_mem A.nodup_toList (by simpa using h)]; simp [bit,h]
    · simp [List.count_eq_zero_of_not_mem (show x∉A.toList by simpa using h),bit,h]
  simp [List.count_append,one,flat middle perm,Nat.add_comm,Nat.add_left_comm,Nat.add_assoc]

/-- A returned mode, including an arbitrary tie, decodes intersection. -/
theorem range_mode (S X : Finset U) (middle : List (List U)) (z : U)
    (perm : ∀ l∈middle,∀ x,l.count x=1)
    (best : ∀ x,(S.toList++middle.flatten++X.toList).count x ≤ (S.toList++middle.flatten++X.toList).count z) :
    z∈S∩X ↔ (S∩X).Nonempty := by
  constructor
  · exact fun h => ⟨z,h⟩
  · rintro ⟨j,h⟩
    obtain ⟨sj,xj⟩ := Finset.mem_inter.mp h
    have count x := mode_count S X x middle (fun l hl => perm l hl x)
    have b := best j
    rw [count j,count z] at b
    by_cases sz : z∈S <;> by_cases xz : z∈X <;> simp_all [bit]
    all_goals omega

/-- Prefix sums after at least one entry, starting from a given offset. -/
def prefixes : ℤ → List ℤ → List ℤ
  | _,[] => []
  | a,h::t => (a+h)::prefixes (a+h) t

theorem prefixes_append (a : ℤ) (xs ys : List ℤ) :
    prefixes a (xs++ys)=prefixes a xs++prefixes (a+xs.sum) ys := by
  induction xs generalizing a with
  | nil => simp [prefixes]
  | cons x xs ih => simp [prefixes,ih,add_assoc]

def pairs (S : ℕ → U → Prop) (j : U) : ℕ → List ℤ
  | 0 => []
  | m+1 => pairs S j m ++ (if S m j then [1,1] else [2,0])

omit [DecidableEq U] in
theorem pairs_sum [DecidableEq U] (S : ℕ → U → Prop) (j : U) (m : ℕ) : (pairs S j m).sum=2*(m:ℤ) := by
  induction m with
  | zero => simp [pairs]
  | succ m ih => by_cases h : S m j <;> simp [pairs,h,ih] <;> ring

theorem pair_prefix (S : ℕ → U → Prop) (j : U) (m : ℕ) (a v : ℤ) :
    v∈prefixes a (pairs S j m) ↔
      (∃ i : Fin m,v=a+2*((i.val:ℤ)+1)) ∨ (∃ i : Fin m,S i.val j ∧ v=a+2*(i.val:ℤ)+1) := by
  induction m with
  | zero => simp [pairs,prefixes]
  | succ m ih =>
    rw [pairs,prefixes_append,List.mem_append,ih,pairs_sum,Fin.exists_fin_succ',Fin.exists_fin_succ']
    have castv (i : Fin m) : i.castSucc.val=i.val := rfl
    have even : a+2*(m:ℤ)+1+1=a+2*((m:ℤ)+1) := by ring
    have even' : a+2*(m:ℤ)+2=a+2*((m:ℤ)+1) := by ring
    by_cases h : S m j <;> simp only [h,if_true,if_false,prefixes,List.mem_cons,List.not_mem_nil,or_false,
      Fin.val_last,castv,even,even',add_zero,true_and,false_and,or_false,or_comm,or_left_comm,or_assoc,false_or,or_self,or_self_left]

def block (S : ℕ → U → Prop) (X : Set U) (j : U) (m : ℕ) : List ℤ :=
  [if j∈X then -2*(m:ℤ) else 0] ++ pairs S j m ++ [if j∈X then 0 else -2*(m:ℤ)]

theorem block_sum (S : ℕ → U → Prop) (X : Set U) (j : U) (m : ℕ) : (block S X j m).sum=0 := by
  by_cases h : j∈X <;> simp [block,h,pairs_sum]

theorem block_hit (S : ℕ → U → Prop) (X : Set U) (j : U) {m : ℕ} (q : Fin m) :
    let a : ℤ := 2*((m:ℤ)-(q.val:ℤ)-1)+1
    0∈prefixes a (block S X j m) ↔ j∈X ∧ S q.val j := by
  intro a
  have pos : 0<a := by dsimp [a]; have := q.isLt; omega
  by_cases h : j∈X
  · simp only [block,h,if_true,prefixes_append,List.mem_append,List.sum_singleton,List.sum_append,pairs_sum,
      prefixes,List.mem_cons,List.not_mem_nil,or_false,pair_prefix,true_and]
    constructor
    · rintro ((head | ⟨i,eq⟩ | ⟨i,si,eq⟩) | tail)
      · dsimp [a] at head; omega
      · dsimp [a] at eq; omega
      · have eqi : i=q := Fin.ext (by dsimp [a] at eq; omega)
        exact eqi ▸ si
      · omega
    · intro sq; exact Or.inl (Or.inr (Or.inr ⟨q,sq,by dsimp [a]; ring⟩))
  · simp only [block,h,if_false,prefixes_append,List.mem_append,List.sum_singleton,List.sum_append,pairs_sum,
      prefixes,List.mem_cons,List.not_mem_nil,or_false,pair_prefix,false_and]
    constructor
    · rintro ((head | ⟨i,eq⟩ | ⟨i,si,eq⟩) | tail) <;> omega
    · exact False.elim

theorem langerman (S : ℕ → U → Prop) (X : Set U) (cols : List U) {m : ℕ} (q : Fin m) :
    let a : ℤ := 2*((m:ℤ)-(q.val:ℤ)-1)+1
    0∈prefixes 0 (a::cols.flatMap (fun j => block S X j m)) ↔ ∃ j∈cols,j∈X ∧ S q.val j := by
  intro a
  have pos : 0<a := by dsimp [a]; have := q.isLt; omega
  simp only [prefixes,zero_add,List.mem_cons]; rw [or_iff_right pos.ne]
  induction cols with
  | nil => simp [prefixes]
  | cons j js ih =>
    rw [List.flatMap_cons,prefixes_append,List.mem_append,block_sum,add_zero,show (0∈prefixes a (block S X j m)) ↔ _ from block_hit S X j q]
    constructor
    · rintro (h|h)
      · exact ⟨j,by simp,h⟩
      · obtain ⟨y,hy,ok⟩ := ih.mp h; exact ⟨y,by simp [hy],ok⟩
    · rintro ⟨y,mem,ok⟩; rcases List.mem_cons.mp mem with rfl|hy
      · exact Or.inl ok
      · exact Or.inr (ih.mpr ⟨y,hy,ok⟩)

end
end DisjointnessDraft.Applications.Arrays
