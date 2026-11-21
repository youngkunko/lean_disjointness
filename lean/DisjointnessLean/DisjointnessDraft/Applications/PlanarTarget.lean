import DisjointnessDraft.Applications.PlanarEncoding
import DisjointnessDraft.Transfer.Initialization
import DisjointnessDraft.Applications.ShortTransfer

/-! The target receives physical positive-weight edge insertions into an
initially empty planar graph and arbitrary vertex-pair distance queries.
Coordinates and static graph descriptions are not supplied to its queries. -/
namespace DisjointnessDraft.Applications.PlanarTarget
open PlanarEncoding PlanarPadding WeightedWalk Transfer.Compiler Classical
noncomputable section
abbrev Edit (T : Type) := (T × T) × ℤ
abbrev Ask (T : Type) := T × T
abbrev Hist (T : Type) := List (Instr (Edit T) (Ask T))
def syntactic (h : Hist T) := h.filterMap Sum.getLeft?
def graph (h : Hist T) (u : T) (k : ℤ) (v : T) := ((u,v),k)∈syntactic h
def legal (B : ℤ) (_ : Unit) (h : Hist T) :=
  ((syntactic h).map Prod.fst).Nodup ∧
  (∀ u k v,graph h u k v → 0<k ∧ k≤B) ∧ Nonempty (Drawing (plain (graph h)))
def minimum (E : T → ℤ → T → Prop) (q : Ask T) : Option ℕ :=
  if h : ∃ k : ℕ,Path (sym E) q.1 (k:ℤ) q.2 then some (Nat.find h) else none
def exactSpec (_ : Unit) (h : Hist T) := minimum (graph h)
def thresholdSpec (t : ℤ) (_ : Unit) (h : Hist T) (q : Ask T) :=
  decide (∃ k : ℤ,k≤t ∧ Path (sym (graph h)) q.1 k q.2)

theorem exact_value (E : T → ℤ → T → Prop) (q : Ask T) (d : ℤ) (nn : 0≤d) (p : Path (sym E) q.1 d q.2)
    (low : ∀ t,Path (sym E) q.1 t q.2 → d≤t) : minimum E q=some d.toNat := by
  have good : Path (sym E) q.1 (d.toNat:ℤ) q.2 := by simpa [Int.toNat_of_nonneg nn] using p
  have possible : ∃ k : ℕ,Path (sym E) q.1 k q.2 := ⟨_,good⟩
  rw [minimum,dif_pos possible,Option.some.injEq]
  apply le_antisymm (Nat.find_min' possible good)
  have l := low _ (Nat.find_spec possible); omega

theorem threshold_value (E : T → ℤ → T → Prop) (q : Ask T) (d t : ℤ) (p : Path (sym E) q.1 d q.2)
    (low : ∀ k,Path (sym E) q.1 k q.2 → d≤k) :
    (∃ k : ℤ,k≤t ∧ Path (sym E) q.1 k q.2) ↔ d≤t :=
  ⟨fun ⟨k,le,h⟩ => (low k h).trans le,fun le => ⟨d,le,p⟩⟩

theorem legal_prefix {h H : Hist T} {B : ℤ} (p : h <+: H) (ok : legal B () H) : legal B () h := by
  have sub := p.filterMap Sum.getLeft?
  refine ⟨ok.1.sublist (sub.map Prod.fst).sublist,fun u k v e => ok.2.1 u k v (sub.subset e),?_⟩
  exact ok.2.2.some.mono (fun _ _ ⟨k,e⟩ => ⟨k,sub.subset e⟩)

def key (ab : W n pad × W n pad) : Edit (W n pad) := (ab,weight ab.1 ab.2)
def original (f : Family n) : Finset (W n pad × W n pad) := Finset.univ.filter (fun ab => plain (input f []) ab.1 ab.2)
def pairs (f : Family n) (xs : List (Fin n)) : List (W n pad × W n pad) := (original f).toList++xs.map ends
def initial (f : Family n) : Hist (W n pad) :=
  ((original f).toList.map key).map Sum.inl ++
    List.replicate (Fintype.card (W n pad × W n pad)-(original (pad:=pad) f).card) (.inr (.inl (root n),.inl (root n)))
def init (n pad : ℕ) : Initialization (Family n) Unit (Edit (W n pad)) (Ask (W n pad)) where
  initial _ := ()
  steps := initial
  length := Fintype.card (W n pad × W n pad)
  fixed f := by
    have lim := Finset.card_le_univ (original (pad:=pad) f)
    simp only [initial,List.length_append,List.length_map,Finset.length_toList,List.length_replicate]; omega
def plan (n pad : ℕ) (d : A) (decode : A → Bool) : Schedule n (Family n) (Edit (W n pad)) (Ask (W n pad)) A :=
  ⟨id,fun j => [key (ends j)],fun q => [.inr (query q)],fun _ xs => decode (xs.headD d)⟩

@[simp] theorem edits_append (h s : Hist T) : syntactic (h++s)=syntactic h++syntactic s := List.filterMap_append
theorem initial_data (f : Family n) : syntactic (initial (pad:=pad) f)=(original f).toList.map key := by
  have ignored (k : ℕ) (a : Ask (W n pad)) : syntactic (List.replicate k (.inr a))=[] := by
    induction k with
    | zero => rfl
    | succ k ih => simpa only [syntactic,List.replicate_succ,List.filterMap_cons,Sum.getLeft?_inr] using ih
  simp only [initial,edits_append,ignored,List.append_nil]
  simp [syntactic,List.filterMap_map,Function.comp_def]

theorem before_data (d : A) (c : A → Bool) (xs : List (Fin n)) :
    syntactic (before (plan n pad d c) xs)=(xs.map ends).map key := by
  simp [syntactic,before,plan,←List.map_eq_flatMap,List.filterMap_map,List.map_map,Function.comp_def]

theorem data_mem (f : Family n) (xs : List (Fin n)) (a b : W n pad) (k : ℤ) :
    ((a,b),k)∈(pairs f xs).map key ↔ input f xs a k b := by
  rw [connector]
  simp only [List.mem_map,pairs,List.mem_append,Finset.mem_toList,original,Finset.mem_filter,
    Finset.mem_univ,true_and]
  constructor
  · rintro ⟨ab,old|⟨x,hx,rfl⟩,e⟩
    · have t : ab=(a,b) := congrArg Prod.fst e
      subst ab
      obtain ⟨j,hj⟩ := old
      have eq : j=k := (actual_weight hj).trans (congrArg Prod.snd e)
      exact Or.inl (eq▸hj)
    · exact Or.inr ⟨x,hx,(congrArg Prod.fst e).symm,by cases e; rfl⟩
  · rintro (old|⟨x,h,hpair,w⟩)
    · exact ⟨(a,b),Or.inl ⟨k,old⟩,by simp [key,←actual_weight old]⟩
    · exact ⟨(a,b),Or.inr ⟨x,h,hpair.symm⟩,by simp [key,w]⟩

theorem fresh (f : Family n) (xs : List (Fin n)) (nd : xs.Nodup) : (pairs (pad:=pad) f xs).Nodup := by
  refine List.nodup_append.mpr ⟨Finset.nodup_toList _,nd.map ends_injective,?_⟩
  intro e old inside
  obtain ⟨x,_,rfl⟩ := List.mem_map.mp inside
  exact missing f x (by simpa [original] using old)

theorem final_edges (d : A) (c : A → Bool) (f : Family n) (xs : List (Fin n)) :
    graph (initial f++before (plan n pad d c) xs)=input f xs := by
  funext a k b; apply propext
  simpa only [graph,edits_append,initial_data,before_data,pairs,List.map_append] using data_mem f xs a b k

def limit (n : ℕ) := 8*(dim n:ℤ)*(dim n+1)
theorem path_valid (d : A) (c : A → Bool) (f : Family n) (xs : List (Fin n)) (q : Fin n)
    (nd : xs.Nodup) (h : Hist (W n pad)) (pre : h <+: before (plan n pad d c) xs ++ (plan n pad d c).finish q) :
    initLegal (init n pad) (legal (limit n)) f h := by
  apply legal_prefix (show initial f++h <+: initial f++(before (plan n pad d c) xs++(plan n pad d c).finish q) from
    by obtain ⟨rest,e⟩ := pre; exact ⟨rest,by simp [e,List.append_assoc]⟩)
  let final := initial f++(before (plan n pad d c) xs++(plan n pad d c).finish q)
  have all : syntactic final=(pairs f xs).map key := by
    simp only [final,edits_append,initial_data,before_data,pairs,List.map_append]
    change _++(_++[]) = _; simp
  have rel : graph final=input f xs := by
    funext a k b; apply propext; simpa only [graph,all] using data_mem f xs a b k
  change ((syntactic final).map Prod.fst).Nodup ∧ _
  rw [all]
  refine ⟨by simpa [List.map_map,key,Function.comp_def] using fresh (pad:=pad) f xs nd,?_,?_⟩
  · intro u k v e; rw [rel] at e
    exact bound (by have := q.isLt; omega) e
  · rw [rel]; exact planar f xs

end
end DisjointnessDraft.Applications.PlanarTarget
