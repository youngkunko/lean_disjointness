import DisjointnessDraft.Applications.Components
import DisjointnessDraft.Applications.GraphVariants
import DisjointnessDraft.Transfer.Initialization
import DisjointnessDraft.Transfer.Lower

namespace DisjointnessDraft.Applications.GraphHistories
open DisjointnessFoundations Graphs Reachability Transfer.Compiler
noncomputable section
open Classical
variable {n p : ℕ}

def Raw (es : List (Edge W)) (a b : W) := (a,b)∈es

def Realizes (F : Family n) (xs : List (Fin n)) (a b : Vertex n p) :=
  match a,b with
  | .inl u,.inl v => base (extRows F) (·∈xs) u v
  | _,_ => False

theorem edge_exact (F : Family n) (xs : List (Fin n)) (a b : Vertex n p) :
    Raw (edges F xs) a b ↔ Realizes F xs a b := by
  constructor
  · intro h
    cases a with
    | inl a =>
      cases b with
      | inl b => exact projects F xs h
      | inr v =>
        rcases List.mem_append.mp h with x|x <;> obtain ⟨_,_,bad⟩ := List.mem_map.mp x <;>
          have y := congrArg Prod.snd bad <;> cases y
    | inr a =>
      rcases List.mem_append.mp h with x|x <;> obtain ⟨_,_,bad⟩ := List.mem_map.mp x <;>
        have y := congrArg Prod.fst bad <;> cases y
  · cases a with
    | inr => exact False.elim
    | inl a =>
      cases b with
      | inr => exact False.elim
      | inl b =>
        cases a <;> cases b <;> intro h <;> try contradiction
        · rename_i r j
          cases r with
          | inl q =>
            apply List.mem_append_left; exact List.mem_map.mpr ⟨(q,j),by simp,by simp [staticArc,show j∈F q from h]⟩
          | inr q =>
            apply List.mem_append_left; exact List.mem_map.mpr ⟨(q,j),by simp,by simp [staticArc,show j∉F q from h]⟩
        · exact List.mem_append_right _ (List.mem_map.mpr ⟨_,h,rfl⟩)

inductive Kind | source | back | triangle deriving DecidableEq
def select (k : Kind) (q : Fin n) : Edge (Vertex n p) := match k with
  | .source => (.inl .source,row q)
  | .back => (target n p,row q)
  | .triangle => (row q,target n p)

def strict (es : List (Edge W)) := es.Nodup ∧ ∀ e∈es,e.1≠e.2 ∧ e.swap∉es
theorem prefix_strict {xs ys : List (Edge W)} (h : xs <+: ys) (s : strict ys) : strict xs :=
  ⟨h.sublist.nodup s.1,fun e he => ⟨(s.2 e (h.sublist.subset he)).1,fun t => (s.2 e (h.sublist.subset he)).2 (h.sublist.subset t)⟩⟩

theorem no_loop (F : Family n) (xs : List (Fin n)) (e : Edge (Vertex n p)) (h : e∈edges F xs) :
    e.1≠e.2 ∧ e.swap∉edges F xs := by
  obtain ⟨a,b⟩ := e
  rcases List.mem_append.mp h with mem|mem
  · obtain ⟨⟨i,j⟩,_,e⟩ := List.mem_map.mp mem
    obtain ⟨rfl,rfl⟩ := Prod.mk.inj e
    refine ⟨by simp,fun bad => ?_⟩
    exact (projects F xs bad : False)
  · obtain ⟨j,hj,e⟩ := List.mem_map.mp mem
    obtain ⟨rfl,rfl⟩ := Prod.mk.inj e
    exact ⟨by simp [target],fun bad => (projects F xs bad : False)⟩

theorem extra (F : Family n) (xs : List (Fin n)) (q : Fin n) (k : Kind) :
    let e := select (p:=p) k q
    e.1≠e.2 ∧ e∉edges F xs ∧ e.swap∉edges F xs := by
  cases k <;> exact ⟨by simp [select,row,target],fun h => (projects F xs h : False),fun h => (projects F xs h : False)⟩

theorem path_valid (F : Family n) (xs : List (Fin n)) (nd : xs.Nodup) (q : Fin n) (k : Kind) :
    strict (edges F xs++[select (p:=p) k q]) := by
  have h := extra (p:=p) F xs q k
  constructor
  · simpa using (List.nodup_append.mpr ⟨(legal F xs nd).1,by simp,by simpa using h.2.1⟩ :
      (edges F xs++[select (p:=p) k q]).Nodup)
  · intro e mem
    rcases List.mem_append.mp mem with a|b
    · have z := no_loop F xs e a
      refine ⟨z.1,fun bad => ?_⟩
      rcases List.mem_append.mp bad with a'|b'
      · exact z.2 a'
      · have eq := List.mem_singleton.mp b'
        have e' := congrArg Prod.swap eq; simp only [Prod.swap_swap] at e'; rw [e'] at a
        exact h.2.2 a
    · obtain rfl := List.mem_singleton.mp b
      refine ⟨h.1,fun bad => ?_⟩
      rcases List.mem_append.mp bad with a'|b'
      · exact h.2.2 a'
      · exact h.1 (congrArg Prod.snd (List.mem_singleton.mp b'))

def operations (h : List (Instr E Q)) := h.filterMap Sum.getLeft?
def legalGraph {W Q : Type} (_ : Unit) (h : List (Instr (Edge W) Q)) := strict (operations h)

def frame (n p : ℕ) (Q : Type) : Initialization (Family n) Unit (Edge (Vertex n p)) Q :=
  ⟨fun _ => (),fun F => (setup F).map Sum.inl,n*n,fun f => by simp [setup_length]⟩

def schedule (k : Kind) (query : Fin n → Q) (decode : Fin n → List A → Bool) :
    Schedule n (Family n) (Edge (Vertex n p)) Q A :=
  ⟨id,fun j => [arc j],fun q => [.inl (select k q),.inr (query q)],decode⟩

theorem ops_full (F : Family n) (xs : List (Fin n)) (k : Kind) (q : Fin n) (ask : Fin n→Q) (dec : Fin n→List A→Bool) :
    operations ((frame n p Q).steps F++before (schedule k ask dec) xs++(schedule k ask dec).finish q) =
      edges F xs++[select k q] := by
  simp [operations,frame,before,schedule,edges,List.filterMap_append,List.filterMap_map,Function.comp_def]
  induction xs <;> simp_all

theorem legal_prefix (F : Family n) (xs : List (Fin n)) (nd : xs.Nodup) (k : Kind) (q : Fin n)
    (ask : Fin n→Q) (dec : Fin n→List A→Bool) (h : List (Instr (Edge (Vertex n p)) Q))
    (pre : h <+: before (schedule k ask dec) xs++(schedule k ask dec).finish q) :
    initLegal (frame n p Q) legalGraph F h := by
  apply prefix_strict _ (path_valid F xs nd q k)
  rw [←ops_full F xs k q ask dec]
  obtain ⟨rest,eq⟩ := pre
  rw [List.append_assoc,←eq]
  refine ⟨operations rest,?_⟩
  simp [operations,List.filterMap_append,List.append_assoc]

end
end DisjointnessDraft.Applications.GraphHistories
