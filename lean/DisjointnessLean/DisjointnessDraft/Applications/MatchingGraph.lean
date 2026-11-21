import DisjointnessDraft.Applications.MatchingSize
import DisjointnessDraft.Transfer.Initialization
import DisjointnessDraft.Applications.ShortTransfer

/-! The physical bipartite problem starts with no edges. True initial
incidences and the padding matching are inserted during preprocessing. Unit
queries pad its operation count without changing the logical graph. -/
namespace DisjointnessDraft.Applications.MatchingGraph
open MatchingSize Transfer.Compiler Classical
noncomputable section
abbrev Edge (n p r : ℕ) := Left n p × Right n p r
abbrev Hist (n p r : ℕ) := List (Instr (Edge n p r) Unit)
def edits (h : Hist n p r) : List (Edge n p r) := h.filterMap Sum.getLeft?
def graph (h : Hist n p r) (a : Left n p) (b : Right n p r) := (a,b)∈edits h
def legal (_ : Unit) (h : Hist n p r) := (edits h).Nodup
def sizeSpec (_ : Unit) (h : Hist n p r) (_ : Unit) := MatchingSize.maximum (graph h)
def perfectSpec (_ : Unit) (h : Hist n p r) (_ : Unit) := decide (MatchingSize.Perfect (graph h))
def base (f : Family n) : Left n p → Right n p r → Prop :=
  padded (Matching.edge (fun i j => j∈f i) (fun _ => False) (fun _ => False))
def original (f : Family n) : Finset (Edge n p r) := Finset.univ.filter (fun ab => base f ab.1 ab.2)
def dataEdge (j : Fin n) : Edge n p r := (.inl (.col j),.inl (.inl .endpt))
def choiceEdge (q : Fin n) : Edge n p r := (.inl .endpt,.inl (.inl (.row q)))
def initProgram (f : Family n) : Hist n p r :=
  (original f).toList.map Sum.inl ++ List.replicate (Fintype.card (Edge n p r)-(original (p:=p) (r:=r) f).card) (.inr ())
def init (n p r : ℕ) : Initialization (Family n) Unit (Edge n p r) Unit where
  initial _ := ()
  steps := initProgram
  length := Fintype.card (Edge n p r)
  fixed f := by
    have lim := Finset.card_le_univ (original (p:=p) (r:=r) f)
    simp only [initProgram,List.length_append,List.length_map,Finset.length_toList,List.length_replicate]; omega

theorem edits_noise (m : ℕ) : edits (n:=n) (p:=p) (r:=r) (List.replicate m (.inr ()))=[] := by
  induction m with
  | zero => rfl
  | succ m ih => simp [edits,List.replicate_succ,show (List.replicate m (.inr ()) : Hist n p r).filterMap Sum.getLeft? = [] from ih]
@[simp] theorem edits_init (f : Family n) : edits (initProgram (p:=p) (r:=r) f)=(original f).toList := by
  change ((original f).toList.map Sum.inl ++ _).filterMap Sum.getLeft?=_
  simp only [List.filterMap_append,List.filterMap_map]
  rw [show List.filterMap Sum.getLeft? (List.replicate _ (.inr ()))=([] : List (Edge n p r)) from edits_noise _]
  simp [Function.comp_def]
def plan (A : Type) (decode : A → Bool) (d : A) (n p r : ℕ) : Schedule n (Family n) (Edge n p r) Unit A :=
  ⟨id,fun j => [dataEdge j],fun q => [.inl (choiceEdge q),.inr ()],fun _ vs => decode (vs.headD d)⟩
@[simp] theorem edits_before (A : Type) (test : A → Bool) (d : A) (xs : List (Fin n)) :
    edits (before (plan A test d n p r) xs)=xs.map dataEdge := by
  simp [edits,before,plan,←List.map_eq_flatMap,List.filterMap_map,Function.comp_def]
def fullList (f : Family n) (xs : List (Fin n)) (q : Fin n) : List (Edge n p r) :=
  (original f).toList++xs.map dataEdge++[choiceEdge q]
@[simp] theorem original_mem (f : Family n) (a : Left n p) (b : Right n p r) :
    (a,b)∈(original f).toList ↔ base f a b := by simp [original]

theorem fresh (f : Family n) (xs : List (Fin n)) (q : Fin n) (nd : xs.Nodup) :
    (fullList (p:=p) (r:=r) f xs q).Nodup := by
  have dinj : Function.Injective (@dataEdge n p r) := by intro a b h; simpa [dataEdge] using (congrArg Prod.fst h)
  have dataFresh : (xs.map (@dataEdge n p r)).Nodup := nd.map dinj
  have rest : List.Disjoint (original (p:=p) (r:=r) f).toList (xs.map dataEdge) := by
    intro e he hd
    obtain ⟨j,_,rfl⟩ := List.mem_map.mp hd
    simp [dataEdge,original,base,padded,Matching.edge] at he
  refine List.nodup_append.mpr ⟨List.nodup_append.mpr ⟨Finset.nodup_toList _,dataFresh,rest⟩,by simp,?_⟩
  intro e he last
  obtain rfl := List.mem_singleton.mp last
  rcases List.mem_append.mp he with h|h
  · simp [choiceEdge,original,base,padded,Matching.edge] at h
  · obtain ⟨j,_,bad⟩ := List.mem_map.mp h
    simp [dataEdge,choiceEdge] at bad

theorem prefix_valid (A : Type) (test : A → Bool) (d : A) (f : Family n) (xs : List (Fin n))
    (q : Fin n) (nd : xs.Nodup) (h : Hist n p r)
    (pre : h <+: before (plan A test d n p r) xs ++ (plan A test d n p r).finish q) :
    initLegal (init n p r) legal f h := by
  have l := pre.filterMap Sum.getLeft?
  have prior : edits h <+: xs.map dataEdge ++ [choiceEdge q] := by
    change edits h <+: edits (before (plan A test d n p r) xs ++ [Sum.inl (choiceEdge q),Sum.inr ()]) at l
    simpa only [edits,List.filterMap_append,List.filterMap_cons,Sum.getLeft?_inl,Sum.getLeft?_inr,
      List.filterMap_nil,← edits_before A test d xs] using l
  obtain ⟨suffix,eq⟩ := prior
  have sub : (original (p:=p) (r:=r) f).toList++edits h <+: fullList f xs q :=
    ⟨suffix,by simp [fullList,List.append_assoc,eq]⟩
  have good := (fresh f xs q nd).sublist sub.sublist
  change (edits (initProgram f++h)).Nodup
  simpa only [edits,List.filterMap_append,←edits_init] using good

theorem realized (f : Family n) (xs : List (Fin n)) (q : Fin n) :
    (fun a b => (a,b)∈fullList (p:=p) (r:=r) f xs q)=
     padded (Matching.edge (fun i j => j∈f i) (·∈xs) (·=q)) := by
  funext a b; apply propext
  cases a with
  | inl a =>
    rcases b with (b|j)|j
    · cases a <;> cases b <;> simp [fullList,original,base,padded,Matching.edge,dataEdge,choiceEdge]
    · cases a <;> simp [fullList,original,base,padded,dataEdge,choiceEdge]
    · cases a <;> simp [fullList,original,base,padded,dataEdge,choiceEdge]
  | inr a =>
    rcases b with (b|j)|j <;> simp [fullList,original,base,padded,dataEdge,choiceEdge]

theorem final_graph (A : Type) (test : A → Bool) (d : A) (f : Family n) (xs : List (Fin n)) (q : Fin n) :
    graph (initProgram f++(before (plan A test d n p r) xs++[.inl (choiceEdge q)]))=
      fun a b => (a,b)∈fullList f xs q := by
  have all : ∀ a b : Hist n p r,edits (a++b)=edits a++edits b := fun _ _ => List.filterMap_append
  funext a b
  simp only [graph,all,edits_init,edits_before,fullList,List.append_assoc]
  rfl

theorem decode (f : Family n) (xs : List (Fin n)) (q : Fin n) :
    decide (¬Matching.Perfect (Matching.edge (fun i j => j∈f i) (·∈xs) (·=q)))=answer f xs q := by
  apply decide_eq_decide.mpr
  simp only [Matching.perfect_iff,not_exists]; tauto

theorem size_valid : Valid (plan ℕ (fun k => decide (k≠leftCount n p)) 0 n p r)
    (initLegal (init n p r) legal) (initSpec (init n p r) sizeSpec) := by
  refine ⟨fun f xs q nd h pre => prefix_valid _ _ _ f xs q nd h pre,?_⟩
  intro f xs q _
  change decide (MatchingSize.maximum (graph (initProgram f++(before _ xs++[.inl (choiceEdge q)])))≠leftCount n p)=_
  rw [final_graph,realized,←left_card,←decode f xs q]
  apply decide_eq_decide.mpr
  simp only [ne_eq,largest,padded_full]

theorem perfect_valid : Valid (plan Bool (!·) false n p 0)
    (initLegal (init n p 0) legal) (initSpec (init n p 0) perfectSpec) := by
  refine ⟨fun f xs q nd h pre => prefix_valid _ _ _ f xs q nd h pre,?_⟩
  intro f xs q _
  change (!decide (MatchingSize.Perfect (graph (initProgram f++(before _ xs++[.inl (choiceEdge q)])))))=_
  rw [final_graph,realized,perfect _ (by simp),padded_full,←decide_not]
  exact decode f xs q

end
end DisjointnessDraft.Applications.MatchingGraph
