import DisjointnessDraft.Applications.MatchUpdates
import DisjointnessDraft.Transfer.Initialization
import DisjointnessDraft.Applications.ShortTransfer

/-! Initially empty, unrestricted weighted bipartite graph, with single-edge
insertions and an unparameterized maximum matching query. The data structure
is promised planarity and distinct positive-weight edge insertions. -/
namespace DisjointnessDraft.Applications.MatchTarget
open MatchGraph MatchUpdates PlanarPadding Transfer.Compiler Classical
noncomputable section
variable {n pad : ℕ}
abbrev Edit (A B : Type) := (A×B)×ℤ
abbrev Hist (A B : Type) := List (Instr (Edit A B) Unit)
def edits (h : Hist A B) := h.filterMap Sum.getLeft?
def edges (h : Hist A B) (u : A) (k : ℤ) (v : B) := ((u,v),k)∈edits h
def legal (bound : ℤ) (_ : Unit) (h : Hist A B) :=
  ((edits h).map Prod.fst).Nodup ∧ (∀u k v,edges h u k v → 0<k ∧ k≤bound) ∧
  Nonempty (Drawing (MatchGraph.plain (edges h)))
def valueSpec (_ : Unit) (h : Hist A B) (_ : Unit) := BipartiteOptimum.maximum (edges h)
def decisionSpec (t : ℤ) (u : Unit) (h : Hist A B) (q : Unit) := decide (t≤valueSpec u h q)

theorem legal_prefix {h H : Hist A B} {Bnd : ℤ} (p : h <+: H) (ok : legal Bnd () H) : legal Bnd () h := by
  have sub := p.filterMap Sum.getLeft?
  refine ⟨ok.1.sublist (sub.map Prod.fst).sublist,fun u k v e => ok.2.1 u k v (sub.subset e),?_⟩
  apply ok.2.2.some.mono
  intro u v e
  rcases u with u|u <;> rcases v with v|v <;> try contradiction
  obtain ⟨k,h⟩ := e
  exact ⟨k,sub.subset h⟩

def key (z : Pair n pad) : Edit (L n) (R n pad) := (z,pairWeight z)
def initialPairs (f : Family n) : Finset (Pair n pad) := Finset.univ.filter (original f)
def initial (f : Family n) : Hist (L n) (R n pad) :=
  ((initialPairs f).toList.map key).map Sum.inl ++
    List.replicate (Fintype.card (Pair n pad)-(initialPairs (pad:=pad) f).card) (.inr ())
def init (n pad : ℕ) : Initialization (Family n) Unit (Edit (L n) (R n pad)) Unit :=
  ⟨fun _ => (),initial,Fintype.card (Pair n pad),fun f => by
    have lim := Finset.card_le_univ (initialPairs (pad:=pad) f)
    simp only [initial,List.length_append,List.length_map,Finset.length_toList,List.length_replicate]; omega⟩
def plan (n pad : ℕ) (d : A) (dec : A→Bool) : Schedule n (Family n) (Edit (L n) (R n pad)) Unit A :=
  ⟨id,fun x => [key (connector x)],fun q => [.inl (key (entry q)),.inl (key (exitEdge q)),.inr ()],
    fun _ l => dec (l.headD d)⟩
@[simp] theorem edits_append (h s : Hist A B) : edits (h++s)=edits h++edits s := List.filterMap_append
private theorem initial_data (f : Family n) : edits (initial (pad:=pad) f)=(initialPairs f).toList.map key := by
  have empty (k : ℕ) : edits (A:=L n) (B:=R n pad) (List.replicate k (.inr ()))=[] := by
    induction k with
    | zero => rfl
    | succ k ih => simpa only [edits,List.replicate_succ,List.filterMap_cons,Sum.getLeft?_inr] using ih
  simp only [initial,edits_append,empty,List.append_nil]
  simp [edits,List.filterMap_map,Function.comp_def]
private theorem before_data (d : A) (dec : A→Bool) (xs : List (Fin n)) :
    edits (before (plan n pad d dec) xs)=(xs.map connector).map key := by
  simp [edits,before,plan,←List.map_eq_flatMap,List.filterMap_map,List.map_map,Function.comp_def]
def pairs (F : Family n) (xs : List (Fin n)) (q : Fin n) : List (Pair n pad) :=
  (initialPairs F).toList++xs.map connector++[entry q,exitEdge q]

theorem pair_mem (F : Family n) (xs : List (Fin n)) (q : Fin n) (z : Pair n pad) (k : ℤ) :
    (z,k)∈(pairs F xs q).map key ↔ graph F xs q z.1 k z.2 := by
  rw [components]
  have eq : (z,k)∈(pairs F xs q).map key ↔ z∈pairs F xs q ∧ k=pairWeight z := by
    constructor
    · rintro h; obtain ⟨t,mem,e⟩ := List.mem_map.mp h
      have et : t=z := congrArg Prod.fst e
      subst t; exact ⟨mem,(congrArg Prod.snd e).symm⟩
    · rintro ⟨mem,rfl⟩; exact List.mem_map.mpr ⟨z,mem,rfl⟩
  rw [eq]
  simp only [pairs,List.mem_append,Finset.mem_toList,initialPairs,Finset.mem_filter,Finset.mem_univ,true_and,
    List.mem_map,List.mem_cons,List.not_mem_nil,or_false,or_assoc]
  simp [eq_comm]

theorem fresh (F : Family n) (xs : List (Fin n)) (q : Fin n) (nd : xs.Nodup) : (pairs (pad:=pad) F xs q).Nodup := by
  have initFresh : List.Disjoint (initialPairs F).toList (xs.map (@connector n pad)) := by
    intro z old inside
    obtain ⟨x,_,rfl⟩ := List.mem_map.mp inside
    exact missing F x (by simpa [initialPairs] using old)
  apply List.nodup_append.mpr
  refine ⟨List.nodup_append.mpr ⟨Finset.nodup_toList _,nd.map connector_inj,initFresh⟩,
    by simp [entry,exitEdge],?_⟩
  intro z core sel
  rcases List.mem_append.mp core with core|core
  · simp only [Finset.mem_toList,initialPairs,Finset.mem_filter,Finset.mem_univ,true_and] at core
    rcases List.mem_cons.mp sel with rfl|s
    · exact core
    · simp [List.mem_singleton.mp s,exitEdge,original] at core
  · obtain ⟨x,_,rfl⟩ := List.mem_map.mp core
    simp [connector,entry,exitEdge] at sel

abbrev queryHistory (d : A) (dec : A→Bool) (F : Family n) (xs : List (Fin n)) (q : Fin n) : Hist (L n) (R n pad) :=
  initial F++((before (plan n pad d dec) xs++[.inl (key (entry q))])++[.inl (key (exitEdge q))])
private theorem all_data (d : A) (dec : A→Bool) (F : Family n) (xs : List (Fin n)) (q : Fin n) :
    edits (queryHistory (pad:=pad) d dec F xs q)=(pairs F xs q).map key := by
  simp only [queryHistory,edits_append,initial_data,before_data,pairs,List.map_append]
  simp [edits,List.append_assoc]
theorem final_graph (d : A) (dec : A→Bool) (F : Family n) (xs : List (Fin n)) (q : Fin n) :
    edges (queryHistory (pad:=pad) d dec F xs q)=graph F xs q := by
  funext u k v; apply propext; simpa only [edges,all_data] using pair_mem F xs q (u,v) k

private theorem path_valid (d : A) (dec : A→Bool) (F : Family n) (xs : List (Fin n)) (q : Fin n) (nd : xs.Nodup)
    (h : Hist (L n) (R n pad)) (pre : h <+: before (plan n pad d dec) xs++(plan n pad d dec).finish q) :
    initLegal (init n pad) (legal (limit n)) F h := by
  let H := queryHistory (pad:=pad) d dec F xs q++[.inr ()]
  have p : initial F++h <+: H := by
    obtain ⟨tail,eq⟩ := pre
    refine ⟨tail,?_⟩
    simp only [H,queryHistory,List.append_assoc]
    simpa [plan,List.append_assoc] using congrArg (initial F++·) eq
  apply legal_prefix p
  have all : edits H=(pairs F xs q).map key := by
    change edits (_++_) = _; rw [edits_append,all_data]; simp [edits]
  have rel : edges H=graph F xs q := by
    funext u k v; apply propext; simpa only [edges,all] using pair_mem F xs q (u,v) k
  refine ⟨?_,?_,?_⟩
  · rw [all]
    simpa [List.map_map,key,Function.comp_def] using fresh (pad:=pad) F xs q nd
  · intro u k v e; exact weight_bound F xs q (rel ▸ e)
  · rw [rel]; exact planar F xs q

private theorem decode (F : Family n) (xs : List (Fin n)) (q : Fin n) :
    (!(decide (value n+1≤BipartiteOptimum.maximum (graph (pad:=pad) F xs q))))=answer F xs q := by
  rw [optimum]
  by_cases h : ∃x∈xs,x∈F q <;> simp [h,answer]
  exact fun x hx hxF => h ⟨x,hx,hxF⟩

theorem value_valid (n pad : ℕ) : Valid (plan n pad (0:ℤ) (fun z => !(decide (value n+1≤z))))
    (initLegal (init n pad) (legal (limit n))) (initSpec (init n pad) valueSpec) := by
  constructor
  · exact path_valid _ _
  · intro F xs q _
    change (!(decide (value n+1≤BipartiteOptimum.maximum (edges (queryHistory _ _ F xs q)))))=_
    rw [final_graph]; exact decode F xs q

theorem decision_valid (n pad : ℕ) : Valid (plan n pad false (!·))
    (initLegal (init n pad) (legal (limit n))) (initSpec (init n pad) (decisionSpec (value n+1))) := by
  constructor
  · exact path_valid _ _
  · intro F xs q _
    change (!(decide (value n+1≤BipartiteOptimum.maximum (edges (queryHistory _ _ F xs q)))))=_
    rw [final_graph]; exact decode F xs q

end
end DisjointnessDraft.Applications.MatchTarget
