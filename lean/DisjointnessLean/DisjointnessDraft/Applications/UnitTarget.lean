import DisjointnessDraft.Applications.UnitMetric
import DisjointnessDraft.Applications.WeightedPlanarLower

/-! The target update carries only the endpoints of a unit edge. Every
vertex of an incomplete connector remains present when its first edge is
absent. Extra target vertices are pendant leaves. -/
namespace DisjointnessDraft.Applications.UnitTarget
open FiniteSubdivision UnitEncoding PlanarPadding PlanarEncoding WeightedWalk Classical Transfer.Compiler
noncomputable section
abbrev Pair (T : Type) := T × T
abbrev Hist (T : Type) := List (Instr (Pair T) (Pair T))
def keys (h : Hist T) := h.filterMap Sum.getLeft?
def graph (h : Hist T) (a : T) (k : ℤ) (b : T) := k=1 ∧ (a,b)∈keys h
def legal (_ : Unit) (h : Hist T) := (keys h).Nodup ∧ Nonempty (Drawing (fun a b => (a,b)∈keys h))
def exactSpec (_ : Unit) (h : Hist T) := PlanarTarget.minimum (graph h)
def thresholdSpec (t : ℤ) (_ : Unit) (h : Hist T) (q : Pair T) := decide (∃ k : ℤ,k≤t ∧ Path (sym (graph h)) q.1 k q.2)
theorem prefix_valid {h H : Hist T} (p : h <+: H) (o : legal () H) : legal () h :=
  ⟨o.1.sublist (p.filterMap Sum.getLeft?).sublist,o.2.some.mono (fun _ _ e => (p.filterMap Sum.getLeft?).subset e)⟩

variable {n pad : ℕ} (hn : 0<n)
abbrev V (n pad : ℕ) (nz : 0<n) := U n nz ⊕ Fin pad
def rootU : U n hn := .inl (root n)
def present (f : Family n) (xs : List (Fin n)) : V n pad hn → ℤ → V n pad hn → Prop :=
  extend (unit (mesh (dim n) (sourceDim hn)) (on f xs)) (rootU hn)
def edgeKey (j : Fin n) : Pair (V n pad hn) := (.inl (added hn j).1,.inl (added hn j).2)
def terminals (q : Fin n) : Pair (V n pad hn) := (.inl (UnitEncoding.query hn q).1,.inl (UnitEncoding.query hn q).2)

theorem weight_one {f : Family n} {xs : List (Fin n)} {u v : V n pad hn} {k} (e : present hn f xs u k v) : k=1 := by
  rcases u with u|u <;> rcases v with v|v <;> try contradiction
  · exact e.1
  · exact e.2

theorem is_planar (f : Family n) (xs : List (Fin n)) :
    Nonempty (Drawing (plain (present (pad:=pad) hn f xs))) := by
  let G := mesh (dim n) (sourceDim hn)
  have eq : plain (unit G (on f xs))=enabledEdge hn f xs := by funext a b; simp [plain,unit,enabledEdge,G]
  let D := UnitEncoding.drawing hn f xs
  let D' : Drawing (plain (unit G (on f xs))) := ⟨D.point,D.injective,fun h => D.miss (eq▸h),fun f e => D.apart (eq▸f) (eq▸e)⟩
  exact PlanarPadding.drawing _ (rootU hn) D' (upper_plane hn f xs) (root_y n)

theorem actual (f : Family n) (xs : List (Fin n)) (u v : V n pad hn) :
    plain (present hn f xs) u v ↔ plain (present hn f []) u v ∨ ∃x∈xs,(u,v)=edgeKey hn x := by
  rcases u with u|u <;> rcases v with v|v
  case inl.inr | inr.inl | inr.inr => simp [plain,present,PlanarPadding.extend,edgeKey,Prod.mk.injEq]
  simp only [plain,present,PlanarPadding.extend,unit,exists_eq_left',edgeKey,Prod.mk.injEq,Sum.inl.injEq]
  simpa [enabledEdge,Prod.ext_iff] using first_edge hn f xs u v

theorem new_edge (f : Family n) (j : Fin n) :
    ¬plain (present (pad:=pad) hn f []) (edgeKey hn j).1 (edgeKey hn j).2 :=
  fun ⟨_,_,ed⟩ => absent hn f j ed

theorem edge_inj : Function.Injective (edgeKey (pad:=pad) hn) := by
  intro x y e; apply added_injective hn
  apply Prod.ext
  · exact Sum.inl.inj (congrArg Prod.fst e)
  · exact Sum.inl.inj (congrArg Prod.snd e)

theorem distance (f : Family n) (xs : List (Fin n)) (q : Fin n) :
    let d := PlanarTarget.normal n - (if ∃x∈xs,x∈f q then 1 else 0)
    let term := terminals (pad:=pad) hn q
    Path (sym (present hn f xs)) term.1 d term.2 ∧ ∀ k,Path (sym (present hn f xs)) term.1 k term.2 → d≤k := by
  have core := UnitEncoding.distance hn f xs q
  exact ⟨upper_path (rootU hn) core.1,fun k p => by obtain ⟨d,le,h⟩ := lower_path p; exact (core.2 d h).trans le⟩

def original (f : Family n) : Finset (Pair (V n pad hn)) := Finset.univ.filter (fun p => plain (present hn f []) p.1 p.2)
def allKeys (f : Family n) (xs : List (Fin n)) : List (Pair (V n pad hn)) := (original hn f).toList++xs.map (edgeKey hn)
def initial (f : Family n) : Hist (V n pad hn) :=
  (original hn f).toList.map Sum.inl++List.replicate (Fintype.card (Pair (V n pad hn))-(original (pad:=pad) hn f).card)
    (.inr (.inl (rootU hn),.inl (rootU hn)))
def init (pad : ℕ) : Initialization (Family n) Unit (Pair (V n pad hn)) (Pair (V n pad hn)) where
  initial _ := ()
  steps := initial hn
  length := Fintype.card (Pair (V n pad hn))
  fixed f := by
    have lim := Finset.card_le_univ (original (pad:=pad) hn f)
    simp only [initial,List.length_append,List.length_map,Finset.length_toList,List.length_replicate]; omega
def plan (pad : ℕ) (d : A) (readout : A → Bool) : Schedule n (Family n) (Pair (V n pad hn)) (Pair (V n pad hn)) A :=
  ⟨id,fun j => [edgeKey hn j],fun q => [.inr (terminals hn q)],fun _ xs => readout (xs.headD d)⟩

theorem native_mem (f : Family n) (xs : List (Fin n)) (a b : V n pad hn) : (a,b)∈allKeys hn f xs ↔ plain (present hn f xs) a b := by
  rw [actual]; simp [allKeys,original,eq_comm]

theorem fresh (f : Family n) (xs : List (Fin n)) (nd : xs.Nodup) : (allKeys (pad:=pad) hn f xs).Nodup := by
  refine List.nodup_append.mpr ⟨Finset.nodup_toList _,nd.map (edge_inj hn),?_⟩
  intro e old ins; obtain ⟨j,_,rfl⟩ := List.mem_map.mp ins
  exact new_edge hn f j (by simpa [original] using old)

@[simp] theorem keys_append (h s : Hist T) : keys (h++s)=keys h++keys s := List.filterMap_append
theorem initial_keys (f : Family n) : keys (initial (pad:=pad) hn f)=(original hn f).toList := by
  have ignored (k : ℕ) (a : Pair (V n pad hn)) : keys (List.replicate k (.inr a))=[] := by
    induction k with
    | zero => rfl
    | succ k ih => simpa only [keys,List.replicate_succ,List.filterMap_cons,Sum.getLeft?_inr] using ih
  simp only [initial,keys_append,ignored,List.append_nil]; simp [keys,List.filterMap_map,Function.comp_def]
theorem before_keys (d : A) (c : A → Bool) (xs : List (Fin n)) :
    keys (before (plan hn pad d c) xs)=xs.map (edgeKey hn) := by
  simp [keys,before,plan,←List.map_eq_flatMap,List.filterMap_map,Function.comp_def]

theorem final_graph (f : Family n) (xs : List (Fin n)) (d : A) (c : A → Bool) :
    graph (initial hn f++before (plan hn pad d c) xs)=present hn f xs := by
  funext a k b; apply propext
  change k=1 ∧ (a,b)∈keys (initial hn f++before _ xs) ↔ _
  rw [keys_append,initial_keys,before_keys,← allKeys,native_mem]
  constructor
  · rintro ⟨rfl,t,e⟩; simpa only [weight_one hn e] using e
  · intro e; exact ⟨weight_one hn e,k,e⟩

theorem valid_path (d : A) (c : A → Bool) (f : Family n) (xs : List (Fin n)) (q : Fin n)
    (nd : xs.Nodup) (h : Hist (V n pad hn)) (pre : h <+: before (plan hn pad d c) xs++(plan hn pad d c).finish q) :
    initLegal (init hn pad) legal f h := by
  apply prefix_valid (show initial hn f++h <+: initial hn f++(before (plan hn pad d c) xs++(plan hn pad d c).finish q) from
    by obtain ⟨rest,e⟩ := pre; exact ⟨rest,by simp [e,List.append_assoc]⟩)
  let final := initial hn f++(before (plan hn pad d c) xs++(plan hn pad d c).finish q)
  have eq : keys final=allKeys hn f xs := by
    simp only [final,keys_append,initial_keys,before_keys,allKeys]; change _++(_++[]) = _; simp
  refine ⟨by change (keys final).Nodup; rw [eq]; exact fresh hn f xs nd,?_⟩
  apply (is_planar (pad:=pad) hn f xs).some.mono
  intro a b e
  exact (native_mem hn f xs a b).mp (eq ▸ e)

end
end DisjointnessDraft.Applications.UnitTarget
