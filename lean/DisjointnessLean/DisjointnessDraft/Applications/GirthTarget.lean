import DisjointnessDraft.Applications.GirthDrawing
import DisjointnessDraft.Applications.ShortTransfer
import DisjointnessDraft.Transfer.Initialization

/-! Exact and threshold directed girth on an initially empty finite planar digraph.
The single selector insertion is charged to the query. -/
namespace DisjointnessDraft.Applications.GirthTarget
open GirthDrawing PlanarPadding WeightedWalk Transfer.Compiler ShortTransfer Classical
noncomputable section
variable {V : Type}
abbrev Edit (V : Type) := (V × V) × ℤ
abbrev Hist (V : Type) := List (Instr (Edit V) Unit)
def edits (h : Hist V) := h.filterMap Sum.getLeft?
def graph (h : Hist V) (u : V) (k : ℤ) (v : V) := ((u,v),k)∈edits h
def legal (B : ℤ) (_ : Unit) (h : Hist V) :=
  ((edits h).map Prod.fst).Nodup ∧
  (∀u k v,graph h u k v → 0<k ∧ k≤B) ∧ Nonempty (Tracing (plain (graph h)))
def Cycle (E : V → ℤ → V → Prop) (k : ℤ) := 0<k ∧ ∃u,Path E u k u
def exactSpec (_ : Unit) (h : Hist V) (_ : Unit) : Option ℕ :=
  if poss : ∃ k : ℕ,Cycle (graph h) k then some (Nat.find poss) else none
def testSpec (D : ℤ) (_ : Unit) (h : Hist V) (_ : Unit) := decide (∃k,k≤D ∧ Cycle (graph h) k)

structure Core (n : ℕ) (V : Type) where
  network : Family n → List (Fin n) → V → ℤ → V → Prop
  weight : V → V → ℤ
  put : Fin n → V × V
  src : Fin n → V
  dst : Fin n → V
  canonical : ∀ f xs u w v,network f xs u w v → w=weight u v
  activity : ∀ f xs u w v,network f xs u w v ↔ network f [] u w v ∨
    ∃x∈xs,(u,v)=put x ∧ w=weight u v
  fresh : ∀ f x,¬plain (network f []) (put x).1 (put x).2
  injective : Function.Injective put
  selector : ∀ f xs q,¬plain (network f xs) (dst q) (src q)

structure Certificate (C : Core n V) (B D : ℤ) : Prop where
  bound : ∀f xs q u k v,addBack (C.network f xs) (C.src q) (C.dst q) u k v → 0<k ∧ k≤B
  planar : ∀f xs q,Nonempty (Tracing (plain (addBack (C.network f xs) (C.src q) (C.dst q))))
  girth : ∀f xs q,let d := D+1-(if ∃x∈xs,x∈f q then (1:ℤ) else 0)
    Cycle (addBack (C.network f xs) (C.src q) (C.dst q)) d ∧
      ∀k,Cycle (addBack (C.network f xs) (C.src q) (C.dst q)) k → d≤k

variable [Fintype V] (C : Core n V)
def original (f : Family n) := Finset.univ.filter (fun a : V×V => plain (C.network f []) a.1 a.2)
def tag (u : V×V) : Edit V := (u,C.weight u.1 u.2)
def back (q : Fin n) : Edit V := ((C.dst q,C.src q),1)
def initial (f : Family n) : Hist V :=
  ((original C f).toList.map (tag C)).map Sum.inl ++
    List.replicate (Fintype.card (V×V)-(original C f).card) (.inr ())
def init : Initialization (Family n) Unit (Edit V) Unit where
  initial _ := ()
  steps := initial C
  length := Fintype.card (V×V)
  fixed f := by have lim := Finset.card_le_univ (original C f); simp only [initial,List.length_append,List.length_map,Finset.length_toList,List.length_replicate]; omega
def plan (a : A) (decode : A → Bool) : Schedule n (Family n) (Edit V) Unit A :=
  ⟨id,fun x => [tag C (C.put x)],fun q => [.inl (back C q),.inr ()],fun _ xs => decode (xs.headD a)⟩

omit [Fintype V] in
@[simp] theorem edits_append [Fintype V] (a b : Hist V) : edits (a++b)=edits a++edits b := List.filterMap_append
theorem setup_data (f : Family n) : edits (initial C f)=(original C f).toList.map (tag C) := by
  have nils (k : ℕ) : edits (List.replicate k (.inr () : Instr (Edit V) Unit))=[] := by
    induction k with | zero => rfl | succ k ih => simpa only [edits,List.replicate_succ,List.filterMap_cons,Sum.getLeft?_inr] using ih
  simp [initial,nils,edits,List.filterMap_map,Function.comp_def]
theorem data_before (d : A) (c : A → Bool) (xs : List (Fin n)) :
    edits (before (plan C d c) xs)=(xs.map C.put).map (tag C) := by
  -- Retain the original section instance in the theorem's signature.
  let _compatVertexTypes := (inferInstance : Fintype V)
  simp [edits,before,plan,←List.map_eq_flatMap,List.filterMap_map,List.map_map,Function.comp_def]

def pairs (f : Family n) (xs : List (Fin n)) := (original C f).toList++xs.map C.put
theorem data_core (f : Family n) (xs : List (Fin n)) (u v : V) (k : ℤ) :
    ((u,v),k)∈(pairs C f xs).map (tag C) ↔ C.network f xs u k v := by
  rw [C.activity]
  simp only [pairs,List.mem_map,List.mem_append,Finset.mem_toList,original,Finset.mem_filter,Finset.mem_univ,true_and]
  constructor
  · rintro ⟨ab,on|⟨x,on,rfl⟩,same⟩
    · have e : ab=(u,v) := congrArg Prod.fst same; subst ab
      obtain ⟨w,ow⟩ := on
      have wk : w=k := (C.canonical _ _ _ _ _ ow).trans (congrArg Prod.snd same)
      exact Or.inl (wk▸ow)
    · have hp : C.put x=(u,v) := congrArg Prod.fst same
      have hw : C.weight (C.put x).1 (C.put x).2=k := congrArg Prod.snd same
      rw [hp] at hw; exact Or.inr ⟨x,on,hp.symm,hw.symm⟩
  · rintro (old|⟨x,p,eq,wt⟩)
    · exact ⟨(u,v),Or.inl ⟨k,old⟩,by simp [tag,←C.canonical _ _ _ _ _ old]⟩
    · exact ⟨(u,v),Or.inr ⟨x,p,eq.symm⟩,by simp [tag,wt]⟩

theorem full (f : Family n) (xs : List (Fin n)) (q : Fin n) (h : Hist V)
    (all : edits h=(pairs C f xs).map (tag C)++[back C q]) :
    graph h=addBack (C.network f xs) (C.src q) (C.dst q) := by
  funext u k v; apply propext; simp only [graph,all,List.mem_append,List.mem_singleton,data_core,addBack,back,Prod.mk.injEq]
  tauto

omit [Fintype V] in
theorem prefix_legal [Fintype V] {h H : Hist V} {B : ℤ} (p : h <+: H) (ok : legal B () H) : legal B () h := by
  have sub := p.filterMap Sum.getLeft?
  exact ⟨ok.1.sublist (sub.map Prod.fst).sublist,fun _ _ _ e => ok.2.1 _ _ _ (sub.subset e),
    ok.2.2.some.mono (fun _ _ ⟨k,e⟩ => ⟨k,sub.subset e⟩)⟩

def billed (f : Family n) (xs : List (Fin n)) (q : Fin n) (a : A) (c : A → Bool) :=
  initial C f++(before (plan C a c) xs++[.inl (back C q)])
theorem billed_data (f : Family n) (xs : List (Fin n)) (q : Fin n) (a : A) (c : A → Bool) :
    edits (billed C f xs q a c)=(pairs C f xs).map (tag C)++[back C q] := by
  simp only [billed,edits_append,setup_data,data_before,pairs,List.map_append,List.append_assoc]; rfl
theorem path_valid {B D : ℤ} (cert : Certificate C B D) (d : A) (c : A → Bool) (f : Family n) (xs : List (Fin n)) (q : Fin n)
    (nd : xs.Nodup) (h : Hist V) (pre : h <+: before (plan C d c) xs++(plan C d c).finish q) :
    initLegal (init C) (legal B) f h := by
  let H := billed C f xs q d c++[.inr ()]
  apply prefix_legal (H:=H) (by obtain ⟨r,e⟩ := pre; refine ⟨r,?_⟩; simpa [init,H,billed,plan,List.append_assoc] using congrArg (initial C f++·) e)
  have all : edits H=(pairs C f xs).map (tag C)++[back C q] := by simp only [H,edits_append,billed_data]; simp [edits]
  have graphEq := full C f xs q H all
  have nd' : (pairs C f xs).Nodup := List.nodup_append.mpr ⟨Finset.nodup_toList _,nd.map C.injective,by
    intro e old into; obtain ⟨x,_,rfl⟩ := List.mem_map.mp into; exact C.fresh f x (by simpa [original] using old)⟩
  have no : (C.dst q,C.src q)∉pairs C f xs := by
    intro mem
    exact C.selector f xs q ⟨_,(data_core C f xs _ _ _).mp (List.mem_map.mpr ⟨_,mem,rfl⟩)⟩
  change ((edits H).map Prod.fst).Nodup ∧ _
  rw [all]; refine ⟨?_,?_,?_⟩
  · simpa [List.map_append,List.map_map,tag,back,Function.comp_def,nd',List.nodup_append] using no
  · intro u k v e; rw [graphEq] at e; exact cert.bound f xs q u k v e
  · rw [graphEq]; exact cert.planar f xs q

def read (D : ℤ) (a : Option ℕ) := decide (a=some (D+1).toNat)
private theorem nohit (f : Family n) (xs : List (Fin n)) (q : Fin n) :
    decide (¬∃x∈xs,x∈f q)=answer f xs q := by apply decide_eq_decide.mpr; simp
theorem exact_valid {B D : ℤ} (cert : Certificate C B D) :
    Valid (plan C none (read D)) (initLegal (init C) (legal B)) (initSpec (init C) exactSpec) := by
  refine ⟨fun f xs q nd h pre => path_valid C cert _ _ f xs q nd h pre,?_⟩
  intro f xs q _
  let h := billed C f xs q none (read D)
  change read D (exactSpec () h ())=_
  have ge := full C f xs q h (billed_data ..)
  let d := D+1-(if ∃x∈xs,x∈f q then (1:ℤ) else 0)
  have z := cert.girth f xs q
  change Cycle _ d ∧ _ at z
  have c : Cycle (graph h) (d.toNat:ℤ) := by simpa [ge,Int.toNat_of_nonneg z.1.1.le] using z.1
  have poss : ∃ k : ℕ,Cycle (graph h) k := ⟨_,c⟩
  have eq : Nat.find poss=d.toNat := by
    apply le_antisymm (Nat.find_min' _ c)
    have atMin := Nat.find_spec poss; have hmin := z.2 (Nat.find poss) (show Cycle _ ((Nat.find poss:ℕ):ℤ) from ge ▸ atMin); omega
  rw [←nohit]; unfold exactSpec read; rw [dif_pos poss,eq]
  apply decide_eq_decide.mpr; rw [Option.some.injEq]
  by_cases hit : ∃x∈xs,x∈f q
  · have pos := z.1.1; simp [d,hit] at pos ⊢; omega
  · simp [d,hit]

theorem test_valid {B D : ℤ} (cert : Certificate C B D) :
    Valid (plan C false (!·)) (initLegal (init C) (legal B)) (initSpec (init C) (testSpec D)) := by
  refine ⟨fun f xs q nd h pre => path_valid C cert _ _ f xs q nd h pre,?_⟩
  intro f xs q _
  let h := billed C f xs q false (!·)
  change (!decide (∃k,k≤D ∧ Cycle (graph h) k))=_
  rw [full C f xs q h (billed_data ..),←nohit,←decide_not]; apply decide_eq_decide.mpr
  apply not_congr
  have z := cert.girth f xs q
  constructor
  · rintro ⟨k,kd,p⟩; have le := z.2 k p; by_contra miss; simp [miss] at le; omega
  · intro hit; exact ⟨_,by simp [hit],z.1⟩

theorem physical {B D : ℤ} (cert : Certificate C B D) (lo hi c : ℝ) (N : ℕ)
    (rates : Realizes lo hi c n N) :
    Bound lo hi c N true (legal (V:=V) B) exactSpec ∧ Bound lo hi c N true (legal (V:=V) B) (testSpec D) := by
  constructor
  · intro w tu tq tu1 tq1 wl wh Ω _ μ _ D' H
    have h := rates (plan C none (read D)) true (exact_valid C cert) (by simp [plan]) (by simp [plan]) (by simp)
    exact h w tu tq tu1 tq1 wl wh Ω μ (initialized D' (init C)) (init_guarantees μ D' _ H)
  · intro w tu tq tu1 tq1 wl wh Ω _ μ _ D' H
    have h := rates (plan C false (!·)) true (test_valid C cert) (by simp [plan]) (by simp [plan]) (by simp)
    exact h w tu tq tu1 tq1 wl wh Ω μ (initialized D' (init C)) (init_guarantees μ D' _ H)
end
end DisjointnessDraft.Applications.GirthTarget
