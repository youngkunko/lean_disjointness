import DisjointnessDraft.Applications.DiameterLower
import DisjointnessDraft.Transfer.Initialization

/-! Empty-start planar diameter. Only the graph at a query must be connected.
Preprocessing physically inserts every edge in the connected input gadget
before making any of its padding queries. -/
namespace DisjointnessDraft.Applications.DiameterEmpty
open DiameterGraph PlanarPadding WeightedWalk GraphHistories Transfer.Compiler ShortTransfer MeasureTheory Filter Real
open Classical
noncomputable section

abbrev Hist (Z : Type) := List (Instr (WeightEdge Z) Unit)
def network (h : Hist Z) : Net Z := fun u k v => ((u,v),k)∈operations h
def Connected (F : Net Z) := ∀u v,∃k,Path (sym F) u k v
def legal (bound : ℤ) (_ : Unit) (h : Hist Z) :=
  ((operations h).map Prod.fst).Nodup ∧
  (∀u k v,network h u k v → 0<k ∧ k≤bound) ∧ Nonempty (Drawing (plain (network h))) ∧
  ∀pre : Hist Z, pre++[.inr ()] <+: h → Connected (network pre)
theorem legal_prefix (B : ℤ) {g h : Hist Z} (pre : g <+: h) (ok : legal B () h) : legal B () g := by
  have sub : operations g <+: operations h := pre.filterMap Sum.getLeft?
  refine ⟨ok.1.sublist (sub.map Prod.fst).sublist,fun _ _ _ e => ok.2.1 _ _ _ (sub.subset e),
    ok.2.2.1.some.mono (fun _ _ ⟨k,e⟩ => ⟨k,sub.subset e⟩),fun _ p => ok.2.2.2 _ (p.trans pre)⟩

def response (read : Net Z→A) (_ : Unit) (h : Hist Z) (_ : Unit) := read (network h)
def exactSpec (_ : Unit) (h : Hist Z) (_ : Unit) := diameter (network h)
def thresholdSpec (d : ℤ) (_ : Unit) (h : Hist Z) (_ : Unit) :=
  decide (∃j,Diameter.HasDiameter (sym (network h)) j ∧ j≤d)

variable {Z : Type} [Fintype Z]
def endpoints (F : Net Z) : Finset (Z×Z) := Finset.univ.filter fun e => plain F e.1 e.2
def tagged (F : Net Z) (e : Z×Z) : WeightEdge Z := (e,if h : plain F e.1 e.2 then Classical.choose h else 0)
def updates (F : Net Z) := (endpoints F).toList.map (tagged F)
def load (F : Net Z) : Hist Z := (updates F).map Sum.inl
def idle (F : Net Z) : Hist Z := List.replicate (Fintype.card (Z×Z)-(endpoints F).card) (.inr ())
def setup (Z : Type) [Fintype Z] : Initialization (Net Z) Unit (WeightEdge Z) Unit where
  initial _ := ()
  steps F := load F++idle F
  length := Fintype.card (Z×Z)
  fixed F := by
    have lim := Finset.card_le_univ (endpoints F)
    simp only [load,updates,idle,List.length_append,List.length_map,Finset.length_toList,List.length_replicate]; omega

def Functional (F : Net Z) := ∀u v j k,F u j v→F u k v→j=k

private theorem actual (f : Family n) : Functional (graph (pad:=pad) f []) := by
  intro u v j k a b
  rcases u with (u|s)|i <;> rcases v with (v|t)|i <;> try contradiction
  · exact (FinitePlanarDistance.weight_eq a).trans (FinitePlanarDistance.weight_eq b).symm
  · exact a.2.trans b.2.symm
  · change fan [] s v j at a; change fan [] s v k at b
    simp [fan] at a b
    exact a.2.trans b.2.symm
  · exact a.2.trans b.2.symm

theorem updates_mem {F : Net Z} (one : Functional F) (u v : Z) (k : ℤ) :
    ((u,v),k)∈updates F ↔ F u k v := by
  simp only [updates,List.mem_map,Finset.mem_toList,endpoints,Finset.mem_filter,Finset.mem_univ,true_and]
  constructor
  · rintro ⟨e,h,eq⟩
    obtain rfl : e=(u,v) := congrArg Prod.fst eq
    have w : Classical.choose h=k := by simpa [tagged,h] using congrArg Prod.snd eq
    exact w ▸ Classical.choose_spec h
  · intro h
    have e : plain F u v := ⟨k,h⟩
    exact ⟨(u,v),e,by simp [tagged,e,one u v _ _ (Classical.choose_spec e) h]⟩

private theorem load_ops (F : Net Z) : operations (load F)=updates F := by
  simp [load,operations,List.filterMap_map,Function.comp_def]
private theorem idle_ops (F : Net Z) : operations (idle F)=[] := by
  unfold idle; generalize Fintype.card (Z×Z)-(endpoints F).card=m
  induction m with
  | zero => rfl
  | succ m h => simpa only [operations,List.replicate_succ,List.filterMap_cons,Sum.getLeft?_inr] using h

theorem loaded_ops (F : Net Z) (h : Hist Z) : operations ((setup Z).steps F++h)=updates F++operations h := by
  change operations ((load F++idle F)++h)=_
  have app (a b : Hist Z) : operations (a++b)=operations a++operations b := List.filterMap_append
  rw [app,app,load_ops,idle_ops,List.append_nil]

theorem loaded {F : Net Z} (one : Functional F) (h : Hist Z) :
    network ((setup Z).steps F++h)=history F h := by
  funext u k v; apply propext
  simp only [network,loaded_ops,List.mem_append,updates_mem one,history,Merged]

theorem compatible {F : Net Z} (one : Functional F) (conn : Connected F) (B : ℤ) (h : Hist Z)
    (ok : DiameterGraph.legal B F h) : initLegal (setup Z) (legal B) F h := by
  change legal B () ((setup Z).steps F++h)
  refine ⟨?_,?_,?_,?_⟩
  · rw [loaded_ops,List.map_append,List.nodup_append]
    have eq : (updates F).map Prod.fst=(endpoints F).toList := by simp [updates,List.map_map,tagged,Function.comp_def]
    rw [eq]
    refine ⟨Finset.nodup_toList _,ok.1,?_⟩
    intro e he mem
    obtain ⟨w,hw,rfl⟩ := List.mem_map.mp mem
    exact ok.2.1 w hw (by simpa [endpoints] using he)
  · rw [loaded one]; exact ok.2.2.1
  · rw [loaded one]; exact ok.2.2.2.1
  · intro pre pq
    have first : load F <+: (setup Z).steps F++h :=
      (List.prefix_append (load F) (idle F)).trans (List.prefix_append _ h)
    rcases List.prefix_or_prefix_of_prefix first pq with yes|no
    · have incl : updates F <+: operations pre := by
        have preops : operations (load F) <+: operations (pre++[.inr ()]) := yes.filterMap Sum.getLeft?
        rw [load_ops] at preops
        simpa only [operations,List.filterMap_append,List.filterMap_cons,Sum.getLeft?_inr,List.filterMap_nil,List.append_nil] using preops
      have edge {u v k} (e : F u k v) : network pre u k v := incl.subset ((updates_mem one u v k).mpr e)
      intro u v
      obtain ⟨k,walk⟩ := conn u v
      exact ⟨k,walk.mono (fun _ _ _ e => e.elim (fun z=>Or.inl (edge z)) (fun z=>Or.inr (edge z)))⟩
    · have member := no.subset (show (.inr () : Instr (WeightEdge Z) Unit)∈pre++[.inr ()] by simp)
      simp [load] at member

private theorem adapted (hn : 1≤n) (decode : List A→Bool) (read : Net (W n pad)→A)
    (ok : Valid (plan n pad decode) (DiameterGraph.legal (3*span n))
      (fun F h (_ : Unit) => read (history F h))) :
    Valid (plan n pad decode) (initLegal (setup _) (legal (3*span n))) (initSpec (setup _) (response read)) := by
  refine ⟨fun f xs q nd h pre => compatible (actual f) (connected f [] hn) _ h (ok.1 f xs q nd h pre),?_⟩
  intro f xs q nd
  have e := ok.2 f xs q nd
  simpa only [plan,answers,initSpec,response,loaded (actual f)] using e

/-- Every large N. Updates build a planar positive-weight graph from empty;
all queries in the reduction occur on connected N-vertex graphs. -/
theorem lower (lo hi : ℝ) (lp : 0<lo) (lh : lo≤hi) :
    ∃c : ℝ,0<c ∧ ∀ᶠ N : ℕ in atTop,let n := ShortTransfer.stringSize N
      let p := DiameterGraph.padding N
      Fintype.card (W n p)=N ∧ Bound lo hi c N true (legal (Z:=W n p) (3*span n)) exactSpec ∧
      Bound lo hi c N true (legal (Z:=W n p) (3*span n)) (thresholdSpec (threshold n)) := by
  obtain ⟨c,cp,event⟩ := ShortTransfer.eventual lo hi lp lh
  obtain ⟨k,b⟩ := eventually_atTop.mp event
  obtain ⟨_,_,counts⟩ := DiameterGraph.lower lo hi lp lh
  refine ⟨c,cp,?_⟩
  filter_upwards [ShortTransfer.string_geometry (max k 40),counts] with N geom counts
  let n := ShortTransfer.stringSize N; let p := DiameterGraph.padding N
  obtain ⟨kn,n1,fit,low,high⟩ := geom
  have h : 40≤n := (le_max_right ..).trans kn
  have spare : size n<N := by
    change 9*(n*n)≤N at fit
    dsimp [size,PlanarEncoding.dim]; nlinarith [Nat.mul_le_mul_left n h]
  have can : 0<p := Nat.sub_pos_of_lt spare
  refine ⟨counts.1,?_,?_⟩
  · intro w tu tq tu1 tq1 wl wh Ω _ μ _ D H
    have cert := b n ((le_max_left ..).trans kn) N low high (plan n p (rc n)) true
      (adapted n1 _ diameter (valid_exact n1 can)) (by simp [plan]) (by simp [plan]) (by simp)
    exact cert w tu tq tu1 tq1 wl wh Ω μ (initialized D (setup _)) (init_guarantees μ D _ H)
  · intro w tu tq tu1 tq1 wl wh Ω _ μ _ D H
    let read := fun (F : Net (W n p)) => decide (∃d,Diameter.HasDiameter (sym F) d ∧ d≤threshold n)
    have cert := b n ((le_max_left ..).trans kn) N low high (plan n p rb) true
      (adapted n1 _ read (valid_test n1 can)) (by simp [plan]) (by simp [plan]) (by simp)
    exact cert w tu tq tu1 tq1 wl wh Ω μ (initialized D (setup _)) (init_guarantees μ D _ H)

end
end DisjointnessDraft.Applications.DiameterEmpty
