import DisjointnessDraft.Applications.SubgraphCosts
import DisjointnessDraft.Applications.SetDisjointness
import DisjointnessDraft.Applications.ShortTransfer
import DisjointnessDraft.Transfer.Initialization
/-! A direct Boolean reduction with one final target query. The target may
write during queries and may interleave queries with subsequent updates. -/
namespace DisjointnessDraft.Transfer.DirectPrograms
open DisjointnessFoundations Compiler Applications.ShortTransfer
noncomputable section

variable {n : ℕ} {F E Q : Type}

def updates (h : List (Instr E Q)) : List E := h.filterMap Sum.getLeft?

def legal (P : Problem F E Q) (f : F) (h : List (Instr E Q)) := P.legal f (updates h)
def spec (P : Problem F E Q) (f : F) (h : List (Instr E Q)) := P.answer f (updates h)

private def load (A : Preload.Map n F E Q) : Initialization (Family n) F E Q where
  initial := A.initial
  steps f := (A.setup f).map Sum.inl
  length := A.length
  fixed f := by simp [A.fixed]

private def schedule (A : Preload.Map n F E Q) : Schedule n (Family n) E Q Bool :=
  ⟨id,fun x => [A.insert x],fun q => [.inr (A.ask q)],fun _ vs => InputReduction.out A.negate (vs.headD false)⟩

private theorem history (A : Preload.Map n F E Q) (f : Family n) (xs : List (Fin n)) :
    updates ((load A).steps f ++ before (schedule A) xs) = A.setup f ++ xs.map A.insert := by
  simp [updates,load,before,schedule,List.filterMap_append,←List.map_eq_flatMap,List.filterMap_map,Function.comp_def]

private theorem valid (P : Problem F E Q) (A : Preload.Map n F E Q) (direct : Direct P A)
    (closed : ∀ f {u v : List E}, u <+: v → P.legal f v → P.legal f u) :
    Valid (schedule A) (initLegal (load A) (legal P)) (initSpec (load A) (spec P)) := by
  constructor
  · intro f xs q fresh h pre
    change P.legal (A.initial f) (updates ((load A).steps f ++ h))
    apply closed _ _ (direct.legal f xs fresh)
    rw [←history A f xs]
    have full : (load A).steps f ++ h <+: ((load A).steps f ++ before (schedule A) xs) ++ [.inr (A.ask q)] := by
      obtain ⟨tail,ht⟩ := pre
      refine ⟨tail,?_⟩
      simpa only [List.append_assoc] using congrArg ((load A).steps f ++ ·) ht
    simpa [updates,List.filterMap_append] using full.filterMap Sum.getLeft?
  · intro f xs q fresh
    change InputReduction.out A.negate (P.answer (A.initial f) (updates ((load A).steps f ++ before (schedule A) xs)) (A.ask q)) = _
    rw [history,direct.correct f xs q fresh]
    cases A.negate <;> simp [InputReduction.out]

/-- Transfer both query-only lower bounds from one operation per insertion and
one final query, including targets whose earlier queries can change memory. -/
theorem lower {lo hi c : ℝ} {N : ℕ} (bound : Realizes lo hi c n N) (P : Problem F E Q)
    (A : Preload.Map n F E Q) (correct : Direct P A)
    (closed : ∀ f {u v : List E}, u <+: v → P.legal f v → P.legal f u) :
    Bound lo hi c N false (legal P) (spec P) := by
  intro w tu tq u q wl wh Ω _ μ _ D gu
  have low := bound (schedule A) false (valid P A correct closed)
    (by simp [schedule]) (by simp [schedule]) (by simp [schedule])
  exact low w tu tq u q wl wh Ω μ (initialized D (load A)) (init_guarantees μ D _ gu)

end
end DisjointnessDraft.Transfer.DirectPrograms

namespace DisjointnessDraft.Applications.BooleanTargets
open DisjointnessFoundations Transfer Graphs Reachability ShortTransfer Filter Classical
noncomputable section

def sinkProblem {W : Type} (sink : W) : Problem Unit (Edge W) W where
  legal _ es := layered es
  answer _ es q := decide (reach (fun u v => (u,v)∈es) q sink)

private theorem sink_direct (n p : ℕ) : Direct (sinkProblem (target n p)) (translation n p) := by
  refine ⟨fun f xs distinct => Reachability.legal f xs distinct,?_⟩
  intro f xs q _
  change decide (reach (fun u v => (u,v) ∈ edges (pad:=p) f xs) (row q) (target n p)) =
    InputReduction.out true (DisjointnessDraft.answer f xs q)
  rw [reachable]
  by_cases hit : ∃ j∈xs,j∈f q
  · have no : ¬ ∀ j∈xs,j∉f q := fun h => hit.elim (fun j m => h j m.1 m.2)
    simp [InputReduction.out,DisjointnessDraft.answer,hit,no]
  · have all : ∀ j∈xs,j∉f q := fun j m member => hit ⟨j,m,member⟩
    simp [InputReduction.out,DisjointnessDraft.answer,hit]; exact all

private theorem layers_prefix {W : Type} {u v : List (Edge W)} (pre : u <+: v) (h : layered v) : layered u :=
  ⟨pre.sublist.nodup h.1,h.2.choose,fun x hx => h.2.choose_spec x (pre.subset hx)⟩

/-- Fixed-sink and fixed-source reachability on depth-two DAGs, and
connectivity under vertex activation, for targets with writable queries. -/
theorem graphs (lo hi : ℝ) (pos : 0<lo) (ordered : lo≤hi) :
    ∃ c : ℝ, 0<c ∧ ∀ᶠ N : ℕ in atTop,
      let n := N/4
      let p := pad N
      let P := sinkProblem (target n p)
      let R := reverseProblem (target n p)
      let C := SubgraphCosts.problem (Vertex n p)
      Fintype.card (Vertex n p)=N ∧
      Bound lo hi c N false (DirectPrograms.legal P) (DirectPrograms.spec P) ∧
      Bound lo hi c N false (DirectPrograms.legal R) (DirectPrograms.spec R) ∧
      Bound lo hi c N false (DirectPrograms.legal C) (DirectPrograms.spec C) := by
  obtain ⟨c,cp,H⟩ := eventual lo hi pos ordered
  obtain ⟨k,hk⟩ := eventually_atTop.mp H
  refine ⟨c,cp,?_⟩
  filter_upwards [eventually_ge_atTop (4*k+16)] with N big
  let n := N/4
  have kn : k≤n := by dsimp [n]; omega
  have n4 : 4≤n := by dsimp [n]; omega
  have cube : N≤n^3 := by
    have limit : N≤4*n+3 := by dsimp [n]; omega
    nlinarith only [limit,Nat.mul_le_mul_right n n4,Nat.mul_le_mul_right (n^2) n4,n4]
  have low : Realizes lo hi c n N := @hk n kn N (Nat.div_le_self N 4) cube
  refine ⟨cardinality (by omega),DirectPrograms.lower low _ _ (sink_direct ..) (fun _ {_ _} pre h => layers_prefix pre h),
    DirectPrograms.lower low _ _ (reverse_valid ..) (fun _ {_ _} pre h => layers_prefix pre h),?_⟩
  apply DirectPrograms.lower low _ _ (SubgraphCosts.valid ..)
  intro f u v pre h
  exact ⟨pre.sublist.nodup h.1,fun x hx => h.2 x (pre.subset hx)⟩

/-- Dynamic set disjointness with writable queries and a bounded universe. -/
theorem sets (lo hi : ℝ) (pos : 0<lo) (ordered : lo≤hi) :
    ∃c : ℝ, 0<c ∧ ∀ᶠ n : ℕ in atTop,
      let P := SetDisjointness.problem n
      Bound lo hi c n false (DirectPrograms.legal P) (DirectPrograms.spec P) := by
  obtain ⟨c,cp,H⟩ := eventual lo hi pos ordered
  refine ⟨c,cp,?_⟩
  filter_upwards [H,eventually_ge_atTop 1] with n low hn
  have cube : n≤n^3 := by simpa [pow_succ,Nat.mul_assoc] using Nat.le_mul_of_pos_left n (Nat.mul_pos hn hn)
  apply DirectPrograms.lower (@low n le_rfl cube) _ _ (SetDisjointness.correct n)
  intro f u v pre h
  exact ⟨pre.sublist.nodup h.1,fun x hx => h.2 x (pre.subset hx)⟩

end
end DisjointnessDraft.Applications.BooleanTargets
