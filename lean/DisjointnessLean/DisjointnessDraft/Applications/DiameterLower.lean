import DisjointnessDraft.Applications.DiameterGeometry
import DisjointnessDraft.Applications.ShortTransfer

/-! Exact diameter on connected planar graphs with positive integer weights.
The initial graph is connected. All updates are ordinary single-edge
insertions, including the two shortcuts which precede the final query. -/
namespace DisjointnessDraft.Applications.DiameterGraph
open PlanarEncoding PlanarPadding WeightedWalk GraphHistories Transfer.Compiler ShortTransfer MeasureTheory Filter Real CoreSize
open Classical
noncomputable section
variable {n pad : ℕ} {Z : Type}

theorem endpoint_injective : Function.Injective (fun z : Act n => (inserted (pad:=pad) z).1) := by
  intro a b e
  cases a <;> cases b
  case attach.attach x y => simpa [inserted] using congrArg Prod.fst e
  case attach.select => cases e
  case select.attach => cases e
  case select.select s q t r =>
    have same : s=t := by simpa [inserted,center] using congrArg Prod.fst e
    subst t
    have qr := visitor_inj s (show visitor s q.castSucc=visitor s r.castSucc by simpa [inserted] using congrArg Prod.snd e)
    obtain rfl := Fin.castSucc_injective _ qr; rfl

def history (F : Net Z) (h : List (Instr (WeightEdge Z) Unit)) := Merged F (operations h)

def legal (bound : ℤ) (F : Net Z) (h : List (Instr (WeightEdge Z) Unit)) :=
  ((operations h).map Prod.fst).Nodup ∧ (∀e∈operations h,¬plain F e.1.1 e.1.2) ∧
  (∀u k v,history F h u k v → 0<k ∧ k≤bound) ∧
  Nonempty (Drawing (plain (history F h))) ∧ (∀u v,∃k,Path (sym (history F h)) u k v)

theorem diameter_unique {E : Net Z} {d j : ℤ} (a : Diameter.HasDiameter E d) (b : Diameter.HasDiameter E j) : d=j := by
  have le {i t : ℤ} (A : Diameter.HasDiameter E i) (B : Diameter.HasDiameter E t) : i≤t := by
    obtain ⟨⟨u,v,_,least⟩,_⟩ := A; obtain ⟨k,le,walk⟩ := B.2 u v; exact (least _ walk).trans le
  exact le_antisymm (le a b) (le b a)

def diameter (F : Net Z) : Option ℤ := if h : ∃ d,Diameter.HasDiameter (sym F) d then some (Classical.choose h) else none
theorem value_eq {F : Net Z} {d : ℤ} (h : Diameter.HasDiameter (sym F) d) : diameter F=some d := by
  have ex := Exists.intro d h; rw [diameter,dif_pos ex,diameter_unique (Classical.choose_spec ex) h]

def threshold (n : ℕ) := 2*span n+2*PlanarCore.H (dim n)
def spec (F : Net Z) (h : List (Instr (WeightEdge Z) Unit)) (_ : Unit) := diameter (history F h)
def testSpec (t : ℤ) (F : Net Z) (h : List (Instr (WeightEdge Z) Unit)) (_ : Unit) := decide (∃d,Diameter.HasDiameter (sym (history F h)) d ∧ d≤t)

def plan (n pad : ℕ) (read : List A→Bool) : Schedule n (Net (W n pad)) (WeightEdge (W n pad)) Unit A :=
  ⟨fun F => graph F [],fun j => [inserted (.attach j)],fun q =>
    [.inl (inserted (.select false q)),.inl (inserted (.select true q)),.inr ()],fun _ => read⟩
def rc (n : ℕ) (r : List (Option ℤ)) := decide (r.headD none=some (threshold n+1))
def rb (r : List Bool) := !(r.headD false)
theorem full_nd (xs : List (Fin n)) (q : Fin n) (nd : xs.Nodup) : (full xs q).Nodup := by
  apply List.nodup_append.mpr
  refine ⟨nd.map (fun _ _ h => Act.attach.inj h),by simp,?_⟩
  intro x a b; obtain ⟨j,_,rfl⟩ := List.mem_map.mp a; simp at b

theorem complete_ops (read : List A→Bool) (xs : List (Fin n)) (q : Fin n) :
    operations (before (plan n pad read) xs++(plan n pad read).finish q)=(full xs q).map inserted := by
  simp [operations,before,plan,full,←List.map_eq_flatMap,List.filterMap_append,List.filterMap_map,List.map_map,Function.comp_def]

theorem prefix_valid (read : List A→Bool) (hn : 1≤n) (f : Family n) (xs : List (Fin n)) (q : Fin n)
    (nd : xs.Nodup) (h) (pre : h <+: before (plan n pad read) xs++(plan n pad read).finish q) :
    legal (3*span n) (graph f []) h := by
  have p := pre.filterMap Sum.getLeft?
  change operations h <+: operations _ at p
  rw [complete_ops] at p
  let a := (full xs q).take (operations h).length
  have eq : operations h=a.map inserted := by
    rw [show a.map inserted=((full xs q).map (inserted (pad:=pad))).take (operations h).length by simp [a]]
    exact List.prefix_iff_eq_take.mp p
  have rel : history (graph (pad:=pad) f []) h=graph f a := by rw [history,eq,←acts]
  refine ⟨?_,?_,?_,?_,?_⟩
  · rw [eq,List.map_map]
    exact ((full_nd xs q nd).sublist (List.take_sublist ..)).map endpoint_injective
  · intro e he; rw [eq] at he; obtain ⟨z,_,rfl⟩ := List.mem_map.mp he; exact fresh f z
  · rw [rel]; exact fun _ _ _ => bounded f a hn
  · rw [rel]; exact planar f a
  · rw [rel]; exact connected f a hn

theorem query_state (read : List A→Bool) (f : Family n) (xs : List (Fin n)) (q : Fin n) :
    history (graph f []) ((before (plan n pad read) xs++[.inl (inserted (.select false q))])++[.inl (inserted (.select true q))])=graph f (full xs q) := by
  have eq := complete_ops (pad:=pad) read xs q
  unfold history; rw [acts f (full xs q)]
  apply congrArg (Merged (graph (pad:=pad) f []))
  simpa [operations,plan,List.filterMap_append,List.append_assoc] using eq

theorem valid_exact (hn : 1≤n) (hp : 0<pad) : Valid (plan n pad (rc n)) (legal (3*span n)) spec := by
  constructor
  · exact prefix_valid _ hn
  · intro f xs q nd
    change decide (diameter (history (graph f []) _) = some (threshold n+1)) = _
    rw [query_state,value_eq (answer_diameter f xs q hn hp)]
    apply decide_eq_decide.mpr
    simp only [Option.some.injEq]; unfold threshold val
    by_cases hit : ∃x∈xs,x∈f q
    · obtain ⟨j,t,s⟩ := hit
      simp [show ∃x∈xs,x∈f q from ⟨j,t,s⟩,show ¬∀x∈xs,x∉f q from fun all => all _ t s]
    · have no : ∀x∈xs,x∉f q := fun j h s => hit ⟨j,h,s⟩
      simp [hit,no]
      exact no

theorem valid_test (hn : 1≤n) (hp : 0<pad) : Valid (plan n pad rb) (legal (3*span n)) (testSpec (threshold n)) := by
  constructor
  · exact prefix_valid _ hn
  · intro f xs q nd
    change (!decide (∃ d,Diameter.HasDiameter (sym (history (graph f []) _)) d ∧ d≤threshold n)) = _
    rw [query_state,←decide_not]; apply decide_eq_decide.mpr
    have r := answer_diameter f xs q hn hp
    have relation : (∃ d,Diameter.HasDiameter (sym (graph (pad:=pad) f (full xs q))) d ∧ d≤threshold n) ↔ 2*span n+val f xs q+1≤threshold n :=
      ⟨fun ⟨d,h,le⟩ => diameter_unique h r ▸ le,fun le => ⟨_,r,le⟩⟩
    rw [relation]; unfold threshold val
    by_cases hit : ∃x∈xs,x∈f q
    · obtain ⟨j,t,s⟩ := hit
      simp [show ∃x∈xs,x∈f q from ⟨j,t,s⟩,show ¬∀x∈xs,x∉f q from fun all => all _ t s]
      omega
    · have no : ∀x∈xs,x∉f q := fun j h s => hit ⟨j,h,s⟩
      simp [hit,no]
      exact no

def size (n : ℕ) := 8*(dim n)^2+4*(dim n)+2
def padding (N : ℕ) := N-size (ShortTransfer.stringSize N)
theorem lower (lo hi : ℝ) (lp : 0<lo) (lh : lo≤hi) :
    ∃ c : ℝ,0<c ∧ ∀ᶠ N : ℕ in atTop,let n := ShortTransfer.stringSize N
      let p := padding N
      Fintype.card (W n p)=N ∧ Bound lo hi c N true (legal (Z:=W n p) (3*span n)) spec ∧
      Bound lo hi c N true (legal (Z:=W n p) (3*span n)) (testSpec (threshold n)) := by
  obtain ⟨c,cp,event⟩ := ShortTransfer.eventual lo hi lp lh
  obtain ⟨k,b⟩ := eventually_atTop.mp event; refine ⟨c,cp,?_⟩
  filter_upwards [ShortTransfer.string_geometry (max k 40)] with N g
  let n := ShortTransfer.stringSize N; let p := padding N
  obtain ⟨kn,n1,fit,low,high⟩ := g
  have h : 40≤n := (le_max_right ..).trans kn
  have spare : size n<N := by
    change 9*(n*n)≤N at fit
    dsimp [size,dim]; nlinarith [Nat.mul_le_mul_left n h]
  have count : Fintype.card (W n p)=N := by
    change Fintype.card (((Bool×Menu (dim n))⊕Bool)⊕Fin p)=_
    simp only [Fintype.card_sum,Fintype.card_fin,Fintype.card_bool,paired_size]
    exact Nat.add_sub_of_le spare.le
  have can : 0<p := Nat.sub_pos_of_lt spare
  refine ⟨count,?_,?_⟩
  · exact b n ((le_max_left ..).trans kn) N low high (plan n p (rc n)) true (valid_exact n1 can)
      (by simp [plan]) (by simp [plan]) (by simp)
  · exact b n ((le_max_left ..).trans kn) N low high (plan n p rb) true (valid_test n1 can)
      (by simp [plan]) (by simp [plan]) (by simp)
end
end DisjointnessDraft.Applications.DiameterGraph
