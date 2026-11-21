import DisjointnessDraft.Preload
import DisjointnessDraft.Applications.Graphs

/-! Incremental reachability from an empty graph. For each potential
incidence we insert precisely one arc, choosing the queried row or a dummy
row. This makes the number of initialization operations input-independent
and keeps every intermediate graph a depth-two DAG. -/
namespace DisjointnessDraft.Reachability
open DisjointnessFoundations CellProbe Applications.Graphs Preload MeasureTheory
open scoped ENNReal
noncomputable section
open Classical

abbrev Core (n : ℕ) := V (Fin n ⊕ Fin n) (Fin n)
abbrev Vertex (n pad : ℕ) := Core n ⊕ Fin pad
abbrev Edge (v : Type) := v × v

def target (n pad : ℕ) : Vertex n pad := .inl .target

def row (q : Fin n) : Vertex n pad := .inl (.row (.inl q))
def arc (j : Fin n) : Edge (Vertex n pad) := (.inl (.col j),target n pad)

def staticArc (F : Family n) (p : Fin n × Fin n) : Edge (Vertex n pad) :=
  (.inl (.row (if p.2∈F p.1 then .inl p.1 else .inr p.1)),.inl (.col p.2))

def setup (F : Family n) : List (Edge (Vertex n pad)) :=
  (Finset.univ : Finset (Fin n × Fin n)).toList.map (staticArc F)

theorem setup_length (F : Family n) : (setup (pad:=pad) F).length=n*n := by simp [setup]

def translation (n pad : ℕ) : Map n Unit (Edge (Vertex n pad)) (Vertex n pad) :=
  ⟨fun _ => (),setup,n*n,setup_length,arc,row,true⟩

def edges (F : Family n) (xs : List (Fin n)) : List (Edge (Vertex n pad)) := setup F++xs.map arc

def layered {v : Type} (es : List (Edge v)) : Prop :=
  es.Nodup ∧ ∃ level : v → Fin 3, ∀ e∈es,level e.1<level e.2

def depthLabel : Vertex n pad → Fin 3
  | .inl (.col _) => 1
  | .inl .target => 2
  | _ => 0

theorem legal (F : Family n) (xs : List (Fin n)) (nd : xs.Nodup) : layered (edges (pad:=pad) F xs) := by
  have inj : Function.Injective (staticArc (pad:=pad) F) := by
    rintro ⟨a,b⟩ ⟨i,j⟩ eq
    have y := congrArg Prod.snd eq
    have z := congrArg Prod.fst eq
    simp only [staticArc,Sum.inl.injEq,V.col.injEq,V.row.injEq] at y z
    subst j
    split_ifs at z <;> simp_all
  have inc : Function.Injective (arc (n:=n) (pad:=pad)) := by
    intro i j h; simpa [arc] using congrArg Prod.fst h
  constructor
  · apply List.nodup_append.mpr
    refine ⟨Finset.univ.nodup_toList.map inj,nd.map inc,?_⟩
    intro a ha hb
    obtain ⟨p,_,rfl⟩ := List.mem_map.mp ha
    obtain ⟨j,_,eq⟩ := List.mem_map.mp hb
    have h := congrArg Prod.snd eq
    simp [staticArc,arc,target] at h
  · refine ⟨depthLabel,?_⟩
    intro e he
    rcases List.mem_append.mp he with a|b
    · obtain ⟨p,_,rfl⟩ := List.mem_map.mp a; exact (by decide : (0:Fin 3)<1)
    · obtain ⟨j,_,rfl⟩ := List.mem_map.mp b; exact (by decide : (1:Fin 3)<2)

def extRows (F : Family n) : (Fin n ⊕ Fin n) → Fin n → Prop
  | .inl i,j => j∈F i
  | .inr i,j => j∉F i

def strip : Vertex n pad → Core n | .inl v => v | .inr _ => .source

theorem projects (F : Family n) (xs : List (Fin n)) {u v : Vertex n pad} (h : (u,v)∈edges F xs) :
    base (extRows F) (·∈xs) (strip u) (strip v) := by
  rcases List.mem_append.mp h with h|h
  · obtain ⟨⟨i,j⟩,_,e⟩ := List.mem_map.mp h
    obtain ⟨rfl,rfl⟩ := Prod.mk.inj e
    simp only [strip,base]; split <;> assumption
  · obtain ⟨j,hj,e⟩ := List.mem_map.mp h
    obtain ⟨rfl,rfl⟩ := Prod.mk.inj e
    exact hj

theorem walk_map {U W : Type} {G : U → U → Prop} {H : W → W → Prop} (f : U → W)
    (send : ∀ u v,G u v → H (f u) (f v)) {a b d} (p : Walk G a d b) : Walk H (f a) d (f b) := by
  induction p with | nil => exact .nil _ | cons h _ ih => exact .cons (send _ _ h) ih

theorem reachable (F : Family n) (xs : List (Fin n)) (q : Fin n) :
    reach (fun u v => (u,v)∈edges (pad:=pad) F xs) (row q) (target n pad) ↔ ∃ j∈xs, j∈F q := by
  constructor
  · rintro ⟨d,path⟩
    have p := walk_map strip (fun _ _ => projects F xs) path
    obtain ⟨j,hj,mem⟩ := (reach_iff _ _ _).mp ⟨_,p⟩
    exact ⟨j,mem,hj⟩
  · rintro ⟨j,mem,hj⟩
    have first : (row q,.inl (.col j))∈edges (pad:=pad) F xs := by
      apply List.mem_append_left
      apply List.mem_map.mpr
      exact ⟨(q,j),by simp,by simp [staticArc,row,hj]⟩
    have second : arc (pad:=pad) j ∈ edges F xs := List.mem_append_right _ (List.mem_map.mpr ⟨j,mem,rfl⟩)
    exact ⟨2,.cons first (.cons second (.nil _))⟩

/-- These are guarantees of the incremental target itself, on every strict
depth-two insertion history starting empty and with one fixed target vertex. -/
structure OnDAG {v : Type} {w : ℕ} {Ω C : Type} [MeasurableSpace Ω] (μ : Measure Ω)
    (D : DataStructure w Unit (Edge v) v C) (R : RandomTape Ω C) (sink : v) (tu : ℕ) (tq : ℝ) : Prop where
  update : ∀ a (es : List (Edge v)), layered es → SingleSelector.Pays D R tu a () es
  right : ∀ a (es : List (Edge v)) q, layered es →
    (finalRun D R a () es q).map Prod.fst = some (decide (reach (fun u v => (u,v)∈es) q sink))
  measurable : ∀ (es : List (Edge v)) q, layered es → Measurable (fun a => cost (finalRun D R a () es q))
  query : ∀ (es : List (Edge v)) q, layered es → (∫⁻ a,cost (finalRun D R a () es q) ∂μ) ≤ ENNReal.ofReal tq

theorem guarantees {n pad w tu : ℕ} {tq : ℝ} {Ω C : Type} [MeasurableSpace Ω] (μ : Measure Ω)
    (D : DataStructure w Unit (Edge (Vertex n pad)) (Vertex n pad) C) (R : RandomTape Ω C)
    (h : OnDAG μ D R (target n pad) tu tq) : Guarantees (translation n pad) D R μ tu tq := by
  refine ⟨fun a f xs nd => h.update a _ (legal f xs nd),?_,
    fun f xs q nd => h.measurable _ _ (legal f xs nd),fun f xs q nd => h.query _ _ (legal f xs nd)⟩
  intro a f xs q nd
  change (finalRun D R a () (edges f xs) (row q)).map Prod.fst = _
  rw [h.right _ _ _ (legal f xs nd),reachable]
  by_cases meet : ∃ j∈xs,j∈f q
  · obtain ⟨j,hx,hj⟩ := meet
    have yes : ∃ j∈xs,j∈f q := ⟨j,hx,hj⟩
    have no : ¬∀ x∈xs,x∉f q := fun h => h j hx hj
    simp [translation,InputReduction.out,answer,yes,no]
  · have no : ∀ x∈xs,x∉f q := fun x hx hj => meet ⟨x,hx,hj⟩
    simp [translation,InputReduction.out,answer,meet,no]; exact no

end
end DisjointnessDraft.Reachability
