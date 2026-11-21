import DisjointnessDraft.Directed
import DisjointnessDraft.Transfer.Direct

/-! Reversing every inserted arc transfers the depth-two DAG result to
reachability from one fixed source, including initialization from no edges. -/
namespace DisjointnessDraft.Reachability
open DisjointnessFoundations CellProbe Applications.Graphs Preload Transfer MeasureTheory Filter Real
open scoped ENNReal
noncomputable section
open Classical

variable {U : Type}
theorem walk_snoc {G : U → U → Prop} {a b c : U} {d : ℕ} (p : Walk G a d b) (bc : G b c) :
    Walk G a (d+1) c := by
  induction p with | nil => exact .cons bc (.nil _) | cons e _ ih => exact .cons e (ih bc)

theorem walk_rev {G : U → U → Prop} {a b : U} {d : ℕ} (p : Walk G a d b) :
    Walk (fun y x => G x y) b d a := by
  induction p with | nil => exact .nil _ | cons e _ ih => exact walk_snoc ih e

def reverseMap (n pad : ℕ) : Map n Unit (Edge (Vertex n pad)) (Vertex n pad) :=
  ⟨fun _ => (),fun F => (setup F).map Prod.swap,n*n,fun F => by simp [setup_length],
    fun j => (arc j).swap,row,true⟩

def reverseProblem (source : U) : Problem Unit (Edge U) U where
  legal _ es := layered es
  answer _ es q := decide (reach (fun u v => (u,v)∈es) source q)

theorem reverse_legal {es : List (Edge U)} (h : layered es) : layered (es.map Prod.swap) := by
  obtain ⟨nd,L,up⟩ := h
  refine ⟨nd.map (Equiv.prodComm U U).injective,fun v => Fin.rev (L v),?_⟩
  intro e he; obtain ⟨⟨x,y⟩,hx,rfl⟩ := List.mem_map.mp he
  simpa using up (x,y) hx

theorem reverse_reach {es : List (Edge U)} {x y : U} :
    reach (fun a b => (a,b)∈es.map Prod.swap) y x ↔ reach (fun a b => (a,b)∈es) x y := by
  have ed (a b : U) : (a,b)∈es.map Prod.swap ↔ (b,a)∈es := by
    constructor
    · intro h; obtain ⟨⟨j,k⟩,hj,ev⟩ := List.mem_map.mp h; cases ev; exact hj
    · intro h; exact List.mem_map.mpr ⟨(b,a),h,rfl⟩
  constructor <;> rintro ⟨k,p⟩
  · exact ⟨k,walk_map id (fun a b h => (ed b a).mp h) (walk_rev p)⟩
  · exact ⟨k,walk_map id (fun a b h => (ed a b).mpr h) (walk_rev p)⟩

theorem reverse_valid (n pad : ℕ) : Direct (reverseProblem (target n pad)) (reverseMap n pad) := by
  have hist (F : Family n) (xs : List (Fin n)) :
      (reverseMap n pad).setup F++xs.map (reverseMap n pad).insert = (edges F xs).map Prod.swap := by
    simp [reverseMap,edges,List.map_map,Function.comp_def]
  constructor
  · intro f xs nd; rw [hist]; exact reverse_legal (legal f xs nd)
  · intro f xs q _
    rw [hist]
    change decide (reach _ _ _)=InputReduction.out true (DisjointnessDraft.answer f xs q)
    rw [reverse_reach]
    change decide (reach (fun a b => (a,b)∈edges f xs) (row q) (target n pad))=_
    rw [reachable]
    by_cases meet : ∃ j∈xs,j∈f q
    · obtain ⟨j,hx,hj⟩ := meet
      have yes : ∃ j∈xs,j∈f q := ⟨j,hx,hj⟩
      have no : ¬∀ x∈xs,x∉f q := fun h => h j hx hj
      simp [InputReduction.out,answer,yes,no]
    · have no : ∀ x∈xs,x∉f q := fun x hx hj => meet ⟨x,hx,hj⟩
      (simp [InputReduction.out,answer,meet,no]; exact no)

theorem fixed_source (lo hi : ℝ) (lp : 0<lo) (lh : lo≤hi) :
    ∃ c : ℝ,0<c ∧ ∀ᶠ N : ℕ in atTop,
    let n := N/4
    let V' := Vertex n (pad N)
    Fintype.card V'=N ∧ ∀ w tu : ℕ,1≤tu → lo*logb 2 N≤w → (w:ℝ)≤hi*logb 2 N →
    ∀ (Ω C : Type) [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
      (D : DataStructure w Unit (Edge V') V' C) (R : RandomTape Ω C) (tq : ℝ),1≤tq →
      Target μ (reverseProblem (target n (pad N))) D R tu tq →
      c*(Tradeoff.ratio N w tu)^2≤tq ∧ c*(FixedFamilySizes.logRatio N)^2≤max (tu:ℝ) tq := by
  obtain ⟨c,cp,lim⟩ := direct_bounds lo hi lp lh 3 (by norm_num)
  obtain ⟨L,H⟩ := eventually_atTop.mp lim
  refine ⟨c,cp,?_⟩; filter_upwards [eventually_ge_atTop (4*L+16)] with N big
  intro n V'
  have large : L≤n := by dsimp [n]; omega
  have n4 : 4≤n := by dsimp [n]; omega
  have cube : N≤n^3 := by
    have nf : N≤4*n+3 := by dsimp [n]; omega
    nlinarith only [nf,Nat.mul_le_mul_right n n4,Nat.mul_le_mul_right (n^2) n4,n4]
  have logs := ApplicationSizes.log_range (by omega : 2≤n) (Nat.div_le_self N 4) cube
  refine ⟨cardinality (by omega),?_⟩
  intro w tu tp wl wh Ω C _ μ _ D R tq qp h
  exact H n large N w tu (Nat.div_le_self N 4) logs.2 tp wl wh _ _ _ Ω C μ _ (reverseMap n (pad N)) D R tq qp (reverse_valid ..) h

end
end DisjointnessDraft.Reachability
