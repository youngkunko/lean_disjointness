import DisjointnessDraft.Applications.GraphHistories

namespace DisjointnessDraft.Applications.GraphCosts
open DisjointnessFoundations CellProbe Graphs Reachability Components GraphHistories Transfer.Compiler MeasureTheory Filter Real
open scoped ENNReal
noncomputable section
open Classical
variable {n p : ℕ}
abbrev E (n p : ℕ) := Edge (Vertex n p)

def value (spec : List (E n p) → Q → A) (_ : Unit) (h : List (Instr (E n p) Q)) := spec (operations h)

structure Entry (n p : ℕ) (Q A : Type) where
  kind : Kind
  ask : Fin n → Q
  decode : List A → Bool
  spec : List (E n p) → Q → A
  exact : ∀ F xs q,decode [spec (edges F xs++[select kind q]) (ask q)] = answer F xs q

def plan (entry : Entry n p Q A) : Schedule n (Family n) (E n p) Q A := schedule entry.kind entry.ask (fun _ => entry.decode)

theorem valid (t : Entry n p Q A) :
    Valid (plan t) (initLegal (frame n p Q) legalGraph) (initSpec (frame n p Q) (value t.spec)) := by
  constructor
  · intro f xs q hnd h pre; exact legal_prefix f xs hnd t.kind q t.ask _ h pre
  · intro F xs q _
    have ev := ops_full (p:=p) F xs t.kind q t.ask (fun _ => t.decode)
    have eq : operations ((frame n p Q).steps F++(before (plan t) xs++[.inl (select t.kind q)]))=edges F xs++[select t.kind q] := by
      simpa only [plan,schedule,List.append_assoc,operations,List.filterMap_append,List.filterMap_cons,Sum.getLeft?_inl,
        Sum.getLeft?_inr,List.filterMap_nil,Option.toList_some,Option.toList_none,List.cons_append,List.nil_append,List.singleton_append] using ev
    change t.decode [t.spec (operations ((frame n p Q).steps F++(before (plan t) xs++[.inl (select t.kind q)]))) (t.ask q)]=_
    rw [eq]; exact t.exact F xs q

/-- The true fixed-endpoint query has the same probe model for every legal
graph. The reduction preloads the incidence edges into an initially empty target. -/
theorem lower (lo hi : ℝ) (lp : 0<lo) (lh : lo≤hi) :
    ∃ c : ℝ,0<c ∧ ∀ᶠ N : ℕ in atTop,let n := N/4
    Fintype.card (Vertex n (pad N))=N ∧ ∀ w tu : ℕ,1≤tu → lo*logb 2 N≤w → (w:ℝ)≤hi*logb 2 N →
    ∀ (Q A Ω : Type) [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (entry : Entry n (pad N) Q A) (D : Target Unit (E n (pad N)) Q A w Ω) (tq : ℝ),1≤tq →
    Guarantees μ D legalGraph (value entry.spec) tu tq →
      c*(Tradeoff.ratio N w tu)^2≤tq+tu ∧ c*(FixedFamilySizes.logRatio N)^2≤max (tu:ℝ) tq := by
  obtain ⟨c,cp,lim⟩ := Transfer.Compiler.lower lo hi lp lh 1 2 3 (by norm_num)
  obtain ⟨L,H⟩ := eventually_atTop.mp lim
  refine ⟨c,cp,?_⟩; filter_upwards [eventually_ge_atTop (4*L+16)] with N big
  intro n
  have large : L≤n := by dsimp [n]; omega
  have n4 : 4≤n := by dsimp [n]; omega
  have cube : N≤n^3 := by
    have nf : N≤4*n+3 := by dsimp [n]; omega
    nlinarith only [nf,Nat.mul_le_mul_right n n4,Nat.mul_le_mul_right (n^2) n4,n4]
  have logs := ApplicationSizes.log_range (by omega : 2≤n) (Nat.div_le_self N 4) cube
  refine ⟨cardinality (by omega),?_⟩
  intro w tu tp wl wh Q A Ω _ μ _ entry D tq qp h
  let I := frame n (pad N) Q
  have g := init_guarantees μ D I h
  exact H n large N w tu (Nat.div_le_self N 4) logs.2 tp wl wh _ _ _ _ Ω μ (plan entry) (initialized D I) _ _ true tq qp g (valid entry)
    (by intro j; rfl) (by intro q; rfl) (by simp)

end
end DisjointnessDraft.Applications.GraphCosts
