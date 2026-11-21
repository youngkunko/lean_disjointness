import DisjointnessDraft.Reverse

namespace DisjointnessDraft.Applications.SubgraphCosts
open DisjointnessFoundations CellProbe Transfer Graphs Reachability MeasureTheory Filter Real
noncomputable section
open Classical

structure Initial (W : Type) where
  adjacent : W → W → Prop
  symmetric : Symmetric adjacent
  active : W → Prop

def isOn (f : Initial W) (xs : List W) (v : W) := f.active v ∨ v∈xs

def onPath (init : Initial W) (xs : List W) (a b : W) :=
  init.adjacent a b ∧ (init.active a ∨ a∈xs) ∧ (init.active b ∨ b∈xs)

def problem (W : Type) : Problem (Initial W) W (W×W) where
  legal f xs := xs.Nodup ∧ ∀ a∈xs,¬f.active a
  answer f xs q := decide (isOn f xs q.1 ∧ isOn f xs q.2 ∧ reach (onPath f xs) q.1 q.2)

/-- A length-zero walk belongs to the induced graph exactly when its vertex is on. -/
theorem self_query (f : Initial W) (xs : List W) (v : W) :
    (problem W).answer f xs (v,v) = decide (isOn f xs v) := by
  have path : reach (onPath f xs) v v := ⟨0, .nil v⟩
  simp [problem, path]

def init (f : Family n) : Initial (Vertex n p) where
  adjacent
    | .inl a,.inl b => sym (base (extRows f) (fun _ => True)) a b
    | _,_ => False
  symmetric := by
    intro a b h; cases a <;> cases b <;> try contradiction
    exact Or.symm h
  active
    | .inl (.row _) | .inl .target => True
    | _ => False

def col (j : Fin n) : Vertex n p := .inl (.col j)
def map (n p : ℕ) : Preload.Map n (Initial (Vertex n p)) (Vertex n p) (Vertex n p × Vertex n p) :=
  ⟨init,fun _ => [],0,fun _ => rfl,col,fun q => (row q,target n p),true⟩

theorem project (f : Family n) (xs : List (Fin n)) (a b : Vertex n p)
    (e : onPath (init f) (xs.map col) a b) : enabled (extRows f) (·∈xs) (strip a) (strip b) := by
  have cact (j : Fin n) : ((init f).active (col (p:=p) j) ∨ col (p:=p) j∈xs.map col) ↔ j∈xs := by
    simp [col,init,List.mem_map]
  rcases e with ⟨adj,oa,ob⟩
  cases a with
  | inr z => cases b <;> contradiction
  | inl a =>
    cases b with
    | inr z => contradiction
    | inl b =>
      cases a <;> cases b <;> simp only [init,sym,base] at adj <;> simp only [strip,enabled] <;>
        first | tauto | exact (cact _).mp oa | exact (cact _).mp ob | exact ⟨adj.resolve_right id,(cact _).mp ob⟩ | exact ⟨adj.resolve_left id,(cact _).mp oa⟩

theorem connection (f : Family n) (xs : List (Fin n)) (q : Fin n) :
    reach (onPath (init f) (xs.map col)) (row q) (target n p) ↔ ∃ j∈xs,j∈f q := by
  constructor
  · rintro ⟨l,path⟩
    have h := walk_map strip (project f xs) path
    obtain ⟨j,hj,hx⟩ := (subgraph_iff (extRows f) (·∈xs) (.inl q)).mp ⟨l,h⟩
    exact ⟨j,hx,hj⟩
  · rintro ⟨j,hx,hj⟩
    have on : col (p:=p) j∈xs.map col := List.mem_map.mpr ⟨j,hx,rfl⟩
    exact ⟨2,.cons (show onPath (init f) (xs.map col) (row q) (col j) from ⟨Or.inl hj,Or.inl trivial,Or.inr on⟩)
      (.cons (show onPath (init f) (xs.map col) (col j) (target n p) from ⟨Or.inl trivial,Or.inr on,Or.inl trivial⟩) (.nil _))⟩

theorem valid (n p : ℕ) : Direct (problem _) (map n p) := by
  constructor
  · intro f xs nd
    refine ⟨nd.map (fun a b (h : col (p:=p) a=col b) => by simpa [col] using h),?_⟩
    intro a ha; change a∈xs.map col at ha
    obtain ⟨j,_,rfl⟩ := List.mem_map.mp ha; exact id
  · intro f xs q _
    have rowOn : isOn (init (p:=p) f) (xs.map col) (row q) := Or.inl trivial
    have targetOn : isOn (init f) (xs.map col) (target n p) := Or.inl trivial
    change decide (isOn (init f) (xs.map col) (row q) ∧ isOn (init f) (xs.map col) (target n p) ∧
      reach (onPath (init f) (xs.map col)) (row q) (target n p))=InputReduction.out true (answer f xs q)
    simp only [rowOn,targetOn,true_and,connection]
    by_cases hit : ∃ j∈xs,j∈f q
    · have no : ¬∀ j∈xs,j∉f q := fun h => hit.elim (fun j hj => h j hj.1 hj.2)
      simp [InputReduction.out,answer,hit,no]
    · have all : ∀ j∈xs,j∉f q := fun j h x => hit ⟨j,h,x⟩
      (simp [InputReduction.out,answer,hit,all]; exact all)

theorem lower (lo hi : ℝ) (lp : 0<lo) (lh : lo≤hi) :
    ∃ c : ℝ,0<c ∧ ∀ᶠ N : ℕ in atTop,
    let W := Vertex (N/4) (pad N)
    Fintype.card W=N ∧ ∀ w tu : ℕ,1≤tu → lo*logb 2 N≤w → (w:ℝ)≤hi*logb 2 N →
    ∀ (Ω C : Type) [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
      (D : DataStructure w (Initial W) W (W×W) C) (R : RandomTape Ω C) (tq : ℝ),1≤tq →
      Target μ (problem W) D R tu tq →
      c*(Tradeoff.ratio N w tu)^2≤tq ∧ c*(FixedFamilySizes.logRatio N)^2≤max (tu:ℝ) tq := by
  obtain ⟨c,cp,lim⟩ := direct_bounds lo hi lp lh 3 (by norm_num)
  obtain ⟨L,H⟩ := eventually_atTop.mp lim
  refine ⟨c,cp,?_⟩; filter_upwards [eventually_ge_atTop (4*L+16)] with N big
  intro W
  let n := N/4
  have large : L≤n := by dsimp [n]; omega
  have n4 : 4≤n := by dsimp [n]; omega
  have cube : N≤n^3 := by
    have nf : N≤4*n+3 := by dsimp [n]; omega
    nlinarith only [nf,Nat.mul_le_mul_right n n4,Nat.mul_le_mul_right (n^2) n4,n4]
  have logs := ApplicationSizes.log_range (by omega : 2≤n) (Nat.div_le_self N 4) cube
  refine ⟨cardinality (by omega),?_⟩
  intro w tu tp wl wh Ω C _ μ _ D R tq qp h
  exact H n large N w tu (Nat.div_le_self N 4) logs.2 tp wl wh _ _ _ Ω C μ _ (map n (pad N)) D R tq qp (valid ..) h

end
end DisjointnessDraft.Applications.SubgraphCosts
