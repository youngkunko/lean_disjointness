import DisjointnessDraft.Applications.DistanceLower

/-! Count the reachable vertices other than the source. An extra edge to
the sink and a second query remove the need to store the row cardinality. -/
namespace DisjointnessDraft.Applications.ReachCount
open Graphs GraphHistories GraphCosts Reachability Transfer.Compiler MeasureTheory Filter Real DisjointnessFoundations
open Classical
noncomputable section
variable {n p : ℕ}
abbrev start (n p : ℕ) : Vertex n p := .inl .source
def extraArc (n p : ℕ) : Edge (Vertex n p) := (start n p,target n p)
def nodes {W} [Fintype W] (G : W→W→Prop) (s : W) := Finset.univ.filter (fun v => v≠s ∧ reach G s v)

theorem add_sink {W : Type} [Fintype W] (E : List (Edge W)) (s t : W) (ne : t≠s)
    (sink : ∀b,¬Raw E t b) :
    nodes (Raw (E++[(s,t)])) s = insert t (nodes (Raw E) s) := by
  ext b; simp only [nodes,Finset.mem_filter,Finset.mem_univ,true_and,Finset.mem_insert]
  constructor
  · rintro ⟨diff,k,w⟩
    have closed := w.closed (fun z => z=t ∨ reach (Raw E) s z) (by
      intro u v prev edge
      rcases List.mem_append.mp edge with old|fresh
      · rcases prev with rfl|⟨d,path⟩
        · exact (sink _ old).elim
        · exact Or.inr ⟨_,Components.walk_join path (.cons old (.nil _))⟩
      · exact Or.inl (congrArg Prod.snd (List.mem_singleton.mp fresh))) (Or.inr ⟨0,.nil _⟩)
    exact closed.imp_right (fun r => ⟨diff,r⟩)
  · rintro (rfl|⟨diff,k,w⟩)
    · exact ⟨ne,1,.cons (List.mem_append_right _ (by simp)) (.nil _)⟩
    · exact ⟨diff,k,w.mono (fun _ _ => List.mem_append_left _)⟩

def firstEdges (f : Family n) (xs : List (Fin n)) (q : Fin n) := edges (pad:=p) f xs++[select .source q]

theorem extra_valid (f : Family n) (xs : List (Fin n)) (nd : xs.Nodup) (q : Fin n) :
    strict (firstEdges (p:=p) f xs q++[extraArc n p]) := by
  let e := extraArc n p
  let es := firstEdges (p:=p) f xs q
  have ok : strict es := path_valid f xs nd q .source
  have a : e∉es := by
    intro bad; rcases List.mem_append.mp bad with reg|s
    · exact (projects f xs reg : False)
    · have eq := congrArg Prod.snd (List.mem_singleton.mp s); cases eq
  have b : e.swap∉es := by
    intro bad; rcases List.mem_append.mp bad with reg|s
    · exact (projects f xs reg : False)
    · have eq := congrArg Prod.fst (List.mem_singleton.mp s); cases eq
  have ne : e.1≠e.2 := by simp [e,extraArc,target]
  refine ⟨List.nodup_append.mpr ⟨ok.1,by simp,by simpa using a⟩,?_⟩
  intro v hv
  rcases List.mem_append.mp hv with h|h
  · refine ⟨(ok.2 _ h).1,?_⟩; intro t
    rcases List.mem_append.mp t with y|y
    · exact (ok.2 _ h).2 y
    · have eq := congrArg Prod.swap (List.mem_singleton.mp y); simp only [Prod.swap_swap] at eq
      exact b (eq ▸ h)
  · obtain rfl := List.mem_singleton.mp h
    refine ⟨ne,fun bad => ?_⟩
    rcases List.mem_append.mp bad with z|z
    · exact b z
    · exact ne (congrArg Prod.snd (List.mem_singleton.mp z))

def decode (rs : List ℕ) := !decide (rs[0]?=rs[1]?)
def plan (n p : ℕ) : Schedule n (Family n) (Edge (Vertex n p)) Unit ℕ :=
  ⟨id,fun j => [arc j],fun q => [.inl (select .source q),.inr (),.inl (extraArc _ _),.inr ()],fun _ => decode⟩
def spec (_ : Unit) (h : List (Instr (Edge (Vertex n p)) Unit)) (_ : Unit) := (nodes (Raw (operations h)) (start n p)).card

theorem card_test {W : Type} (A : Finset W) (v : W) : A.card=(insert v A).card ↔ v∈A := by
  by_cases t : v∈A
  · simp [Finset.insert_eq_of_mem t,t]
  · simp [Finset.card_insert_of_not_mem t,t]

set_option maxHeartbeats 1000000 in
theorem valid : Valid (plan n p) (initLegal (frame n p Unit) legalGraph) (initSpec (frame n p Unit) spec) := by
  have B (xs : List (Fin n)) : before (plan n p) xs=DistanceLower.beforeOps xs := by
    simp [before,plan,DistanceLower.beforeOps,←List.map_eq_flatMap,Function.comp_def]
  constructor
  · intro f xs q nd h pr
    rw [B] at pr
    apply DistanceLower.preLegal _ pr
    rw [←List.append_assoc]
    change strict (operations (((frame n p Unit).steps f++DistanceLower.beforeOps xs)++[.inl (select .source q), .inr (), .inl (extraArc n p),.inr ()]))
    rw [operations,List.filterMap_append,←operations,DistanceLower.dataOps]
    simpa [firstEdges,List.append_assoc] using extra_valid (p:=p) f xs nd q
  · intro f xs q nd
    let es := firstEdges (p:=p) f xs q
    let s := start n p
    let t := target n p
    have sink : ∀ b,¬Raw es t b := by
      intro b h
      rcases List.mem_append.mp h with a|a
      · exact (projects f xs a : False)
      · have eq := congrArg Prod.fst (List.mem_singleton.mp a); cases eq
    have diff : t≠s := by simp [t,s,target]
    have counts := congrArg Finset.card (add_sink es s t diff sink)
    have eq : (nodes (Raw es) s).card = (nodes (Raw (es++[(s,t)])) s).card ↔ GraphCosts.explicit_hit f xs q := by
      rw [counts]
      calc
        _ ↔ t∈nodes (Raw es) s := card_test _ _
        _ ↔ GraphCosts.explicit_hit f xs q := by
          simp only [nodes,Finset.mem_filter,Finset.mem_univ,true_and,diff]
          exact and_iff_right diff |>.trans (select_reaches f xs q)
    let pre := before (plan n p) xs
    let L := (frame n p Unit).steps f
    have data : operations (L++pre)=edges f xs := by rw [show pre=DistanceLower.beforeOps xs from B xs]; exact DistanceLower.dataOps f xs
    have e1 : operations (L++(pre++[.inl (select .source q)]))=es := by rw [←List.append_assoc,operations,List.filterMap_append,←operations,data]; rfl
    have e2 : operations (L++(((pre++[.inl (select .source q)])++[.inr ()])++[.inl (extraArc n p)]))=es++[(s,t)] := by
      rw [←List.append_assoc,←List.append_assoc,operations,List.filterMap_append,List.filterMap_append,←operations,e1]; simp [extraArc,s,t]
    change (!decide (some (spec () (L++(pre++[.inl (select .source q)])) ())=some (spec () (L++(((pre++[.inl (select .source q)])++[.inr ()])++[.inl (extraArc n p)])) ()))) = answer f xs q
    unfold spec; rw [e1,e2]
    apply GraphCosts.decode_hit f xs q; simpa using eq

theorem lower (lo hi : ℝ) (lp : 0<lo) (lh : lo≤hi) :
    ∃ c : ℝ,0<c ∧ ∀ᶠ N : ℕ in atTop,let n := N/4
    Fintype.card (Vertex n (Reachability.pad N))=N ∧ ∀ w tu : ℕ,1≤tu → lo*logb 2 N≤w → (w:ℝ)≤hi*logb 2 N →
    ∀ (Ω : Type) [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (D : Target Unit (Edge (Vertex n (Reachability.pad N))) Unit ℕ w Ω) (tq : ℝ),1≤tq →
    Guarantees μ D legalGraph spec tu tq →
      c*(Tradeoff.ratio N w tu)^2≤tq+tu ∧ c*(FixedFamilySizes.logRatio N)^2≤max (tu:ℝ) tq := by
  obtain ⟨c,cp,lim⟩ := Transfer.Compiler.lower lo hi lp lh 1 4 3 (by norm_num)
  obtain ⟨L,H⟩ := eventually_atTop.mp lim
  refine ⟨c,cp,?_⟩; filter_upwards [eventually_ge_atTop (4*L+16)] with N big
  intro n
  have large : L≤n := by dsimp [n]; omega
  have n4 : 4≤n := by dsimp [n]; omega
  have cube : N≤n^3 := by
    have nf : N≤4*n+3 := by dsimp [n]; omega
    nlinarith only [nf,Nat.mul_le_mul_right n n4,Nat.mul_le_mul_right (n^2) n4,n4]
  have logs := ApplicationSizes.log_range (by omega : 2≤n) (Nat.div_le_self N 4) cube
  refine ⟨Reachability.cardinality (by omega),?_⟩
  intro w tu tp wl wh Ω _ μ _ D tq qp h
  let I := frame n (Reachability.pad N) Unit
  exact H n large N w tu (Nat.div_le_self N 4) logs.2 tp wl wh _ _ _ _ Ω μ (plan n _) (initialized D I) _ _ true tq qp
    (init_guarantees μ D I h) valid (by intro; rfl) (by intro; rfl) (by simp)
end
end DisjointnessDraft.Applications.ReachCount
