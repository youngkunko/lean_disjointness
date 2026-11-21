import DisjointnessDraft.Applications.Distances
import DisjointnessDraft.Applications.MarkedLower

/-! Ordinary one-sided numeric reports, including infinity on disconnected
pairs. Reports can vary with the master tape and the preceding queries. -/
namespace DisjointnessDraft.Applications.DistanceLower
open DisjointnessFoundations Graphs GraphVariants GraphHistories Reachability Transfer.Compiler MeasureTheory Filter Real
open scoped ENNReal
noncomputable section
open Classical
variable {n p : ℕ}

def Bound (lo hi c : ℝ) (N : ℕ) (sel : Bool) {F U Q : Type}
    (legal : F → List (Instr U Q) → Prop) (rel : F → List (Instr U Q) → Q → ℝ≥0∞ → Prop) :=
  ∀ (w tu : ℕ) (tq : ℝ), 1≤tu → 1≤tq → lo*logb 2 N≤w → (w:ℝ)≤hi*logb 2 N →
  ∀ (Ω : Type) [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (D : Target F U Q ℝ≥0∞ w Ω), RelGuarantees μ D legal rel tu tq →
    c*(Tradeoff.ratio N w tu)^2≤Transfer.charge sel tu tq ∧ c*(FixedFamilySizes.logRatio N)^2≤max (tu:ℝ) tq

def beforeOps (xs : List (Fin n)) : List (Instr (Edge (Vertex n p)) Q) := xs.map (Sum.inl ∘ arc)
theorem dataOps (F : Family n) (xs : List (Fin n)) :
    operations ((frame n p Q).steps F++beforeOps xs)=edges F xs := by
  simp [operations,frame,edges,beforeOps,List.filterMap_append,List.filterMap_map,Function.comp_def]

theorem preLegal {F : Family n} {xs : List (Fin n)} {tail : List (Instr (Edge (Vertex n p)) Q)}
    (ok : strict (operations ((frame n p Q).steps F++(beforeOps xs++tail)))) {h} (pr : h <+: beforeOps xs++tail) :
    initLegal (frame n p Q) legalGraph F h := by
  apply prefix_strict _ ok
  obtain ⟨r,e⟩ := pr
  refine ⟨operations r,?_⟩
  rw [←e]; simp [operations,List.filterMap_append,List.append_assoc]

def numeric {W Q} (a : ℝ≥0∞) (pair : Q → W × W) (_ : Unit) (h : List (Instr (Edge W) Q)) (q : Q) :=
  Distances.within a (Distances.distance (sym (Raw (operations h))) (pair q).1 (pair q).2)

def queryPair (q : Vertex n p) := (target n p,q)
def fixedPair (_ : Unit) := ((.inl .source : Vertex n p),target n p)
def decode (threshold : ℕ) (rs : List ℝ≥0∞) := !decide (rs.head!<(threshold:ℝ≥0∞))

def single (n p : ℕ) : Schedule n (Family n) (Edge (Vertex n p)) (Vertex n p) ℝ≥0∞ :=
  ⟨id,fun j => [arc j],fun q => [.inr (row q)],fun _ => decode 4⟩
def fixed (n p : ℕ) : Schedule n (Family n) (Edge (Vertex n p)) Unit ℝ≥0∞ :=
  schedule .source (fun _ => ()) (fun _ => decode 5)

theorem valid_single {a : ℝ≥0∞} (near : a*2<4) :
    RelValid (single n p) (initLegal (frame n p _) legalGraph)
      (fun f h => numeric a queryPair () ((frame n p _).steps f++h)) := by
  have B (xs : List (Fin n)) : before (single n p) xs=beforeOps xs := by simp [before,single,beforeOps,←List.map_eq_flatMap,Function.comp_def]
  constructor
  · intro f xs q nd h pr
    rw [B] at pr
    apply preLegal _ pr
    change strict (operations ((frame n p _).steps f++(beforeOps xs++[.inr (row q)])))
    rw [←List.append_assoc]
    simp only [operations,List.filterMap_append,List.filterMap_cons,Sum.getLeft?_inr,List.filterMap_nil,Option.toList_none,List.nil_append,List.append_nil]
    have e := dataOps (Q:=Vertex n p) (p:=p) f xs
    unfold operations at e; rw [List.filterMap_append] at e; rw [e]
    exact prefix_strict ⟨_,rfl⟩ (path_valid (p:=p) f xs nd q .source)
  · intro f xs q _ rs ok
    cases rs with
    | nil => contradiction
    | cons v rs =>
      obtain ⟨h,h'⟩ := ok; change rs=[] at h'; subst rs
      change Distances.within a (Distances.distance _ _ _) v at h
      rw [B] at h
      change Distances.within a (Distances.distance (sym (Raw (operations ((frame n p _).steps f++beforeOps xs)))) (target n p) (row q)) v at h
      rw [dataOps,Distances.symmetric_distance _ (target n p) (row q)] at h
      exact GraphCosts.decode_hit f xs q _ (Distances.immediate f xs q near h)

theorem valid_fixed {a : ℝ≥0∞} (near : a*3<5) :
    RelValid (fixed n p) (initLegal (frame n p _) legalGraph)
      (fun f h => numeric a fixedPair () ((frame n p _).steps f++h)) := by
  constructor
  · intro f xs q nd h pr; exact legal_prefix f xs nd .source q (fun _ => ()) _ h pr
  · intro f xs q _ rs ok
    cases rs with
    | nil => contradiction
    | cons v rs =>
      obtain ⟨h,h'⟩ := ok; change rs=[] at h'; subst rs
      have B : before (fixed n p) xs=beforeOps xs := by simp [fixed,schedule,before,beforeOps,←List.map_eq_flatMap,Function.comp_def]
      change Distances.within a (Distances.distance (sym (Raw (operations ((frame n p _).steps f++(before (fixed n p) xs++[.inl (select .source q)]))))) _ _) v at h
      rw [B,←List.append_assoc] at h
      have eq : operations (((frame n p Unit).steps f++ beforeOps xs)++[.inl (select .source q)])=edges f xs++[select .source q] := by
        rw [operations,List.filterMap_append,←operations,dataOps]; rfl
      rw [eq] at h
      exact GraphCosts.decode_hit f xs q _ (Distances.selected f xs q near h)

def markLegal (F : MarkedLower.Input W) (h : List (Instr W W)) :=
  MarkedLower.good F ∧ (operations h).Nodup ∧ F.initial∉operations h

def markDist (F : MarkedLower.Input W) (xs : List W) (q : W) : ℝ≥0∞ :=
  if ex : ∃ d,∃ v,(v=F.initial ∨ v∈xs) ∧ Walk F.edges q d v then (Nat.find ex:ℕ) else ⊤
def markRel (a : ℝ≥0∞) (f : MarkedLower.Input W) (h : List (Instr W W)) (q : W) :=
  Distances.within a (markDist f (operations h) q)
def mark (n p : ℕ) : Schedule n (MarkedLower.Input (MarkedLower.Vertex n p)) (MarkedLower.Vertex n p) (MarkedLower.Vertex n p) ℝ≥0∞ :=
  ⟨MarkedLower.inp,fun j => [MarkedLower.put j],fun q => [.inr (MarkedLower.ask q)],fun _ => decode 3⟩

theorem markDist_eq (F : MarkedLower.Input W) (xs : List W) (q : W) (d : ℕ)
    (att : ∃v,(v=F.initial ∨ v∈xs) ∧ Walk F.edges q d v)
    (minimal : ∀ v,(v=F.initial ∨ v∈xs) → ∀ k,Walk F.edges q k v → d≤k) :
    markDist F xs q=(d:ℝ≥0∞) := by
  unfold markDist; split
  · rename_i ex; congr 1; apply le_antisymm (Nat.find_min' ex att)
    obtain ⟨v,m,path⟩ := Nat.find_spec ex; exact minimal v m _ path
  · rename_i no; exact (no ⟨d,att⟩).elim

theorem hard_mark (f : Family n) (xs : List (Fin n)) (q : Fin n) :
    markDist (MarkedLower.inp (pad:=p) f) (xs.map MarkedLower.put) (MarkedLower.ask q)=
      (if GraphCosts.explicit_hit f xs q then 1 else 3) := by
  obtain ⟨hit,bound⟩ := MarkedLower.hard_distance (pad:=p) f xs q
  have H := markDist_eq (MarkedLower.inp (pad:=p) f) (xs.map MarkedLower.put) (MarkedLower.ask q) _ hit bound
  rw [H]
  change ((if GraphCosts.explicit_hit f xs q then 1 else 3 : ℕ):ℝ≥0∞)=_
  split <;> norm_num

theorem valid_mark {a : ℝ≥0∞} (near : a<3) :
    RelValid (mark n p) markLegal (markRel a) := by
  have B (xs : List (Fin n)) : before (mark n p) xs=xs.map (Sum.inl ∘ MarkedLower.put) := by simp [before,mark,←List.map_eq_flatMap,Function.comp_def]
  have E (xs : List (Fin n)) : operations (before (mark n p) xs)=xs.map MarkedLower.put := by
    rw [B]; simp [operations,List.filterMap_map,Function.comp_def]
  constructor
  · intro f xs q nd h pr
    have ep : operations h <+: xs.map (MarkedLower.put (pad:=p)) := by
      obtain ⟨r,e⟩ := pr
      have t : operations (h++r)=operations (before (mark n p) xs) := by rw [e]; simp [mark,operations,List.filterMap_append]
      rw [E] at t; exact ⟨operations r,by simpa only [operations,List.filterMap_append] using t⟩
    obtain ⟨g,nd',no⟩ := (MarkedLower.proof n p).legal f xs nd
    exact ⟨g,ep.sublist.nodup nd',fun bad => no (ep.subset bad)⟩
  · intro f xs q _ rs ok
    cases rs with
    | nil => contradiction
    | cons v rs =>
      obtain ⟨h,z⟩ := ok; change rs=[] at z; subst rs
      change Distances.within a (markDist (MarkedLower.inp f) (operations (before (mark n p) xs)) (MarkedLower.ask q)) v at h
      rw [E,hard_mark] at h
      apply GraphCosts.decode_hit f xs q
      by_cases hit : GraphCosts.explicit_hit f xs q
      · simp [hit,Distances.within] at h; exact iff_of_true (lt_of_le_of_lt h.2 near) hit
      · rw [if_neg hit] at h; exact iff_of_false (not_lt_of_ge h.1) hit

theorem factor_two {a : ℝ≥0∞} : a*2<4 ↔ a<2 := by
  have h := ENNReal.lt_div_iff_mul_lt (a:=4) (b:=2) (c:=a) (Or.inl (by norm_num)) (Or.inl (by norm_num))
  have v : (4:ℝ≥0∞)/2=2 := by
    rw [show (4:ℝ≥0∞)=2*2 by norm_num,ENNReal.mul_div_cancel_right (by norm_num) (by norm_num)]
  rw [v] at h; exact h.symm

theorem factor_five_thirds {a : ℝ≥0∞} : a*3<5 ↔ a<5/3 :=
  (ENNReal.lt_div_iff_mul_lt (Or.inl (by norm_num)) (Or.inl (by norm_num))).symm

/-- The fixed vertex of an undirected pair can be supplied as either endpoint.
The three bounds apply on every sufficiently large vertex count. -/
theorem lower (lo hi : ℝ) (lp : 0<lo) (lh : lo≤hi) :
    ∃ c : ℝ,0<c ∧ ∀ᶠ N : ℕ in atTop, let n := N/4
      Fintype.card (Vertex n (Reachability.pad N))=N ∧ Fintype.card (MarkedLower.Vertex n (MarkedLower.pad N))=N ∧
      (∀ a : ℝ≥0∞, a*2<4 → Bound lo hi c N false legalGraph (numeric a (@queryPair n (Reachability.pad N)))) ∧
      (∀ a : ℝ≥0∞, a*3<5 → Bound lo hi c N true legalGraph (numeric a (@fixedPair n (Reachability.pad N)))) ∧
      (∀ a : ℝ≥0∞, a<3 → Bound lo hi c N false markLegal (@markRel (MarkedLower.Vertex n (MarkedLower.pad N)) a)) := by
  obtain ⟨c,cp,l⟩ := rel_lower lo hi lp lh 1 2 3 (by norm_num)
  obtain ⟨k,b⟩ := eventually_atTop.mp l
  refine ⟨c,cp,?_⟩
  filter_upwards [eventually_ge_atTop (4*k+20)] with N big
  intro n
  have nk : k≤n := by dsimp [n]; omega
  have n4 : 4≤n := by dsimp [n]; omega
  have top : N≤n^3 := by
    have nf : N≤4*n+3 := by dsimp [n]; omega
    nlinarith only [nf,Nat.mul_le_mul_right n n4,Nat.mul_le_mul_right (n^2) n4,n4]
  have nN : n≤N := Nat.div_le_self _ _
  have logs := (ApplicationSizes.log_range (by omega : 2≤n) nN top).2
  refine ⟨Reachability.cardinality (by omega),MarkedLower.cardinality _ (by omega),?_,?_,?_⟩
  · intro a sep w tu tq tu1 tq1 wl wh Ω _ μ _ D gu
    let I := frame n (Reachability.pad N) (Vertex n (Reachability.pad N))
    exact b n nk N w tu nN logs tu1 wl wh _ _ _ _ Ω μ (single _ _) (initialized D I) _ _ false tq tq1
      (init_rel μ D I gu) (valid_single sep) (by intro; rfl) (by simp [single]) (by simp [single])
  · intro a sep w tu tq tu1 tq1 wl wh Ω _ μ _ D gu
    let I := frame n (Reachability.pad N) Unit
    exact b n nk N w tu nN logs tu1 wl wh _ _ _ _ Ω μ (fixed _ _) (initialized D I) _ _ true tq tq1
      (init_rel μ D I gu) (valid_fixed sep) (by intro; rfl) (by intro; rfl) (by simp)
  · intro a sep w tu tq tu1 tq1 wl wh Ω _ μ _ D gu
    exact b n nk N w tu nN logs tu1 wl wh _ _ _ _ Ω μ (mark _ _) D _ _ false tq tq1
      gu (valid_mark sep) (by intro; rfl) (by simp [mark]) (by simp [mark])

end
end DisjointnessDraft.Applications.DistanceLower
