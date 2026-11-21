import DisjointnessDraft.Transfer.Direct

/-! Dynamic set disjointness with n+1 maintained sets on an n-point universe,
one insertion and one query. Legal operations insert a previously absent
element in the selected set. -/
namespace DisjointnessDraft.Applications.SetDisjointness
open DisjointnessFoundations CellProbe Transfer MeasureTheory Real Filter
noncomputable section
open Classical
abbrev Name (n : ℕ) := Option (Fin n)
abbrev Sets (n : ℕ) := Name n → Finset (Fin n)
abbrev Insert (n : ℕ) := Name n × Fin n
abbrev Ask (n : ℕ) := Name n × Name n

def current (f : Sets n) (xs : List (Insert n)) (j : Name n) :=
  f j ∪ ((xs.filter (fun p => p.1=j)).map Prod.snd).toFinset

def problem (n : ℕ) : Problem (Sets n) (Insert n) (Ask n) where
  legal f xs := xs.Nodup ∧ ∀ p∈xs, p.2∉f p.1
  answer f xs q := decide (Disjoint (current f xs q.1) (current f xs q.2))

def init (f : Family n) : Sets n | none => ∅ | some j => f j
def ins (j : Fin n) : Insert n := (none,j)
def map (n : ℕ) : Preload.Map n (Sets n) (Insert n) (Ask n) :=
  ⟨init,fun _ => [],0,fun _ => rfl,ins,fun q => (some q,none),false⟩

theorem correct (n : ℕ) : Direct (problem n) (map n) := by
  constructor
  · intro f xs nd
    change (xs.map ins).Nodup ∧ _
    refine ⟨nd.map (fun _ _ h => congrArg Prod.snd h),?_⟩
    intro p hp; change p∈xs.map ins at hp
    obtain ⟨x,_,rfl⟩ := List.mem_map.mp hp
    simp [map,init,ins]
  · intro f xs q _
    have source : current (init f) (xs.map ins) (some q)=f q := by simp [current,ins,init,List.filter_map,Function.comp_def]
    have upd : current (init f) (xs.map ins) none=xs.toFinset := by simp [current,ins,init,List.filter_map,List.map_map,Function.comp_def]
    change decide (Disjoint (current (init f) (xs.map ins) (some q)) (current (init f) (xs.map ins) none))=DisjointnessDraft.answer f xs q
    rw [source,upd]
    apply decide_eq_decide.mpr
    simp [Finset.disjoint_right]

theorem lower (lo hi : ℝ) (lp : 0<lo) (lh : lo≤hi) :
    ∃ c : ℝ,0<c ∧ ∀ᶠ n : ℕ in atTop,∀ w tu : ℕ,1≤tu → lo*logb 2 n≤w → (w:ℝ)≤hi*logb 2 n →
    ∀ (Ω C : Type) [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
      (D : DataStructure w (Sets n) (Insert n) (Ask n) C) (R : RandomTape Ω C) (tq : ℝ),1≤tq →
      Target μ (problem n) D R tu tq → c*(Tradeoff.ratio n w tu)^2≤tq ∧ c*(FixedFamilySizes.logRatio n)^2≤max (tu:ℝ) tq := by
  obtain ⟨c,cp,H⟩ := direct_bounds lo hi lp lh 1 (by norm_num)
  refine ⟨c,cp,?_⟩; filter_upwards [H] with n h
  intro w tu up wl wh Ω C _ μ _ D R tq qp t
  exact h n w tu le_rfl (by simp) up wl wh _ _ _ Ω C μ _ (map n) D R tq qp (correct n) t

end
end DisjointnessDraft.Applications.SetDisjointness
