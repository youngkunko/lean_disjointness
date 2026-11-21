import DisjointnessDraft.Applications.ModeFrequency
import DisjointnessDraft.Transfer.Relational

/-! An actual point-assignment array and a contiguous interval mode query,
with no deterministic tie-breaking convention imposed on the target. -/
namespace DisjointnessDraft.Applications.RangeMode
open Transfer.Compiler Real Filter MeasureTheory
open Classical
noncomputable section
abbrev Edit (n : ℕ) := Pos n × Color n
def write (a : Array n) (e : Edit n) : Array n := fun p => if p=e.1 then e.2 else a p
def state (a : Array n) (h : List (Instr (Edit n) Window)) :=
  h.foldl (fun v op => op.elim (write v) (fun _ => v)) a
def edits (j : Fin n) : List (Edit n) :=
  [((.inr (),.inl (j,false)),.data j),((.inr (),.inl (j,true)),.data j)]
def mode (a : Array n) (h : List (Instr (Edit n) Window)) (w : Window) (z : Color n) :=
  ∀ y,frequency (state a h) w y≤frequency (state a h) w z
def legal (_ : Array n) (h : List (Instr (Edit n) Window)) :=
  ∀ w,Sum.inr w∈h → (∃ p : Pos n, coordinate p=w.1) ∧
    (∃ p : Pos n, coordinate p=w.2) ∧ ∃ p : Pos n,covers w p
def plan (n : ℕ) : Schedule n (Array n) (Edit n) Window (Color n) :=
  ⟨fun f => marked f ∅,edits,fun q => [.inr (chosen q)],fun _ vs => decide (vs.head?=some .signal)⟩

theorem next (f : Family n) (X : Finset (Fin n)) (j : Fin n) :
    (edits j).foldl write (marked f X)=marked f (insert j X) := by
  funext p
  rcases p with ⟨(⟨i,h⟩|⟨⟩),(⟨k,c⟩|u)⟩ <;> try rfl
  cases c <;> by_cases e : k=j <;> simp [write,edits,marked,e]

theorem history (f : Family n) (xs : List (Fin n)) :
    state (marked f ∅) (before (plan n) xs)=marked f xs.toFinset := by
  induction xs using List.reverseRecOn with
  | nil => rfl
  | append_singleton xs j ih =>
    rw [before_append,before_singleton]
    change state _ (before _ xs ++ ((edits j).map Sum.inl))=_
    have step (a : Array n) (h : List (Instr (Edit n) Window)) :
        state a (h++((edits j).map Sum.inl))=(edits j).foldl write (state a h) := by simp [edits,state,List.foldl_append]
    rw [step,ih,next]
    simp [Finset.insert_eq,Finset.union_comm]

theorem detected (f : Family n) (X : Finset (Fin n)) (q : Fin n) (z : Color n)
    (best : ∀ y,frequency (marked f X) (chosen q) y≤frequency (marked f X) (chosen q) z) :
    z=.signal ↔ ∀ x∈X,x∉f q := by
  constructor
  · rintro rfl x hx hit
    have e := best (.data x)
    simp [signal_score,data_score,hit,hx] at e
  · intro no
    have e := best .signal
    rw [signal_score] at e
    cases z with
    | signal => rfl
    | filler p => have b := filler_score f X q p; omega
    | data x =>
      rw [data_score] at e
      by_cases h : x∈X
      · simp [h,no x h] at e
      · by_cases hit : x∈f q <;> simp [h,hit] at e

theorem valid (n : ℕ) : RelValid (plan n) legal mode := by
  constructor
  · intro f xs q _ h pre w hw
    have m := pre.subset hw
    simp only [List.mem_append,before,List.mem_map,plan,List.mem_singleton,Sum.inr.injEq] at m
    have ew : w=chosen q := by rcases m with ⟨_,_,bad⟩|eq; contradiction; exact eq
    rw [ew]
    exact ⟨(chosen_endpoints q).1,(chosen_endpoints q).2,⟨(.inr (),.inr 0),(covered q _ _).mpr trivial⟩⟩
  · intro f xs q _ reports accept
    cases reports with
    | nil => cases accept
    | cons z zs =>
      change mode (marked f ∅) (before (plan n) xs) (chosen q) z ∧ zs=[] at accept
      obtain ⟨best,rfl⟩ := accept
      simp only [mode,history] at best
      change decide (([z] : List (Color n)).head?=some .signal)=_
      apply decide_eq_decide.mpr
      simpa only [List.head?_cons,Option.some.injEq,List.mem_toFinset] using detected f xs.toFinset q z best

def Bound (lo hi c : ℝ) (N n : ℕ) := ∀ (w tu : ℕ) (tq : ℝ),1≤tu → 1≤tq →
    lo*logb 2 N≤w → (w:ℝ)≤hi*logb 2 N →
    ∀ (Ω : Type) [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
      (D : Target (Array n) (Edit n) Window (Color n) w Ω), RelGuarantees μ D legal mode tu tq →
      c*(DisjointnessFoundations.Tradeoff.ratio N w tu)^2≤tq ∧ c*(DisjointnessFoundations.FixedFamilySizes.logRatio N)^2≤max (tu:ℝ) tq

theorem lower (lo hi : ℝ) (lp : 0<lo) (lh : lo≤hi) :
    ∃ c : ℝ,0<c ∧ ∀ᶠ N : ℕ in atTop, let n := ShortTransfer.stringSize N
      Fintype.card (Pos n)≤N ∧ Bound lo hi c N n := by
  obtain ⟨c,cp,event⟩ := rel_lower lo hi lp lh 2 1 3 (by norm_num)
  obtain ⟨k,b⟩ := eventually_atTop.mp event
  refine ⟨c,cp,?_⟩
  filter_upwards [ShortTransfer.string_geometry (max k 3)] with N g
  let n := ShortTransfer.stringSize N
  obtain ⟨kn,hn,fit,low,high⟩ := g
  change max k 3≤n at kn
  have n3 : 3≤n := (le_max_right ..).trans kn
  have right : (n*2+1)*(n*2+3)≤N := by
    change 9*(n*n)≤N at fit
    nlinarith [Nat.mul_le_mul_left n n3]
  refine ⟨by simpa [Pos,Bucket,Slot,Fintype.card_sum] using right,?_⟩
  intro w tu tq tu1 tq1 wl wh Ω _ μ _ D gu
  have hn0 : (0:ℝ)<N := by exact_mod_cast (hn.trans low)
  have l := logb_le_logb_of_le (b:=2) (by norm_num) hn0 (by exact_mod_cast high : (N:ℝ)≤(n:ℝ)^3)
  rw [logb_pow] at l
  have cert := b n ((le_max_left ..).trans kn) N w tu low (by simpa using l) tu1 wl wh
    (Array n) (Edit n) Window (Color n) Ω μ (plan n) D legal mode false tq tq1 gu (valid n)
    (by simp [plan,edits]) (by simp [plan]) (by simp [plan])
  simpa [Transfer.charge] using cert

end
end DisjointnessDraft.Applications.RangeMode
