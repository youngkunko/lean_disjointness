import DisjointnessDraft.Transfer.Lower

/-! An operation may return any value satisfying the target relation. Ties
may depend on the tape, prior operations, and the machine's private state. -/
namespace DisjointnessDraft.Transfer.Compiler
open DisjointnessFoundations CellProbe WordProgram MeasureTheory Filter Real
noncomputable section

structure RelGuarantees [MeasurableSpace Ω] (μ : Measure Ω) (D : Target F U Q A w Ω)
    (legal : F → List (Instr U Q) → Prop) (rel : F → List (Instr U Q) → Q → A → Prop)
    (tu : ℕ) (tq : ℝ) : Prop extends Costs μ D legal tu tq where
  correct : ∀ a f h q, legal f (h++[.inr q]) →
    rel f h q ((D.query a h.length q).run (observed D a f h).2.1).1

def Allowed (rel : F → List (Instr U Q) → Q → A → Prop) (f : F) (h : List (Instr U Q)) :
    List (Instr U Q) → List A → Prop
  | [], reports => reports=[]
  | .inl u :: ops, reports => Allowed rel f (h++[.inl u]) ops reports
  | .inr _ :: _, [] => False
  | .inr q :: ops, a::reports => rel f h q a ∧ Allowed rel f (h++[.inr q]) ops reports

def RelValid (S : Schedule n F U Q A) (legal : F → List (Instr U Q) → Prop)
    (rel : F → List (Instr U Q) → Q → A → Prop) : Prop :=
  (∀ f xs q, xs.Nodup → ∀ h : List (Instr U Q), h <+: before S xs ++ S.finish q → legal (S.initial f) h) ∧
  (∀ f xs q, xs.Nodup → ∀ reports, Allowed rel (S.initial f) (before S xs) (S.finish q) reports →
    S.decode q reports=DisjointnessDraft.answer f xs q)

theorem actual_allowed [MeasurableSpace Ω] (μ : Measure Ω) (D : Target F U Q A w Ω)
    (a : Ω) (rel : F → List (Instr U Q) → Q → A → Prop) (g : RelGuarantees μ D legal rel tu tq)
    (f : F) (pre ops : List (Instr U Q)) (ok : OnPath legal f pre ops) :
    Allowed rel f pre ops ((script D a pre.length ops).run (observed D a f pre).2.1).1 := by
  induction ops generalizing pre with
  | nil => rfl
  | cons x xs ih =>
    have head := ok [x] ⟨xs,rfl⟩
    have tail : OnPath legal f (pre++[x]) xs := by
      rintro h ⟨rest,eq⟩
      simpa using ok (x::h) ⟨rest,by simp [eq]⟩
    have cont := ih (pre++[x]) tail
    rw [next_memory] at cont
    simp only [List.length_append,List.length_singleton] at cont
    cases x with
    | inl u => simpa [Allowed,script,targetStep,Program.run_bind] using cont
    | inr q => simpa [Allowed,script,targetStep,Program.run_bind] using And.intro (g.correct a f pre q head) cont

theorem rel_lower (lo hi : ℝ) (lp : 0<lo) (lh : lo≤hi) (us fs : ℕ) (d : ℝ) (d1 : 1≤d) :
    ∃ c : ℝ,0<c ∧ ∀ᶠ n : ℕ in atTop, ∀ N w tu : ℕ, n≤N → logb 2 N≤d*logb 2 n →
    1≤tu → lo*logb 2 N≤w → (w:ℝ)≤hi*logb 2 N →
    ∀ (F U Q A Ω : Type) [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
      (S : Schedule n F U Q A) (D : Target F U Q A w Ω)
      (legal : F → List (Instr U Q) → Prop) (rel : F → List (Instr U Q) → Q → A → Prop)
      (sel : Bool) (tq : ℝ), 1≤tq → RelGuarantees μ D legal rel tu tq → RelValid S legal rel →
      (∀ x,(S.insert x).length≤us) → (∀ q,(S.finish q).length≤fs) →
      (∀ q u,.inl u∈S.finish q → sel=true) →
      c*(Tradeoff.ratio N w tu)^2≤Transfer.charge sel tu tq ∧
      c*(FixedFamilySizes.logRatio N)^2≤max (tu:ℝ) tq := by
  obtain ⟨c,cp,cert⟩ := lower_actual lo hi lp lh us fs d d1
  refine ⟨c,cp,?_⟩
  filter_upwards [cert] with n useBound
  intro N w tu nN size tu1 wl wh F U Q A Ω _ μ _ S D legal rel sel tq tq1 g ok ucap qcap gate
  apply useBound N w tu nN size tu1 wl wh F U Q A Ω μ S D legal sel tq tq1 g.toCosts ok.1 _ ucap qcap gate
  intro a f xs q nd
  exact ok.2 f xs q nd _ (actual_allowed μ D a rel g _ _ _ (finish_path S ok.1 f xs q nd))

end
end DisjointnessDraft.Transfer.Compiler
