import DisjointnessDraft.Transfer.Bounds
import DisjointnessDraft.Preload

namespace DisjointnessDraft.Transfer
open DisjointnessFoundations CellProbe MeasureTheory Filter Real
open scoped ENNReal
noncomputable section
open Classical

/-- A Boolean target problem, specified on all legal histories independently
of any particular reduction. All histories start in the supplied initial input. -/
structure Problem (F E Q : Type) where
  legal : F → List E → Prop
  answer : F → List E → Q → Bool

structure Target {F E Q C Ω : Type} {w : ℕ} [MeasurableSpace Ω] (μ : Measure Ω)
    (P : Problem F E Q) (D : DataStructure w F E Q C) (R : RandomTape Ω C) (tu : ℕ) (tq : ℝ) : Prop where
  pays : ∀ a f xs,P.legal f xs → SingleSelector.Pays D R tu a f xs
  correct : ∀ a f xs q,P.legal f xs → (finalRun D R a f xs q).map Prod.fst=some (P.answer f xs q)
  measurable : ∀ f xs q,P.legal f xs → Measurable (fun a => cost (finalRun D R a f xs q))
  query : ∀ f xs q,P.legal f xs → (∫⁻ a,cost (finalRun D R a f xs q) ∂μ)≤ENNReal.ofReal tq

structure Direct {n : ℕ} {F E Q : Type} (P : Problem F E Q) (A : Preload.Map n F E Q) : Prop where
  legal : ∀ f (xs : List (Fin n)),xs.Nodup → P.legal (A.initial f) (A.setup f++xs.map A.insert)
  correct : ∀ f (xs : List (Fin n)) q,xs.Nodup → P.answer (A.initial f) (A.setup f++xs.map A.insert) (A.ask q)=
    InputReduction.out A.negate (DisjointnessDraft.answer f xs q)

theorem direct {n w tu : ℕ} {F E Q C Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (P : Problem F E Q) (D : DataStructure w F E Q C) (R : RandomTape Ω C) {tq : ℝ} (H : Target μ P D R tu tq)
    (A : Preload.Map n F E Q) (valid : Direct P A) :
    Fresh.OnFresh μ (Preload.algorithm A D R tu) (Padding.tape Ω) tu tq := by
  apply Preload.transfer
  exact ⟨fun a f xs nd => H.pays _ _ _ (valid.legal f xs nd),fun a f xs q nd =>
    (H.correct _ _ _ _ (valid.legal f xs nd)).trans (congrArg some (valid.correct f xs q nd)),
    fun f xs q nd => H.measurable _ _ _ (valid.legal f xs nd),fun f xs q nd => H.query _ _ _ (valid.legal f xs nd)⟩

theorem direct_bounds (lo hi : ℝ) (lp : 0<lo) (lh : lo≤hi) (d : ℝ) (d1 : 1≤d) :
    ∃ c : ℝ,0<c ∧ ∀ᶠ n : ℕ in atTop,∀ N w tu : ℕ, n≤N → logb 2 N≤d*logb 2 n →
    1≤tu → lo*logb 2 N≤w → (w:ℝ)≤hi*logb 2 N →
    ∀ (F E Q Ω C : Type) [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
      (P : Problem F E Q) (A : Preload.Map n F E Q) (D : DataStructure w F E Q C) (R : RandomTape Ω C) (tq : ℝ),
      1≤tq → Direct P A → Target μ P D R tu tq →
      c*(Tradeoff.ratio N w tu)^2≤tq ∧ c*(FixedFamilySizes.logRatio N)^2≤max (tu:ℝ) tq := by
  obtain ⟨c,cp,H⟩ := lower lo hi lp lh 1 1 1 (by decide) (by decide) (by decide) d d1
  refine ⟨c,cp,?_⟩; filter_upwards [H] with n lb
  intro N w tu nN size t1 wl wh F E Q Ω C _ μ _ P A D R tq q1 valid target
  have sim := direct μ P D R target A valid
  simpa [charge] using lb N w w tu nN size t1 wl wh le_rfl (by simp) Ω (ℕ×Ω) μ _ _ false tq q1 (by simpa [charge] using sim)

end
end DisjointnessDraft.Transfer
