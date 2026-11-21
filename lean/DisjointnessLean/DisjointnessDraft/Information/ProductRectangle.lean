import DisjointnessDraft.Information.Rectangle

/-! The near-rectangle comparison for any acceptance error and event. -/
namespace DisjointnessDraft.Information
open Finset Real MeasureTheory ProbabilityTheory DisjointnessFoundations.FiniteSampling DisjointnessFoundations.EntropyBridge
open scoped ProbabilityTheory BigOperators
open Classical
noncomputable section

/-- Passing to independent marginals increases an event probability by at most
the square root of half the mutual information in nats. The two marginal
atom bounds, expressed by the common cap, are preserved. -/
theorem product_rectangle {Ω L : Type*} [Fintype Ω] [MeasurableSpace Ω] [MeasurableSingletonClass Ω]
    [Fintype L] [Nonempty L] [MeasurableSpace L] [MeasurableSingletonClass L]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (a b : Ω→L) (E : Finset (L×L))
    (cap δ κ : ℝ)
    (capA : ∀z, μ.real (a ⁻¹' {z}) ≤ cap) (capB : ∀z, μ.real (b ⁻¹' {z}) ≤ cap)
    (mono : μ.real ((prod a b) ⁻¹' (E : Set (L×L))) ≤ δ)
    (info : I[a:b;μ] / log 2 ≤ κ) :
    let pa := law μ a (measurable_of_finite a)
    let pb := law μ b (measurable_of_finite b)
    (∀z, pa.weight z ≤ cap) ∧ (∀z, pb.weight z ≤ cap) ∧
    ∑z∈E,(pairLaw pa pb).weight z ≤ δ + sqrt ((log 2/2)*κ) := by
  intro pa pb
  refine ⟨capA,capB,?_⟩
  let j := law μ (prod a b) (measurable_of_finite _)
  let pr := pairLaw pa pb
  have ac (t : L×L) (h : pr.weight t=0) : j.weight t=0 := by
    rcases mul_eq_zero.mp h with z|z
    · exact le_antisymm ((measureReal_mono (fun v h => congrArg Prod.fst (show (a v,b v)=t from h))).trans_eq z) (j.nonneg _)
    · exact le_antisymm ((measureReal_mono (fun v h => congrArg Prod.snd (show (a v,b v)=t from h))).trans_eq z) (j.nonneg _)
  have pin := DisjointnessFoundations.ProductTransfer.pinsker_sq j pr ac
  have id := joint_product_kl μ b (measurable_of_finite b) a (measurable_of_finite a)
  rw [mutualInfo_comm (measurable_of_finite b) (measurable_of_finite a)] at id
  have lp := log_pos (by norm_num : (1:ℝ)<2)
  have corr : DisjointnessFoundations.InformationLoss.kl j.weight pr.weight=I[a:b;μ] := (div_left_inj' lp.ne').mp id
  rw [corr] at pin
  have corrLe := (div_le_iff₀ lp).mp info
  have dist : DisjointnessFoundations.ProductTransfer.tv j pr ≤ sqrt ((log 2/2)*κ) := by
    apply Real.le_sqrt_of_sq_le
    linarith only [pin,corrLe]
  let flag := fun t : L×L => if t∈E then (1:ℝ) else 0
  have tr := DisjointnessFoundations.ProductTransfer.expectation_transfer j pr flag 1
    (fun t => by dsimp [flag]; split_ifs <;> norm_num) (fun t => by dsimp [flag]; split_ifs <;> norm_num)
  have sum_flag (law' : InputLaw (L×L)) : (∑t,law'.weight t*flag t)=∑t∈E,law'.weight t := by
    simp [flag,mul_ite,←Finset.sum_filter]
  rw [sum_flag,sum_flag,one_mul] at tr
  have mass : (∑t∈E,j.weight t)=μ.real ((prod a b) ⁻¹' (E : Set (L×L))) :=
    sum_measureReal_preimage_singleton E (fun _ _ => (Set.toFinite _).measurableSet)
  rw [mass] at tr
  exact tr.trans (add_le_add mono dist)
end
end DisjointnessDraft.Information
