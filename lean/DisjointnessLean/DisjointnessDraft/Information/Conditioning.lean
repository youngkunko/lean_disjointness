import DisjointnessDraft.Information.DirectSum

namespace DisjointnessDraft.Information
open MeasureTheory ProbabilityTheory
open scoped ProbabilityTheory
noncomputable section
variable {Ω A B C D : Type*} [Fintype Ω] [MeasurableSpace Ω] [MeasurableSingletonClass Ω]
  [Fintype A] [MeasurableSpace A] [MeasurableSingletonClass A]
  [Fintype B] [MeasurableSpace B] [MeasurableSingletonClass B]
  [Fintype C] [MeasurableSpace C] [MeasurableSingletonClass C]
  [Fintype D] [MeasurableSpace D] [MeasurableSingletonClass D]

theorem process (μ : Measure Ω) [IsProbabilityMeasure μ] (a : Ω→A) (b : Ω→B)
    (c : Ω→C) (f : B→D) : I[a:f ∘ b|c;μ] ≤ I[a:b|c;μ] := by
  rw [condMutualInfo_eq' (measurable_of_finite _) (measurable_of_finite _) (measurable_of_finite _),
    condMutualInfo_eq' (measurable_of_finite _) (measurable_of_finite _) (measurable_of_finite _)]
  exact sub_le_sub_left (condEntropy_comp_ge μ (measurable_of_finite (prod b c)) (measurable_of_finite a)
    (fun u => (f u.1,u.2))) _

theorem drop_condition (μ : Measure Ω) [IsProbabilityMeasure μ] (a : Ω→A) (b : Ω→B)
    (c : Ω→C) (d : Ω→D) (h : I[b:d|prod a c;μ]=0) :
    I[a:b|prod c d;μ] ≤ I[a:b|c;μ] := by
  rw [condMutualInfo_comm (measurable_of_finite a) (measurable_of_finite b),
      condMutualInfo_comm (X:=a) (Y:=b) (Z:=c) (measurable_of_finite a) (measurable_of_finite b)]
  rw [condMutualInfo_eq' (measurable_of_finite _) (measurable_of_finite _) (measurable_of_finite _),
    condMutualInfo_eq' (measurable_of_finite _) (measurable_of_finite _) (measurable_of_finite _)]
  rw [condMutualInfo_eq' (measurable_of_finite _) (measurable_of_finite _) (measurable_of_finite _)] at h
  have eq := recode μ b (prod a (prod c d)) (prod d (prod a c))
    (fun u => (u.2.2,(u.1,u.2.1))) (fun u => (u.2.1,(u.2.2,u.1))) rfl rfl
  have le := condEntropy_comp_ge μ (measurable_of_finite (prod c d)) (measurable_of_finite b) Prod.fst
  change H[b|prod c d;μ] ≤ H[b|c;μ] at le
  linarith only [le,h,eq]

theorem independent_condition (μ : Measure Ω) [IsProbabilityMeasure μ] (a : Ω→A) (b : Ω→B)
    (c : Ω→C) (d : Ω→D) (h : IndepFun (prod a (prod b c)) d μ) :
    I[a:b|prod c d;μ] = I[a:b|c;μ] := by
  rw [condMutualInfo_eq' (measurable_of_finite _) (measurable_of_finite _) (measurable_of_finite _),
    condMutualInfo_eq' (measurable_of_finite _) (measurable_of_finite _) (measurable_of_finite _)]
  have projected : IndepFun (prod a c) d μ :=
    h.comp (measurable_of_finite (fun u : A×(B×C) => (u.1,u.2.2))) measurable_id
  have eq := recode μ a (prod b (prod c d)) (prod (prod b c) d)
    (fun u => ((u.1,u.2.1),u.2.2)) (fun u => (u.1.1,(u.1.2,u.2))) rfl rfl
  rw [eq,condEntropy_prod_eq_of_indepFun (measurable_of_finite _) (measurable_of_finite _) (measurable_of_finite _) projected,
    condEntropy_prod_eq_of_indepFun (measurable_of_finite _) (measurable_of_finite _) (measurable_of_finite _) h]
end
end DisjointnessDraft.Information
