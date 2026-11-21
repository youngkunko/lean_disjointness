import DisjointnessDraft.Information.ProtocolConditioning

namespace DisjointnessDraft.Information
open MeasureTheory ProbabilityTheory
open scoped ProbabilityTheory BigOperators
noncomputable section
open Classical

scoped instance optSpace {A : Type*} : MeasurableSpace (Option A) := ⊤
scoped instance optMeas {A : Type*} : MeasurableSingletonClass (Option A) := ⟨fun _ => trivial⟩

variable {Ω X Y Z T W : Type*} [Fintype Ω] [MeasurableSpace Ω] [MeasurableSingletonClass Ω]
  [Fintype X] [MeasurableSpace X] [MeasurableSingletonClass X]
  [Fintype Y] [MeasurableSpace Y] [MeasurableSingletonClass Y]
  [Fintype Z] [MeasurableSpace Z] [MeasurableSingletonClass Z]
  [Fintype T] [MeasurableSpace T] [MeasurableSingletonClass T]
  [Fintype W] [MeasurableSpace W] [MeasurableSingletonClass W]
variable {m : ℕ}

/-- Two observations decoding each other on the underlying sample space have
the same conditional entropy, including observations with unused codewords. -/
theorem recode (μ : Measure Ω) [IsProbabilityMeasure μ] (x : Ω→X) (y : Ω→Y) (z : Ω→Z)
    (f : Y→Z) (g : Z→Y) (ef : z=f ∘ y) (eg : y=g ∘ z) : H[x | y ; μ]=H[x | z ; μ] :=
  le_antisymm (ef ▸ condEntropy_comp_ge μ (measurable_of_finite y) (measurable_of_finite x) f)
    (eg ▸ condEntropy_comp_ge μ (measurable_of_finite z) (measurable_of_finite x) g)

def history (F : Ω→Family m W) (v : Ω→Z) (j : ℕ) (ω : Ω) := (v ω,rowPrefix j (F ω))

theorem direct_sum [Nonempty W] (μ : Measure Ω) [IsProbabilityMeasure μ] (F : Ω→Family m W)
    (y : Ω→Y) (v : Ω→Z) :
    (∑ q : Fin m,I[(fun ω => F ω q) : y | history F v q.val ; μ])= I[F : y | v ; μ] := by
  classical
  letI : Inhabited W := ⟨Classical.choice (inferInstance : Nonempty W)⟩
  let Hs := fun j => H[y | history F v j ; μ]
  have step (q : Fin m) : I[(fun ω => F ω q) : y | history F v q.val ; μ]=Hs q.val-Hs (q.val+1) := by
    rw [condMutualInfo_comm (measurable_of_finite _) (measurable_of_finite y),
      condMutualInfo_eq' (measurable_of_finite y) (measurable_of_finite _) (measurable_of_finite _)]
    congr 1
    let put := fun p : W × (Z × (Fin m→Option W)) => (p.2.1,fun j => if j=q then some p.1 else p.2.2 j)
    let get := fun p : Z × (Fin m→Option W) => ((p.2 q).getD default,(p.1,fun j => if j.val<q.val then p.2 j else none))
    apply recode μ y _ (history F v (q.val+1)) put get
    · funext ω; refine Prod.ext rfl ?_; funext j
      by_cases e : j=q
      · subst j; simp [put,history,rowPrefix]
      · have iff : j.val<q.val+1 ↔ j.val<q.val := by have : j.val≠q.val := fun h => e (Fin.ext h); omega
        simp [put,history,rowPrefix,e,iff]
    · funext ω; dsimp [get,history,prod,rowPrefix]; simp only [Nat.lt_succ_self,↓reduceIte,Option.getD_some]
      congr 2; funext j
      by_cases h : j.val<q.val <;> simp [rowPrefix,h,Nat.lt_succ_of_lt]
  simp_rw [step]
  rw [Fin.sum_univ_eq_sum_range (fun j => Hs j-Hs (j+1)),Finset.sum_range_sub']
  rw [condMutualInfo_comm (measurable_of_finite F) (measurable_of_finite y),
    condMutualInfo_eq' (measurable_of_finite y) (measurable_of_finite F) (measurable_of_finite v)]
  congr 1
  · exact recode μ y _ v Prod.fst (fun b => (b,fun _ => none)) rfl (by funext ω; refine Prod.ext rfl ?_; funext j; simp [history,rowPrefix,Function.comp])
  · apply recode μ y _ (prod F v) (fun p => (fun j => (p.2 j).getD default,p.1)) (fun p => (p.2,fun j => some (p.1 j)))
    · funext ω; simp [history,prod,rowPrefix]
    · funext ω; refine Prod.ext rfl ?_; funext j; simp [history,prod,rowPrefix,Function.comp]

/-- Revealing a deterministic test of a larger target cannot increase the
remaining correlation past the former information about that target. -/
theorem reveal_test (μ : Measure Ω) [IsProbabilityMeasure μ]
    (x : Ω→X) (y : Ω→Y) (z : Ω→Z) (flag : Ω→T) (decode : Y×Z→T)
    (h : flag=decode ∘ prod y z) :
    I[x : y | prod z flag ; μ]≤I[x : y | z ; μ] := by
  rw [condMutualInfo_eq' (measurable_of_finite x) (measurable_of_finite y) (measurable_of_finite _),
      condMutualInfo_eq' (measurable_of_finite x) (measurable_of_finite y) (measurable_of_finite z)]
  have first := condEntropy_comp_ge μ (measurable_of_finite (prod z flag)) (measurable_of_finite x) Prod.fst
  have second := recode μ x (prod y (prod z flag)) (prod y z) (fun p => (p.1,p.2.1))
    (fun p => (p.1,(p.2,decode p))) rfl (by rw [h]; rfl)
  change H[x | prod z flag ; μ] ≤ H[x | z ; μ] at first
  linarith only [first,second]

end
end DisjointnessDraft.Information
