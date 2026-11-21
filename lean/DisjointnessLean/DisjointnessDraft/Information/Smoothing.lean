import DisjointnessDraft.Information.ProtocolConditioning
import DisjointnessFoundations.SparseProductApproximation

namespace DisjointnessDraft.Information
open Finset Real DisjointnessFoundations.FiniteSampling DisjointnessFoundations.InformationLoss
open scoped BigOperators
noncomputable section
open Classical

variable {L : Type*} [Fintype L] [Nonempty L]

def flat (L : Type*) [Fintype L] [Nonempty L] : InputLaw L where
  weight _ := (Fintype.card L:ℝ)⁻¹
  nonneg _ := by positivity
  total := by simp [Fintype.card_ne_zero]

/-- The pointwise KL contribution above its tangent at one. -/
theorem atom_tangent {p q : ℝ} (hp : 0≤p) (hq : 0<q) : p-q ≤ p*log (p/q) := by
  rcases hp.eq_or_lt with h|h
  · simp [←h,hq.le]
  · have u := mul_le_mul_of_nonneg_left (one_sub_inv_le_log_of_pos (div_pos h hq)) h.le
    rw [inv_div, mul_sub, mul_one, mul_div_cancel₀ _ h.ne'] at u
    exact u

/-- A likely one-sided restriction capping the row likelihood ratio.
The allowance of one natural unit bounds all negative KL contributions. -/
theorem smooth (p : InputLaw L) {K : ℝ} (one : 1<K)
    (budget : 4*(kl p.weight (flat L).weight+1)≤log K) :
    ∃ E : Finset L, 3/4≤∑a∈E,p.weight a ∧
      ∀a∈E,p.weight a*(Fintype.card L:ℝ)≤K := by
  let E := univ.filter (fun x => p.weight x*(Fintype.card L:ℝ)≤K)
  let D := Eᶜ
  let cost := fun x => p.weight x*log (p.weight x/(flat L).weight x)
  have cp : (0:ℝ)<Fintype.card L := by exact_mod_cast Fintype.card_pos
  have miss : ∀ x∈D, K < p.weight x*(Fintype.card L:ℝ) := by
    intro x hx; simpa [D,E] using hx
  have hcost : (∑x∈D,p.weight x)*log K ≤∑x∈D,cost x := by
    rw [sum_mul]; apply sum_le_sum
    intro x hx
    apply mul_le_mul_of_nonneg_left _ (p.nonneg x)
    simpa [flat,div_eq_mul_inv] using log_le_log (by linarith : 0<K) (miss x hx).le
  have rest : -(1:ℝ) ≤∑x∈E,cost x := by
    have each (x) : -(flat L).weight x ≤ cost x := by
      exact (by linarith [p.nonneg x] : -(flat L).weight x ≤ p.weight x-(flat L).weight x).trans
        (atom_tangent (p.nonneg x) (by dsimp [flat]; positivity))
    have full : (∑x∈E,(flat L).weight x)≤1 :=
      (sum_le_sum_of_subset_of_nonneg (subset_univ E) (fun x _ _ => (flat L).nonneg x)).trans_eq (flat L).total
    have neg := sum_le_sum (s:=E) (fun x _ => each x)
    rw [sum_neg_distrib] at neg
    linarith only [full,neg]
  have dc : (∑x∈E,cost x)+(∑x∈D,cost x)=kl p.weight (flat L).weight := sum_add_sum_compl E cost
  have norm : (∑x∈E,p.weight x)+(∑x∈D,p.weight x)=1 := (sum_add_sum_compl E p.weight).trans p.total
  have posLog := log_pos one
  have small : (∑x∈D,p.weight x)≤1/4 := by
    apply (mul_le_mul_right posLog).mp
    linarith only [rest,hcost,dc,budget]
  exact ⟨E,by linarith only [norm,small],fun x hx => (mem_filter.mp hx).2⟩

/-- Restricting a finite law and normalizing by the actual mass. -/
def restrict (p : InputLaw L) (E : Finset L) (pos : 0<∑x∈E,p.weight x) : InputLaw L where
  weight x := if x∈E then p.weight x/(∑y∈E,p.weight y) else 0
  nonneg x := by split_ifs <;> first | exact div_nonneg (p.nonneg x) pos.le | rfl
  total := by rw [←sum_filter]; simp [←sum_div,pos.ne']

variable {N s : ℕ}

def extendLaw (p : InputLaw (Layer N s)) : Corruption.Weights N :=
  fun x => if h : x∈Corruption.layer N s then p.weight ⟨x,h⟩ else 0

theorem subtype_sum (f : Corruption.Row N→ℝ) :
    ∑a∈Corruption.layer N s,f a=∑a : Layer N s,f a.val :=
  sum_subtype _ (fun _ => Iff.rfl) f

theorem extend_capped (p : InputLaw (Layer N s))
    (cap : ∀x,p.weight x*Fintype.card (Layer N s)≤Corruption.capFactor s) :
    Corruption.Capped (s:=s) (extendLaw p) := by
  refine ⟨fun x hx => by simpa [extendLaw,hx] using p.nonneg ⟨x,hx⟩,?_,?_⟩
  · rw [subtype_sum]; simpa [extendLaw] using p.total
  · intro x hx
    simpa [extendLaw,hx] using cap ⟨x,hx⟩

/-- The corruption lower bound for arbitrary distributions on the subtype of
rows, in the ordinary finite product-law notation used by the protocol. -/
theorem product_lower (hs : 200≤s) (hN : 0<N) (hm : s^2∣N) (p q : InputLaw (Layer N s))
    (cp : ∀x,p.weight x*Fintype.card (Layer N s)≤Corruption.capFactor s)
    (cq : ∀x,q.weight x*Fintype.card (Layer N s)≤Corruption.capFactor s) :
    (s:ℝ)^2/(100*N) ≤ ∑a : Layer N s, p.weight a*(∑b : Layer N s, if Disjoint a.val b.val then 0 else q.weight b) := by
  have lower := Corruption.product_corruption hs hN hm _ _ (extend_capped p cp) (extend_capped q cq)
  convert lower using 1
  unfold Corruption.intersectionMass Corruption.hitProb
  rw [subtype_sum]
  apply sum_congr rfl
  intro a _
  simp only [extendLaw,a.property,dif_pos]
  congr 1
  rw [sum_filter,subtype_sum]
  apply sum_congr rfl
  intro b _
  by_cases h : Disjoint a.val b.val <;> simp [h,b.property]

end
end DisjointnessDraft.Information
