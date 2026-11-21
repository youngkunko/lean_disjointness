import DisjointnessDraft.Information.Smoothing
import Mathlib.Data.Complex.ExponentialBounds

/-! Smoothing at the full range of parameters in the draft. -/
namespace DisjointnessDraft.Information
open Finset Real DisjointnessFoundations.FiniteSampling DisjointnessFoundations.InformationLoss
open scoped BigOperators
open Classical
noncomputable section
variable {L : Type*} [Fintype L] [Nonempty L]

private theorem lower_atom {v u : ℝ} (v0 : 0 ≤ v) (u0 : 0 < u) :
    -(u*exp (-1)) ≤ v*log (v/u) := by
  rcases v0.eq_or_lt with eq|vp
  · rw [←eq,zero_mul]; linarith [mul_pos u0 (exp_pos (-1))]
  have e0 := exp_pos (-1)
  have tan := atom_tangent vp.le (mul_pos u0 e0)
  rw [show v/(u*exp (-1))=(v/u)/exp (-1) by ring, log_div (div_pos vp u0).ne' e0.ne',log_exp] at tan
  linarith only [tan]

/-- If KL to uniform is at most t bits with t>1 and α≥4, the retained
event has mass at least 1−1/α and its normalized atom cap is 2^(2αt)/|L|. -/
theorem smoothing (p : InputLaw L) (t α : ℝ) (ht : 1<t) (ha : 4≤α)
    (hKL : klBits p.weight (flat L).weight ≤ t) :
    ∃ E : Finset L, ∃ h : 0<∑x∈E,p.weight x, 1-1/α ≤ ∑x∈E,p.weight x ∧
      ∀x,(restrict p E h).weight x * (Fintype.card L:ℝ) ≤ (2:ℝ)^(2*α*t) := by
  let B := α*(t*log 2+2/5)
  let E := univ.filter fun x => p.weight x*(Fintype.card L:ℝ)≤exp B
  let D := Eᶜ
  let cost := fun x => p.weight x*log (p.weight x/(flat L).weight x)
  have ae : 0 < α := by linarith
  have log2 : (2:ℝ)/3 ≤ log 2 := by linarith [log_two_gt_d9]
  have tl : 2/3≤t*log 2 := log2.trans (by nlinarith [mul_nonneg (sub_nonneg.mpr ht.le) (by linarith : 0≤log 2)])
  have budget := (div_le_iff₀ (by linarith : 0<log 2)).mp hKL
  have posB : 0<B := mul_pos ae (by linarith)
  have high : (∑x∈D,p.weight x)*B≤∑x∈D,cost x := by
    rw [sum_mul]; apply sum_le_sum
    intro x hx
    have miss : exp B < p.weight x*(Fintype.card L:ℝ) := by simpa [D,E] using hx
    have bound := log_le_log (exp_pos _) miss.le
    rw [log_exp] at bound
    exact mul_le_mul_of_nonneg_left (by simpa [flat,div_eq_mul_inv] using bound) (p.nonneg _)
  have low : -(exp (-1))≤∑x∈E,cost x := by
    have le := sum_le_sum (s:=E) (fun x _ => lower_atom (p.nonneg x) (show 0<(flat L).weight x by dsimp [flat]; positivity))
    have full : (∑x∈E,(flat L).weight x)≤1 :=
      (sum_le_sum_of_subset_of_nonneg (subset_univ E) (fun x _ _ => (flat L).nonneg x)).trans_eq (flat L).total
    rw [sum_neg_distrib,←sum_mul] at le
    linarith only [le,mul_le_mul_of_nonneg_right full (exp_pos (-1)).le]
  have dc : (∑x∈E,cost x)+(∑x∈D,cost x)=kl p.weight (flat L).weight := sum_add_sum_compl E cost
  have total : (∑x∈E,p.weight x)+(∑x∈D,p.weight x)=1 := (sum_add_sum_compl E p.weight).trans p.total
  have tail : (∑x∈D,p.weight x)≤1/α := by
    apply (mul_le_mul_right posB).mp
    rw [show 1/α*B=t*log 2+2/5 by dsimp [B]; field_simp]
    linarith [exp_neg_one_lt_d9]
  have mass : 1-1/α ≤ ∑x∈E,p.weight x := by linarith only [tail,total]
  have quarter : 1/α≤1/4 := one_div_le_one_div_of_le (by norm_num) ha
  have pos : 0<∑x∈E,p.weight x := by linarith only [quarter,mass]
  refine ⟨E,pos,mass,?_⟩
  intro x
  by_cases hx : x∈E
  · have raw := (mem_filter.mp hx).2
    change p.weight x*(Fintype.card L:ℝ) ≤ exp B at raw
    have price : B+1/3≤log 2*(2*α*t) := by
      dsimp [B]
      nlinarith only [mul_nonneg (sub_nonneg.mpr ha) (sub_nonneg.mpr tl),tl,ha]
    have expbound := exp_le_exp.mpr price
    rw [exp_add,←rpow_def_of_pos (by norm_num : (0:ℝ)<2)] at expbound
    have extra := add_one_le_exp (1/3:ℝ)
    have large : exp B*(4/3) ≤ (2:ℝ)^(2*α*t) :=
      (mul_le_mul_of_nonneg_left (by linarith only [extra] : 4/3≤exp (1/3)) (exp_pos _).le).trans expbound
    have m3 : 3/4 ≤ ∑x∈E,p.weight x := by linarith only [quarter,mass]
    simp only [restrict,hx,if_pos,div_mul_eq_mul_div]
    apply (div_le_iff₀ pos).mpr
    nlinarith only [raw,large,mul_le_mul_of_nonneg_left m3 (rpow_nonneg (by norm_num : (0:ℝ)≤2) (2*α*t))]
  · simp [restrict,hx,Real.rpow_nonneg]
end
end DisjointnessDraft.Information
