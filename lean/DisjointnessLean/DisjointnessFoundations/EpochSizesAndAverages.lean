import Mathlib.Analysis.MeanInequalities
import Mathlib.Probability.Distributions.Uniform
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.List.FinRange
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

namespace DisjointnessFoundations.HardDistribution

noncomputable section

open Finset
open Classical

def epochSize {ℓ : ℕ} (g : ℕ) (i : Fin ℓ) := g^(2*(i.val+1))

def mean {α : Type*} [Fintype α] (f : α → ℝ) : ℝ :=
  (∑ a, f a) / Fintype.card α

theorem mean_equiv {α β : Type*} [Fintype α] [Fintype β]
    (e : α ≃ β) (f : β → ℝ) : mean (f ∘ e) = mean f := by
  unfold mean
  rw [Fintype.card_congr e]
  congr 1
  exact Fintype.sum_equiv e _ _ (fun _ => rfl)

theorem mean_prod {α β : Type*} [Fintype α] [Fintype β] (f : α → β → ℝ) :
    mean (fun p : α × β => f p.1 p.2) = mean (fun a => mean (f a)) := by
  simp only [mean, Fintype.card_prod, Nat.cast_mul, Fintype.sum_prod_type]
  rw [← Finset.sum_div, div_div]
  congr 1
  ring

theorem mean_const {α : Type*} [Fintype α] [Nonempty α] (c : ℝ) :
    mean (fun _ : α => c) = c := by
  have hc : (Fintype.card α : ℝ) ≠ 0 := by positivity
  simp [mean, mul_div_cancel_left₀, hc]

theorem mean_eval {ι : Type*} [Fintype ι] [DecidableEq ι]
    {β : ι → Type*} [∀ i, Fintype (β i)] [∀ i, Nonempty (β i)]
    (i : ι) (f : β i → ℝ) : mean (fun x : ∀ j, β j => f (x i)) = mean f := by
  let e := Equiv.piSplitAt i β
  change mean ((fun p : β i × (∀ j : {k // k ≠ i}, β j) => f p.1) ∘ e) = _
  rw [mean_equiv e, mean_prod (fun a (_ : ∀ j : {k // k ≠ i}, β j) => f a)]
  simp only [mean_const]

theorem mean_sum {α ι : Type*} [Fintype α] [Fintype ι] (f : ι → α → ℝ) :
    mean (fun x => ∑ i, f i x) = ∑ i, mean (f i) := by
  simp only [mean, ← Finset.sum_div]
  rw [Finset.sum_comm]

theorem mean_product {ι : Type*} [Fintype ι] [DecidableEq ι] {β : ι → Type*}
    [∀ i, Fintype (β i)] (f : (i : ι) → β i → ℝ) :
    mean (fun x : ∀ i, β i => ∏ i, f i (x i)) = ∏ i, mean (f i) := by
  simp only [mean, Fintype.card_pi, Nat.cast_prod, Finset.prod_div_distrib, Fintype.prod_sum]

/-- Weighted AM–GM adds one factor of one to the geometric mean. -/
private theorem no_hit_step {n : ℕ} (hn : 1 ≤ n) :
    (1-1/(n:ℝ))^n ≤ (1-1/((n+1:ℕ):ℝ))^(n+1) := by
  have h1 : (1:ℝ) ≤ n := by exact_mod_cast hn
  let x : ℝ := 1-1/n
  let y : ℝ := 1-1/((n+1:ℕ):ℝ)
  have hx : 0 ≤ x := sub_nonneg.mpr (div_le_one_of_le₀ h1 (by positivity))
  have avg : (n:ℝ)/(n+1)*x + 1/((n:ℝ)+1)*1 = y := by
    dsimp [x,y]
    push_cast
    field_simp
    ring
  have amgm := Real.geom_mean_le_arith_mean2_weighted
    (show 0 ≤ (n:ℝ)/(n+1) by positivity)
    (show 0 ≤ (1:ℝ)/((n:ℝ)+1) by positivity)
    hx (show (0:ℝ) ≤ 1 by norm_num)
    (show (n:ℝ)/(n+1)+1/((n:ℝ)+1)=1 by field_simp)
  rw [avg, Real.one_rpow, mul_one] at amgm
  have raised := pow_le_pow_left₀ (Real.rpow_nonneg hx _) amgm (n+1)
  rw [← Real.rpow_mul_natCast hx] at raised
  have expo : (n:ℝ)/(n+1)*((n+1:ℕ):ℝ) = n := by push_cast; field_simp
  rw [expo, Real.rpow_natCast] at raised
  exact raised

theorem quarter_le_no_hit_power {ℓ : ℕ} (hℓ : 2 ≤ ℓ) :
    (1/4:ℝ) ≤ (1-1/(ℓ:ℝ))^ℓ := by
  induction ℓ, hℓ using Nat.le_induction with
  | base => norm_num
  | succ n hn ih => exact ih.trans (no_hit_step (by omega : 1 ≤ n))

end

end DisjointnessFoundations.HardDistribution
