import DisjointnessFoundations.FiniteBernoulliLaw
import PFR.Mathlib.Analysis.SpecialFunctions.NegMulLog
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith

namespace DisjointnessFoundations.InformationLoss
open DisjointnessFoundations.FiniteSampling
noncomputable section
variable {A L Z : Type*} [Fintype A] [Fintype L]

def kl (p q : A → ℝ) : ℝ := ∑ a, p a * Real.log (p a / q a)

def klBits (p q : A → ℝ) : ℝ := kl p q / Real.log 2

theorem kl_nonneg (p q : InputLaw A) (ac : ∀ a, q.weight a = 0 → p.weight a = 0) :
    0 ≤ kl p.weight q.weight := by
  simpa [p.total, q.total, kl] using Real.sum_mul_log_div_leq (s := Finset.univ)
    (fun a _ => p.nonneg a) (fun a _ => q.nonneg a) (fun a _ => ac a)

def mass (w : InputLaw L) (J : Finset L) : ℝ := ∑ l ∈ J, w.weight l

def jointRow (w : InputLaw L) (q : L → InputLaw A) (J : Finset L) (a : A) : ℝ :=
  ∑ l ∈ J, w.weight l * (q l).weight a

def rowCost (w : InputLaw L) (q : L → InputLaw A) (ref : InputLaw A) (J : Finset L) : ℝ :=
  ∑ a, jointRow w q J a * Real.log (jointRow w q J a / (mass w J * ref.weight a))

theorem rowCost_eq_weighted_posterior (w : InputLaw L) (q : L → InputLaw A)
    (ref : InputLaw A) (J : Finset L) (hm : mass w J ≠ 0) :
    rowCost w q ref J =
      mass w J * kl (fun a => jointRow w q J a / mass w J) ref.weight := by
  unfold rowCost kl
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a _
  rw [← mul_assoc, mul_div_cancel₀ _ hm, div_div]

theorem rowCost_le (w : InputLaw L) (q : L → InputLaw A) (ref : InputLaw A) (J : Finset L)
    (ac : ∀ l a, ref.weight a = 0 → (q l).weight a = 0) :
    rowCost w q ref J ≤ ∑ l ∈ J, w.weight l * kl (q l).weight ref.weight := by
  unfold rowCost kl jointRow mass
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_le_sum
  intro a _
  calc
    _ = (∑ l ∈ J, w.weight l * (q l).weight a) *
          Real.log ((∑ l ∈ J, w.weight l * (q l).weight a) /
            (∑ l ∈ J, w.weight l * ref.weight a)) := by
      have e := Finset.sum_mul J w.weight (ref.weight a)
      rw [← e, Finset.sum_mul]
    _ ≤ ∑ l ∈ J, (w.weight l * (q l).weight a) *
        Real.log ((w.weight l * (q l).weight a) / (w.weight l * ref.weight a)) :=
      Real.sum_mul_log_div_leq (fun l _ => mul_nonneg (w.nonneg l) ((q l).nonneg a))
        (fun l _ => mul_nonneg (w.nonneg l) (ref.nonneg a)) (fun l _ h => by
          rcases mul_eq_zero.mp h with hh | hh
          · simp [hh]
          · simp [ac l a hh])
    _ = _ := by
      apply Finset.sum_congr rfl
      intro l _
      by_cases h : w.weight l = 0
      · simp [h]
      · rw [mul_div_mul_left _ _ h, mul_assoc]

def jointInformation (w : InputLaw L) (q : L → InputLaw A) (ref : InputLaw A) : ℝ :=
  ∑ l, w.weight l * kl (q l).weight ref.weight

theorem jointInformation_eq (w : InputLaw L) (q : L → InputLaw A) (ref : InputLaw A) :
    jointInformation w q ref = ∑ l, w.weight l * kl (q l).weight ref.weight := rfl

def marginal (w : InputLaw L) (q : L → InputLaw A) : InputLaw A where
  weight a := ∑ l, w.weight l * (q l).weight a
  nonneg a := Finset.sum_nonneg fun l _ => mul_nonneg (w.nonneg l) ((q l).nonneg a)
  total := by
    rw [Finset.sum_comm]
    simp_rw [← Finset.mul_sum, InputLaw.total, mul_one]
    exact w.total

def mutualInformationBits (w : InputLaw L) (q : L → InputLaw A) : ℝ :=
  jointInformation w q (marginal w q) / Real.log 2

end
end DisjointnessFoundations.InformationLoss
