import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Fintype.Pi
import Mathlib.Tactic.Ring

namespace DisjointnessFoundations.FiniteSampling

open scoped BigOperators
noncomputable section

def coinMean (p : ℝ) (f : Bool → ℝ) : ℝ := p*f true + (1-p)*f false

/-- The expectation over the product Bernoulli law on full length-`n` masks. -/
def bitMean (p : ℝ) (n : Nat) (f : List Bool → ℝ) : ℝ :=
  ∑ b : Fin n → Bool, (∏ i, if b i then p else 1-p) * f (List.ofFn b)

theorem totalWeights (p : ℝ) (n : ℕ) :
    (∑ b : Fin n → Bool, ∏ i, if b i then p else 1-p) = 1 := by
  rw [← Fintype.prod_sum (fun (_ : Fin n) (b : Bool) => if b then p else 1-p)]
  simp [Fintype.sum_bool]

theorem bitMean_const (p c : ℝ) (n : Nat) :
    bitMean p n (fun _ => c) = c := by
  rw [bitMean, ← Finset.sum_mul, totalWeights, one_mul]

theorem bitMean_congr (p : ℝ) (n : Nat) (f g : List Bool → ℝ)
    (agree : ∀ s, s.length = n → f s = g s) : bitMean p n f = bitMean p n g := by
  apply Finset.sum_congr rfl
  intro b _
  rw [agree _ List.length_ofFn]

theorem bitMean_scale (p c : ℝ) (n : Nat) (f : List Bool → ℝ) :
    bitMean p n (fun s => c * f s) = c * bitMean p n f := by
  simp only [bitMean, Finset.mul_sum]
  exact Finset.sum_congr rfl (fun _ _ => by ring)

structure InputLaw (X : Type*) [Fintype X] where
  weight : X → ℝ
  nonneg : ∀ x, 0 ≤ weight x
  total : ∑ x, weight x = 1

structure SamplingRate where
  p : ℝ
  positive : 0 < p
  le_one : p ≤ 1

theorem weight_nonneg (r : SamplingRate) (b : Fin n → Bool) :
    0 ≤ (∏ i, if b i then r.p else 1-r.p) := by
  apply Finset.prod_nonneg
  intro i _
  split
  · exact r.positive.le
  · exact sub_nonneg.mpr r.le_one

end
end DisjointnessFoundations.FiniteSampling
