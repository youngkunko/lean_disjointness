import DisjointnessFoundations.FiniteBernoulliLaw
import Mathlib.Data.Complex.ExponentialBounds
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity

namespace DisjointnessFoundations.Acceptance

open FiniteSampling
open scoped BigOperators
noncomputable section
open Classical

variable {n : Nat}

theorem bitMean_mono (r : SamplingRate) (n : Nat) (f g : List Bool → ℝ)
    (h : ∀ s, s.length = n → f s ≤ g s) : bitMean r.p n f ≤ bitMean r.p n g := by
  apply Finset.sum_le_sum
  intro b _
  exact mul_le_mul_of_nonneg_left (h _ List.length_ofFn) (weight_nonneg r b)

theorem bitMean_add (p : ℝ) (n : Nat) (f g : List Bool → ℝ) :
    bitMean p n (fun s => f s + g s) = bitMean p n f + bitMean p n g := by
  simp [bitMean, mul_add, Finset.sum_add_distrib]

def sampledCount (C : Fin n → Bool) (s : List Bool) : Nat :=
  ∑ i : Fin n, if C i = true ∧ s[i.val]? = some true then 1 else 0

def population (C : Fin n → Bool) : Nat :=
  ∑ i : Fin n, if C i = true then 1 else 0

/-- At base two, each counted position contributes the factor `1 + p`. -/
theorem count_mgf (p : ℝ) (n : Nat) (C : Fin n → Bool) :
    bitMean p n (fun s => (2:ℝ) ^ sampledCount C s) = (1+p) ^ population C := by
  let f (i : Fin n) (b : Bool) : ℝ :=
    (if b then p else 1-p) * (2:ℝ)^(if C i = true ∧ b = true then (1:ℕ) else 0)
  have part (i : Fin n) : (∑ b : Bool, f i b) = (1+p)^(if C i = true then (1:ℕ) else 0) := by
    cases h : C i
    · simp [Fintype.sum_bool, f, h]
    · simp [Fintype.sum_bool, f, h]
      ring
  calc
    _ = ∑ b : Fin n → Bool, ∏ i, f i (b i) := by
      unfold bitMean
      apply Finset.sum_congr rfl
      intro b _
      simp only [sampledCount, List.getElem?_ofFn, Fin.is_lt, dif_pos, Option.some.injEq, Fin.eta,
        Finset.prod_pow_eq_pow_sum, f, Finset.prod_mul_distrib]
    _ = ∏ i, ∑ b, f i b := (Fintype.prod_sum f).symm
    _ = _ := by simp only [part, population, Finset.prod_pow_eq_pow_sum]

/-- Markov at base two bounds the upper tail by the moment generating function. -/
theorem sample_cap_tail (r : SamplingRate) (n : Nat) (C : Fin n → Bool)
    (bound : ℝ) (hC : (population C : ℝ) ≤ bound) :
    bitMean r.p n (fun s => if 2*r.p*bound < (sampledCount C s : ℝ) then 1 else 0) ≤
      Real.exp (-(r.p*bound)/3) := by
  let t := r.p*bound
  have t_nonneg : 0 ≤ t := mul_nonneg r.positive.le ((Nat.cast_nonneg _).trans hC)
  let a := Real.exp (-2*t*Real.log 2)
  have step (s : List Bool) :
      (if 2*r.p*bound < (sampledCount C s : ℝ) then (1:ℝ) else 0)
        ≤ a * (2:ℝ)^sampledCount C s := by
    split
    · rename_i h
      rw [← Real.rpow_natCast, Real.rpow_def_of_pos (by norm_num : (0:ℝ)<2)]
      rw [show (1:ℝ) = Real.exp 0 by simp, show a = Real.exp (-2*t*Real.log 2) by rfl,
        ← Real.exp_add]
      apply Real.exp_le_exp.mpr
      have h' : 2*t ≤ (sampledCount C s:ℝ) := by dsimp [t]; linarith
      have hl := mul_le_mul_of_nonneg_right h' (Real.log_nonneg (by norm_num : (1:ℝ)≤2))
      linarith
    · dsimp [a]; positivity
  have expand := bitMean_mono r n _ _ (fun s _ => step s)
  rw [bitMean_scale, count_mgf] at expand
  have mgf : (1+r.p)^population C ≤ Real.exp t := calc
    _ ≤ (Real.exp r.p)^population C := pow_le_pow_left₀ (by linarith [r.positive]) (by simpa [add_comm] using Real.add_one_le_exp r.p) _
    _ = Real.exp ((population C:ℝ)*r.p) := by rw [← Real.exp_nat_mul]
    _ ≤ _ := Real.exp_le_exp.mpr (by dsimp [t]; rw [mul_comm r.p]; exact mul_le_mul_of_nonneg_right hC r.positive.le)
  refine expand.trans ((mul_le_mul_of_nonneg_left mgf (Real.exp_pos _).le).trans ?_)
  change Real.exp (-2*t*Real.log 2)*Real.exp t ≤ Real.exp (-t/3)
  rw [←Real.exp_add]
  apply Real.exp_le_exp.mpr
  have log_bound : (2:ℝ)/3 ≤ Real.log 2 := by linarith [Real.log_two_gt_d9]
  have aux := mul_le_mul_of_nonneg_left log_bound t_nonneg
  linarith

end
end DisjointnessFoundations.Acceptance
