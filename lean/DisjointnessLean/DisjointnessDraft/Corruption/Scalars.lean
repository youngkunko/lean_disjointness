import DisjointnessDraft.Corruption.Counting
import Mathlib.Data.Complex.ExponentialBounds

/-! Numerical margins in the sparse-set bound, for the constants 1/40,
1/100, and the manuscript's lower threshold s ≥ 200. -/
namespace DisjointnessDraft.Corruption
open Finset Real
open scoped BigOperators
noncomputable section

def capFactor (s : ℕ) : ℝ := (2:ℝ)^((s:ℝ)/40)
def half (s : ℕ) := (s+1)/2
def groups (s : ℕ) := s/6
theorem cap_pos (s : ℕ) : 0<capFactor s := Real.rpow_pos_of_pos (by norm_num) _

theorem small_tail {s : ℕ} (hs : 200≤s) :
    capFactor s * (2:ℝ)^s * (1/6:ℝ)^(half s) < 1/2 := by
  have two : (0:ℝ)<2 := by norm_num
  have six : (0:ℝ)<6 := by norm_num
  have log2 := log_pos (by norm_num : (1:ℝ)<2)
  have comp := log_le_log (by norm_num : (0:ℝ)<2^5) (by norm_num : (2:ℝ)^5≤6^2)
  simp only [Real.log_pow] at comp
  have hk : s ≤ 2*half s := by unfold half; omega
  have hk' : (s:ℝ) ≤ 2*half s := by exact_mod_cast hk
  have hS : (200:ℝ) ≤ s := by exact_mod_cast hs
  have one : s+(s:ℝ)/40+1 < (5:ℝ)/2*half s := by linarith
  have ls : log 2 * (s+(s:ℝ)/40+1) < log 6 * (half s) := by
    apply (mul_lt_mul_of_pos_left one log2).trans_le
    have t : log 2*(5/2:ℝ)≤log 6 := by norm_num at comp; linarith
    nlinarith only [mul_le_mul_of_nonneg_right t (Nat.cast_nonneg (half s))]
  apply (Real.log_lt_log_iff (by unfold capFactor; positivity) (by norm_num)).mp
  rw [Real.log_mul (mul_pos (cap_pos s) (pow_pos two s)).ne' (by positivity), Real.log_mul (cap_pos _).ne' (by positivity)]
  simp only [capFactor,Real.log_rpow two,Real.log_pow,one_div,Real.log_inv]
  linarith only [ls]

theorem column_margin {s : ℕ} (hs : 200≤s) :
    capFactor s*exp (-(groups s:ℝ)/6) < exp (-(Real.log 2)*(groups s:ℝ)/50) := by
  have low : s≤6*groups s+5 := by unfold groups; omega
  have rl : (s:ℝ)≤6*groups s+5 := by exact_mod_cast low
  have gs : 33≤groups s := by unfold groups; omega
  have gr : (33:ℝ)≤groups s := by exact_mod_cast gs
  have l2 : log 2 < 3/4 := by linarith [log_two_lt_d9]
  rw [capFactor,Real.rpow_def_of_pos (by norm_num),←Real.exp_add,Real.exp_lt_exp]
  have x : 0<(s:ℝ)/40+(groups s:ℝ)/50 := by positivity
  nlinarith only [mul_lt_mul_of_pos_right l2 x,rl,gr]

theorem mask_decay {r g : ℕ} (hr : 0<r) {a : ℝ} (ha : 1/(2*(r:ℝ))≤a) :
    ((1+exp (-a))/2)^(r*g) ≤ exp (-(g:ℝ)/6) := by
  have p : (0:ℝ)<r := by exact_mod_cast hr
  have one : 1≤(r:ℝ) := by exact_mod_cast hr
  have hE : (1+1/(2*(r:ℝ))) ≤ exp a := by linarith [Real.add_one_le_exp a]
  have inv : exp (-a) ≤ 1/(1+1/(2*(r:ℝ))) := by
    rw [Real.exp_neg,←one_div]; exact one_div_le_one_div_of_le (by positivity) hE
  have drop : 1/(1+1/(2*(r:ℝ))) ≤ 1-1/(3*(r:ℝ)) := by
    rw [div_le_iff₀ (by positivity : 0<1+1/(2*(r:ℝ)))]
    field_simp
    rw [le_div_iff₀ (by positivity)]
    nlinarith
  have c : (1+exp (-a))/2 ≤ exp (-1/(6*(r:ℝ))) := by
    have U := inv.trans drop
    have T := Real.add_one_le_exp (-1/(6*(r:ℝ)))
    apply le_trans _ T
    calc _ ≤ (1+(1-1/(3*(r:ℝ))))/2 := by linarith only [U]
         _ = _ := by field_simp; ring
  calc _ ≤ (exp (-1/(6*(r:ℝ))))^(r*g) := pow_le_pow_left₀ (by positivity) c _
       _ = _ := by rw [←Real.exp_nat_mul]; congr 1; push_cast; field_simp; ring

end
end DisjointnessDraft.Corruption
