import DisjointnessDraft.Streaming.BitMachine
import DisjointnessDraft.Streaming.Lower
import Mathlib.Data.Nat.Log

/-! The weaker binary-alphabet lower bound uses the actual maximum length of
the substituted expressions. -/
namespace DisjointnessDraft.Streaming.Binary
open DisjointnessFoundations Real Filter MeasureTheory RegularExpression
open scoped ENNReal
noncomputable section
open Classical

abbrev width (n : ℕ) := Nat.log2 (n+n+1)+1
def canonical (n : ℕ) : Code (Symbol n n) (width n) := (exists_code n n).some

def maximum (C : Code (Symbol n n) b) := Finset.univ.sup (fun f : Family n => nodes (substitute C.bits (expression f)))

private theorem growth (code : α → List Bool) (P : RegularExpression α) :
    nodes P≤nodes (substitute code P) := by
  have lit : ∀ xs,1≤nodes (literal xs) := by
    rintro (_|⟨x,_|⟨y,ys⟩⟩) <;> simp [literal,nodes]
  induction P with
  | zero | epsilon => rfl
  | char a => exact lit _
  | plus _ _ a b | comp _ _ a b => exact Nat.add_le_add_right (Nat.add_le_add a b) 1
  | star _ ih => exact Nat.add_le_add_right ih 1

theorem max_range {n : ℕ} (h : 7≤n) (C : Code (Symbol n n) (width n)) :
    maxLength n≤maximum C ∧ maximum C≤(maxLength n)^2 ∧ (width n:ℝ)≤2*logb 2 (maxLength n) := by
  have hn : 1≤n := by omega
  let M := maxLength n
  have n2 : n^2≤M := (quadratic hn).1
  have bn : width n≤n+n+2 := by have := Nat.log2_le_self (n+n+1); dsimp [width]; omega
  have room : 2*width n ≤ M := by nlinarith only [n2,bn,Nat.mul_le_mul_left n h,h]
  have A : n+n+1≤M := by nlinarith only [n2,Nat.mul_le_mul_left n h,h]
  have lower : M≤maximum C := (growth C.bits (expression (fun _ : Fin n => (∅ : Finset (Fin n))))).trans
    (Finset.le_sup (f:=fun f : Family n => nodes (substitute C.bits (expression f))) (Finset.mem_univ _))
  have size : maximum C≤M^2 := by
    apply Finset.sup_le
    intro f _
    exact (binary_size C (by unfold width; omega) _).trans
      ((Nat.mul_le_mul room (Streaming.maximum hn f).1).trans_eq (pow_two M).symm)
  have lg : (Nat.log2 (n+n+1) : ℝ)≤logb 2 M := by
    have pow := Nat.pow_log_le_self 2 (show n+n+1≠0 by omega)
    rw [←Nat.log2_eq_log_two] at pow
    have H := logb_le_logb_of_le (b:=2) (by norm_num) (show 0<(2:ℝ)^(Nat.log2 (n+n+1)) by positivity)
      (show (2:ℝ)^(Nat.log2 (n+n+1))≤M by exact_mod_cast pow.trans A)
    simpa [Real.logb_pow] using H
  have L : 1≤logb 2 M := by
    have h' := logb_le_logb_of_le (b:=2) (by norm_num) (by norm_num : (0:ℝ)<2)
      (show (2:ℝ)≤M by exact_mod_cast (show 2≤M by omega))
    simpa using h'
  exact ⟨lower,size,by unfold width; push_cast; linarith⟩

/-- Worst-case bit cost on every binary stream of a fixed-width code.
The operation program can be obtained by truncating any bounded read/write
machine, preserving its exact answer, cost and final memory. -/
theorem lower (lo hi : ℝ) (lp : 0<lo) (hh : lo≤hi) :
    ∃ c : ℝ, 0<c ∧ ∀ᶠ n : ℕ in atTop, ∀ (C : Code (Symbol n n) (width n)) (w t : ℕ),
    1≤t → lo*logb 2 (maximum C)≤w → (w:ℝ)≤hi*logb 2 (maximum C) →
    ∀ D : BitMachine w, BitCorrect D C → BitBudget D C t →
    c*logb 2 (maximum C)/(logb 2 (logb 2 (maximum C)))^2≤t := by
  obtain ⟨d,dp,lb⟩ := some_symbol lo (2*hi) lp (by linarith)
  refine ⟨d/4,by positivity,?_⟩
  filter_upwards [lb,eventually_ge_atTop 7,Tradeoff.log_tends.eventually_ge_atTop 2] with n lb hn ll
  intro C w t tp wl wu D good cheap
  obtain ⟨a,upper,bound⟩ := max_range hn C
  let M := maxLength n
  let B := maximum C
  have mp : (0:ℝ)<M := by exact_mod_cast (show 0<M by
    have := (quadratic (by omega : 1≤n)).1; dsimp [M]; nlinarith)
  have l := logb_le_logb_of_le (b:=2) (by norm_num) mp (show (M:ℝ)≤B by exact_mod_cast a)
  have u := logb_le_logb_of_le (b:=2) (by norm_num) (mp.trans_le (by exact_mod_cast a))
    (show (B:ℝ)≤(M:ℝ)^2 by exact_mod_cast upper)
  rw [logb_pow] at u
  have g : 2≤logb 2 M := ll.trans (log_sizes hn).1
  have gp : 0<logb 2 M := by linarith
  have gl : 0<logb 2 (logb 2 M) := logb_pos (by norm_num) (by linarith)
  have dl := logb_le_logb_of_le (b:=2) (by norm_num) gp l
  have ratio : logb 2 B/(logb 2 (logb 2 B))^2 ≤ 2*logb 2 M/(logb 2 (logb 2 M))^2 :=
    div_le_div₀ (by positivity) (by simpa using u) (by positivity)
      (pow_le_pow_left₀ gl.le dl 2)
  have hwidth : 0<width n := by unfold width; omega
  have pos := Nat.mul_pos hwidth tp
  obtain ⟨meas,z,hu,hq⟩ := implements D C hwidth good cheap
  have H := lb w (width n*t) pos ((mul_le_mul_of_nonneg_left l lp.le).trans wl)
    (wu.trans ((mul_le_mul_of_nonneg_left (by simpa using u) (lp.le.trans hh)).trans_eq (by ring)))
    Unit Unit (Measure.dirac ()) (combined D C) tape ((width n:ℝ)*t) (by exact_mod_cast pos) meas z hu hq
  simp only [Nat.cast_mul,max_self] at H
  change d*(logb 2 M/logb 2 (logb 2 M))^2≤(width n:ℝ)*t at H
  have b := mul_le_mul_of_nonneg_right bound (Nat.cast_nonneg (α:=ℝ) t)
  change (width n:ℝ)*t≤2*logb 2 M*t at b
  rw [div_pow] at H
  have H' : d*(logb 2 M)^2 ≤ (2*logb 2 M*t)*(logb 2 (logb 2 M))^2 :=
    (div_le_iff₀ (by positivity)).mp (by simpa [mul_div_assoc'] using H.trans b)
  have one : d*(logb 2 M) ≤ 2*t*(logb 2 (logb 2 M))^2 := by
    apply le_of_mul_le_mul_left (a:=logb 2 M) _ gp
    nlinarith only [H']
  have mv := mul_le_mul_of_nonneg_left ratio (show 0≤d/4 by positivity)
  change d/4*logb 2 B/(logb 2 (logb 2 B))^2 ≤ _
  rw [mul_div_assoc]
  apply mv.trans
  rw [←mul_div_assoc,div_le_iff₀ (by positivity)]
  linarith only [one]

end
end DisjointnessDraft.Streaming.Binary
