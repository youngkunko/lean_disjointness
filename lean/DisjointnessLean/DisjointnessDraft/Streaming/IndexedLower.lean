import DisjointnessDraft.Streaming.IndexedPositive
import DisjointnessDraft.Transfer.Lower

/-! Worst-case probe lower bound per bit for an arbitrary tape-dependent
binary streaming machine, including free access to the absolute bit number. -/
namespace DisjointnessDraft.Streaming.Binary.Indexed
open DisjointnessFoundations Transfer.Compiler Filter Real MeasureTheory Classical
noncomputable section

theorem lower (lo hi : ℝ) (lp : 0<lo) (hh : lo≤hi) :
    ∃ c : ℝ,0<c ∧ ∀ᶠ n : ℕ in atTop,∀ (C : Code (Symbol n n) (width n)) (w t : ℕ),
      1≤t → lo*logb 2 (maximum C)≤w → (w:ℝ)≤hi*logb 2 (maximum C) →
      ∀ (Ω : Type) (D : Machine w Ω) (seed : Ω),Correct D seed C → Budget D seed C t →
      c*logb 2 (maximum C)/(logb 2 (logb 2 (maximum C)))^2≤t := by
  obtain ⟨d,dp,raw⟩ := Transfer.Compiler.lower lo hi lp hh 1 1 6 (by norm_num)
  refine ⟨d/2,by positivity,?_⟩
  filter_upwards [raw,eventually_ge_atTop 7,Tradeoff.log_tends.eventually_ge_atTop 2] with n key h7 ll
  intro C w t t1 wl wh Ω D seed correct budget
  let N := maximum C
  let M := maxLength n
  have r := max_range h7 C
  have nM : n≤M := by have := (quadratic (show 1≤n by omega)).1; change n≤maxLength n; nlinarith
  have mpos : (0:ℝ)<M := by exact_mod_cast (show 0<M by omega)
  have nN : n≤N := nM.trans r.1
  have logs := log_sizes h7
  have MN : logb 2 M≤logb 2 N := logb_le_logb_of_le (by norm_num) mpos (by exact_mod_cast r.1)
  have NM := logb_le_logb_of_le (b:=2) (by norm_num) (mpos.trans_le (by exact_mod_cast r.1 : (M:ℝ)≤N))
    (show (N:ℝ)≤(M:ℝ)^2 by exact_mod_cast r.2.1)
  rw [logb_pow] at NM
  have Nn : logb 2 N≤6*logb 2 n := calc
    _ ≤ (2:ℝ)*logb 2 M := by simpa using NM
    _ ≤ 2*(3*logb 2 n) := mul_le_mul_of_nonneg_left logs.2 (by norm_num)
    _ = _ := by ring
  have bp : 0<width n := by unfold width; omega
  have bt : 1≤width n*t := Nat.mul_pos bp t1
  have H := (key N w (width n*t) nN Nn bt wl wh _ _ _ _ Unit (Measure.dirac ()) (plan n)
    (target D seed C) (fun _ _ => True) (spec C) false (width n*t:ℕ) (by exact_mod_cast bt)
    (guarantees D seed C bp t correct budget) (valid C bp) (by simp [plan]) (by simp [plan]) (by simp [plan])).2
  simp only [max_self,Nat.cast_mul] at H
  have wid : (width n:ℝ)≤2*logb 2 N := r.2.2.trans (by linarith only [MN])
  have g : 2≤logb 2 N := ll.trans (logs.1.trans MN)
  have L : 0<logb 2 N := by linarith
  have P : 0<logb 2 (logb 2 N) := logb_pos (by norm_num) (by linarith)
  change d*(logb 2 N/logb 2 (logb 2 N))^2≤(width n:ℝ)*t at H
  have top := H.trans (mul_le_mul_of_nonneg_right wid (Nat.cast_nonneg (α:=ℝ) t))
  rw [div_pow] at top
  have square : d*(logb 2 N)^2≤(2*logb 2 N*t)*(logb 2 (logb 2 N))^2 :=
    (div_le_iff₀ (by positivity)).mp (by simpa [mul_div_assoc'] using top)
  have line : d*logb 2 N≤2*t*(logb 2 (logb 2 N))^2 := by
    apply le_of_mul_le_mul_left (a:=logb 2 N) _ L
    linarith only [square]
  apply (div_le_iff₀ (by positivity : 0<(logb 2 (logb 2 N))^2)).mpr
  linarith only [line]

/-- Worst-case zero-error promises over arbitrary nonempty spaces of master tapes. -/
theorem uniform_lower (lo hi : ℝ) (lp : 0<lo) (hh : lo≤hi) :
    ∃ c : ℝ,0<c ∧ ∀ᶠ n : ℕ in atTop,∀ (C : Code (Symbol n n) (width n)) (w t : ℕ),
      lo*logb 2 (maximum C)≤w → (w:ℝ)≤hi*logb 2 (maximum C) →
      ∀ (Ω : Type) [Nonempty Ω] (D : Machine w Ω),(∀seed,Correct D seed C) → (∀seed,Budget D seed C t) →
      c*logb 2 (maximum C)/(logb 2 (logb 2 (maximum C)))^2≤t := by
  obtain ⟨c,p,e⟩ := lower lo hi lp hh
  refine ⟨c,p,?_⟩
  filter_upwards [e,eventually_ge_atTop 1] with n h np
  intro C w t wl wh Ω ne D correct budget
  let s := Classical.choice ne
  have tp := positive_budget D s C np (by unfold width; omega) t (correct s) (budget s)
  exact h C w t tp wl wh Ω D s (correct s) (budget s)
end
end DisjointnessDraft.Streaming.Binary.Indexed
