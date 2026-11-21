import DisjointnessDraft.Streaming.Machine
import DisjointnessDraft.Streaming.Size
import DisjointnessDraft.Maximum
import DisjointnessDraft.Native.Main
import DisjointnessFoundations.PolynomialScaleComparison

/-! Both streaming lower bounds on the maximum expression length in the family. -/
namespace DisjointnessDraft.Streaming
open DisjointnessFoundations CellProbe Real Filter MeasureTheory
open scoped ENNReal
noncomputable section

theorem log_sizes {n : ℕ} (hn : 7≤n) : logb 2 n ≤ logb 2 (maxLength n) ∧
    logb 2 (maxLength n) ≤ 3*logb 2 n := by
  obtain ⟨low,up⟩ := quadratic (show 1≤n by omega)
  apply ApplicationSizes.log_range (by omega) ((Nat.le_self_pow (by decide : 2≠0) n).trans low)
  exact up.trans (by nlinarith only [Nat.mul_le_mul_right (n^2) hn])

theorem selector_lower (lo hi : ℝ) (lp : 0<lo) (hh : lo≤hi) :
    ∃ c : ℝ, 0<c ∧ ∀ᶠ n : ℕ in atTop, ∀ w ta : ℕ, 1≤ta →
    lo*logb 2 (maxLength n)≤w → (w:ℝ)≤hi*logb 2 (maxLength n) →
    ∀ (Ω C : Type) [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
      (E : Engine n n w C) (R : RandomTape Ω C) (tc : ℝ), 1≤tc →
    MeasurableRuns (process E) R → ZeroError (process E) R reports → DataBound E R ta →
    SelectorBound μ E R tc → c*(Tradeoff.ratio (maxLength n) w ta)^2 ≤ tc := by
  obtain ⟨d,dp,lb⟩ := Native.main lo (3*hi) lp (by linarith)
  refine ⟨d/9,by positivity,?_⟩
  filter_upwards [lb,eventually_ge_atTop 7,Tradeoff.log_tends.eventually_ge_atTop (2/lo)] with n h hn strong
  intro w ta ta1 wl wu Ω C _ μ _ E R tc tc1 hm hz hu hq
  obtain ⟨l,u⟩ := log_sizes hn
  have mid := (mul_le_mul_of_nonneg_left l lp.le).trans wl
  have two := (div_le_iff₀ lp).mp strong
  have w2 : (2:ℝ)≤w := by linarith
  have tap : (1:ℝ)≤ta := by exact_mod_cast ta1
  have den : 0<logb 2 ((ta:ℝ)*w) :=
    logb_pos (by norm_num) (by nlinarith only [mul_le_mul_of_nonneg_right tap (Nat.cast_nonneg (α:=ℝ) w),w2])
  have nonneg : 0≤Tradeoff.ratio (maxLength n) w ta := div_nonneg
    (logb_nonneg (by norm_num) (by exact_mod_cast (show 1≤maxLength n from
      (one_le_pow₀ (by omega : 1≤n)).trans (quadratic (by omega : 1≤n)).1))) den.le
  have comparison : Tradeoff.ratio (maxLength n) w ta ≤ 3*Tradeoff.ratio n w ta := by
    unfold Tradeoff.ratio
    rw [mul_div_assoc']
    exact div_le_div_of_nonneg_right u den.le
  have square := pow_le_pow_left₀ nonneg comparison 2
  obtain ⟨A,ma,ze,wa,qa⟩ := transfer μ E R ta tc hm hz hu hq
  have hb := h w ta ta1 mid (wu.trans ((mul_le_mul_of_nonneg_left u (lp.le.trans hh)).trans_eq (by ring)))
    Ω (ℕ×Ω) μ A (Padding.tape Ω) tc tc1 ma ze wa qa
  nlinarith only [mul_le_mul_of_nonneg_left square dp.le,hb]

theorem some_symbol (lo hi : ℝ) (lp : 0<lo) (hh : lo≤hi) :
    ∃ c : ℝ, 0<c ∧ ∀ᶠ n : ℕ in atTop, ∀ w ta : ℕ, 1≤ta →
    lo*logb 2 (maxLength n)≤w → (w:ℝ)≤hi*logb 2 (maxLength n) →
    ∀ (Ω C : Type) [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
      (E : Engine n n w C) (R : RandomTape Ω C) (tc : ℝ), 1≤tc →
    MeasurableRuns (process E) R → ZeroError (process E) R reports → DataBound E R ta →
    SelectorBound μ E R tc → c*(FixedFamilySizes.logRatio (maxLength n))^2 ≤ max (ta:ℝ) tc := by
  obtain ⟨d,dp,lb⟩ := selector_lower lo hi lp hh
  refine ⟨min 1 (d/16),lt_min (by norm_num) (by positivity),?_⟩
  filter_upwards [lb,eventually_ge_atTop 7,Tradeoff.log_tends.eventually_ge_atTop 2,
    Tradeoff.log_tends.eventually_ge_atTop hi,Tradeoff.log_tends.eventually_ge_atTop (2/lo)] with n h hn big bigh strong
  intro w ta ta1 wl wu Ω C _ μ _ E R tc tc1 hm hz hu hq
  have lower := (log_sizes hn).1
  have two := (div_le_iff₀ lp).mp strong
  have mid := (mul_le_mul_of_nonneg_left lower lp.le).trans wl
  have w2 : 2≤w := by exact_mod_cast (show (2:ℝ)≤w by linarith)
  exact max_from_tradeoff dp ta1 w2 (big.trans lower) (bigh.trans lower) wu
    (h w ta ta1 wl wu Ω C μ E R tc tc1 hm hz hu hq)

end
end DisjointnessDraft.Streaming
