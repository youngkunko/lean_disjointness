import DisjointnessDraft.Model
import DisjointnessFoundations.BalancedOperationScale

/-! The maximum-operation corollary, with the word-width constant tracked. -/
namespace DisjointnessDraft
open DisjointnessFoundations CellProbe MeasureTheory Real Filter
open scoped ENNReal
noncomputable section

theorem max_from_tradeoff {n w tu : ℕ} {tq c hi : ℝ} (cp : 0<c) (T : 1≤tu) (W : 2≤w)
    (S2 : 2≤logb 2 (n:ℝ)) (H : hi≤logb 2 (n:ℝ)) (wh : (w:ℝ)≤hi*logb 2 n)
    (bound : c*(Tradeoff.ratio n w tu)^2≤tq) :
    min 1 (c/16)*(FixedFamilySizes.logRatio n)^2≤max (tu:ℝ) tq := by
  let S := logb 2 (n:ℝ)
  let L := logb 2 S
  have sp : 0<S := by change 2≤S at S2; linarith
  have L1 : 1≤L := by simpa [L] using logb_le_logb_of_le (b:=2) (by norm_num) (by norm_num : (0:ℝ)<2) S2
  have lp : 0<L := by linarith
  have rpos : 0≤FixedFamilySizes.logRatio n := div_nonneg sp.le lp.le
  by_cases large : S^2≤(tu:ℝ)
  · have leS : FixedFamilySizes.logRatio n≤S := (div_le_iff₀ lp).mpr (by simpa using mul_le_mul_of_nonneg_left L1 sp.le)
    calc _ ≤ 1*(FixedFamilySizes.logRatio n)^2 := mul_le_mul_of_nonneg_right (min_le_left _ _) (sq_nonneg _)
         _ ≤ S^2 := by simpa using pow_le_pow_left₀ rpos leS 2
         _ ≤ (tu:ℝ) := large
         _ ≤ _ := le_max_left _ _
  · have two : (2:ℝ)≤tu*w := (by exact_mod_cast W : (2:ℝ)≤w).trans
      (by simpa using mul_le_mul_of_nonneg_right (show (1:ℝ)≤tu by exact_mod_cast T) (Nat.cast_nonneg w))
    let A := logb 2 ((tu:ℝ)*w)
    have ap : 0<A := logb_pos (by norm_num) (by linarith)
    have product : (tu:ℝ)*w≤S^4 := by
      have a := mul_le_mul_of_nonneg_right H sp.le
      change (w:ℝ) ≤ hi*S at wh
      calc _ ≤ S^2*(S*S) := mul_le_mul (le_of_not_ge large) (wh.trans a) (Nat.cast_nonneg w) (sq_nonneg _)
           _ = _ := by ring
    have logUpper := logb_le_logb_of_le (b:=2) (by norm_num) (by linarith : (0:ℝ)<tu*w) product
    rw [logb_pow] at logUpper
    change A ≤ (4:ℝ)*L at logUpper
    have rle : FixedFamilySizes.logRatio n≤4*Tradeoff.ratio n w tu := by
      change S/L≤4*(S/A)
      rw [mul_div_assoc',div_le_div_iff₀ lp ap]
      nlinarith only [mul_le_mul_of_nonneg_left logUpper sp.le]
    have sq := pow_le_pow_left₀ rpos rle 2
    calc _ ≤ (c/16)*(FixedFamilySizes.logRatio n)^2 := mul_le_mul_of_nonneg_right (min_le_right _ _) (sq_nonneg _)
         _ ≤ (c/16)*(4*Tradeoff.ratio n w tu)^2 := mul_le_mul_of_nonneg_left sq (by positivity)
         _ = c*(Tradeoff.ratio n w tu)^2 := by ring
         _ ≤ tq := bound
         _ ≤ _ := le_max_right _ _

theorem maximum_of (bound : MainBound) (lo hi : ℝ) (lp : 0<lo) (lu : lo≤hi) :
    ∃ c : ℝ, 0<c ∧ ∀ᶠ n : ℕ in atTop, ∀ w tu : ℕ, 1≤tu →
    lo*logb 2 n≤w → (w:ℝ)≤hi*logb 2 n →
    ∀ (Ω C : Type) [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
      (D : Machine n w C) (R : RandomTape Ω C) (tq : ℝ),
      1≤tq → MeasurableRuns D R → ZeroError D R answer → WorstUpdate D R (tu:ℝ≥0∞) → QueryBound μ D R tq →
      c*(FixedFamilySizes.logRatio n)^2≤max (tu:ℝ) tq := by
  obtain ⟨d,dp,lower⟩ := bound lo hi lp lu
  refine ⟨min 1 (d/16),lt_min (by norm_num) (by positivity),?_⟩
  filter_upwards [lower,Tradeoff.log_tends.eventually_ge_atTop 2,Tradeoff.log_tends.eventually_ge_atTop hi,
    Tradeoff.log_tends.eventually_ge_atTop (2/lo)] with n lb S2 H big
  intro w tu tu1 wl wu Ω C _ μ _ D R tq tq1 hm zero worst qc
  have h := (div_le_iff₀ lp).mp big
  have w2 : 2≤w := by exact_mod_cast (show (2:ℝ)≤w by nlinarith only [h,wl])
  exact max_from_tradeoff dp tu1 w2 S2 H wu (lb w tu tu1 wl wu Ω C μ D R tq tq1 hm zero worst qc)


end
end DisjointnessDraft
