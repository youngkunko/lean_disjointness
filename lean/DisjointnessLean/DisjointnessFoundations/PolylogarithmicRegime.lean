import DisjointnessFoundations.GeometricEpochEstimates
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

namespace DisjointnessFoundations.FinalBounds

open Filter Asymptotics Real
open scoped Topology
noncomputable section

theorem polylog_budget (C : ℝ) : ∀ᶠ n : ℝ in atTop,
    C*(logb 2 n)^3 ≤ n^(1/50:ℝ) := by
  have base := isLittleO_log_rpow_atTop (show (0:ℝ)<1/150 by norm_num)
  have cube := base.pow (n:=3) (by decide)
  have scaled := cube.const_mul_left (C / (log 2)^3)
  filter_upwards [scaled.bound (show (0:ℝ)<1 by norm_num), eventually_ge_atTop (0:ℝ)] with x h hx
  have eq : (x^(1/150:ℝ))^3 = x^(1/50:ℝ) := by rw [←rpow_mul_natCast hx]; norm_num
  simp only [eq, one_mul, Real.norm_eq_abs, abs_of_nonneg (rpow_nonneg hx _)] at h
  calc C*(logb 2 x)^3 = (C/(log 2)^3)*(log x)^3 := by rw [logb,div_pow]; ring
       _ ≤ |(C/(log 2)^3)*(log x)^3| := le_abs_self _
       _ ≤ _ := by simpa [Real.norm_eq_abs] using h

end
end DisjointnessFoundations.FinalBounds
