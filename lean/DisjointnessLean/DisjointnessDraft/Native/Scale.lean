import DisjointnessDraft.Native.EpochGeometry
import DisjointnessFoundations.PolylogarithmicRegime

/-! Uniform asymptotic bounds used at the two ends of the native communication
contradiction. All logarithms in the trade-off use base two. -/
namespace DisjointnessDraft.Native
open DisjointnessFoundations Filter Real
noncomputable section

theorem log_le_native {ℓ g n : ℕ} (hl : 0<ℓ) (hg : 2≤g) (fit : occupied ℓ g≤n) :
    (ℓ:ℝ)≤logb 2 n := by
  have low := (occupied_low (g:=g) hl).trans fit
  have h := logb_le_logb_of_le (b:=2) (by norm_num) (by positivity : (0:ℝ)<(g:ℝ)^(4*ℓ))
    (by exact_mod_cast low : (g:ℝ)^(4*ℓ)≤n)
  have one : (1:ℝ)≤logb 2 g := by
    simpa using logb_le_logb_of_le (b:=2) (by norm_num) (by norm_num : (0:ℝ)<2) (by exact_mod_cast hg : (2:ℝ)≤g)
  rw [logb_pow] at h; push_cast at h
  have p := mul_le_mul_of_nonneg_left one (by positivity : (0:ℝ)≤4*ℓ)
  linarith

theorem scale (lo : ℝ) (lp : 0<lo) : ∀ᶠ n : ℕ in atTop, ∀ ℓ g : ℕ,
    0<ℓ → 2≤g → occupied ℓ g≤n → lo*logb 2 n≤g → 2*(ℓ+1)≤g^4 := by
  filter_upwards [Tradeoff.log_tends.eventually_ge_atTop ((4/lo+4)/lo)] with n hn
  intro ℓ g hl hg fit word
  have bound := log_le_native hl hg fit
  have gp : (2:ℝ)≤g := by exact_mod_cast hg
  have big : 4/lo+4≤(g:ℝ) :=
    ((div_le_iff₀ lp).mp hn).trans (by simpa [mul_comm] using word)
  have product := (div_le_iff₀ lp).mp (show 4/lo≤(g:ℝ) by linarith)
  have ell : (ℓ:ℝ)*lo≤g := (mul_le_mul_of_nonneg_right bound lp.le).trans (by simpa [mul_comm] using word)
  have H : 4*(ℓ:ℝ)≤(g:ℝ)^2 := by
    have x := mul_le_mul_of_nonneg_left product (Nat.cast_nonneg ℓ)
    have y := mul_le_mul_of_nonneg_left ell (Nat.cast_nonneg g)
    nlinarith only [x,y]
  have powle : (g:ℝ)^2 ≤ (g:ℝ)^4 := pow_le_pow_right₀ (by linarith) (by norm_num)
  have one : (1:ℝ)≤ℓ := by exact_mod_cast hl
  exact_mod_cast (show 2*((ℓ:ℝ)+1)≤(g:ℝ)^4 by linarith)

theorem lower_acceptance : ∀ᶠ n : ℕ in atTop, ∀ (ℓ g : ℕ) (τ ρ : ℝ),
    0<ℓ → 2560≤g → occupied ℓ g≤n → 0≤τ → τ≤(ℓ:ℝ)/64 →
    (1/8:ℝ)*((1/(1280*(g:ℝ)))^(8*τ))-exp (-(n:ℝ)^(1/4:ℝ)/3)≤ρ → (n:ℝ)^(-(1/6):ℝ)≤ρ := by
  have grow (d : ℝ) (p : 0<d) (c : ℝ) : ∀ᶠ n : ℕ in atTop,c≤(n:ℝ)^d :=
    (tendsto_rpow_atTop p).comp tendsto_natCast_atTop_atTop |>.eventually_ge_atTop c
  filter_upwards [grow (1/6-1/16) (by norm_num) 16,grow (1/4-1/6) (by norm_num) 3,eventually_ge_atTop 1] with n a b hp
  intro ℓ g τ ρ hl hg fit nn low acc
  have np : (0:ℝ)<n := by exact_mod_cast hp
  have gp : (0:ℝ)<g := by exact_mod_cast (by omega : 0<g)
  have g1 : (1:ℝ)≤g := by exact_mod_cast (by omega : 1≤g)
  have g1280 : (1280:ℝ)≤g := by exact_mod_cast (by omega : 1280≤g)
  have base : 1280*(g:ℝ)≤(g:ℝ)^2 := by nlinarith only [mul_le_mul_of_nonneg_right g1280 gp.le]
  have lg := (occupied_low (g:=g) hl).trans fit
  have upper : (1280*(g:ℝ))^(8*τ)≤(n:ℝ)^(1/16:ℝ) := calc
    _ ≤ ((g:ℝ)^2)^(8*τ) := rpow_le_rpow (by positivity) base (by linarith)
    _ = (g:ℝ)^(2*(8*τ)) := by rw [←rpow_natCast_mul gp.le]; norm_num
    _ ≤ (g:ℝ)^((4*(ℓ:ℝ))*(1/16)) := rpow_le_rpow_of_exponent_le g1 (by linarith)
    _ = ((g:ℝ)^(4*ℓ))^(1/16:ℝ) := by rw [←rpow_natCast_mul gp.le]; push_cast; rfl
    _ ≤ _ := rpow_le_rpow (by positivity) (by exact_mod_cast lg) (by norm_num)
  have sampling := inv_anti₀ (rpow_pos_of_pos (by positivity : 0<1280*(g:ℝ)) _) upper
  rw [show (1/(1280*(g:ℝ)))^(8*τ)=((1280*(g:ℝ))^(8*τ))⁻¹ by rw [one_div,inv_rpow (by positivity)]] at acc
  have A := mul_le_mul_of_nonneg_right a (rpow_nonneg np.le (-(1/6):ℝ))
  rw [← rpow_add np] at A
  have B := mul_le_mul_of_nonneg_right b (rpow_nonneg np.le (1/6:ℝ))
  rw [← rpow_add np] at B
  norm_num at A B
  have tail : exp (-(n:ℝ)^(1/4:ℝ)/3)≤(n:ℝ)^(-(1/6):ℝ) := by
    rw [neg_div,exp_neg,rpow_neg np.le]
    apply inv_anti₀ (rpow_pos_of_pos np _)
    linarith only [B,Real.add_one_le_exp ((n:ℝ)^(1/4:ℝ)/3)]
  rw [←rpow_neg np.le] at sampling
  linarith only [acc,sampling,tail,A]

end
end DisjointnessDraft.Native
