import DisjointnessDraft.Information.Asymptotics

/-! Uniform scalar inequalities for the named intermediate statements. -/
namespace DisjointnessDraft.Information
open Filter Real
open scoped Topology
noncomputable section

structure IntermediateBudgets (n s ub ab : ℕ) (ρ : ℝ) : Prop where
  query : ((ub+n*ab : ℕ):ℝ)/(n*ρ)≤(n:ℝ)^(1/5:ℝ)
  common : (ub:ℝ)/n≤(n:ℝ)^(-2/5:ℝ)
  large : 1<(3/4:ℝ)*(2:ℝ)^((s:ℝ)/80)
  smooth : 4*(4*(n:ℝ)^(1/5:ℝ)*log 2+1)≤log ((3/4:ℝ)*(2:ℝ)^((s:ℝ)/80))
  packet : 4*(2:ℝ)^((s:ℝ)/160)/ρ≤(3/4:ℝ)*(2:ℝ)^((s:ℝ)/80)
  correlation : (4/3:ℝ)*4*(n:ℝ)^(-2/5:ℝ)/ρ≤(n:ℝ)^(-1/5:ℝ)

theorem eventual_intermediate (hi : ℝ) : ∀ᶠ n : ℕ in atTop, ∀ ℓ s g w ub ab : ℕ, ∀ tq ρ : ℝ,
    0<ℓ → (ℓ:ℝ)≤logb 2 n → n≤s^3 → s^2≤n → g^95≤n →
    1≤tq → tq≤(logb 2 n)^2 → (w:ℝ)≤hi*logb 2 n →
    (ub:ℝ)≤5*g*s → (ab:ℝ)≤17*tq*w → (n:ℝ)^(-1/6:ℝ)≤ρ →
    IntermediateBudgets n s ub ab ρ := by
  have huge : ∀ᶠ n : ℕ in atTop,20000≤(n:ℝ)^(1/30:ℝ) :=
    tendsto_natCast_atTop_atTop.eventually ((tendsto_rpow_atTop (by norm_num : (0:ℝ)<1/30)).eventually_ge_atTop _)
  have logs := tendsto_natCast_atTop_atTop.eventually (DisjointnessFoundations.FinalBounds.polylog_budget 1)
  filter_upwards [eventually_ge_atTop 2,eventual_budgets hi,huge,logs] with n n2 raw huge poly
  intro ℓ s g w ub ab tq ρ positive depth ns sn gn tq1 tqmax wh hu ha rho
  let a := (n:ℝ)
  let L := logb 2 a
  have ap : 0<a := by dsimp [a]; exact_mod_cast (by omega : 0<n)
  have a1 : 1≤a := by dsimp [a]; exact_mod_cast (by omega : 1≤n)
  have rp : 0<ρ := (rpow_pos_of_pos ap _).trans_le rho
  have lp : 0<log 2 := log_pos (by norm_num)
  have lowlog : 1/2≤log 2 := by linarith [log_two_gt_d9]
  have highlog : log 2≤1 := by linarith [log_le_sub_one_of_pos (by norm_num : (0:ℝ)<2)]
  have La : 1≤L := by
    have le := logb_le_logb_of_le (by norm_num : (1:ℝ)<2) (by norm_num : (0:ℝ)<2) (by dsimp [a]; exact_mod_cast n2 : (2:ℝ)≤a)
    simpa [L,logb_self_eq_one (by norm_num : (1:ℝ)<2)] using le
  have add (b c : ℝ) : a^b*a^c=a^(b+c) := (rpow_add ap b c).symm
  have up {b c : ℝ} (h : b≤c) : a^b≤a^c := rpow_le_rpow_of_exponent_le a1 h
  have big (e : ℝ) : 20000*a^e≤a^(1/30+e) := by
    rw [←add]; exact mul_le_mul_of_nonneg_right huge (rpow_pos_of_pos ap _).le
  have s0 : (0:ℝ)≤s := Nat.cast_nonneg _
  have sl : a^(1/3:ℝ)≤s := by
    have h := rpow_le_rpow ap.le (by dsimp [a]; exact_mod_cast ns : a≤(s:ℝ)^3) (by norm_num : (0:ℝ)≤1/3)
    rw [←rpow_natCast (s:ℝ) 3,←rpow_mul s0] at h; norm_num at h; exact h
  have su : (s:ℝ)≤a^(1/2:ℝ) := by
    have h := rpow_le_rpow (sq_nonneg (s:ℝ)) (by dsimp [a]; exact_mod_cast sn : (s:ℝ)^2≤a) (by norm_num : (0:ℝ)≤1/2)
    rw [←rpow_natCast (s:ℝ) 2,←rpow_mul s0] at h; norm_num at h; exact h
  have gu : (g:ℝ)≤a^(1/95:ℝ) := by
    have h := rpow_le_rpow (pow_nonneg (Nat.cast_nonneg g : (0:ℝ)≤g) 95) (by dsimp [a]; exact_mod_cast gn : (g:ℝ)^95≤a) (by norm_num : (0:ℝ)≤1/95)
    rw [←rpow_natCast (g:ℝ) 95,←rpow_mul (Nat.cast_nonneg g)] at h; norm_num at h; exact h
  have sLarge := (big (1/5)).trans ((up (by norm_num : (1/30+1/5:ℝ)≤1/3)).trans sl)
  have t1 : 1≤a^(1/5:ℝ) := one_le_rpow a1 (by norm_num)
  have s1 : (20000:ℝ)≤s := by linarith only [sLarge,t1]
  have Lpow : L≤a^(1/50:ℝ) := by
    have l3 : L≤L^3 := by simpa using pow_le_pow_right₀ La (by decide : 1≤3)
    change 1*L^3≤a^(1/50:ℝ) at poly
    exact l3.trans (by simpa only [one_mul] using poly)
  have Lsmall : 20000*L≤s := (mul_le_mul_of_nonneg_left Lpow (by norm_num : (0:ℝ)≤20000)).trans
    ((big (1/50)).trans ((up (by norm_num : (1/30+1/50:ℝ)≤1/3)).trans sl))
  have cb : 1/2 ≤ (3/4:ℝ) := by norm_num
  have log34 : -1≤log (3/4:ℝ) := by
    have le := log_le_log (by norm_num : (0:ℝ)<1/2) cb
    rw [one_div,log_inv] at le
    linarith only [le,highlog]
  have expand : log ((3/4:ℝ)*(2:ℝ)^((s:ℝ)/80))=log (3/4:ℝ)+((s:ℝ)/80)*log 2 := by
    rw [log_mul (by norm_num) (rpow_pos_of_pos (by norm_num) _).ne',log_rpow (by norm_num : (0:ℝ)<2)]
  refine ⟨?_,?_,?_,?_,?_,?_⟩
  · have b := (raw ℓ s g w ub ab 0 tq positive depth ns sn gn tq1 tqmax wh hu ha (by simpa only [Nat.cast_zero] using div_nonneg s0 (by norm_num : (0:ℝ)≤160))).q
    apply (div_le_iff₀ (mul_pos ap rp)).mpr
    have le := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left rho ap.le) (rpow_pos_of_pos ap (1/5)).le
    have ub0 := Nat.cast_nonneg (ub+n*ab) (α:=ℝ)
    nlinarith only [le,b,mul_le_mul_of_nonneg_left lowlog ub0,ub0]
  · apply (div_le_iff₀ ap).mpr
    have u := mul_le_mul gu su s0 (rpow_pos_of_pos ap (1/95)).le
    rw [add] at u
    have big' := (big (1/95+1/2)).trans (up (by norm_num : (1/30+(1/95+1/2):ℝ)≤(-2/5)+1))
    change (ub:ℝ)≤a^(-2/5:ℝ)*a
    rw [show a^(-2/5:ℝ)*a=a^(-2/5+1:ℝ) by simpa only [rpow_one] using add (-2/5) 1]
    nlinarith only [hu,u,big',(rpow_pos_of_pos ap (1/95+1/2:ℝ))]
  · have h : (2:ℝ)≤(2:ℝ)^((s:ℝ)/80) := by
      simpa using rpow_le_rpow_of_exponent_le (show (1:ℝ)≤2 by norm_num) (by linarith only [s1] : (1:ℝ)≤s/80)
    linarith
  · rw [expand]
    have lhs := mul_le_mul_of_nonneg_left highlog (rpow_pos_of_pos ap (1/5)).le
    have rhs := mul_le_mul_of_nonneg_left lowlog s0
    nlinarith only [lhs,rhs,log34,sLarge,t1]
  · apply (div_le_iff₀ rp).mpr
    have rn : (2:ℝ)^(-L/6)≤ρ := by
      rw [show -L/6=L*(-1/6) by ring,rpow_mul (by norm_num : (0:ℝ)≤2),show (2:ℝ)^L=a from rpow_logb (by norm_num) (by norm_num) ap]
      exact rho
    apply le_trans _ (mul_le_mul_of_nonneg_left rn (by positivity))
    rw [mul_assoc,←rpow_add (by norm_num : (0:ℝ)<2)]
    have bexp : (s:ℝ)/160+3≤s/80+ -L/6 := by linarith only [s1,Lsmall]
    have le := rpow_le_rpow_of_exponent_le (by norm_num : (1:ℝ)≤2) bexp
    rw [rpow_add (by norm_num : (0:ℝ)<2)] at le
    norm_num at le
    linarith [rpow_pos_of_pos (by norm_num : (0:ℝ)<2) ((s:ℝ)/160)]
  · apply (div_le_iff₀ rp).mpr
    apply le_trans _ (mul_le_mul_of_nonneg_left rho (rpow_pos_of_pos ap (-1/5)).le)
    change (4/3:ℝ)*4*a^(-2/5:ℝ)≤a^(-1/5:ℝ)*a^(-1/6:ℝ)
    rw [add]
    have h := (big (-2/5)).trans (up (by norm_num : (1/30+ -2/5:ℝ)≤ -1/5+ -1/6))
    nlinarith only [h,(rpow_pos_of_pos ap (-2/5:ℝ))]

end
end DisjointnessDraft.Information
