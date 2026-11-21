import DisjointnessDraft.Information.Communication
import DisjointnessFoundations.PolylogarithmicRegime

namespace DisjointnessDraft.Information
open Real Filter MeasureTheory DisjointnessFoundations.HardIndependence
open scoped BigOperators Topology
noncomputable section
open Classical

/-- Scalar consequences needed by the finite communication theorem at the
manuscript's acceptance threshold. Bounds are uniform in the epoch and in
both machine costs. -/
structure Budgets (n ℓ s ub ab pb : ℕ) : Prop where
  size : 200≤s
  q : 4*((ub+n*ab : ℕ)*log 2)≤(n*(n:ℝ)^(-1/6:ℝ))*(n:ℝ)^(1/5:ℝ)
  c : 4*(ub*log 2)≤(n*(n:ℝ)^(-1/6:ℝ))*(n:ℝ)^(-1/5:ℝ)
  p : 4*(2:ℝ)^pb≤(n:ℝ)^(-1/6:ℝ)*(Corruption.capFactor s/2)
  large : 1<Corruption.capFactor s/2
  querySmooth : 4*((n:ℝ)^(1/5:ℝ)+1)≤log (Corruption.capFactor s/2)
  rare : (n:ℝ)^(-1/5:ℝ)<((s:ℝ)^2/(100*(ℓ*s^2:ℕ)))^2/2

theorem eventual_budgets (hi : ℝ) : ∀ᶠ n : ℕ in atTop, ∀ ℓ s g w ub ab pb : ℕ, ∀ tq : ℝ,
    0<ℓ → (ℓ:ℝ)≤logb 2 n → n≤s^3 → s^2≤n → g^95≤n →
    1≤tq → tq≤(logb 2 n)^2 → (w:ℝ)≤hi*logb 2 n →
    (ub:ℝ)≤5*g*s → (ab:ℝ)≤17*tq*w → (pb:ℝ)≤(s:ℝ)/160 →
    Budgets n ℓ s ub ab pb := by
  let H := 100000*(1+(abs hi))
  have eventualNat {p : ℝ→Prop} (he : ∀ᶠ x in atTop,p x) : ∀ᶠ n : ℕ in atTop,p n :=
    tendsto_natCast_atTop_atTop.eventually he
  have grow : ∀ᶠ x : ℝ in atTop,20000≤x^(1/30:ℝ) :=
    (tendsto_rpow_atTop (by norm_num : (0:ℝ)<1/30)).eventually_ge_atTop _
  filter_upwards [eventualNat (DisjointnessFoundations.FinalBounds.polylog_budget H),eventualNat grow,eventually_ge_atTop 2] with n poly huge n2
  intro ℓ s g w ub ab pb tq lp depth ns sn gn tpos tqmax wh hu ha hpb
  let a := (n:ℝ)
  let L := logb 2 a
  have ap : (0:ℝ)<a := by dsimp [a]; exact_mod_cast (by omega : 0<n)
  have a1 : 1≤a := by dsimp [a]; exact_mod_cast (by omega : 1≤n)
  have one : 1≤L := by
    have h := logb_le_logb_of_le (by norm_num : (1:ℝ)<2) (by norm_num : (0:ℝ)<2) (by dsimp [a]; exact_mod_cast n2 : (2:ℝ)≤a)
    simpa [L,logb_self_eq_one (by norm_num : (1:ℝ)<2)] using h
  change H*L^3≤a^(1/50:ℝ) at poly
  change 20000≤a^(1/30:ℝ) at huge
  change (ℓ:ℝ)≤L at depth
  change tq≤L^2 at tqmax
  change (w:ℝ)≤hi*L at wh
  have up {b c : ℝ} (e : b≤c) : a^b≤a^c := rpow_le_rpow_of_exponent_le a1 e
  have add (b c : ℝ) : a^b*a^c=a^(b+c) := (rpow_add ap b c).symm
  have time (b : ℝ) : a*a^b=a^(1+b) := by simpa using add 1 b
  have pos (b : ℝ) : 0<a^b := rpow_pos_of_pos ap _
  have s0 : (0:ℝ)≤s := Nat.cast_nonneg _
  have g0 : (0:ℝ)≤g := Nat.cast_nonneg _
  have sLower : a^(1/3:ℝ)≤s := by
    have h := rpow_le_rpow ap.le (by dsimp [a]; exact_mod_cast ns : a≤(s:ℝ)^3) (by norm_num : (0:ℝ)≤1/3)
    rw [←rpow_natCast (s:ℝ) 3,←rpow_mul s0] at h; norm_num at h; exact h
  have sUpper : (s:ℝ)≤a^(1/2:ℝ) := by
    have h := rpow_le_rpow (sq_nonneg (s:ℝ)) (by dsimp [a]; exact_mod_cast sn : (s:ℝ)^2≤a) (by norm_num : (0:ℝ)≤1/2)
    rw [←rpow_natCast (s:ℝ) 2,←rpow_mul s0] at h; norm_num at h; exact h
  have gUpper : (g:ℝ)≤a^(1/95:ℝ) := by
    have h := rpow_le_rpow (pow_nonneg g0 95) (by dsimp [a]; exact_mod_cast gn : (g:ℝ)^95≤a) (by norm_num : (0:ℝ)≤1/95)
    rw [←rpow_natCast (g:ℝ) 95,←rpow_mul g0] at h; norm_num at h; exact h
  have merlin : (ub:ℝ)≤5*a^(11/20:ℝ) := calc
    _ ≤ _ := hu
    _ ≤ 5*(a^(1/95:ℝ)*a^(1/2:ℝ)) := by
      rw [mul_assoc]; exact mul_le_mul_of_nonneg_left (mul_le_mul gUpper sUpper s0 (pos _).le) (by norm_num)
    _ ≤ _ := by rw [add]; exact mul_le_mul_of_nonneg_left (up (by norm_num)) (by norm_num)
  have cheap : (ab:ℝ)≤17*(abs hi)*L^3 := by
    have wh' : (w:ℝ)≤(abs hi)*L := wh.trans (mul_le_mul_of_nonneg_right (le_abs_self _) (by linarith))
    have mul := mul_le_mul tqmax wh' (Nat.cast_nonneg w) (sq_nonneg L)
    nlinarith only [ha,mul]
  have big (b : ℝ) : 20000*a^b≤a^(1/30+b) := by
    rw [←add]; exact mul_le_mul_of_nonneg_right huge (pos _).le
  have l3 : 1≤L^3 := one_le_pow₀ one
  have l23 : L^2≤L^3 := by exact pow_le_pow_right₀ one (by decide)
  have l13 : L≤L^3 := by simpa using pow_le_pow_right₀ one (by decide : 1≤3)
  have lac : 4*(5+17*(abs hi)*L^3)≤a^(1/50:ℝ) := by
    apply le_trans _ poly; dsimp [H]; nlinarith only [l3,mul_nonneg (abs_nonneg hi) (pow_nonneg (by linarith : 0≤L) 3)]
  have logsmall : L≤a^(1/50:ℝ) := l13.trans (le_trans (by dsimp [H]; nlinarith only [l3,mul_nonneg (abs_nonneg hi) (pow_nonneg (by linarith : 0≤L) 3)]) poly)
  have log2 := log_lt_sub_one_of_pos (by norm_num : (0:ℝ)<2) (by norm_num : (2:ℝ)≠1)
  have hiLog : log 2≤1 := by linarith
  have loLog : 1/2≤log 2 := by linarith [log_two_gt_d9]
  have sHuge : 20000*a^(1/5:ℝ)≤s := (big _).trans ((up (by norm_num)).trans sLower)
  have s200 : 200≤s := by
    have h : 1≤a^(1/5:ℝ) := one_le_rpow a1 (by norm_num)
    exact_mod_cast (by nlinarith only [sHuge,h] : (200:ℝ)≤s)
  have sp : (0:ℝ)<s := by exact_mod_cast (by omega : 0<s)
  have lf : 20000*L≤s := by
    apply (mul_le_mul_of_nonneg_left logsmall (by norm_num : (0:ℝ)≤20000)).trans
    exact (big _).trans ((up (by norm_num)).trans sLower)
  have qq : (4:ℝ)*((ub:ℝ)+a*ab)≤a*a^(1/30:ℝ) := by
    have u := up (by norm_num : (11/20:ℝ)≤1)
    rw [rpow_one] at u
    have ab' := mul_le_mul_of_nonneg_left cheap ap.le
    have mul := mul_le_mul_of_nonneg_left (lac.trans (up (by norm_num : (1/50:ℝ)≤1/30))) ap.le
    nlinarith only [merlin,u,ab',mul]
  have cp : 4*(ub:ℝ)≤a^(19/30:ℝ) := by
    have bound := (big (11/20)).trans (up (by norm_num : (1/30+11/20:ℝ)≤19/30))
    nlinarith only [merlin,bound,(pos (11/20))]
  have lr : log (Corruption.capFactor s/2)=(s/40-1)*log 2 := by
    rw [log_div (Corruption.cap_pos _).ne' (by norm_num),Corruption.capFactor,log_rpow (by norm_num : (0:ℝ)<2)]; ring
  refine ⟨s200,?_,?_,?_,?_,?_,?_⟩
  · push_cast
    change 4*(((ub:ℝ)+a*ab)*log 2)≤(a*a^(-1/6:ℝ))*a^(1/5:ℝ)
    rw [time,add,show (1+ -1/6+1/5:ℝ)=1+1/30 by norm_num,←time]
    nlinarith only [qq,mul_le_mul_of_nonneg_left hiLog (show 0≤(ub:ℝ)+a*ab by positivity)]
  · change 4*((ub:ℝ)*log 2)≤(a*a^(-1/6:ℝ))*a^(-1/5:ℝ)
    rw [time,add,show (1+ -1/6+ -1/5:ℝ)=19/30 by norm_num]
    nlinarith only [cp,mul_le_mul_of_nonneg_left hiLog (Nat.cast_nonneg ub)]
  · have powNeg : a^(-1/6:ℝ)=(2:ℝ)^(-L/6) := by
      rw [show -L/6=L*(-1/6) by ring,rpow_mul (by norm_num : (0:ℝ)≤2),show (2:ℝ)^L=a from rpow_logb (by norm_num) (by norm_num) ap]
    change 4*(2:ℝ)^pb≤a^(-1/6:ℝ)*(Corruption.capFactor s/2)
    rw [powNeg,←mul_div_assoc,le_div_iff₀ (by norm_num : (0:ℝ)<2),Corruption.capFactor,←rpow_add (by norm_num : (0:ℝ)<2)]
    calc _ = (2:ℝ)^(3+(pb:ℝ)) := by rw [rpow_add (by norm_num : (0:ℝ)<2),rpow_natCast]; norm_num; ring
         _ ≤ _ := rpow_le_rpow_of_exponent_le (by norm_num) (by
           have sr : (200:ℝ)≤s := by exact_mod_cast s200
           linarith only [hpb,lf,sr,one])
  · apply (lt_div_iff₀ (by norm_num : (0:ℝ)<2)).mpr
    have sr : (200:ℝ)≤s := by exact_mod_cast s200
    change 1*2<(2:ℝ)^((s:ℝ)/40)
    convert (rpow_lt_rpow_of_exponent_lt (by norm_num : (1:ℝ)<2) (by linarith : (1:ℝ)<s/40)) using 1
    norm_num
  · rw [lr]
    have neg : 0≤(s:ℝ)/40-1 := by
      have sr : (200:ℝ)≤s := by exact_mod_cast s200
      linarith only [sr]
    have p := mul_le_mul_of_nonneg_left loLog neg
    change 4*(a^(1/5:ℝ)+1)≤_
    nlinarith only [sHuge,p,one_le_rpow a1 (by norm_num : (0:ℝ)≤1/5)]
  · have ellp : (0:ℝ)<ℓ := by exact_mod_cast lp
    have square := pow_le_pow_left₀ ellp.le depth 2
    have L2 : 20000*(ℓ:ℝ)^2<a^(1/5:ℝ) := by
      apply lt_of_lt_of_le _ (poly.trans (up (by norm_num : (1/50:ℝ)≤1/5)))
      dsimp [H]; nlinarith only [square,l23,l3,mul_nonneg (abs_nonneg hi) (pow_nonneg (by linarith : 0≤L) 3)]
    push_cast
    change a^(-1/5:ℝ)<((s:ℝ)^2/(100*((ℓ:ℝ)*s^2)))^2/2
    rw [show (-1/5:ℝ)= -(1/5) by ring,rpow_neg ap.le]
    rw [show ((s:ℝ)^2/(100*((ℓ:ℝ)*s^2)))^2/2=(20000*(ℓ:ℝ)^2)⁻¹ by field_simp; ring]
    exact inv_lt_inv₀ (pos _) (by positivity) |>.mpr L2

end
end DisjointnessDraft.Information
