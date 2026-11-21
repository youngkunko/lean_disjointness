import DisjointnessDraft.Native.Untruncated

/-! The manuscript's success-probability corollary in its usual quantified
form. For every positive exponent the protocol eventually beats that inverse
power, when its expected number of epoch cells is little-o of the log ratio. -/
namespace DisjointnessDraft.Native
open DisjointnessFoundations FiniteSampling VerifierLaw CellProbe PhysicalProtocol HardDistribution Filter Real Asymptotics
open scoped ENNReal Topology DisjointnessDraft.Information
noncomputable section

theorem physical_full {n ℓ g w tu : ℕ} {C Ω : Type}
    (fit : occupied ℓ g≤n) (hg : 2≤g) (hl : 2≤ℓ) (hn : 0<n) (D : Machine n w C)
    (R : RandomTape Ω C) (hu : WorstUpdate D R (tu:ℝ≥0∞)) (hz : FreshCorrect D R)
    (a : Ω) (i : Fin ℓ) {tq : ℝ} (qp : 0<tq)
    (cheap : mean (fun z : Native.Draw n ℓ g => (reads fit D R a z:ℝ))≤tq)
    (scale : (n:ℝ)^(1/4:ℝ)≤(1/(1280*(g:ℝ)))*((epochSize g i*tu:ℕ):ℝ)) :
    let r := samplingRate g (by omega)
    let S := snapshot fit hg D R hu a i
    let G := S.game ⌊2*r.p*(epochSize g i*tu:ℕ)⌋₊ ⌊8*tq⌋₊
    (1/8:ℝ)*(r.p^(8*fullTau fit D R a i))-exp (-(n:ℝ)^(1/4:ℝ)/3) ≤
      Information.acceptance G (HardIndependence.unif (Outside g i)) (masks r (2^w)) := by
  intro r S G
  have b := physical_lower fit hg hl hn D R hu hz a i qp cheap scale
  have comp := rpow_le_rpow_of_exponent_ge r.positive r.le_one
    (mul_le_mul_of_nonneg_left (tau_le_full fit D R a hu hz i ⌊8*tq⌋₊) (by norm_num : (0:ℝ)≤8))
  exact (sub_le_sub_right (mul_le_mul_of_nonneg_left comp (by norm_num : (0:ℝ)≤1/8)) _).trans b

theorem subpolynomial (g : ℕ → ℕ) (τ ρ : ℕ → ℝ)
    (grows : ∀ᶠ n : ℕ in atTop,2560≤g n) (positive : ∀ᶠ n : ℕ in atTop,0≤τ n)
    (few : τ =o[atTop] (fun n => log (n:ℝ)/log (g n:ℝ)))
    (simulates : ∀ᶠ n : ℕ in atTop,(1/8:ℝ)*(1/(1280*(g n:ℝ)))^(8*τ n)-
      exp (-(n:ℝ)^(1/4:ℝ)/3)≤ρ n) :
    ∀ δ : ℝ,0<δ → ∀ᶠ n : ℕ in atTop,(n:ℝ)^(-δ)≤ρ n := by
  intro δ dp
  let j := min (δ/2) (1/16)
  have jp : 0<j := lt_min (by linarith) (by norm_num)
  have jd : 2*j≤δ := by have h : j≤δ/2 := min_le_left ..; linarith
  have js : j≤1/16 := min_le_right ..
  have grow (t : ℝ) (pos : 0<t) (c : ℝ) : ∀ᶠ n : ℕ in atTop,c≤(n:ℝ)^t :=
    ((tendsto_rpow_atTop pos).comp tendsto_natCast_atTop_atTop).eventually_ge_atTop c
  filter_upwards [grows,positive,simulates,few.bound (show 0<j/16 by positivity),
    grow j jp 16,grow (1/4-2*j) (by linarith) 3,eventually_ge_atTop 2] with n gn nn prob small gain tailbig two
  have np : (1:ℝ)<n := by exact_mod_cast two
  have posn : (0:ℝ)<n := by linarith
  have gp : (1:ℝ)<g n := by exact_mod_cast (by omega : 1<g n)
  have posg : (0:ℝ)<g n := by linarith
  have lg := log_pos gp
  have ln := log_pos np
  simp only [Real.norm_eq_abs,abs_of_nonneg nn,abs_of_nonneg (div_nonneg ln.le lg.le)] at small
  have z : 8*τ n*(2*log (g n:ℝ))≤j*log (n:ℝ) := by
    have h := mul_le_mul_of_nonneg_right small lg.le
    rw [mul_assoc,div_mul_cancel₀ _ lg.ne'] at h
    nlinarith only [h]
  have gg : 1280*(g n:ℝ)≤(g n:ℝ)^2 := by
    have h : (1280:ℝ)≤g n := by exact_mod_cast (by omega : 1280≤g n)
    nlinarith only [mul_le_mul_of_nonneg_right h posg.le]
  have k := log_le_log (by positivity : (0:ℝ)<1280*(g n:ℝ)) gg
  rw [log_pow] at k
  have pow : (1280*(g n:ℝ))^(8*τ n)≤(n:ℝ)^j := by
    rw [rpow_def_of_pos (by positivity),rpow_def_of_pos posn,exp_le_exp]
    have h := mul_le_mul_of_nonneg_right k (show 0≤8*τ n by positivity)
    norm_num at h; linarith only [h,z]
  have inv := inv_anti₀ (rpow_pos_of_pos (by positivity : 0<1280*(g n:ℝ)) _) pow
  rw [show (1/(1280*(g n:ℝ)))^(8*τ n)=((1280*(g n:ℝ))^(8*τ n))⁻¹ by rw [one_div,inv_rpow (by positivity)]] at prob
  rw [←rpow_neg posn.le] at inv
  have A := mul_le_mul_of_nonneg_right gain (rpow_nonneg posn.le (-(2*j)))
  rw [←rpow_add posn,show j+ -(2*j) = -j by ring] at A
  have B := mul_le_mul_of_nonneg_right tailbig (rpow_nonneg posn.le (2*j))
  rw [←rpow_add posn,sub_add_cancel] at B
  have tail : exp (-(n:ℝ)^(1/4:ℝ)/3)≤(n:ℝ)^(-(2*j)) := by
    rw [neg_div,exp_neg,rpow_neg posn.le]; apply inv_anti₀ (rpow_pos_of_pos posn _)
    linarith only [B,Real.add_one_le_exp ((n:ℝ)^(1/4:ℝ)/3)]
  apply (rpow_le_rpow_of_exponent_le np.le (neg_le_neg jd)).trans
  linarith only [prob,inv,A,tail]

end
end DisjointnessDraft.Native
