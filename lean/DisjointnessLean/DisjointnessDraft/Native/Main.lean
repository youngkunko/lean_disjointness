import DisjointnessDraft.Native.Bridge
import DisjointnessDraft.Information.PhysicalUpper

/-! The manuscript's own proof of the main trade-off. The physical protocol
and the information bound are evaluated on the very same native distribution.
The sparse corruption theorem supplies the contradiction for the chosen epoch. -/
namespace DisjointnessDraft.Native
open DisjointnessFoundations HardDistribution CellProbe HardIndependence PhysicalProtocol MeasureTheory Filter Real
open scoped ENNReal BigOperators DisjointnessDraft.Information
noncomputable section
open Classical

set_option maxHeartbeats 1200000 in
theorem explicit_tradeoff :
    ∀ lo hi : ℝ, 0<lo → lo≤hi → ∀ᶠ n : ℕ in atTop,
    ∀ w tu : ℕ, 1≤tu → lo*logb 2 n≤w → (w:ℝ)≤hi*logb 2 n →
    ∀ (Ω C : Type) [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
      (D : Machine n w C) (R : RandomTape Ω C) (tq : ℝ),
      1≤tq → FreshMeasurable D R → FreshCorrect D R →
      WorstUpdate D R (tu:ℝ≥0∞) → FreshQuery μ D R tq →
      (1/100000:ℝ)*(Tradeoff.ratio n w tu)^2≤tq := by
  intro lo hi lp lh
  filter_upwards [scale lo lp,sampling_scale,lower_acceptance,Snapshot.acceptance_upper hi,
    Tradeoff.log_tends.eventually_ge_atTop (2560/lo),eventually_ge_atTop 2] with n scaleN scaleS acc upper nw n2
  intro w tu hp wl wh Ω C _ μ _ D R tq qp meas hz hu hq
  let g := tu*w
  have gov : w≤g := Nat.le_mul_of_pos_left _ hp
  have gw : 2560≤w := by
    have z := (div_le_iff₀ lp).mp nw
    exact_mod_cast (show (2560:ℝ)≤w by nlinarith only [wl,z])
  have hG : 2560≤g := gw.trans gov
  have hg : 2≤g := by omega
  have npos : 0<n := by omega
  have gp : (0:ℝ)<g := by exact_mod_cast (by omega : 0<g)
  have lG : 1≤logb 2 (g:ℝ) := by simpa using logb_le_logb_of_le (b:=2) (by norm_num) (by norm_num : (0:ℝ)<2) (show (2:ℝ)≤g by exact_mod_cast hg)
  let r := Tradeoff.ratio n w tu
  have rr : r=logb 2 n/logb 2 (g:ℝ) := by simp [r,Tradeoff.ratio,g]
  have lpN : 0≤logb 2 (n:ℝ) := logb_nonneg (by norm_num) (by exact_mod_cast (by omega : 1≤n))
  have rp : 0≤r := by rw [rr]; exact div_nonneg lpN (by linarith)
  change 1/100000*r^2≤tq
  by_cases small : g^95≤n
  · obtain ⟨ℓ,hl,fit,next⟩ := depth_twenty (by omega) small
    have lpos : 0<ℓ := by omega
    have sc := scaleN ℓ g lpos hg fit (wl.trans (by exact_mod_cast gov))
    have lg := log_geometry lpos hg fit next sc
    have rℓ : r≤12*ℓ := by rw [rr]; exact (div_le_iff₀ (by linarith)).mpr lg.2
    by_contra! cheap
    have T : tq≤(ℓ:ℝ)^2/256 := by
      have sq := pow_le_pow_left₀ rp rℓ 2
      nlinarith only [cheap,sq,sq_nonneg (ℓ:ℝ)]
    have sTrue := log_le_native lpos hg fit
    have tqlog : tq≤(logb 2 n)^2 :=
      (by nlinarith only [T,sq_nonneg (ℓ:ℝ)] : tq≤(ℓ:ℝ)^2).trans (pow_le_pow_left₀ (Nat.cast_nonneg ℓ) sTrue 2)
    obtain ⟨a,fixed⟩ := fix_tape μ lpos (by omega) npos fit D R (by linarith : 0≤tq) meas hz hq
    let k := ⌊8*tq⌋₊
    obtain ⟨i,mem,limit⟩ := select_epoch fit D R a hu hz hl k fixed
    let τ := tau fit D R a k i
    have cardinal := chronogram_card ℓ
    have nc : 0<(chronogram ℓ).card := by omega
    have cover : (ℓ:ℝ)≤4*(chronogram ℓ).card := by exact_mod_cast (by omega : ℓ≤4*(chronogram ℓ).card)
    have bound : τ≤(ℓ:ℝ)/64 := by
      apply limit.trans
      apply (div_le_iff₀ (by exact_mod_cast nc : (0:ℝ)<(chronogram ℓ).card)).mpr
      nlinarith only [T,mul_le_mul_of_nonneg_right cover (Nat.cast_nonneg ℓ)]
    have nn : 0≤τ := by dsimp [τ,tau,mean]; positivity
    let s := epochSize g i
    have lsz := large_epoch hg next sc i mem
    have hsz := epoch_upper fit i
    let rate := samplingRate g (by omega)
    let S := snapshot fit hg D R hu a i
    letI (j : Fin ℓ) : Nonempty (Block ℓ g j) := layer_nonempty lpos (by omega) j
    have balanced : (unif (Whole ℓ g)).map S.block=unif (Information.Layer (ℓ*s^2) s) :=
      HardIndependence.eval_uniform (β:=Block ℓ g) i
    have sound := game_sound fit hg D R hu a hz i ⌊2*rate.p*(s*tu:ℕ)⌋₊ k
    have U := upper ℓ s g w tu tq rate S lpos sTrue lsz hsz small rfl hG (by omega) qp tqlog wh rfl sound balanced
    have B := physical_lower fit hg (by omega) npos D R hu hz a i (by linarith : 0<tq) fixed
      (scaleS s tu w g rfl hp (by omega) small lsz)
    apply (not_lt_of_ge (acc ℓ g τ _ lpos hG fit nn bound B))
    simpa only [neg_div] using U
  · have z := logb_le_logb_of_le (b:=2) (by norm_num) (by exact_mod_cast npos : (0:ℝ)<n)
      (by exact_mod_cast (Nat.le_of_not_ge small) : (n:ℝ)≤(g:ℝ)^95)
    rw [logb_pow] at z
    have maxr : r≤95 := by rw [rr]; exact (div_le_iff₀ (by linarith)).mpr (by simpa using z)
    have sq := pow_le_pow_left₀ rp maxr 2
    nlinarith only [sq,qp]

theorem main_on_fresh :
    ∀ lo hi : ℝ, 0<lo → lo≤hi → ∃ c : ℝ, 0<c ∧ ∀ᶠ n : ℕ in atTop,
    ∀ w tu : ℕ, 1≤tu → lo*logb 2 n≤w → (w:ℝ)≤hi*logb 2 n →
    ∀ (Ω C : Type) [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
      (D : Machine n w C) (R : RandomTape Ω C) (tq : ℝ),
      1≤tq → FreshMeasurable D R → FreshCorrect D R →
      WorstUpdate D R (tu:ℝ≥0∞) → FreshQuery μ D R tq →
      c*(Tradeoff.ratio n w tu)^2≤tq := by
  intro lo hi lp lh
  exact ⟨1/100000,by norm_num,explicit_tradeoff lo hi lp lh⟩

theorem main : MainBound := by
  intro lo hi lp lh
  obtain ⟨c,cp,large⟩ := main_on_fresh lo hi lp lh
  refine ⟨c,cp,?_⟩
  filter_upwards [large] with n bound
  intro w tu hp wl wh Ω C _ μ _ D R tq qp meas hz hu hq
  exact bound w tu hp wl wh Ω C μ D R tq qp (fun f xs q _ => meas.2.1 f xs q)
    (fun a f xs q _ => hz a f xs q) hu (fun f xs q _ => hq f xs q)
end
end DisjointnessDraft.Native
