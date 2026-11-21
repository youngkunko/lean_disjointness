import DisjointnessDraft.Native.Charges
import DisjointnessDraft.Native.GoodMass
import DisjointnessDraft.Native.Scale
import DisjointnessDraft.Simulation.Averaging

/-! Instantiate the protocol's random coins, physical last-write budget and
success inequality on the native distribution and its actual fixed tape. -/
namespace DisjointnessDraft.Native
open DisjointnessFoundations VerifierLaw CellProbe HardIndependence FiniteSampling HardDistribution PhysicalProtocol MeasureTheory Filter Real
open scoped ENNReal BigOperators DisjointnessDraft.Information
noncomputable section
open Classical
variable {n ℓ g w tu : ℕ} {Ω C : Type}
def samplingRate (g : ℕ) (p : 0<g) : SamplingRate where
  p := 1/(1280*(g:ℝ))
  positive := by positivity
  le_one := by
    have h : (1:ℝ)≤g := by exact_mod_cast p
    exact (div_le_one (by positivity)).mpr (by linarith)

theorem sampling_scale : ∀ᶠ n : ℕ in atTop,∀ s tu w g : ℕ, g=tu*w → 0<tu → 0<w →
    g^95≤n → n≤s^3 → (n:ℝ)^(1/4:ℝ)≤(1/(1280*(g:ℝ)))*((s*tu:ℕ):ℝ) := by
  have grow := (tendsto_rpow_atTop (by norm_num : (0:ℝ)<1/3-(1/4+1/95))).comp tendsto_natCast_atTop_atTop
  filter_upwards [grow.eventually_ge_atTop 1280,eventually_ge_atTop 1] with n gain hn
  intro s tu w g defg tp wp small large
  have np : (0:ℝ)<n := by exact_mod_cast hn
  have T : (0:ℝ)<tu := by exact_mod_cast tp
  have W : (0:ℝ)<w := by exact_mod_cast wp
  have h := rpow_le_rpow (Nat.cast_nonneg n) (by exact_mod_cast large : (n:ℝ)≤(s:ℝ)^3) (by norm_num : (0:ℝ)≤1/3)
  rw [←rpow_natCast_mul (Nat.cast_nonneg s)] at h; norm_num at h
  have k := rpow_le_rpow (by positivity : (0:ℝ)≤(g:ℝ)^95) (by exact_mod_cast small : (g:ℝ)^95≤n) (by norm_num : (0:ℝ)≤1/95)
  rw [←rpow_natCast_mul (Nat.cast_nonneg g)] at k; norm_num at k
  have wg : (w:ℝ)≤g := by exact_mod_cast (show w≤g by rw [defg]; exact Nat.le_mul_of_pos_left w tp)
  have prod := mul_le_mul_of_nonneg_left (wg.trans k) (rpow_nonneg np.le (1/4:ℝ))
  rw [←rpow_add np] at prod
  change 1280≤(n:ℝ)^(1/3-(1/4+1/95):ℝ) at gain
  have high := mul_le_mul_of_nonneg_right gain (rpow_nonneg np.le (1/4+1/95:ℝ))
  rw [←rpow_add np,sub_add_cancel] at high
  have pos := mul_le_mul_of_nonneg_left prod (by norm_num : (0:ℝ)≤1280)
  have sn := high.trans h
  rw [defg,Nat.cast_mul,Nat.cast_mul]
  rw [show 1/(1280*((tu:ℝ)*w))*((s:ℝ)*tu)=(s*tu:ℝ)/(1280*(tu*w)) by ring,
    le_div_iff₀ (by positivity : 0<1280*((tu:ℝ)*w))]
  nlinarith only [mul_le_mul_of_nonneg_right (pos.trans sn) T.le]

theorem snap_tau (fit : occupied ℓ g≤n) (hg : 2≤g) (D : Machine n w C) (R : RandomTape Ω C)
    (hu : WorstUpdate D R (tu:ℝ≥0∞)) (a : Ω) (i : Fin ℓ) (fuel : ℕ) :
    mean (fun d : Separated n ℓ g i => ((snapshot fit hg D R hu a i).hits fuel d:ℝ))=
      tau fit D R a fuel i := by
  let S := snapshot fit hg D R hu a i
  let f := fun d : Separated n ℓ g i => (S.hits fuel d:ℝ)
  change mean f=_
  rw [←mean_equiv (separate i) f]
  unfold tau
  apply congrArg mean
  funext z
  obtain ⟨q,F,x⟩ := z
  have iv : join i ((split g i x).1) ((split g i x).2)=x := (split g i).symm_apply_apply x
  change ((S.early F ((split g i x).1) ((split g i x).2) ∩ touched
    (S.actual fuel F ((split g i x).1) ((split g i x).2) q).probes).card:ℝ)=_
  rw [show S.actual fuel F ((split g i x).1) ((split g i x).2) q=trace fit D R a (q,F,x) fuel by
    dsimp [S]; rw [snap_trace,iv]]
  simp only [S,Snapshot.early,snapshot,iv,hits,lastCells]

theorem physical_lower (fit : occupied ℓ g≤n) (hg : 2≤g) (hl : 2≤ℓ) (hn : 0<n) (D : Machine n w C)
    (R : RandomTape Ω C) (hu : WorstUpdate D R (tu:ℝ≥0∞)) (hz : FreshCorrect D R)
    (a : Ω) (i : Fin ℓ) {tq : ℝ} (qp : 0<tq)
    (cheap : mean (fun z : Native.Draw n ℓ g => (reads fit D R a z:ℝ))≤tq)
    (scale : (n:ℝ)^(1/4:ℝ)≤(1/(1280*(g:ℝ)))*((epochSize g i*tu:ℕ):ℝ)) :
    let r := samplingRate g (by omega)
    let S := snapshot fit hg D R hu a i
    let fuel := ⌊8*tq⌋₊
    let G := S.game ⌊2*r.p*(epochSize g i*tu:ℕ)⌋₊ fuel
    (1/8:ℝ)*(r.p^(8*tau fit D R a fuel i))-exp (-(n:ℝ)^(1/4:ℝ)/3) ≤
      Information.acceptance G (unif (Outside g i)) (masks r (2^w)) := by
  letI (j : Fin ℓ) : Nonempty (Block ℓ g j) := layer_nonempty (by omega) (by omega) j
  letI : NeZero n := ⟨hn.ne'⟩
  intro r S fuel G
  have mass' := snapshot_mass hl hg hn fit D R a hu hz qp i cheap
  have good : 1/8≤mean (fun d : Separated n ℓ g i => if S.good fuel d then (1:ℝ) else 0) := by
    apply mass'.trans
    apply mean_mono; intro d
    by_cases v : S.good fuel d <;> simp_all only [S,fuel,Snapshot.good,if_true,if_false,le_refl]
  have prob := S.acceptance_lower r fuel (tau fit D R a fuel i) good (snap_tau fit hg D R hu a i fuel).le
  have x := exp_le_exp.mpr (show -(r.p*((epochSize g i*tu:ℕ):ℝ))/3≤ -(n:ℝ)^(1/4:ℝ)/3 by dsimp [r,samplingRate]; linarith)
  exact (sub_le_sub_left x _).trans prob

end
end DisjointnessDraft.Native
