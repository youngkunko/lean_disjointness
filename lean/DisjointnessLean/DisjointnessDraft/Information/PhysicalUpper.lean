import DisjointnessDraft.Information.Asymptotics
import DisjointnessDraft.Simulation.Averaging
import DisjointnessDraft.Simulation.Lengths

namespace DisjointnessDraft.PhysicalProtocol.Snapshot
open Filter Real MeasureTheory DisjointnessFoundations FiniteSampling VerifierLaw HardIndependence
open DisjointnessDraft.Information
open scoped BigOperators
noncomputable section
open Classical

/-- Native communication lower bound on the actual game of one chronogram
epoch. The cardinality of every physical message code and its asymptotic
contribution are discharged here. -/
theorem acceptance_upper (hi : ℝ) : ∀ᶠ n : ℕ in atTop, ∀ {W O : Type} [Fintype W] [MeasurableSpace W] [MeasurableSingletonClass W] [Nonempty W]
    [Fintype O] [MeasurableSpace O] [MeasurableSingletonClass O] [Nonempty O], ∀ (ℓ s g w tu : ℕ) (tq : ℝ)
    (r : SamplingRate) (S : Snapshot n (ℓ*s^2) s w (s*tu) (2*s*tu/g^2) W O),
    0<ℓ → (ℓ:ℝ)≤logb 2 n → n≤s^3 → s^2≤n → g^95≤n → g=tu*w → 2560≤g → 10≤w →
    1≤tq → tq≤(logb 2 n)^2 → (w:ℝ)≤hi*logb 2 n → r.p=1/(1280*(g:ℝ)) →
    (S.game ⌊2*r.p*(s*tu:ℕ)⌋₊ ⌊8*tq⌋₊).Sound → (unif W).map S.block=unif (Layer (ℓ*s^2) s) →
    acceptance (S.game ⌊2*r.p*(s*tu:ℕ)⌋₊ ⌊8*tq⌋₊) (unif O) (masks r (2^w)) < (n:ℝ)^(-1/6:ℝ) := by
  filter_upwards [eventual_budgets hi,eventually_ge_atTop (1280^3 : ℕ)] with n sizes large
  intro W O _ _ _ _ _ _ _ _ ℓ s g w tu tq r S hl depth ns sn gn eq gg ww tp tqmax wh rate sound balanced
  have nb : 0<n := by omega
  have sb : 1280≤s := by
    by_contra! small
    have h := Nat.pow_le_pow_left (show s≤1279 by omega) 3
    omega
  have realS : (1280:ℝ)≤s := by exact_mod_cast sb
  have realG : (2560:ℝ)≤g := by exact_mod_cast gg
  have gp : (0:ℝ)<g := by linarith only [realG]
  have rg : (g:ℝ)=(tu:ℝ)*w := by exact_mod_cast eq
  have sp : 0<s := by omega
  let e := s*tu
  let l := 2*s*tu/g^2
  let k := ⌊2*r.p*(s*tu:ℕ)⌋₊
  let f := ⌊8*tq⌋₊
  let ub := adviceBits w e l
  let ab := replyBits w f
  let pb := packetBits w l k
  have leReal : (l:ℝ)*(g:ℝ)^2≤2*(s:ℝ)*tu := by
    exact_mod_cast Nat.div_mul_le_self (2*s*tu) (g^2)
  have late : (l:ℝ)*w≤(1/40)*(s:ℝ)/32 := by
    have h := mul_le_mul_of_nonneg_right leReal (Nat.cast_nonneg w)
    have a : ((l:ℝ)*w*(g:ℝ))*(g:ℝ)≤(2*(s:ℝ))*(g:ℝ) := by
      calc _ = ((l:ℝ)*(g:ℝ)^2)*w := by ring
           _ ≤ _ := h
           _ = _ := by rw [rg]; ring
    have a' := (mul_le_mul_right gp).mp a
    have hG := mul_le_mul_of_nonneg_left realG (show 0≤(l:ℝ)*w by positivity)
    linarith only [a',hG]
  have leEpoch : l≤e := by
    have h := Nat.div_mul_le_self (2*s*tu) (g^2)
    have gg2 : 2≤g^2 := (by omega : 2≤g).trans (Nat.le_self_pow (by decide : 2≠0) _)
    have h' := Nat.mul_le_mul_left l gg2
    change l*g^2≤2*s*tu at h
    rw [Nat.mul_assoc] at h
    dsimp only [e]; omega
  have kBound : (k:ℝ)*w≤(1/40)*(s:ℝ)/16 := by
    have rp := r.positive
    have floor := Nat.floor_le (show (0:ℝ)≤2*r.p*(s*tu:ℕ) by positivity)
    apply (mul_le_mul_of_nonneg_right floor (Nat.cast_nonneg w)).trans_eq
    rw [rate,Nat.cast_mul]
    field_simp
    rw [rg]; ring
  have ucap : (ub:ℝ)≤5*(g:ℝ)*s := by
    calc _ ≤ ((5*w*e:ℕ):ℝ) := by exact_mod_cast advice_length (by omega : 2≤w) leEpoch
         _ = _ := by dsimp [e]; push_cast; rw [rg]; ring
  have acap : (ab:ℝ)≤17*tq*w := reply_length (w:=w) ww tp
  have pcap : (pb:ℝ)≤(s:ℝ)/160 := by
    apply (packet_length (by omega : 4≤w) (by linarith only [realS] : 32≤(1/40:ℝ)*s) late kBound).trans_eq
    ring
  have b := sizes ℓ s g w ub ab pb tq hl depth ns sn gn tp tqmax wh ucap acap pcap
  letI : Nonempty (Layer (ℓ*s^2) s) := ⟨S.block (Classical.choice (inferInstance : Nonempty W))⟩
  have card : (Fintype.card (Packet w l k):ℝ)≤(2:ℝ)^pb := by exact_mod_cast packet_bits w l k
  exact communication_bound (S.game k f) (unif O) (masks r (2^w)) sound balanced nb b.size
    (Nat.mul_pos hl (pow_pos sp _)) (dvd_mul_left _ _) ub ab (advice_bits _ _ _) (reply_bits _ _)
    _ _ _ (rpow_pos_of_pos (by exact_mod_cast nb) _) (rpow_pos_of_pos (by exact_mod_cast nb) _)
    (rpow_pos_of_pos (by exact_mod_cast nb) _) b.q b.c ((mul_le_mul_of_nonneg_left card (by norm_num : (0:ℝ)≤4)).trans b.p)
    b.large b.querySmooth b.rare

end
end DisjointnessDraft.PhysicalProtocol.Snapshot
