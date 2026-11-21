import DisjointnessDraft.Maximum
import DisjointnessDraft.Fresh

/-! Uniform rescaling for a constant-operation simulation with polynomial size
distortion and constant word expansion. The output-query bound distinguishes
whether the source query uses target updates. -/
namespace DisjointnessDraft.Transfer
open DisjointnessFoundations CellProbe MeasureTheory Filter Real
open scoped ENNReal
noncomputable section

def charge (usesUpdate : Bool) (tu : ℕ) (tq : ℝ) := tq+if usesUpdate then (tu:ℝ) else 0

theorem costs {n N w src u A W : ℕ} {d : ℝ}
    (w2 : 2≤w) (tu : 1≤u) (A1 : 1≤A) (W1 : 1≤W) (n1 : 1≤n) (_N1 : 1≤N)
    (wlow : w≤src) (whi : src≤W*w) (dpos : 0<d) (size : logb 2 (N:ℝ)≤d*logb 2 n) :
    Tradeoff.ratio N w u ≤ (d*(1+logb 2 ((A*W:ℕ):ℝ)))*Tradeoff.ratio n src (A*u) := by
  let t := (u:ℝ)*w
  let v := ((A:ℝ)*u)*src
  let k := ((A*W:ℕ):ℝ)
  have t2 : (2:ℝ)≤t := by dsimp [t]; exact_mod_cast (w2.trans (Nat.le_mul_of_pos_left _ tu))
  have s2 : (2:ℝ)≤v := by dsimp [v]; exact_mod_cast ((w2.trans wlow).trans (Nat.le_mul_of_pos_left _ (Nat.mul_pos A1 tu)))
  have k1 : 1≤k := by dsimp [k]; exact_mod_cast (Nat.mul_pos A1 W1)
  have lv : 0<logb 2 v := logb_pos (by norm_num) (by linarith)
  have lt1 : 1≤logb 2 t := by simpa using logb_le_logb_of_le (b:=2) (by norm_num) (by norm_num : (0:ℝ)<2) t2
  have lk : 0≤logb 2 k := logb_nonneg (by norm_num) k1
  have vp : v≤k*t := by
    have a := Nat.mul_le_mul_left (A*u) whi
    dsimp [v,k,t]; push_cast
    calc _ ≤ ((A:ℝ)*u)*((W:ℝ)*w) := by exact_mod_cast a
         _ = _ := by ring
  have b := logb_le_logb_of_le (b:=2) (by norm_num) (by linarith : 0<v) vp
  rw [logb_mul (by linarith : k≠0) (by linarith : t≠0)] at b
  have den : logb 2 v≤(1+logb 2 k)*logb 2 t := by nlinarith only [b,mul_le_mul_of_nonneg_left lt1 lk]
  have pn := logb_nonneg (by norm_num : (1:ℝ)<2) (by exact_mod_cast n1 : (1:ℝ)≤n)
  change logb 2 N/logb 2 t ≤ (d*(1+logb 2 k))*(logb 2 n/logb 2 v)
  rw [mul_div_assoc',div_le_div_iff₀ (by linarith) lv]
  nlinarith only [mul_le_mul_of_nonneg_right size lv.le,mul_le_mul_of_nonneg_left den (mul_nonneg dpos.le pn)]

/-! Two-sided polynomial size distortion also permits a target smaller than the source. -/
theorem polynomial (lo hi : ℝ) (lp : 0<lo) (lh : lo≤hi) (A B W : ℕ) (A1 : 1≤A) (B1 : 1≤B) (W1 : 1≤W)
    (d e₀ : ℝ) (d1 : 1≤d) (e1 : 1≤e₀) :
    ∃ c : ℝ,0<c ∧ ∀ᶠ n : ℕ in atTop, ∀ N w v tu : ℕ, logb 2 n ≤ e₀*logb 2 N → logb 2 N≤d*logb 2 n →
    1≤tu → lo*logb 2 N≤w → (w:ℝ)≤hi*logb 2 N → w≤v → v≤W*w →
    ∀ (Ω C : Type) [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
      (D : Machine n v C) (R : RandomTape Ω C) (sel : Bool) (tq : ℝ), 1≤tq →
      Fresh.OnFresh μ D R (A*tu) (B*charge sel tu tq) →
      c*(Tradeoff.ratio N w tu)^2≤charge sel tu tq ∧
      c*(FixedFamilySizes.logRatio N)^2≤max (tu:ℝ) tq := by
  have epos : 0<e₀ := by linarith
  have wlpos := div_pos lp epos
  have smallLo : lo/e₀≤lo := (div_le_iff₀ epos).mpr (by simpa using mul_le_mul_of_nonneg_left e1 lp.le)
  have b1 : (1:ℝ)≤B := by exact_mod_cast B1
  have w1 : (1:ℝ)≤W := by exact_mod_cast W1
  have hp := lp.trans_le lh
  have dl : 0<d := by linarith
  have expand1 : hi≤(W:ℝ)*hi := by simpa using mul_le_mul_of_nonneg_right w1 hp.le
  have expand2 : (W:ℝ)*hi≤(W:ℝ)*hi*d := by simpa using mul_le_mul_of_nonneg_left d1 (show 0≤(W:ℝ)*hi by positivity)
  have expansion := lh.trans (expand1.trans expand2)
  obtain ⟨k,kp,L⟩ := Fresh.lower (lo/e₀) (W*hi*d) wlpos (smallLo.trans expansion)
  let K := d*(1+logb 2 ((A*W:ℕ):ℝ))
  have kp' : 0<K := by
    have one : (1:ℝ)≤(A*W:ℕ) := by exact_mod_cast (Nat.mul_pos A1 W1)
    have h := logb_nonneg (by norm_num : (1:ℝ)<2) one
    exact mul_pos dl (by linarith)
  let e := k/(B*K^2)
  have ep : 0<e := div_pos kp (by positivity)
  let c := min e (min 1 (e/16)/2)
  refine ⟨c,lt_min ep (div_pos (lt_min (by norm_num) (by positivity)) (by norm_num)),?_⟩
  filter_upwards [L,eventually_ge_atTop 2,Tradeoff.log_tends.eventually_ge_atTop (2/(lo/e₀)),
    Tradeoff.log_tends.eventually_ge_atTop (e₀*2),Tradeoff.log_tends.eventually_ge_atTop (e₀*hi)] with n low n2 big two top
  intro N w v tu nN Ns tu1 wl wh wv vw Ω C _ μ _ D R sel tq tq1 sim
  have wn : lo/e₀*logb 2 n ≤ w := by
    have h := mul_le_mul_of_nonneg_left nN wlpos.le
    calc _ ≤ lo/e₀*(e₀*logb 2 N) := h
         _ = lo*logb 2 N := by field_simp; ring
         _ ≤ _ := wl
  have twoN := (mul_le_mul_left epos).mp (two.trans nN)
  have hiN := (mul_le_mul_left epos).mp (top.trans nN)
  have N1 : 1≤N := by
    cases N with
    | zero => norm_num [Real.logb] at twoN
    | succ k => exact Nat.succ_le_succ (Nat.zero_le _)
  have w2 : 2≤w := by
    have H := (div_le_iff₀ wlpos).mp big
    exact_mod_cast (show (2:ℝ)≤w by nlinarith only [wn,H])
  have cap : (v:ℝ)≤(W:ℝ)*hi*d*logb 2 n := by
    have z := mul_le_mul_of_nonneg_left (wh.trans (mul_le_mul_of_nonneg_left Ns hp.le)) (Nat.cast_nonneg W)
    exact (by exact_mod_cast vw : (v:ℝ)≤(W:ℝ)*w).trans (z.trans_eq (by ring))
  have pay1 : 1≤charge sel tu tq := by
    cases sel
    · simpa [charge] using tq1
    · simp only [charge,if_true]; linarith [show 0≤(tu:ℝ) from Nat.cast_nonneg _]
  have pay := low v (A*tu) (by omega) (Nat.mul_pos A1 tu1) (wn.trans (by exact_mod_cast wv)) cap Ω C μ D R _ (one_le_mul_of_one_le_of_one_le b1 pay1) sim
  have rr := costs w2 tu1 A1 W1 (by omega) (by omega) wv vw dl Ns
  have non : 0≤Tradeoff.ratio N w tu := div_nonneg (logb_nonneg (by norm_num) (by exact_mod_cast (by omega : 1≤N))) (logb_nonneg (by norm_num)
    (by exact_mod_cast (Nat.mul_pos tu1 (by omega : 0<w)) : (1:ℝ)≤tu*w))
  have hsq := pow_le_pow_left₀ non rr 2
  change (Tradeoff.ratio N w tu)^2 ≤ (K*Tradeoff.ratio n v (A*tu))^2 at hsq
  have fin : e*(Tradeoff.ratio N w tu)^2≤charge sel tu tq := calc
    _ ≤ e*(K*Tradeoff.ratio n v (A*tu))^2 := mul_le_mul_of_nonneg_left hsq ep.le
    _ = k*(Tradeoff.ratio n v (A*tu))^2/B := by dsimp [e]; field_simp; ring
    _ ≤ _ := (div_le_iff₀ (by linarith)).mpr (by simpa [mul_comm] using pay)
  have m := max_from_tradeoff ep tu1 w2 twoN hiN wh fin
  have qcap : max (tu:ℝ) (charge sel tu tq)≤2*max (tu:ℝ) tq := by
    have x := le_max_left (tu:ℝ) tq; have y := le_max_right (tu:ℝ) tq
    apply max_le
    · linarith [show 0≤(tu:ℝ) from Nat.cast_nonneg _]
    · cases sel <;> simp only [charge,if_false,if_true,add_zero,Bool.false_eq_true] <;> linarith [show 0≤(tu:ℝ) from Nat.cast_nonneg _]
  refine ⟨(mul_le_mul_of_nonneg_right (min_le_left _ _) (sq_nonneg _)).trans fin,?_⟩
  have le := mul_le_mul_of_nonneg_right (min_le_right e (min 1 (e/16)/2)) (sq_nonneg (FixedFamilySizes.logRatio N))
  change _≤_ at le
  dsimp [c]; linarith only [le,m,qcap]

theorem lower (lo hi : ℝ) (lp : 0<lo) (lh : lo≤hi) (A B W : ℕ) (A1 : 1≤A) (B1 : 1≤B) (W1 : 1≤W)
    (d : ℝ) (d1 : 1≤d) :
    ∃ c : ℝ,0<c ∧ ∀ᶠ n : ℕ in atTop, ∀ N w v tu : ℕ, n≤N → logb 2 N≤d*logb 2 n →
    1≤tu → lo*logb 2 N≤w → (w:ℝ)≤hi*logb 2 N → w≤v → v≤W*w →
    ∀ (Ω C : Type) [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
      (D : Machine n v C) (R : RandomTape Ω C) (sel : Bool) (tq : ℝ), 1≤tq →
      Fresh.OnFresh μ D R (A*tu) (B*charge sel tu tq) →
      c*(Tradeoff.ratio N w tu)^2≤charge sel tu tq ∧
      c*(FixedFamilySizes.logRatio N)^2≤max (tu:ℝ) tq := by
  obtain ⟨c,hc,H⟩ := polynomial lo hi lp lh A B W A1 B1 W1 d 1 d1 le_rfl
  refine ⟨c,hc,?_⟩
  filter_upwards [H,eventually_ge_atTop 1] with n bound pos
  intro N w v tu nN
  have le := logb_le_logb_of_le (b:=2) (by norm_num) (show (0:ℝ)<n by exact_mod_cast pos) (show (n:ℝ)≤N by exact_mod_cast nN)
  exact bound N w v tu (by simpa using le)

end
end DisjointnessDraft.Transfer
