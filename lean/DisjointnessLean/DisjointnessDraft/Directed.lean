import DisjointnessDraft.Reachability
import DisjointnessDraft.Maximum
import DisjointnessFoundations.PolynomialScaleComparison

/-! The two bounds on single-sink incremental directed reachability at
each sufficiently large vertex count, with an empty initial graph. -/
namespace DisjointnessDraft.Reachability
open DisjointnessFoundations CellProbe Applications.Graphs MeasureTheory Filter Real
open scoped ENNReal
noncomputable section

def coreEquiv (n : ℕ) : Core n ≃ ((Fin n ⊕ Fin n) ⊕ Fin n) ⊕ Bool where
  toFun
    | .row r => .inl (.inl r)
    | .col j => .inl (.inr j)
    | .source => .inr false
    | .target => .inr true
  invFun
    | .inl (.inl r) => .row r
    | .inl (.inr j) => .col j
    | .inr false => .source
    | .inr true => .target
  left_inv x := by cases x <;> rfl
  right_inv x := by rcases x with (r|j)|(t|t) <;> rfl

def pad (N : ℕ) := N-(3*(N/4)+2)

theorem cardinality {N : ℕ} (h : 8≤N) : Fintype.card (Vertex (N/4) (pad N))=N := by
  rw [show Fintype.card (Vertex (N/4) (pad N))=Fintype.card (Core (N/4))+pad N by simp [Vertex],
    Fintype.card_congr (coreEquiv (N/4))]
  simp only [Fintype.card_sum,Fintype.card_fin,Fintype.card_bool,pad]
  omega

theorem directed (lo hi : ℝ) (lp : 0<lo) (lu : lo≤hi) :
    ∃ c : ℝ, 0<c ∧ ∀ᶠ N : ℕ in atTop,
    let n := N/4
    let V' := Vertex n (pad N)
    Fintype.card V'=N ∧ ∀ w tu : ℕ, 1≤tu → lo*logb 2 N≤w → (w:ℝ)≤hi*logb 2 N →
    ∀ (Ω C : Type) [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
      (D : DataStructure w Unit (Edge V') V' C) (R : RandomTape Ω C) (tq : ℝ),
      1≤tq → OnDAG μ D R (target n (pad N)) tu tq →
      c*(Tradeoff.ratio N w tu)^2≤tq ∧ c*(FixedFamilySizes.logRatio N)^2≤max (tu:ℝ) tq := by
  have hp := lp.trans_le lu
  obtain ⟨d,dp,H⟩ := Fresh.lower lo (3*hi) lp (by linarith)
  obtain ⟨L,hL⟩ := eventually_atTop.mp H
  let e := d/9
  let c := min (min 1 (e/16)) e
  have ep : 0<e := div_pos dp (by norm_num)
  refine ⟨c,lt_min (lt_min (by norm_num) (by positivity)) ep,?_⟩
  filter_upwards [eventually_ge_atTop (4*L+16),Tradeoff.log_tends.eventually_ge_atTop (2/lo),
    Tradeoff.log_tends.eventually_ge_atTop 2,Tradeoff.log_tends.eventually_ge_atTop hi] with N big nw two four
  intro n V'
  have large : L≤n := by dsimp [n]; omega
  have n4 : 4≤n := by dsimp [n]; omega
  have cube : N≤n^3 := by
    have nf : N≤4*n+3 := by dsimp [n]; omega
    have z := Nat.mul_le_mul_right n n4
    have y := Nat.mul_le_mul_right (n^2) n4
    nlinarith only [nf,z,y,n4]
  have logs := ApplicationSizes.log_range (by omega : 2≤n) (Nat.div_le_self N 4) cube
  refine ⟨cardinality (by omega),?_⟩
  intro w tu tp wl wh Ω C _ μ _ D R tq qp promises
  have w2 : 2≤w := by
    have z := (div_le_iff₀ lp).mp nw
    exact_mod_cast (show (2:ℝ)≤w by nlinarith only [wl,z])
  let A := translation n (pad N)
  have ok := Preload.transfer A D R μ tu tq (guarantees μ D R promises)
  have cap : (w:ℝ)≤3*hi*logb 2 n := wh.trans ((mul_le_mul_of_nonneg_left logs.2 hp.le).trans_eq (by ring))
  have b := hL n large w tu (by omega) tp ((mul_le_mul_of_nonneg_left logs.1 lp.le).trans wl) cap
    Ω (ℕ × Ω) μ _ _ tq qp ok
  have prod : (2:ℝ)≤tu*w := (by exact_mod_cast w2 : (2:ℝ)≤w).trans
    (by simpa using mul_le_mul_of_nonneg_right (show (1:ℝ)≤tu by exact_mod_cast tp) (Nat.cast_nonneg w))
  have logpos := logb_pos (by norm_num : (1:ℝ)<2) (by linarith : 1<(tu:ℝ)*w)
  have rp : 0≤Tradeoff.ratio N w tu := div_nonneg (by linarith : 0≤logb 2 N) logpos.le
  have rr : Tradeoff.ratio N w tu≤3*Tradeoff.ratio n w tu := by
    unfold Tradeoff.ratio; rw [mul_div_assoc']; exact div_le_div_of_nonneg_right logs.2 logpos.le
  have trade : e*(Tradeoff.ratio N w tu)^2≤tq := calc
    _ ≤ e*(3*Tradeoff.ratio n w tu)^2 := mul_le_mul_of_nonneg_left (pow_le_pow_left₀ rp rr 2) ep.le
    _ = d*(Tradeoff.ratio n w tu)^2 := by dsimp [e]; ring
    _ ≤ tq := b
  exact ⟨(mul_le_mul_of_nonneg_right (min_le_right _ _) (sq_nonneg _)).trans trade,
    (mul_le_mul_of_nonneg_right (min_le_left _ _) (sq_nonneg _)).trans (max_from_tradeoff ep tp w2 two four wh trade)⟩

end
end DisjointnessDraft.Reachability
