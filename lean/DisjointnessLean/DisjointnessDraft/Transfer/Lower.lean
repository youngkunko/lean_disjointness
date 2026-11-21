import DisjointnessDraft.Transfer.Operational
import DisjointnessFoundations.IndexAddressCapacity

/-! The target's original word width may carry any fixed positive multiple
of log N. A constant-factor widening supplies the disjoint clock address and
enough room for every operation ordinal on a fresh source history. -/
namespace DisjointnessDraft.Transfer.Compiler
open DisjointnessFoundations CellProbe MeasureTheory Filter Real
noncomputable section

theorem polynomial_actual (lo hi : ℝ) (lp : 0<lo) (lh : lo≤hi) (us fs : ℕ) (d e : ℝ) (d1 : 1≤d) (e1 : 1≤e) :
    ∃ c : ℝ,0<c ∧ ∀ᶠ n : ℕ in atTop, ∀ N w tu : ℕ, logb 2 n≤e*logb 2 N → logb 2 N≤d*logb 2 n →
    1≤tu → lo*logb 2 N≤w → (w:ℝ)≤hi*logb 2 N →
    ∀ (F U Q A Ω : Type) [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
      (S : Schedule n F U Q A) (D : Target F U Q A w Ω)
      (legal : F → List (Instr U Q) → Prop)
      (sel : Bool) (tq : ℝ), 1≤tq → Costs μ D legal tu tq →
      (∀ f xs q, xs.Nodup → ∀ h, h <+: before S xs ++ S.finish q → legal (S.initial f) h) →
      (∀ a f xs q, xs.Nodup →
        S.decode q ((script D a (before S xs).length (S.finish q)).run (observed D a (S.initial f) (before S xs)).2.1).1 =
         DisjointnessDraft.answer f xs q) →
      (∀ x,(S.insert x).length≤us) → (∀ q,(S.finish q).length≤fs) →
      (∀ q u,.inl u∈S.finish q → sel=true) →
      c*(Tradeoff.ratio N w tu)^2≤Transfer.charge sel tu tq ∧
      c*(FixedFamilySizes.logRatio N)^2≤max (tu:ℝ) tq := by
  have ep : 0<e := by linarith
  have small := div_pos lp ep
  obtain ⟨words,fit⟩ := ExtraQueries.index_room 2 (lo/e) small
  obtain ⟨c,cp,bound⟩ := Transfer.polynomial lo hi lp lh (us+2) (fs+1) (words+2)
    (by omega) (by omega) (by omega) d e d1 e1
  refine ⟨c,cp,?_⟩
  filter_upwards [bound,eventually_ge_atTop 2,eventually_ge_atTop us] with n lowerBound n2 nus
  intro N w tu nN sz tu1 wl wh F U Q A Ω _ μ _ S D legal sel tq tq1 gu path val sizeU sizeF gate
  have nn : 0<n := by omega
  have wn : lo/e*logb 2 n≤w := by
    calc _ ≤ lo/e*(e*logb 2 N) := mul_le_mul_of_nonneg_left nN small.le
         _ = lo*logb 2 N := by field_simp; ring
         _ ≤ _ := wl
  have logpos := logb_pos (b:=2) (by norm_num) (by exact_mod_cast (by omega : 1<n) : (1:ℝ)<n)
  have wp : 0<w := by exact_mod_cast ((mul_pos small logpos).trans_le wn)
  let v := (words+2)*w
  have hv : w<v := by simpa [v] using Nat.mul_lt_mul_of_pos_right (show 1<words+2 by omega) wp
  have big := fit n (n*us) w nn (by simpa [pow_two] using Nat.mul_le_mul_left n nus) wn
  have room : n*us<2^v := big.trans_lt (Nat.pow_lt_pow_right (by decide : 1<2) (by dsimp [v]; rw [Nat.add_mul]; omega))
  exact lowerBound N w v tu nN sz tu1 wl wh hv.le le_rfl Ω Ω μ (machine (layout w v hv) S D)
    (tape Ω) sel tq tq1 (by simpa only [Nat.cast_add,Nat.cast_one] using on_fresh_actual S (layout w v hv) D μ nn gu path val tu1 tq1 sizeU sizeF sel gate room)

theorem lower_actual (lo hi : ℝ) (lp : 0<lo) (lh : lo≤hi) (us fs : ℕ) (d : ℝ) (d1 : 1≤d) :
    ∃ c : ℝ,0<c ∧ ∀ᶠ n : ℕ in atTop, ∀ N w tu : ℕ, n≤N → logb 2 N≤d*logb 2 n →
    1≤tu → lo*logb 2 N≤w → (w:ℝ)≤hi*logb 2 N →
    ∀ (F U Q A Ω : Type) [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
      (S : Schedule n F U Q A) (D : Target F U Q A w Ω)
      (legal : F → List (Instr U Q) → Prop)
      (sel : Bool) (tq : ℝ), 1≤tq → Costs μ D legal tu tq →
      (∀ f xs q, xs.Nodup → ∀ h, h <+: before S xs ++ S.finish q → legal (S.initial f) h) →
      (∀ a f xs q, xs.Nodup →
        S.decode q ((script D a (before S xs).length (S.finish q)).run (observed D a (S.initial f) (before S xs)).2.1).1 =
         DisjointnessDraft.answer f xs q) →
      (∀ x,(S.insert x).length≤us) → (∀ q,(S.finish q).length≤fs) →
      (∀ q u,.inl u∈S.finish q → sel=true) →
      c*(Tradeoff.ratio N w tu)^2≤Transfer.charge sel tu tq ∧
      c*(FixedFamilySizes.logRatio N)^2≤max (tu:ℝ) tq := by
  obtain ⟨c,cp,H⟩ := polynomial_actual lo hi lp lh us fs d 1 d1 le_rfl
  refine ⟨c,cp,?_⟩
  filter_upwards [H,eventually_ge_atTop 1] with n res pos
  intro N w tu nN
  have le := logb_le_logb_of_le (b:=2) (by norm_num) (show (0:ℝ)<n by exact_mod_cast pos) (show (n:ℝ)≤N by exact_mod_cast nN)
  exact res N w tu (by simpa using le)

theorem lower (lo hi : ℝ) (lp : 0<lo) (lh : lo≤hi) (us fs : ℕ) (d : ℝ) (d1 : 1≤d) :
    ∃ c : ℝ,0<c ∧ ∀ᶠ n : ℕ in atTop, ∀ N w tu : ℕ, n≤N → logb 2 N≤d*logb 2 n →
    1≤tu → lo*logb 2 N≤w → (w:ℝ)≤hi*logb 2 N →
    ∀ (F U Q A Ω : Type) [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
      (S : Schedule n F U Q A) (D : Target F U Q A w Ω)
      (legal : F → List (Instr U Q) → Prop) (spec : F → List (Instr U Q) → Q → A)
      (sel : Bool) (tq : ℝ), 1≤tq → Guarantees μ D legal spec tu tq → Valid S legal spec →
      (∀ x,(S.insert x).length≤us) → (∀ q,(S.finish q).length≤fs) →
      (∀ q u,.inl u∈S.finish q → sel=true) →
      c*(Tradeoff.ratio N w tu)^2≤Transfer.charge sel tu tq ∧
      c*(FixedFamilySizes.logRatio N)^2≤max (tu:ℝ) tq := by
  obtain ⟨c,cp,cert⟩ := lower_actual lo hi lp lh us fs d d1
  refine ⟨c,cp,?_⟩
  filter_upwards [cert] with n useBound
  intro N w tu nN size tu1 wl wh F U Q A Ω _ μ _ S D legal spec sel tq tq1 g ok ucap qcap gate
  apply useBound N w tu nN size tu1 wl wh F U Q A Ω μ S D legal sel tq tq1 g.costs ok.1 _ ucap qcap gate
  intro a f xs q nd
  rw [actual_answers μ D a spec g _ _ _ (finish_path S ok.1 f xs q nd)]
  exact ok.2 f xs q nd

theorem polynomial (lo hi : ℝ) (lp : 0<lo) (lh : lo≤hi) (us fs : ℕ) (d e : ℝ) (d1 : 1≤d) (e1 : 1≤e) :
    ∃ c : ℝ,0<c ∧ ∀ᶠ n : ℕ in atTop, ∀ N w tu : ℕ, logb 2 n≤e*logb 2 N → logb 2 N≤d*logb 2 n →
    1≤tu → lo*logb 2 N≤w → (w:ℝ)≤hi*logb 2 N →
    ∀ (F U Q A Ω : Type) [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
      (S : Schedule n F U Q A) (D : Target F U Q A w Ω)
      (legal : F → List (Instr U Q) → Prop) (spec : F → List (Instr U Q) → Q → A)
      (sel : Bool) (tq : ℝ), 1≤tq → Guarantees μ D legal spec tu tq → Valid S legal spec →
      (∀ x,(S.insert x).length≤us) → (∀ q,(S.finish q).length≤fs) →
      (∀ q u,.inl u∈S.finish q → sel=true) →
      c*(Tradeoff.ratio N w tu)^2≤Transfer.charge sel tu tq ∧
      c*(FixedFamilySizes.logRatio N)^2≤max (tu:ℝ) tq := by
  obtain ⟨c,cp,cert⟩ := polynomial_actual lo hi lp lh us fs d e d1 e1
  refine ⟨c,cp,?_⟩
  filter_upwards [cert] with n useBound
  intro N w tu nN size tu1 wl wh F U Q A Ω _ μ _ S D legal spec sel tq tq1 g ok ucap qcap gate
  apply useBound N w tu nN size tu1 wl wh F U Q A Ω μ S D legal sel tq tq1 g.costs ok.1 _ ucap qcap gate
  intro a f xs q nd
  rw [actual_answers μ D a spec g _ _ _ (finish_path S ok.1 f xs q nd)]
  exact ok.2 f xs q nd

end
end DisjointnessDraft.Transfer.Compiler
