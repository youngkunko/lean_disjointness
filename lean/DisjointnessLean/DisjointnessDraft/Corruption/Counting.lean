import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Nat.Choose.Bounds
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic

/-! Counting uniform subsets without replacement. Bounds are written without
division by the layer size, including empty intersections and small complements. -/
namespace DisjointnessDraft.Corruption
open Finset Real
open scoped BigOperators
open Classical
noncomputable section

def layer (N s : ℕ) : Finset (Finset (Fin N)) := (univ : Finset (Fin N)).powersetCard s
@[simp] theorem mem_layer {N s : ℕ} {a : Finset (Fin N)} : a∈layer N s ↔ a.card=s := by simp [layer]
@[simp] theorem card_layer (N s : ℕ) : (layer N s).card=N.choose s := by simp [layer]

/-- The ratio of successive falling-factorial factors is bounded by its first ratio. -/
theorem choose_fraction {m N k : ℕ} (hm : m≤N) (hN : 0<N) :
    (m.choose k : ℝ) ≤ (m/(N:ℝ))^k * (N.choose k : ℝ) := by
  have pos : (0:ℝ)<N := by exact_mod_cast hN
  have aux (j : ℕ) : (m.descFactorial j:ℝ) ≤ (m/(N:ℝ))^j * (N.descFactorial j:ℝ) := by
    induction j with
    | zero => simp
    | succ j ih =>
      by_cases hj : j<m
      · have step : ((m-j:ℕ):ℝ) ≤ m/(N:ℝ)*(N-j:ℕ) := by
          rw [Nat.cast_sub hj.le,Nat.cast_sub (hj.le.trans hm),div_mul_eq_mul_div,le_div_iff₀ pos]
          nlinarith only [mul_le_mul_of_nonneg_left (show (m:ℝ)≤N by exact_mod_cast hm) (Nat.cast_nonneg j)]
        simp only [Nat.descFactorial_succ,Nat.cast_mul,pow_succ]
        calc _ ≤ _ := mul_le_mul step ih (Nat.cast_nonneg _) (by positivity)
             _ = _ := by ring
      · rw [Nat.descFactorial_succ,Nat.sub_eq_zero_of_le (by omega : m≤j),zero_mul,Nat.cast_zero]
        positivity
  have h := aux k
  simp only [Nat.descFactorial_eq_factorial_mul_choose,Nat.cast_mul] at h
  have fac : (0:ℝ)<k.factorial := by exact_mod_cast k.factorial_pos
  exact (le_of_mul_le_mul_left (a:= (k.factorial:ℝ)) (by nlinarith only [h]) fac)

theorem supersets_card {N s : ℕ} (T : Finset (Fin N)) :
    ((layer N s).filter (fun a => T⊆a)).card ≤ (N-T.card).choose (s-T.card) := by
  let U := (univ : Finset (Fin N)) \ T
  have bound : ((layer N s).filter (fun a => T⊆a)).card ≤ (U.powersetCard (s-T.card)).card := by
    apply card_le_card_of_injOn (fun a => a \ T)
    · intro a ha
      obtain ⟨h,inc⟩ := mem_filter.mp ha
      exact mem_powersetCard.mpr ⟨fun z hz => mem_sdiff.mpr ⟨mem_univ _,(mem_sdiff.mp hz).2⟩,by rw [card_sdiff inc,mem_layer.mp h]⟩
    · intro a ha b hb eq
      have ia := (mem_filter.mp ha).2
      have ib := (mem_filter.mp hb).2
      simpa only [sdiff_union_of_subset ia,sdiff_union_of_subset ib] using congrArg (· ∪ T) eq
  simpa [U,card_sdiff (subset_univ T)] using bound

theorem many_hit_count {N s k : ℕ} (P : Finset (Fin N)) (hN : 0<N) (hs : s≤N) (hk : k≤s) :
    (((layer N s).filter (fun a => k≤(a∩P).card)).card:ℝ) ≤
      (s.choose k:ℝ)*(P.card/(N:ℝ))^k*(layer N s).card := by
  let incident := fun T : Finset (Fin N) => (layer N s).filter (fun a => T⊆a)
  have cover : ((layer N s).filter (fun a => k≤(a∩P).card)).card ≤ (P.card.choose k)*((N-k).choose (s-k)) := by
    calc
      _ ≤ ((P.powersetCard k).biUnion incident).card := by
        apply card_le_card
        intro a ha
        obtain ⟨la,hp⟩ := mem_filter.mp ha
        obtain ⟨T,sub,size⟩ := exists_subset_card_eq hp
        exact mem_biUnion.mpr ⟨T,mem_powersetCard.mpr ⟨sub.trans inter_subset_right,size⟩,
          mem_filter.mpr ⟨la,sub.trans inter_subset_left⟩⟩
      _ ≤ _ := by
        have v := card_biUnion_le_card_mul (P.powersetCard k) incident ((N-k).choose (s-k)) (by
          intro T hT; have eq := (mem_powersetCard.mp hT).2; simpa only [incident,eq] using supersets_card (s:=s) T)
        simpa only [card_powersetCard] using v
  have p := choose_fraction (k:=k) (show P.card≤N by simpa using card_le_univ P) hN
  have comb : (N.choose s:ℝ)*(s.choose k:ℝ) = (N.choose k:ℝ)*((N-k).choose (s-k):ℝ) := by
    exact_mod_cast Nat.choose_mul hs hk
  rw [card_layer]
  calc
    _ ≤ (P.card.choose k:ℝ)*((N-k).choose (s-k):ℝ) := by exact_mod_cast cover
    _ ≤ _ := mul_le_mul_of_nonneg_right p (Nat.cast_nonneg _)
    _ = _ := by rw [mul_assoc,←comb]; ring

theorem avoidance_count {N s : ℕ} (V : Finset (Fin N)) (hN : 0<N) :
    (((layer N s).filter (fun a => Disjoint a V)).card : ℝ) ≤
      exp (-(s:ℝ)*V.card/N)*(layer N s).card := by
  let U := (univ : Finset (Fin N)) \ V
  have equal : (layer N s).filter (fun a => Disjoint a V) = U.powersetCard s := by
    ext a; simp only [mem_filter,mem_layer,mem_powersetCard]; constructor
    · rintro ⟨size,dis⟩
      exact ⟨fun z hz => mem_sdiff.mpr ⟨mem_univ _,fun h => disjoint_left.mp dis hz h⟩,size⟩
    · rintro ⟨sub,size⟩
      exact ⟨size,disjoint_left.mpr (fun z hz h => (mem_sdiff.mp (sub hz)).2 h)⟩
  have vl : V.card≤N := by simpa using card_le_univ V
  have up : U.card=N-V.card := by simp [U,card_sdiff (subset_univ V)]
  have step : ((N-V.card:ℕ):ℝ)/N ≤ exp (-(V.card:ℝ)/N) := by
    have e := add_one_le_exp (-(V.card:ℝ)/(N:ℝ))
    rw [Nat.cast_sub vl,sub_div,div_self (by exact_mod_cast hN.ne' : (N:ℝ)≠0)]
    simpa only [neg_div,sub_eq_add_neg,add_comm] using e
  rw [equal,card_powersetCard,up,card_layer]
  apply (choose_fraction (k:=s) (Nat.sub_le N V.card) hN).trans
  apply mul_le_mul_of_nonneg_right _ (Nat.cast_nonneg _)
  calc _ ≤ (exp (-(V.card:ℝ)/N))^s := pow_le_pow_left₀ (by positivity) step s
       _ = _ := by rw [←exp_nat_mul]; congr 1; ring

end
end DisjointnessDraft.Corruption
