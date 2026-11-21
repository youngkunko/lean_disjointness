import DisjointnessDraft.Corruption.Scalars
import Mathlib.Data.Finset.Pairwise

/-! Extract many pairwise disjoint fresh pieces from low-intersection rows. -/
namespace DisjointnessDraft.Corruption
open Finset Real
open scoped BigOperators
open Classical
noncomputable section
abbrev Row (N : ℕ) := Finset (Fin N)
abbrev Weights (N : ℕ) := Row N → ℝ

structure Capped {N s : ℕ} (A : Weights N) : Prop where
  nonneg : ∀ a∈layer N s, 0≤A a
  total : ∑ a∈layer N s,A a=1
  atom : ∀ a∈layer N s, A a*(layer N s).card≤capFactor s

def hitProb (N s : ℕ) (B : Weights N) (a : Row N) := ∑ b∈(layer N s).filter (fun b => ¬Disjoint a b),B b
def intersectionMass (N s : ℕ) (A B : Weights N) := ∑ a∈layer N s,A a*hitProb N s B a

theorem mass_cap {N s : ℕ} {A : Weights N} (hA : Capped (s:=s) A) (S : Finset (Row N)) (sub : S⊆layer N s) :
    (∑ a∈S,A a)*(layer N s).card≤capFactor s*S.card := by
  rw [sum_mul]
  calc _ ≤ ∑ _a∈S,capFactor s := sum_le_sum fun a h => hA.atom a (sub h)
       _ = _ := by simp [mul_comm]

private theorem fresh_row {N s : ℕ} (A B : Weights N) (hA : Capped (s:=s) A) (hB : Capped (s:=s) B)
    (hp : 0<N) (hsN : s≤N) (hs : 200≤s) (δ : ℝ) (δp : 0<δ) (low : intersectionMass N s A B<δ)
    (P : Row N) (small : 6*P.card≤N) :
    ∃ a∈layer N s, 0<A a ∧ hitProb N s B a≤2*δ ∧ (a∩P).card<half s := by
  classical
  let F := layer N s
  let k := half s
  let bad := F.filter (fun a => k≤(a∩P).card)
  let other := F.filter (fun a => ¬k≤(a∩P).card)
  have sp : 0<s := by omega
  have ol : (0:ℝ)<F.card := by exact_mod_cast (card_layer N s ▸ Nat.choose_pos hsN)
  have L : (P.card/(N:ℝ))≤1/6 := by
    rw [div_le_iff₀ (by exact_mod_cast hp : (0:ℝ)<N)]
    have h : 6*(P.card:ℝ)≤N := by exact_mod_cast small
    linarith only [h]
  have K := many_hit_count (k:=k) P hp hsN (by dsimp [k,half]; omega)
  have U : (bad.card:ℝ) ≤ (2:ℝ)^s*(1/6:ℝ)^k*F.card := by
    apply K.trans
    exact mul_le_mul_of_nonneg_right (mul_le_mul
      (by exact_mod_cast (Nat.choose_le_two_pow s k sp).le)
      (pow_le_pow_left₀ (by positivity) L k) (by positivity) (by positivity)) (Nat.cast_nonneg _)
  have V := mass_cap hA bad (filter_subset _ _)
  have lim : ∑ a∈bad,A a < 1/2 := by
    apply (mul_lt_mul_right ol).mp
    calc _ ≤ _ := V
         _ ≤ _ := mul_le_mul_of_nonneg_left U (cap_pos s).le
         _ = (capFactor s*(2:ℝ)^s*(1/6:ℝ)^k)*F.card := by ring
         _ < _ := mul_lt_mul_of_pos_right (small_tail hs) ol
  have split : (∑ a∈bad,A a)+(∑ a∈other,A a)=1 :=
    (sum_filter_add_sum_filter_not F _ _).trans hA.total
  by_contra no
  have expensive (a : Row N) (ha : a∈other) : A a*(2*δ) ≤ A a*hitProb N s B a := by
    obtain ⟨mem,sk⟩ := mem_filter.mp ha
    rcases (hA.nonneg a mem).eq_or_lt with zero | pos
    · simp [←zero]
    · apply mul_le_mul_of_nonneg_left _ pos.le
      by_contra! cheap
      exact no ⟨a, mem, pos, cheap.le, lt_of_not_ge sk⟩
  have x := sum_le_sum (s:=other) expensive
  have y : (∑ a∈other,A a*hitProb N s B a) ≤ ∑ a∈F,A a*hitProb N s B a := sum_le_sum_of_subset_of_nonneg (filter_subset _ _) (fun a ha _ =>
    mul_nonneg (hA.nonneg a ha) (sum_nonneg (fun b hb => hB.nonneg b (mem_filter.mp hb).1) : 0≤hitProb N s B a))
  change ∑ a∈F,A a*hitProb N s B a < δ at low
  rw [←sum_mul] at x
  have gt := mul_lt_mul_of_pos_right (show 1/2<(∑ a∈other,A a) by linarith only [lim,split]) (show 0<2*δ by positivity)
  linarith only [x,y,low,gt]

/-- Each pair records its source row and its new piece. Every later piece
is disjoint from the entire source row of every earlier pair. -/
theorem chain_with_source_rows {N s r : ℕ} (A B : Weights N)
    (hA : Capped (s:=s) A) (hB : Capped (s:=s) B)
    (hN : N=r*s^2) (hr : 0<r) (hs : 200≤s) (δ : ℝ) (δp : 0<δ)
    (low : intersectionMass N s A B<δ) :
    ∃ rows : List (Row N × Row N), rows.length=r*groups s ∧
      (∀ p∈rows, p.1∈layer N s ∧ 0<A p.1 ∧ hitProb N s B p.1≤2*δ ∧
        p.2⊆p.1 ∧ p.2.card=half s) ∧
      rows.Pairwise (fun earlier later => Disjoint earlier.1 later.2) := by
  have sp : 0<s := by omega
  have np : 0<N := hN ▸ Nat.mul_pos hr (pow_pos sp _)
  have sn : s≤N := by
    rw [hN]
    exact (Nat.le_self_pow (by decide : 2≠0) s).trans (Nat.le_mul_of_pos_left _ hr)
  have go (j : ℕ) (hj : j≤r*groups s) :
      ∃ rows : List (Row N × Row N), rows.length=j ∧
        (∀ p∈rows, p.1∈layer N s ∧ 0<A p.1 ∧ hitProb N s B p.1≤2*δ ∧
          p.2⊆p.1 ∧ p.2.card=half s) ∧
        rows.Pairwise (fun earlier later => Disjoint earlier.1 later.2) := by
    induction j with
    | zero => exact ⟨[],by simp⟩
    | succ j ih =>
      obtain ⟨rows,len,good,fresh⟩ := ih (by omega)
      let P : Row N := rows.toFinset.biUnion Prod.fst
      have count : rows.toFinset.card≤j := len ▸ List.toFinset_card_le rows
      have rowSize (p : Row N × Row N) (hp : p∈rows.toFinset) : p.1.card≤s :=
        (mem_layer.mp (good p (List.mem_toFinset.mp hp)).1).le
      have pc : P.card≤j*s := (card_biUnion_le_card_mul _ _ _ rowSize).trans
        (Nat.mul_le_mul_right s count)
      have g6 : groups s*6≤s := Nat.div_mul_le_self _ _
      have small : 6*P.card≤N := calc
        _ ≤ 6*(j*s) := Nat.mul_le_mul_left _ pc
        _ ≤ 6*((r*groups s)*s) := Nat.mul_le_mul_left _ (Nat.mul_le_mul_right s (by omega))
        _ = r*s*(groups s*6) := by ring
        _ ≤ r*s*s := Nat.mul_le_mul_left _ g6
        _ = N := by rw [hN]; ring
      obtain ⟨a,ha,positive,cheap,overlap⟩ := fresh_row A B hA hB np sn hs δ δp low P small
      have enough : half s≤(a\P).card := by
        have counted := card_sdiff_add_card_inter a P
        have size := mem_layer.mp ha
        unfold half at *; omega
      obtain ⟨d,inside,size⟩ := exists_subset_card_eq enough
      refine ⟨rows++[(a,d)],by simp [len],?_,?_⟩
      · intro p hp
        rcases List.mem_append.mp hp with old | last
        · exact good p old
        · obtain rfl := List.mem_singleton.mp last
          exact ⟨ha,positive,cheap,inside.trans sdiff_subset,size⟩
      · apply List.pairwise_append.mpr
        refine ⟨fresh,by simp,?_⟩
        intro p hp q hq
        obtain rfl := List.mem_singleton.mp hq
        exact disjoint_left.mpr fun x hx hd =>
          (mem_sdiff.mp (inside hd)).2 (mem_biUnion.mpr ⟨p,List.mem_toFinset.mpr hp,hx⟩)
  exact go _ le_rfl

theorem chain {N s r : ℕ} (A B : Weights N) (hA : Capped (s:=s) A) (hB : Capped (s:=s) B)
    (hN : N=r*s^2) (hr : 0<r) (hs : 200≤s) (δ : ℝ) (δp : 0<δ) (low : intersectionMass N s A B<δ) :
    ∃ D : Finset (Row N), D.card=r*groups s ∧ D.toSet.PairwiseDisjoint id ∧
      ∀ d∈D, d.card=half s ∧ hitProb N s B d≤2*δ := by
  obtain ⟨rows,len,good,fresh⟩ := chain_with_source_rows A B hA hB hN hr hs δ δp low
  let pieces := rows.map Prod.snd
  have piece_info (d : Row N) (hd : d∈pieces) : d.card=half s ∧ hitProb N s B d≤2*δ := by
    obtain ⟨p,hp,rfl⟩ := List.mem_map.mp hd
    obtain ⟨_,_,cheap,inside,size⟩ := good p hp
    refine ⟨size,le_trans ?_ cheap⟩
    apply sum_le_sum_of_subset_of_nonneg
    · intro b hb
      obtain ⟨lb,hit⟩ := mem_filter.mp hb
      exact mem_filter.mpr ⟨lb,fun miss => hit (miss.mono_left inside)⟩
    · intro b hb _; exact hB.nonneg b (mem_filter.mp hb).1
  have dis : pieces.Pairwise Disjoint := List.pairwise_map.mpr
    (fresh.imp_of_mem fun hp _ sep => sep.mono_left (good _ hp).2.2.2.1)
  have distinct : pieces.Nodup := dis.imp_of_mem (by
    intro a b ha _ sep eq
    subst b
    have empty := (Finset.disjoint_self_iff_empty a).mp sep
    have size := (piece_info a ha).1
    simp only [empty,card_empty] at size
    unfold half at size
    omega)
  refine ⟨pieces.toFinset,(List.toFinset_card_of_nodup distinct).trans ?_,?_,?_⟩
  · simpa [pieces] using len
  · exact (List.pairwise_iff_coe_toFinset_pairwise distinct symmetric_disjoint).mpr dis
  · intro d hd
    exact piece_info d (List.mem_toFinset.mp hd)

end
end DisjointnessDraft.Corruption
