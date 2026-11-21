import DisjointnessDraft.Corruption.Moment
import Mathlib.Analysis.SpecialFunctions.Log.Base

/-! The sparse-set corruption lemma and the min-entropy product corollary,
with exact manuscript constants. All probabilities are finite sums. -/
namespace DisjointnessDraft.Corruption
open Finset Real
open scoped BigOperators
open Classical
noncomputable section

/-- Independent distributions on the uniform layer with density at most
`2^(s/40)` relative to uniform. The published min-entropy corollary allows
one bit less concentration. -/
theorem product_corruption {N s : ℕ} (hs : 200≤s) (hN : 0<N) (hm : s^2∣N)
    (A B : Weights N) (hA : Capped (s:=s) A) (hB : Capped (s:=s) B) :
    (s:ℝ)^2/(100*N) ≤ intersectionMass N s A B := by
  obtain ⟨r,er⟩ := hm
  have eq : N=r*s^2 := by simpa [mul_comm] using er
  have sp : 0<s := by omega
  have hr : 0<r := Nat.pos_of_ne_zero (fun hz => by simp [eq,hz] at hN)
  have sn : s≤N := by rw [eq]; exact (Nat.le_self_pow (by decide : 2≠0) _).trans (Nat.le_mul_of_pos_left _ hr)
  have sr : (0:ℝ)<s := by exact_mod_cast sp
  have rr : (0:ℝ)<r := by exact_mod_cast hr
  have ne : (N:ℝ) = r*(s:ℝ)^2 := by exact_mod_cast eq
  by_contra! low
  let δ := (s:ℝ)^2/(100*N)
  have dp : 0<δ := by dsimp [δ]; positivity
  obtain ⟨D,num,dis,good⟩ := chain A B hA hB eq hr hs δ dp low
  have ex : (∑d∈D,hitProb N s B d) ≤ (groups s:ℝ)/50 := calc
    _ ≤ ∑_d∈D,2*δ := sum_le_sum fun d hd => (good d hd).2
    _ = _ := by simp only [sum_const,nsmul_eq_mul,num,Nat.cast_mul]; dsimp [δ]; rw [ne]; field_simp; ring
  have first : exp (-(log 2)*(groups s:ℝ)/50) ≤ moment (s:=s) B D := by
    apply le_trans _ (lower_moment hB D)
    apply exp_le_exp.mpr
    rw [mul_div_assoc]
    exact mul_le_mul_of_nonpos_left ex (by linarith [log_pos (by norm_num : (1:ℝ)<2)])
  have hk : s≤2*half s := by unfold half; omega
  have hreal : (s:ℝ)≤2*(half s:ℝ) := by exact_mod_cast hk
  have scale : 1/(2*(r:ℝ))≤(s:ℝ)*(half s:ℝ)/N := by
    rw [ne,div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith only [mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hreal sr.le) rr.le]
  have last := upper_moment hB hN sn D dis (fun d h => (good d h).1)
  rw [num] at last
  have total := first.trans (last.trans (mul_le_mul_of_nonneg_left (mask_decay (g:=groups s) hr scale) (cap_pos s).le))
  exact (not_le_of_gt (column_margin hs)) total

/-- The uniform distribution on a nonempty finite family. -/
def uniform {N : ℕ} (S : Finset (Row N)) : Weights N :=
  fun a => if a∈S then 1/(S.card:ℝ) else 0

private theorem uniform_capped {N s : ℕ} (sn : s≤N) (S : Finset (Row N)) (sub : S⊆layer N s)
    (large : (2:ℝ)^(-(s:ℝ)/40)*(layer N s).card≤S.card) : Capped (s:=s) (uniform S) := by
  classical
  have fl : (0:ℝ)<(layer N s).card := by rw [card_layer]; exact_mod_cast Nat.choose_pos sn
  have sz : (0:ℝ)<S.card := lt_of_lt_of_le (mul_pos (rpow_pos_of_pos (by norm_num : (0:ℝ)<2) _) fl) large
  have inter : (layer N s).filter (fun a => a∈S)=S := by
    ext a; simp only [mem_filter]; exact ⟨And.right,fun ha => ⟨sub ha,ha⟩⟩
  refine ⟨fun a _ => by by_cases h : a∈S <;> simp [uniform,h],?_,?_⟩
  · simp only [uniform,←sum_filter,inter,sum_const,nsmul_eq_mul]; field_simp
  · intro a _
    by_cases ha : a∈S
    · rw [uniform,if_pos ha,one_div,←div_eq_inv_mul]
      apply (div_le_iff₀ sz).mpr
      rw [neg_div,Real.rpow_neg (by norm_num : (0:ℝ)≤2),←div_eq_inv_mul] at large
      exact (div_le_iff₀ (cap_pos s)).mp large |>.trans_eq (mul_comm _ _)
    · simp [uniform,ha,(cap_pos s).le]

/-- Lemma 1 (uniform combinatorial rectangle), headed “Corruption for sparse sets.” -/
theorem uniform_corruption {N s : ℕ} (hs : 200≤s) (hN : 0<N) (hm : s^2∣N)
    (A B : Finset (Row N)) (a : A⊆layer N s) (b : B⊆layer N s)
    (hA : (2:ℝ)^(-(s:ℝ)/40)*(layer N s).card≤A.card)
    (hB : (2:ℝ)^(-(s:ℝ)/40)*(layer N s).card≤B.card) :
    (s:ℝ)^2/(100*N) ≤ intersectionMass N s (uniform A) (uniform B) := by
  have sn := (Nat.le_self_pow (by decide : 2≠0) s).trans (Nat.le_of_dvd hN hm)
  exact product_corruption hs hN hm _ _ (uniform_capped sn A a hA) (uniform_capped sn B b hB)

/-- The ordered row-and-piece witnesses of the draft's chain claim. Each source
row lies in the prescribed good subfamily of A, and each piece avoids all
earlier source rows. The proof constructs the witnesses at any positive δ. -/
theorem uniform_source_chain {N s : ℕ} (hs : 200≤s) (hN : 0<N) (hm : s^2∣N)
    (A B : Finset (Row N)) (a : A⊆layer N s) (b : B⊆layer N s)
    (hA : (2:ℝ)^(-(s:ℝ)/40)*(layer N s).card≤A.card)
    (hB : (2:ℝ)^(-(s:ℝ)/40)*(layer N s).card≤B.card)
    (δ : ℝ) (δp : 0<δ) (low : intersectionMass N s (uniform A) (uniform B)<δ) :
    ∃ rows : List (Row N × Row N), rows.length=(N/s^2)*groups s ∧
      (∀ p∈rows, p.1∈A ∧ hitProb N s (uniform B) p.1≤2*δ ∧
        p.2⊆p.1 ∧ p.2.card=half s) ∧
      rows.Pairwise (fun earlier later => Disjoint earlier.1 later.2) := by
  have sn := (Nat.le_self_pow (by decide : 2≠0) s).trans (Nat.le_of_dvd hN hm)
  obtain ⟨r,hr⟩ := hm
  have eq : N=r*s^2 := by simpa [mul_comm] using hr
  have rp : 0<r := Nat.pos_of_ne_zero (fun hz => by simp [eq,hz] at hN)
  have sp : 0<s^2 := pow_pos (by omega : 0<s) _
  obtain ⟨rows,len,good,fresh⟩ := chain_with_source_rows _ _
    (uniform_capped sn A a hA) (uniform_capped sn B b hB) eq rp hs δ δp low
  refine ⟨rows,by simpa [eq,Nat.mul_div_cancel _ sp] using len,?_,fresh⟩
  intro p hp
  obtain ⟨_,pos,cheap,sub,size⟩ := good p hp
  have mem : p.1∈A := by
    by_contra absent
    simp [uniform,absent] at pos
  exact ⟨mem,cheap,sub,size⟩

/-- The largest point mass on the layer, with zero adjoined for an empty layer. -/
def maxAtom (N s : ℕ) (A : Weights N) : ℝ :=
  (insert 0 ((layer N s).image A)).max' (insert_nonempty _ _)

def minEntropy (N s : ℕ) (A : Weights N) : ℝ := -(logb 2 (maxAtom N s A))

theorem capped_of_minEntropy {N s : ℕ} (sn : s≤N) (A : Weights N)
    (nonneg : ∀a∈layer N s,0≤A a) (total : ∑ a∈layer N s,A a=1)
    (entropy : logb 2 (layer N s).card - (s:ℝ)/40 ≤ minEntropy N s A) : Capped (s:=s) A := by
  refine ⟨nonneg,total,?_⟩
  intro a ha
  have fl : (0:ℝ)<(layer N s).card := by rw [card_layer]; exact_mod_cast Nat.choose_pos sn
  by_cases p : 0<A a
  · have lemax : A a≤maxAtom N s A := le_max' _ _ (mem_insert_of_mem (mem_image.mpr ⟨a,ha,rfl⟩))
    have logle := Real.logb_le_logb_of_le (by norm_num : (1:ℝ)<2) p lemax
    apply (logb_le_iff_le_rpow (by norm_num : (1:ℝ)<2) (mul_pos p fl)).mp
    rw [logb_mul p.ne' fl.ne']
    unfold minEntropy at entropy
    linarith only [entropy,logle]
  · rw [show A a=0 by linarith [nonneg a ha],zero_mul]
    exact (cap_pos s).le

/-- The published min-entropy product corollary, in bits. -/
theorem min_entropy_corruption {N s : ℕ} (hs : 200≤s) (hN : 0<N) (hm : s^2∣N)
    (A B : Weights N) (a : ∀x∈layer N s,0≤A x) (b : ∀x∈layer N s,0≤B x)
    (an : ∑ x∈layer N s,A x=1) (bn : ∑ x∈layer N s,B x=1)
    (hA : logb 2 (layer N s).card - ((s:ℝ)/40-1) ≤ minEntropy N s A)
    (hB : logb 2 (layer N s).card - ((s:ℝ)/40-1) ≤ minEntropy N s B) :
    (s:ℝ)^2/(100*N) ≤ intersectionMass N s A B := by
  have sn := (Nat.le_self_pow (by decide : 2≠0) s).trans (Nat.le_of_dvd hN hm)
  exact product_corruption hs hN hm A B (capped_of_minEntropy sn A a an (by linarith))
    (capped_of_minEntropy sn B b bn (by linarith))

end
end DisjointnessDraft.Corruption
