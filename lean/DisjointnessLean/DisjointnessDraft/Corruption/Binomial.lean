import DisjointnessDraft.Corruption.Counting
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Analysis.SpecialFunctions.Log.Base

/-! The two binomial estimates and the incidence and avoidance bounds for a
uniform s-subset. The entropy is in bits and the summation cutoff is real. -/
namespace DisjointnessDraft.Corruption.Binomial
open Finset Real Classical
open scoped BigOperators
noncomputable section

theorem choose_bound (u k : ℕ) (pos : 1≤k) :
    (u.choose k:ℝ)≤(exp 1*u/k)^k := by
  have kp : (0:ℝ)<k := by exact_mod_cast pos
  have fact : (0:ℝ)<k.factorial := by exact_mod_cast Nat.factorial_pos k
  have ek : exp (k:ℝ)=(exp 1)^k := by rw [←exp_nat_mul]; simp
  calc
    (u.choose k:ℝ) ≤ (u:ℝ)^k/k.factorial := Nat.choose_le_pow_div k u
    _ = ((u:ℝ)/k)^k*((k:ℝ)^k/k.factorial) := by rw [div_pow]; field_simp
    _ ≤ ((u:ℝ)/k)^k*exp (k:ℝ) := mul_le_mul_of_nonneg_left (pow_div_factorial_le_exp (k:ℝ) kp.le k) (by positivity)
    _ = _ := by rw [ek,←mul_pow]; congr 1; ring

def entropyBits (a : ℝ) := -a*logb 2 a-(1-a)*logb 2 (1-a)

/-- The sum ranges over integer h satisfying the literal cutoff h ≤ αg. -/
theorem entropy_tail (g : ℕ) (a : ℝ) (pos : 0<a) (half : a≤1/2) :
    (∑ h ∈ (range (g+1)).filter (fun h : ℕ => (h:ℝ)≤a*g),(g.choose h:ℝ)) ≤
      (2:ℝ)^(entropyBits a*g) := by
  let t := a/(1-a)
  have comp : 0<1-a := by linarith
  have tp : 0<t := div_pos pos comp
  have tu : t≤1 := (div_le_one comp).mpr (by linarith)
  let S := (range (g+1)).filter (fun h : ℕ => (h:ℝ)≤a*g)
  have each (h : ℕ) (m : h∈S) : t^(a*g)≤t^h := by
    have cut := (mem_filter.mp m).2
    simpa using rpow_le_rpow_of_exponent_ge tp tu cut
  have binom : (∑h∈range (g+1),t^h*(g.choose h:ℝ))=(1+t)^g := by
    rw [add_comm (1:ℝ) t,add_pow]; simp
  have weighted : (∑ h∈S,(g.choose h:ℝ))*t^(a*g)≤(1+t)^g := by
    rw [sum_mul]
    calc
      _ ≤ ∑h∈S,t^h*(g.choose h:ℝ) := sum_le_sum (fun h m => by
        rw [mul_comm]; exact mul_le_mul_of_nonneg_right (each h m) (Nat.cast_nonneg _))
      _ ≤ ∑h∈range (g+1),t^h*(g.choose h:ℝ) := sum_le_sum_of_subset_of_nonneg (filter_subset ..) (by intros; positivity)
      _ = _ := binom
  have reciprocal : 1+t=(1-a)⁻¹ := by dsimp [t]; field_simp
  have L1 : log (1+t)= -log (1-a) := by rw [reciprocal,log_inv]
  have Lt : log t=log a-log (1-a) := log_div pos.ne' comp.ne'
  have hp : 0<1+t := by linarith
  have denom := rpow_pos_of_pos tp (a*g)
  apply ((le_div_iff₀ denom).mpr weighted).trans_eq
  rw [←rpow_natCast (1+t) g,rpow_def_of_pos hp,rpow_def_of_pos tp,←exp_sub,rpow_def_of_pos (by norm_num : (0:ℝ)<2)]
  congr 1; rw [L1,Lt]
  unfold entropyBits logb
  field_simp [log_ne_zero_of_pos_of_ne_one (show (0:ℝ)<2 by norm_num) (by norm_num : (2:ℝ)≠1)]
  ring

def probability (N s : ℕ) (p : Finset (Fin N) → Prop) [DecidablePred p] : ℝ :=
  ((layer N s).filter p).card/(layer N s).card

theorem incidence {N s k : ℕ} (P : Finset (Fin N)) (size : 1≤s) (fits : s≤N) (pos : 1≤k) :
    probability N s (fun a => k≤(a∩P).card)≤(P.card.choose k:ℝ)*(s/(N:ℝ))^k ∧
    (P.card.choose k:ℝ)*(s/(N:ℝ))^k≤(exp 1*P.card*s/(k*N))^k := by
  have nz : 0<N := by omega
  have mass : (0:ℝ)<(layer N s).card := by rw [card_layer]; exact_mod_cast Nat.choose_pos fits
  constructor
  · unfold probability
    apply (div_le_iff₀ mass).mpr
    by_cases ks : k≤s
    · let incident := fun T : Finset (Fin N) => (layer N s).filter (fun a => T⊆a)
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
            have bound := card_biUnion_le_card_mul (P.powersetCard k) incident ((N-k).choose (s-k)) (by
              intro T m; simpa only [incident,(mem_powersetCard.mp m).2] using supersets_card (s:=s) T)
            simpa only [card_powersetCard] using bound
      have denom : (0:ℝ)<N.choose k := by exact_mod_cast Nat.choose_pos (ks.trans fits)
      have id : (N.choose s:ℝ)*(s.choose k:ℝ)=(N.choose k:ℝ)*((N-k).choose (s-k):ℝ) := by exact_mod_cast Nat.choose_mul fits ks
      have hitbound := choose_fraction (k:=k) fits nz
      have fixed : ((N-k).choose (s-k):ℝ)≤(s/(N:ℝ))^k*(N.choose s:ℝ) := by
        apply le_of_mul_le_mul_left (a:=(N.choose k:ℝ)) _ denom
        rw [←id]
        simpa only [mul_comm,mul_left_comm,mul_assoc] using mul_le_mul_of_nonneg_left hitbound (Nat.cast_nonneg (N.choose s))
      have scaled := mul_le_mul_of_nonneg_left fixed (Nat.cast_nonneg (α:=ℝ) (P.card.choose k))
      rw [card_layer,mul_assoc]; apply le_trans _ scaled; exact_mod_cast cover
    · have empty : (layer N s).filter (fun a => k≤(a∩P).card)=∅ := by
        apply Finset.eq_empty_iff_forall_not_mem.mpr
        intro a m
        obtain ⟨h,hit⟩ := mem_filter.mp m
        have less := card_le_card (inter_subset_left (s₁:=a) (s₂:=P))
        exact ks (hit.trans (less.trans_eq (mem_layer.mp h)))
      rw [empty,card_empty,Nat.cast_zero]; positivity
  · calc
      _ ≤ (exp 1*P.card/k)^k*(s/(N:ℝ))^k := mul_le_mul_of_nonneg_right (choose_bound P.card k pos) (by positivity)
      _ = _ := by rw [←mul_pow]; congr 1; ring

theorem avoidance {N s : ℕ} (V : Finset (Fin N)) (size : 1≤s) (fits : s≤N) :
    probability N s (fun a => Disjoint a V)≤(1-V.card/(N:ℝ))^s ∧
    (1-V.card/(N:ℝ))^s≤exp (-(s:ℝ)*V.card/N) := by
  have nz : 0<N := by omega
  have rn : (0:ℝ)<N := by exact_mod_cast nz
  have vl : V.card≤N := by simpa using card_le_univ V
  let U := (univ : Finset (Fin N)) \ V
  have sets : (layer N s).filter (fun a => Disjoint a V)=U.powersetCard s := by
    ext a; simp only [mem_filter,mem_layer,mem_powersetCard]; constructor
    · rintro ⟨h,dis⟩
      exact ⟨fun z hz => mem_sdiff.mpr ⟨mem_univ _,fun e => disjoint_left.mp dis hz e⟩,h⟩
    · rintro ⟨sub,h⟩; exact ⟨h,disjoint_left.mpr (fun z hz held => (mem_sdiff.mp (sub hz)).2 held)⟩
  have frac : ((N-V.card:ℕ):ℝ)/N=1-V.card/N := by rw [Nat.cast_sub vl,sub_div,div_self rn.ne']
  constructor
  · unfold probability; rw [sets,card_powersetCard,card_layer]
    have u : U.card=N-V.card := by simp [U,card_sdiff (subset_univ V)]
    rw [u,←frac]; exact (div_le_iff₀ (by exact_mod_cast Nat.choose_pos fits : (0:ℝ)<N.choose s)).mpr
      (choose_fraction (Nat.sub_le _ _) nz)
  · have up : 1-V.card/(N:ℝ)≤exp (-(V.card:ℝ)/N) := by simpa only [neg_div,sub_eq_add_neg,add_comm] using add_one_le_exp (-(V.card:ℝ)/N)
    have nonneg : 0≤1-V.card/(N:ℝ) := frac ▸ div_nonneg (Nat.cast_nonneg _) rn.le
    calc _ ≤ (exp (-(V.card:ℝ)/N))^s := pow_le_pow_left₀ nonneg up s
         _ = _ := by rw [←exp_nat_mul]; congr 1; ring
end
end DisjointnessDraft.Corruption.Binomial
