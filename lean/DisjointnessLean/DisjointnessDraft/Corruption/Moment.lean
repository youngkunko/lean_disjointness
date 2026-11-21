import DisjointnessDraft.Corruption.Chain

/-! Double-count selected subfamilies of disjoint pieces. A convex exponential
moment controls their avoidance for arbitrary atom-capped column weights. -/
namespace DisjointnessDraft.Corruption
open Finset Real
open scoped BigOperators
open Classical
noncomputable section

def hits {N : ℕ} (D : Finset (Row N)) (b : Row N) :=
  (D.filter (fun d => ¬ Disjoint d b)).card

def moment {N s : ℕ} (B : Weights N) (D : Finset (Row N)) :=
  ∑ b∈layer N s, B b*exp (-(log 2)*(hits D b:ℝ))

theorem mean_hits {N s : ℕ} (B : Weights N) (D : Finset (Row N)) :
    ∑ b∈layer N s,B b*(hits D b:ℝ) = ∑ d∈D,hitProb N s B d := by
  classical
  unfold hitProb
  simp_rw [sum_filter]
  rw [sum_comm]
  apply sum_congr rfl
  intro b _
  rw [←sum_filter]
  simp [hits,mul_comm]

theorem lower_moment {N s : ℕ} {B : Weights N} (hB : Capped (s:=s) B) (D : Finset (Row N)) :
    exp (-(log 2)*(∑ d∈D,hitProb N s B d)) ≤ moment (s:=s) B D := by
  let z := fun b => -(log 2)*(hits D b:ℝ)
  let u := -(log 2)*(∑ d∈D,hitProb N s B d)
  have ez (b) : exp u*(1+z b-u) ≤ exp (z b) := by
    have e := mul_le_mul_of_nonneg_left (add_one_le_exp (z b-u)) (exp_pos u).le
    rw [←exp_add] at e
    simpa only [show u+(z b-u)=z b by ring,show z b-u+1=1+z b-u by ring] using e
  have avg : ∑ b∈layer N s,B b*z b = u := by
    calc _ = -(log 2)*(∑ b∈layer N s,B b*(hits D b:ℝ)) := by
           rw [mul_sum]; apply sum_congr rfl; intro; intro; dsimp [z]; ring
         _ = _ := by rw [mean_hits]
  have linear : (∑ b∈layer N s,B b*(exp u*(1+z b-u))) = exp u := by
    calc _ = exp u*((∑ b∈layer N s,B b)+(∑ b∈layer N s,B b*z b)-u*(∑ b∈layer N s,B b)) := by
           rw [mul_sum,←sum_add_distrib,←sum_sub_distrib,mul_sum]
           apply sum_congr rfl; intro; intro; ring
         _ = _ := by rw [hB.total,avg]; ring
  exact linear ▸ sum_le_sum (fun b hb => mul_le_mul_of_nonneg_left (ez b) (hB.nonneg b hb))

private theorem avoidance_mass {N s : ℕ} {B : Weights N} (hB : Capped (s:=s) B)
    (hp : 0<N) (hs : s≤N) (V : Row N) :
    ∑ b∈(layer N s).filter (fun b => Disjoint b V),B b ≤ capFactor s*exp (-(s:ℝ)*V.card/N) := by
  have ol : (0:ℝ)<(layer N s).card := by rw [card_layer]; exact_mod_cast Nat.choose_pos hs
  apply (mul_le_mul_right ol).mp
  calc _ ≤ _ := mass_cap hB _ (filter_subset _ _)
       _ ≤ _ := mul_le_mul_of_nonneg_left (avoidance_count V hp) (cap_pos s).le
       _ = _ := by ring

private theorem mask_count {N : ℕ} (D : Finset (Row N)) (b : Row N) :
    (2:ℝ)^D.card * exp (-(log 2)*(hits D b:ℝ)) =
      ((D.powerset.filter (fun S => Disjoint b (S.biUnion id))).card:ℝ) := by
  classical
  let M := D.filter (fun d => Disjoint d b)
  have eq : D.powerset.filter (fun S => Disjoint b (S.biUnion id)) = M.powerset := by
    ext S
    simp only [mem_filter,mem_powerset,disjoint_biUnion_right,id_eq]
    constructor
    · rintro ⟨sub,miss⟩ d hd
      exact mem_filter.mpr ⟨sub hd,(miss d hd).symm⟩
    · intro sub
      exact ⟨fun d hd => (mem_filter.mp (sub hd)).1, fun d hd => (mem_filter.mp (sub hd)).2.symm⟩
  have partition : M.card+hits D b=D.card := filter_card_add_filter_neg_card_eq_card _
  have power : exp (-(log 2)*(hits D b:ℝ))=((2:ℝ)^(hits D b))⁻¹ := by
    rw [neg_mul,exp_neg,mul_comm,exp_nat_mul,exp_log (by norm_num : (0:ℝ)<2)]
  rw [eq,card_powerset,Nat.cast_pow,Nat.cast_ofNat,power,←partition,pow_add]
  field_simp

theorem upper_moment {N s k : ℕ} {B : Weights N} (hB : Capped (s:=s) B)
    (hp : 0<N) (hs : s≤N) (D : Finset (Row N)) (dis : D.toSet.PairwiseDisjoint id)
    (sizes : ∀d∈D,d.card=k) :
    moment (s:=s) B D ≤ capFactor s*((1+exp (-((s:ℝ)*k/N)))/2)^D.card := by
  classical
  let a := (s:ℝ)*k/N
  let w := fun (S : Finset (Row N)) => ∑ b∈(layer N s).filter (fun b => Disjoint b (S.biUnion id)),B b
  have count : (2:ℝ)^D.card*moment (s:=s) B D = ∑ S∈D.powerset,w S := by
    unfold moment
    rw [mul_sum]
    unfold w
    simp_rw [sum_filter]
    rw [sum_comm (s:=D.powerset)]
    apply sum_congr rfl
    intro b _
    rw [←sum_filter]
    simp only [sum_const,nsmul_eq_mul,←mask_count D b]
    ring
  have cap (S : Finset (Row N)) (hS : S∈D.powerset) : w S≤capFactor s*(exp (-a))^S.card := by
    have sub := mem_powerset.mp hS
    have sc : (S.biUnion id).card=S.card*k := by
      have sd : S.toSet.PairwiseDisjoint id := fun x hx y hy ne => dis (sub hx) (sub hy) ne
      rw [card_biUnion sd]
      calc _ = ∑ _d∈S,k := sum_congr rfl (fun d hd => sizes d (sub hd))
           _ = _ := by simp
    apply (avoidance_mass hB hp hs (S.biUnion id)).trans_eq
    rw [sc,←exp_nat_mul]
    congr 2
    dsimp [a]; push_cast; ring
  have gen : (∑ S∈D.powerset,(exp (-a))^S.card)=(1+exp (-a))^D.card := by
    simpa using (prod_one_add (f:=fun _ : Row N => exp (-a)) D).symm
  apply (mul_le_mul_left (pow_pos (by norm_num : (0:ℝ)<2) D.card)).mp
  calc _ = _ := count
       _ ≤ _ := sum_le_sum cap
       _ = capFactor s*(1+exp (-a))^D.card := by rw [←mul_sum,gen]
       _ = _ := by rw [div_pow]; field_simp [a]

end
end DisjointnessDraft.Corruption
