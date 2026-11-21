import Mathlib.Analysis.Convex.Birkhoff
import Mathlib.Tactic

/-! The finite flat-source and product-rectangle decomposition. Completing the
capped probability vector to a doubly stochastic matrix gives a mixture
indexed by permutations, including at the full-support endpoint. -/
namespace DisjointnessDraft.Information.Flat
open Finset Matrix
open scoped BigOperators
noncomputable section
open Classical
variable {X Y : Type} [Fintype X] [Fintype Y]
def mass (S : Finset X) (x : X) : ℝ := if x∈S then 1/(S.card:ℝ) else 0

structure Mixture (K : ℕ) (p : X → ℝ) where
  sets : Equiv.Perm X → Finset X
  size : ∀ i,(sets i).card=K
  weight : Equiv.Perm X → ℝ
  positive : ∀ i,0≤weight i
  total : ∑ i,weight i=1
  marginal : ∀ x,p x=∑ i,weight i*mass (sets i) x

theorem decompose {K : ℕ} (hK : 0<K) (p : X → ℝ) (pos : ∀x,0≤p x) (total : ∑ x,p x=1)
    (cap : ∀x,p x≤1/(K:ℝ)) : Nonempty (Mixture K p) := by
  let N := Fintype.card X
  have kp : (0:ℝ)<K := by exact_mod_cast hK
  have size : K≤N := by
    have b := sum_le_sum (s:=univ) (fun x _ => cap x)
    rw [total] at b; simp only [sum_const,card_univ,nsmul_eq_mul] at b
    simpa [N,mul_assoc,ne_of_gt kp] using mul_le_mul_of_nonneg_right b kp.le
  obtain ⟨S,_,card⟩ := exists_subset_card_eq (show K≤(univ : Finset X).card by simpa using size)
  by_cases same : K=N
  · have uniform : ∀x,p x=1/(K:ℝ) := by
      intro x; apply le_antisymm (cap x)
      by_contra no
      have less := lt_of_not_ge no
      have bad := sum_lt_sum (s:=univ) (fun j _ => cap j) ⟨x,mem_univ _,less⟩
      rw [total] at bad
      simp [←show K=Fintype.card X from same,ne_of_gt kp] at bad
    let w := fun i : Equiv.Perm X => if i=1 then (1:ℝ) else 0
    refine ⟨⟨fun _ => univ,fun _ => by simpa [N] using same.symm,w,fun _ => by dsimp [w]; split <;> norm_num,by simp [w],?_⟩⟩
    intro x; simp [w,mass,uniform,same,N]
  have gap : 0<(N:ℝ)-K := by exact sub_pos.mpr (by exact_mod_cast (lt_of_le_of_ne size same))
  let M : Matrix X X ℝ := fun i j => if j∈S then p i else (1-K*p i)/(N-K)
  have compCount : ((Sᶜ.card:ℕ):ℝ)=(N:ℝ)-K := by simp [card_compl,card,N,Nat.cast_sub size]
  have dc : M∈doublyStochastic ℝ X := by
    rw [mem_doublyStochastic_iff_sum]; refine ⟨?_,?_,?_⟩
    · intro i j; dsimp [M]; split
      · exact pos _
      · apply div_nonneg _ gap.le
        have h := (le_div_iff₀ kp).mp (cap i); nlinarith
    · intro i
      rw [←sum_add_sum_compl S]
      have on : ∑ j∈S,M i j=∑ _j∈S,p i := sum_congr rfl (fun j hj => if_pos hj)
      have off : ∑ j∈Sᶜ,M i j=∑ _j∈Sᶜ,(1-K*p i)/(N-K) := sum_congr rfl (fun j hj => if_neg (mem_compl.mp hj))
      rw [on,off]; simp only [sum_const,nsmul_eq_mul,card,compCount]
      field_simp [gap.ne']
    · intro j
      by_cases yes : j∈S
      · simpa [M,yes] using total
      · simp [M,yes,←sum_div,sum_sub_distrib,←mul_sum,total,N,ne_of_gt gap]
  obtain ⟨w,wpos,wt,repr⟩ := exists_eq_sum_perm_of_mem_doublyStochastic dc
  let sets := fun i : Equiv.Perm X => S.map i.symm.toEmbedding
  have sizes : ∀ i,(sets i).card=K := fun i => by simp [sets,card]
  refine ⟨⟨sets,sizes,w,wpos,wt,?_⟩⟩
  intro x
  have expan (j : X) : M x j=∑ σ : Equiv.Perm X,w σ*(σ.permMatrix ℝ x j) := by
    rw [←repr]; simp [Matrix.sum_apply,Matrix.smul_apply]
  have read (σ : Equiv.Perm X) : ∑ j∈S,σ.permMatrix ℝ x j=if σ x∈S then 1 else 0 := by
    simp [Equiv.toPEquiv_apply]
  have left : ∑ j∈S,M x j=K*p x := calc
    _ = ∑ _j∈S,p x := sum_congr rfl (fun j hj => if_pos hj)
    _ = _ := by simp [card]
  have sumFormula : ∑ j∈S,M x j=∑ σ : Equiv.Perm X, w σ*(if σ x∈S then 1 else 0) := by
    simp_rw [expan]; rw [sum_comm]; simp_rw [←mul_sum,read]
  have mem (i : Equiv.Perm X) : x∈sets i ↔ i x∈S := by simp [sets,mem_map]
  unfold mass; simp_rw [sizes,mem]
  have scaled : (∑ i : Equiv.Perm X, w i * (if i x∈S then 1/(K:ℝ) else 0)) =
      (∑ i : Equiv.Perm X,w i*(if i x∈S then 1 else 0))/(K:ℝ) := by
    rw [sum_div]; apply sum_congr rfl
    intro i _; split <;> ring
  rw [scaled,←sumFormula,left]; field_simp [kp.ne']

theorem rectangle {K : ℕ} {p : X → ℝ} {q : Y → ℝ} (A : Mixture K p) (B : Mixture K q) (x : X) (y : Y) :
    p x*q y=∑ i, ∑ j,(A.weight i*B.weight j)*(mass (A.sets i) x*mass (B.sets j) y) := by
  rw [A.marginal,B.marginal,sum_mul]
  apply sum_congr rfl; intro i _; rw [mul_sum]; apply sum_congr rfl; intros; ring

end
end DisjointnessDraft.Information.Flat
