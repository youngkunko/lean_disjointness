import DisjointnessDraft.Native.Input
import DisjointnessFoundations.EpochSizesAndAverages

/-! The native product distribution, including its exact intersection mean and
constant disjointness probability for each fixed query index. -/
namespace DisjointnessDraft.Native
open DisjointnessFoundations HardDistribution
open scoped BigOperators
noncomputable section
open Classical

variable {N s ℓ g m : ℕ}
abbrev Sparse (N s : ℕ) := ↥(Corruption.layer N s)

def permuteLayer (e : Equiv.Perm (Fin N)) : Sparse N s ≃ Sparse N s where
  toFun x := ⟨x.val.map e.toEmbedding,Corruption.mem_layer.mpr (by simpa using Corruption.mem_layer.mp x.property)⟩
  invFun x := ⟨x.val.map e.symm.toEmbedding,Corruption.mem_layer.mpr (by simpa using Corruption.mem_layer.mp x.property)⟩
  left_inv x := by apply Subtype.ext; simp [Finset.map_map]
  right_inv x := by apply Subtype.ext; simp [Finset.map_map]

def flag {α : Type*} [DecidableEq α] (a : α) (x : Finset α) : ℝ := if a∈x then 1 else 0

theorem sum_flags {α : Type*} [Fintype α] [DecidableEq α] (x : Finset α) : ∑ a,flag a x = x.card := by
  simp [flag,←Finset.sum_filter]

theorem uniform_marginal [Nonempty (Sparse N s)] (a : Fin N) :
    mean (fun x : Sparse N s => flag a x.val) = (s:ℝ)/N := by
  have same (b : Fin N) : mean (fun x : Sparse N s => flag a x.val)=mean (fun x : Sparse N s => flag b x.val) := by
    let e := Equiv.swap a b
    have c := mean_equiv (permuteLayer (s:=s) e) (fun x => flag b x.val)
    refine Eq.trans (congrArg mean (funext fun x : Sparse N s => ?_)) c
    change flag a x.val = flag b (x.val.map e.toEmbedding)
    simp [flag,Finset.mem_map_equiv,e]
  have total := mean_sum (fun b (x : Sparse N s) => flag b x.val)
  have counted (x : Sparse N s) : ∑ b,flag b x.val=(s:ℝ) := by rw [sum_flags,Corruption.mem_layer.mp x.property]
  simp_rw [counted,←same] at total
  rw [mean_const] at total
  simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul] at total
  exact (eq_div_iff (by exact_mod_cast (Nat.ne_of_gt (Nat.zero_lt_of_lt a.isLt)) : (N:ℝ)≠0)).mpr (by linarith)

theorem fixed_intersection [Nonempty (Sparse N s)] (x : Sparse N s) :
    mean (fun a : Sparse N s => ((a.val∩x.val).card:ℝ))=(s:ℝ)^2/N := by
  have eq (a : Sparse N s) : ((a.val∩x.val).card:ℝ) = ∑ j, (if j∈x.val then flag j a.val else 0) := by
    rw [←sum_flags]
    apply Finset.sum_congr rfl
    intro j _; by_cases h : j∈x.val <;> simp [flag,h]
  simp_rw [eq]
  rw [mean_sum]
  have f (j : Fin N) : mean (fun a : Sparse N s => if j ∈ x.val then flag j a.val else 0)=
      if j∈x.val then (s:ℝ)/N else 0 := by by_cases h : j∈x.val <;> simp [h,uniform_marginal,mean_const]
  simp_rw [f]; simp [←Finset.sum_filter,Corruption.mem_layer.mp x.property,pow_two,mul_div_assoc]

theorem mean_disjoint [Nonempty (Sparse N s)] (x : Sparse N s) :
    1-(s:ℝ)^2/N ≤ mean (fun a : Sparse N s => if Disjoint a.val x.val then 1 else 0) := by
  calc
    1-(s:ℝ)^2/N = mean (fun _ : Sparse N s => (1:ℝ)) - mean (fun a : Sparse N s => ((a.val∩x.val).card:ℝ)) := by rw [mean_const,fixed_intersection]
    _ ≤ _ := ?_
  simp only [mean,←sub_div,←Finset.sum_sub_distrib]
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
  apply Finset.sum_le_sum
  intro a _
  by_cases d : Disjoint a.val x.val
  · simp [d]
  · have hit : 0<(a.val∩x.val).card := Finset.card_pos.mpr (Finset.not_disjoint_iff_nonempty_inter.mp d)
    have hr : (1:ℝ)≤(a.val∩x.val).card := by exact_mod_cast hit
    simp only [if_neg d]; linarith

theorem block_ratio (hl : 0<ℓ) (hg : 0<g) (i : Fin ℓ) :
    (epochSize g i:ℝ)^2/blockSize ℓ g i=1/(ℓ:ℝ) := by
  have hs : 0<epochSize g i := pow_pos hg _
  simp only [blockSize,Nat.cast_mul,Nat.cast_pow]
  have nh : (ℓ:ℝ) ≠ 0 := by exact_mod_cast hl.ne'
  have ng : (epochSize g i:ℝ) ≠ 0 := by exact_mod_cast hs.ne'
  field_simp [nh,ng]
  exact mul_comm _ _

theorem true_frequency (hl : 2≤ℓ) (hg : 0<g) (fit : occupied ℓ g≤n) (x : Whole ℓ g) (q : Fin n) :
    (1/4:ℝ) ≤ mean (fun F : Fin n → Whole ℓ g => if answer (rows fit F) (updates fit x) q=true then 1 else 0) := by
  letI (i : Fin ℓ) : Nonempty (Block ℓ g i) := layer_nonempty (by omega) hg i
  let v := fun (i : Fin ℓ) (a : Block ℓ g i) => if Disjoint a.val (x i).val then (1:ℝ) else 0
  have eq (F : Fin n → Whole ℓ g) : (if answer (rows fit F) (updates fit x) q=true then (1:ℝ) else 0) =
      ∏ i, v i (F q i) := by
    by_cases h : ∀ i,Disjoint (F q i).val (x i).val
    · simp [correct,h,v]
    · obtain ⟨i,hi⟩ := not_forall.mp h
      rw [if_neg (fun a => h ((correct fit F x q).mp a)),Finset.prod_eq_zero (Finset.mem_univ i) (by simp [v,hi])]
  simp_rw [eq]
  rw [mean_eval (β:=fun _ : Fin n => Whole ℓ g) q (fun y => ∏ i,v i (y i)),mean_product]
  apply (quarter_le_no_hit_power hl).trans
  simpa only [Finset.prod_const,Finset.card_univ,Fintype.card_fin] using
    (Finset.prod_le_prod (s:=Finset.univ) (f:=fun _ : Fin ℓ => 1-1/(ℓ:ℝ))
      (g:=fun i => mean (v i)) (fun _ _ => by have h : (1:ℝ)≤ℓ := by exact_mod_cast (by omega : 1≤ℓ)
                                              exact sub_nonneg.mpr (one_div_le_one_div_of_le one_pos h |>.trans (by norm_num)))
      (fun i _ => by simpa [v,block_ratio (by omega) hg i] using mean_disjoint (x i)))

end
end DisjointnessDraft.Native
