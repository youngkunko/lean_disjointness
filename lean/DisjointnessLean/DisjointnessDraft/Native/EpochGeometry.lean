import DisjointnessDraft.Native.Physical
import DisjointnessFoundations.GeometricEpochEstimates

/-! All indices in Lean are zero based. The chronogram condition uses their
one-based values, as in the manuscript. -/
namespace DisjointnessDraft.Native
open DisjointnessFoundations Parameters Statement Real Filter
noncomputable section
open Classical

theorem occupied_eq (ℓ g : ℕ) : occupied ℓ g=ℓ*problemSize ℓ (g^2) := by
  simp only [occupied,blockSize,problemSize,epochSize,HardDistribution.epochSize,Finset.mul_sum,←pow_mul]
  apply Finset.sum_congr rfl; intro i _; rw [Nat.mul_comm (2*(i.val+1)) 2]

theorem occupied_low {ℓ g : ℕ} (hl : 0<ℓ) : g^(4*ℓ)≤occupied ℓ g := by
  have h := size_lower (g:=g^2) hl
  rw [←pow_mul,show 2*(2*ℓ)=4*ℓ by omega] at h
  rw [occupied_eq]; exact h.trans (Nat.le_mul_of_pos_left _ hl)

theorem occupied_high (ℓ : ℕ) {g : ℕ} (hg : 2≤g) : occupied ℓ g≤(2*ℓ)*g^(4*ℓ) := by
  have h := size_upper ℓ (g:=g^2) (by nlinarith)
  rw [←pow_mul,show 2*(2*ℓ)=4*ℓ by omega] at h
  simpa only [occupied_eq,Nat.mul_left_comm,←Nat.mul_assoc,Nat.mul_comm ℓ 2] using Nat.mul_le_mul_left ℓ h

theorem largest {L n g : ℕ} (hl : 0<L) (hg : 0<g) (fits : occupied L g≤n) :
    ∃ ℓ,L≤ℓ ∧ occupied ℓ g≤n ∧ n<occupied (ℓ+1) g := by
  have le (j : ℕ) (pos : 0<j) : j≤occupied j g := by
    rw [occupied_eq]; exact Nat.le_mul_of_pos_right _ (lt_of_lt_of_le pos (ell_le_size (pow_pos hg 2)))
  let j := Nat.findGreatest (fun j => occupied j g≤n) n
  have ok := (le L hl).trans fits
  refine ⟨j,Nat.le_findGreatest ok fits,Nat.findGreatest_spec (P:=fun i => occupied i g≤n) ok fits,?_⟩
  by_contra! small
  exact Nat.findGreatest_is_greatest (P:=fun i => occupied i g≤n) (Nat.lt_succ_self j) ((le _ (by omega)).trans small) small

theorem depth_twenty {g n : ℕ} (hg : 40≤g) (regime : g^95≤n) :
    ∃ ℓ,20≤ℓ ∧ occupied ℓ g≤n ∧ n<occupied (ℓ+1) g := by
  apply largest (by norm_num) (by omega)
  apply (occupied_high 20 (by omega : 2≤g)).trans
  calc (2*20)*g^(4*20) ≤ g*g^80 := Nat.mul_le_mul_right _ hg
       _ = g^81 := by rw [show g^81=g^80*g from pow_succ g 80,mul_comm]
       _ ≤ g^95 := Nat.pow_le_pow_right (by omega) (by norm_num)
       _ ≤ n := regime

def chronogram (ℓ : ℕ) : Finset (Fin ℓ) := Finset.univ.filter (fun i => 2*(ℓ+2)≤3*(i.val+1))

theorem chronogram_card (ℓ : ℕ) : ℓ ≤ 3*(chronogram ℓ).card+4 := by
  let k := (ℓ-2)/3
  let f (j : Fin k) : ↥(chronogram ℓ) :=
    ⟨⟨ℓ-k+j.val,by have := j.isLt; dsimp [k] at *; omega⟩,Finset.mem_filter.mpr
      ⟨Finset.mem_univ _,by dsimp [k]; omega⟩⟩
  have inj : Function.Injective f := by
    intro a b h; have eq := congrArg (fun y : ↥(chronogram ℓ) => y.val.val) h
    dsimp [f] at eq; exact Fin.ext (by omega)
  have eq := Fintype.card_le_of_injective f inj
  simp only [Fintype.card_fin,Fintype.card_coe] at eq
  dsimp [k] at eq; omega

theorem large_epoch {ℓ g n : ℕ} (hg : 2≤g) (next : n<occupied (ℓ+1) g)
    (scale : 2*(ℓ+1)≤g^4) (i : Fin ℓ) (mem : i∈chronogram ℓ) : n≤(epochSize g i)^3 := by
  have idx := (Finset.mem_filter.mp mem).2
  calc n ≤ (2*(ℓ+1))*g^(4*(ℓ+1)) := next.le.trans (occupied_high _ hg)
       _ ≤ g^4*g^(4*(ℓ+1)) := Nat.mul_le_mul_right _ scale
       _ = g^(4+4*(ℓ+1)) := (pow_add ..).symm
       _ ≤ (epochSize g i)^3 := by
          simp only [epochSize,HardDistribution.epochSize,←pow_mul]
          exact Nat.pow_le_pow_right (by omega) (by omega)

theorem epoch_upper {ℓ g n : ℕ} (fit : occupied ℓ g≤n) (i : Fin ℓ) : (epochSize g i)^2≤n :=
  ((Nat.le_mul_of_pos_left _ (Nat.zero_lt_of_lt i.isLt)).trans
    (Finset.single_le_sum (f:=blockSize ℓ g) (fun _ _ => Nat.zero_le _) (Finset.mem_univ i))).trans fit

theorem log_geometry {ℓ g n : ℕ} (hl : 0<ℓ) (hg : 2≤g) (fit : occupied ℓ g≤n) (next : n<occupied (ℓ+1) g)
    (scale : 2*(ℓ+1)≤g^4) :
    4*(ℓ:ℝ)*logb 2 g≤logb 2 n ∧ logb 2 n≤12*ℓ*logb 2 g := by
  have gp : (0:ℝ)<g := by exact_mod_cast (by omega : 0<g)
  have h1 := (occupied_low (g:=g) hl).trans fit
  have h2 : n≤g^(4*(ℓ+2)) := by
    calc n ≤ _ := next.le.trans (occupied_high _ hg)
         _ ≤ g^4*g^(4*(ℓ+1)) := Nat.mul_le_mul_right _ scale
         _ = _ := by rw [←pow_add]; congr 1; omega
  have npos := (pow_pos (by omega : 0<g) _).trans_le h1
  have a := logb_le_logb_of_le (b:=2) (by norm_num) (pow_pos gp (4*ℓ)) (by exact_mod_cast h1 : (g:ℝ)^(4*ℓ)≤n)
  have b := logb_le_logb_of_le (b:=2) (by norm_num) (by exact_mod_cast npos : (0:ℝ)<n) (by exact_mod_cast h2 : (n:ℝ)≤(g:ℝ)^(4*(ℓ+2)))
  rw [logb_pow] at a b
  push_cast at a b
  have one : (1:ℝ)≤ℓ := by exact_mod_cast hl
  have factor : 4*((ℓ:ℝ)+2)≤12*ℓ := by linarith
  exact ⟨a,b.trans (mul_le_mul_of_nonneg_right factor
    (logb_nonneg (by norm_num) (by exact_mod_cast (by omega : 1≤g))))⟩

end
end DisjointnessDraft.Native
