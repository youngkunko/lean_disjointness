import DisjointnessDraft.Applications.UnitEncoding
import Mathlib.Data.Nat.Find
import Mathlib.Order.Filter.AtTopBot.Basic

/-! A polynomial upper bound on the literal finite strand array suffices
for choosing and padding a hard instance at every target vertex count. -/
namespace DisjointnessDraft.Applications.UnitEncoding
open PlanarEncoding CoreSize FinitePlanarDistance FiniteSubdivision Filter
noncomputable section

theorem mesh_size {n : ℕ} (hn : 16≤n) (nz : 0<n) : Fintype.card (U n nz)≤(n+1)^12 := by
  classical
  let p := dim n
  have hp : 16≤p := by dsimp [p,dim]; omega
  let g := mesh p (sourceDim nz)
  have size : Fintype.card (V p)≤p^3 := by
    rw [show Fintype.card (V p)=_ from paired_size p]
    have h₁ := Nat.mul_le_mul_right (p^2) hp
    have h₂ := Nat.mul_le_mul_right p hp
    nlinarith only [h₁,h₂]
  have s : Fintype.card (Id p)≤p^6 := calc
    _ ≤ Fintype.card (V p × V p) := Fintype.card_subtype_le _
    _ ≤ p^3*p^3 := by simpa only [Fintype.card_prod] using Nat.mul_le_mul size size
    _ =_ := by ring
  have bound (e : Id p) : g.len e-1≤p^3 := by
    have n := (has_weight e (sourceDim nz)).2.2
    change length e-1≤_
    nlinarith only [n,Nat.sub_le (length e) 1,Nat.mul_le_mul_right (p^2) hp,Nat.mul_le_mul_right p hp]
  have newVerts : (∑ e : Id p,(g.len e-1))≤p^9 := calc
    _ ≤ ∑ _ : Id p,p^3 := Finset.sum_le_sum (fun e _ => bound e)
    _ ≤ p^6*p^3 := by simpa using Nat.mul_le_mul_right (p^3) s
    _ =_ := by ring
  change Fintype.card (Nodes g)≤p^12
  simp only [Nodes,Fintype.card_sum,Fintype.card_sigma,Fintype.card_fin]
  have p1 : 1≤p := by omega
  have one : p^3≤p^9 := Nat.pow_le_pow_right p1 (by norm_num)
  have two : 2≤p^3 := (show 2≤p by omega).trans (by simpa using Nat.pow_le_pow_right p1 (by norm_num : 1≤3))
  have pow : p^9*2≤p^12 := (Nat.mul_le_mul_left (p^9) two).trans_eq (by ring)
  omega

def unitSize (N : ℕ) := Nat.findGreatest (fun t => (t+1)^12≤N) N

theorem geometry (k : ℕ) : ∀ᶠ N : ℕ in atTop, k≤unitSize N ∧ 16≤unitSize N ∧
    (unitSize N+1)^12≤N ∧ unitSize N≤N ∧ N≤(unitSize N)^24 := by
  let b := max k 16
  filter_upwards [eventually_ge_atTop ((b+1)^12)] with N hN
  have bp : 1≤b+1 := by omega
  have sb : b+1≤(b+1)^12 := by simpa using Nat.pow_le_pow_right bp (by norm_num : 1≤12)
  have bN : b≤N := by omega
  let n := unitSize N
  have bfit : b≤n := Nat.le_findGreatest bN hN
  have fit : (n+1)^12≤N := Nat.findGreatest_spec (P:=fun t => (t+1)^12≤N) bN hN
  have nN : n≤N := Nat.findGreatest_le _
  have n16 : 16≤n := (le_max_right ..).trans bfit
  have n1 : n+1≤N := (show n+1≤(n+1)^12 by simpa using Nat.pow_le_pow_right (Nat.succ_pos n) (by norm_num : 1≤12)).trans fit
  have tooLarge : N<(n+2)^12 := by
    by_contra! h
    have more : n+1≤n := Nat.le_findGreatest n1 h
    omega
  have dbl : n+2≤n^2 := by nlinarith [Nat.mul_le_mul_right n n16]
  have fin := (Nat.pow_le_pow_left dbl 12)
  rw [←pow_mul] at fin
  exact ⟨(le_max_left ..).trans bfit,n16,fit,nN,tooLarge.le.trans fin⟩

end
end DisjointnessDraft.Applications.UnitEncoding
