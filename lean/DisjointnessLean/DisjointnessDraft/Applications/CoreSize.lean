import DisjointnessDraft.Applications.Planarity
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Tactic.DeriveFintype
import Mathlib.Tactic.Zify

/-! Finite vertex labels and exact sizes of the weighted and unit-weight
cores. Even an absent shortcut contributes no subdivision vertex (weight one).
Every connector's interior is allocated from the start. -/
namespace DisjointnessDraft.Applications.CoreSize
open OriginalGrid Finset
open scoped BigOperators
noncomputable section
inductive Part where | corner | v | w | x deriving DecidableEq,Fintype
inductive Menu (p : ℕ) where
  | site (r c : Fin p) (k : Part) | top (c : Fin p) | right (r : Fin p)
  deriving DecidableEq,Fintype

def pos {p} (r : Fin p) : ℤ := (r.val:ℤ)+1
def vertex {p} : Menu p → Vertex
  | .site r c .corner => .corner (pos r,pos c)
  | .site r c .v => .inside (pos r) (pos c) .v
  | .site r c .w => .inside (pos r) (pos c) .w
  | .site r c .x => .inside (pos r) (pos c) .x
  | .top c => .corner (0,pos c)
  | .right r => .corner (pos r,(p:ℤ)+1)

private theorem pos_range {p} (r : Fin p) : 1≤pos r ∧ pos r≤p := by have := r.isLt; dsimp [pos]; omega
private theorem unique {p} : Function.Injective (@pos p) := by intro a b e; apply Fin.ext; dsimp [pos] at e; omega
private theorem to_index {p : ℕ} {x : ℤ} (lo : 1≤x) (hi : x≤p) : ∃ i : Fin p,pos i=x := by
  have e : ((x-1).toNat:ℤ)=x-1 := Int.toNat_of_nonneg (by omega)
  exact ⟨⟨(x-1).toNat,by omega⟩,by dsimp [pos]; omega⟩

theorem vertex_injective {p} : Function.Injective (@vertex p) := by
  intro a b e
  cases a with
  | site r c k =>
    cases b with
    | site s t l => cases k <;> cases l <;> simp_all [vertex,unique.eq_iff]
    | top t => have := pos_range r; cases k <;> simp_all [vertex]
    | right s => have := pos_range c; cases k <;> simp_all [vertex]
  | top c =>
    cases b with
    | site s t l =>
      have := pos_range s
      cases l <;> simp_all [vertex]
      all_goals omega
    | top t => simp_all [vertex,unique.eq_iff]
    | right s => have := pos_range s; (simp_all [vertex]; omega)
  | right r =>
    cases b with
    | site s t l =>
      have := pos_range t
      cases l <;> simp_all [vertex]
      all_goals omega
    | top t => have := pos_range r; simp_all [vertex]
    | right s => simp_all [vertex,unique.eq_iff]

theorem local_vertices {p : ℕ} {r c : ℤ} (r1 : 1≤r) (rp : r≤p) (c1 : 1≤c) (cp : c≤p)
    (u : Local) : ∃ a : Menu p,vertex a=embed r c u := by
  obtain ⟨i,eqi⟩ := to_index r1 rp
  obtain ⟨j,eqj⟩ := to_index c1 cp
  cases u with
  | a =>
    by_cases e : r=1
    · exact ⟨.top j,by simp [vertex,embed,e,eqj]⟩
    · obtain ⟨k,ek⟩ := to_index (show 1≤r-1 by omega) (show r-1≤(p:ℤ) by omega)
      exact ⟨.site k j .corner,by simp [vertex,embed,ek,eqj]⟩
  | b => exact ⟨.site i j .corner,by simp [vertex,embed,eqi,eqj]⟩
  | c =>
    by_cases h : c=p
    · exact ⟨.right i,by simp [vertex,embed,eqi,h]⟩
    · obtain ⟨k,ek⟩ := to_index (show 1≤c+1 by omega) (show c+1≤(p:ℤ) by omega)
      exact ⟨.site i k .corner,by simp [vertex,embed,eqi,ek]⟩
  | inside a =>
    cases a with
    | v => exact ⟨.site i j .v,by simp [vertex,embed,eqi,eqj]⟩
    | w => exact ⟨.site i j .w,by simp [vertex,embed,eqi,eqj]⟩
    | x => exact ⟨.site i j .x,by simp [vertex,embed,eqi,eqj]⟩

def menuEquiv (p : ℕ) : Menu p ≃ (Fin p × Fin p × Part) ⊕ (Fin p ⊕ Fin p) where
  toFun | .site r c k => .inl (r,c,k) | .top c => .inr (.inl c) | .right r => .inr (.inr r)
  invFun | .inl (r,c,k) => .site r c k | .inr (.inl c) => .top c | .inr (.inr r) => .right r
  left_inv a := by cases a <;> rfl
  right_inv a := by rcases a with ⟨i,j,k⟩|(c|r) <;> rfl

theorem grid_size (p : ℕ) : Fintype.card (Menu p)=4*p^2+2*p := by
  rw [Fintype.card_congr (menuEquiv p)]
  simp [show Fintype.card Part=4 by decide]; ring

theorem paired_size (p : ℕ) : Fintype.card (Bool × Menu p)=8*p^2+4*p := by simp [grid_size]; ring

/-- Per cell, the vertical edge above v has 2c new vertices (c zero based),
the length-two edge has one, and the final horizontal edge has 2p−3.
The other three local edges have unit weight. -/
def cellNew (p : ℕ) (c : Fin p) := 2*c.val+1+(2*p-3)
def bridgeNew (p : ℕ) (j : Fin p) := 4*p*(p+1)+2*(p+1)*(p-(j.val+1))-1
abbrev Expanded (p : ℕ) :=
  (Bool × Menu p) ⊕ ((Bool × Fin p × (Σ c : Fin p, Fin (cellNew p c))) ⊕ (Σ j : Fin p,Fin (bridgeNew p j)))

private theorem double_sum (p : ℕ) : (∑ i : Fin p,2*i.val)=p*(p-1) := by
  rw [←Finset.mul_sum,Finset.sum_fin_eq_sum_range, Nat.mul_comm]
  rw [←sum_range_id_mul_two p]
  congr 1; apply sum_congr rfl; intro i h; simp [mem_range.mp h]

theorem expanded_size (p : ℕ) (p2 : 2≤p) : Fintype.card (Expanded p)=11*p^3+6*p^2+2*p := by
  have one : ∀ c : Fin p,(cellNew p c:ℤ)=2*c.val+(2*(p:ℤ)-2) := by
    intro c; dsimp [cellNew]; omega
  have two : ∀ j : Fin p,(bridgeNew p j:ℤ)=4*(p:ℤ)*(p+1)+2*(p+1)*(p-1)-1-(p+1)*(2*j.val) := by
    intro j; have := j.isLt
    dsimp [bridgeNew]
    have z : 1≤4*p*(p+1)+2*(p+1)*(p-(j.val+1)) := by
      have h : 0<4*p*(p+1) := by positivity
      omega
    push_cast [Nat.cast_sub z,Nat.cast_sub (show j.val+1≤p by omega)]; ring
  have d : ∑ i : Fin p,2*(i.val:ℤ)=(p:ℤ)*(p-1) := by
    have h := congrArg (fun t : ℕ => (t:ℤ)) (double_sum p)
    simpa [Nat.cast_sub (show 1≤p by omega)] using h
  have first : (∑ c : Fin p,(cellNew p c:ℤ))=(p:ℤ)*(p-1)+p*(2*p-2) := by
    simp_rw [one]; rw [Finset.sum_add_distrib,d]; simp; ring
  have other : (∑ j : Fin p,(bridgeNew p j:ℤ))=(p:ℤ)*(4*p*(p+1)+2*(p+1)*(p-1)-1)-(p+1)*(p*(p-1)) := by
    simp_rw [two]; rw [Finset.sum_sub_distrib,←Finset.mul_sum,d]; simp; ring
  apply Nat.cast_injective (R:=ℤ)
  simp [Expanded,Fintype.card_sum,Fintype.card_prod,Fintype.card_sigma,grid_size,first,other]
  ring

end
end DisjointnessDraft.Applications.CoreSize
