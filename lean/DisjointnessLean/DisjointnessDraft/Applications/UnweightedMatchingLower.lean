import DisjointnessDraft.Applications.MatchingGraph

namespace DisjointnessDraft.Applications.MatchingGraph
open MatchingSize Transfer.Compiler ShortTransfer Filter MeasureTheory
noncomputable section

def matchedPadding (n N : ℕ) := N/2-(1+n+n)

theorem lower (lo hi : ℝ) (lp : 0<lo) (lh : lo≤hi) :
    ∃ c : ℝ,0<c ∧ ∀ᶠ N : ℕ in atTop, let n := stringSize N
      let p := matchedPadding n N
      let r := N%2
      Fintype.card (Left n p) + Fintype.card (Right n p r)=N ∧
      Bound lo hi c N true (legal (n:=n) (p:=p) (r:=r)) sizeSpec ∧
      (Even N → Bound lo hi c N true (legal (n:=n) (p:=p) (r:=r)) perfectSpec) := by
  obtain ⟨c,cp,event⟩ := ShortTransfer.eventual lo hi lp lh
  obtain ⟨m,stable⟩ := eventually_atTop.mp event
  refine ⟨c,cp,?_⟩
  filter_upwards [string_geometry (max m 8)] with N geom
  let n := stringSize N
  let p := matchedPadding n N
  obtain ⟨big,_,fit,nN,pow⟩ := geom
  have n8 : 8≤n := (le_max_right ..).trans big
  have cut : 1+n+n ≤ N/2 := by
    apply (Nat.le_div_iff_mul_le (by decide : 0<2)).mpr
    change 9*(n*n)≤N at fit
    nlinarith [Nat.mul_le_mul_left n n8]
  have leftSize : leftCount n p=N/2 := Nat.add_sub_of_le cut
  have useBound := @stable n ((le_max_left ..).trans big) N nN pow
  refine ⟨?_,?_,?_⟩
  · change Fintype.card (Left n p) + Fintype.card (Right n p (N%2))=N
    rw [left_card,right_card,leftSize]; omega
  · intro w tu tq tu1 tq1 wl wh Ω _ μ _ D H
    let I := init n p (N%2)
    let S := plan ℕ (fun k => decide (k≠leftCount n p)) 0 n p (N%2)
    have res := useBound S true size_valid (by simp [S,plan]) (by simp [S,plan]) (by simp)
    exact res w tu tq tu1 tq1 wl wh Ω μ (initialized D I) (init_guarantees μ D _ H)
  · intro evenN
    have eq : N%2=0 := Nat.even_iff.mp evenN
    rw [eq]
    intro w tu tq tu1 tq1 wl wh Ω _ μ _ D H
    let I := init n p 0
    let S := plan Bool (!·) false n p 0
    have res := useBound S true perfect_valid (by simp [S,plan]) (by simp [S,plan]) (by simp)
    exact res w tu tq tu1 tq1 wl wh Ω μ (initialized D I) (init_guarantees μ D _ H)
end
end DisjointnessDraft.Applications.MatchingGraph
