import DisjointnessDraft.Applications.UnitLabels

/-! The finite universal-strand representation in the operational reduction
has exactly the manuscript's cubic number of vertices, before padding. -/
namespace DisjointnessDraft.Applications.UnitLabels
open UnitEncoding FinitePlanarDistance CoreSize FiniteSubdivision Classical
noncomputable section

def nameInner (hp : 2≤p) (i : Σ l : Label p,Fin (meters l-1)) : Σ e : Id p,Fin (length e-1) :=
  ⟨strand hp i.1,⟨i.2.val,by rw [strand_length]; exact i.2.isLt⟩⟩

theorem correspondence (hp : 2≤p) : Function.Bijective (nameInner hp) := by
  constructor
  · rintro ⟨a,i⟩ ⟨b,j⟩ h
    have eq : strand hp a=strand hp b := congrArg Sigma.fst h
    obtain rfl := strand_injective hp eq
    have v : i.val=j.val := congrArg (fun s : Σ e : Id p,Fin (length e-1) => s.2.val) h
    obtain rfl := Fin.ext v; rfl
  · rintro ⟨e,i⟩
    have big : 1<(length e:ℤ) := by have := i.isLt; omega
    obtain ⟨l,m⟩ := classify hp (has_weight e hp).1 big
    have sa : (ends l).1=e.val.1 := PlanarMatching.inj (congrArg Prod.fst m)
    have sb : (ends l).2=e.val.2 := PlanarMatching.inj (congrArg Prod.snd m)
    have s : strand hp l=e := Subtype.ext (Prod.ext sa sb)
    subst e
    refine ⟨⟨l,⟨i.val,by rw [←strand_length hp]; exact i.isLt⟩⟩,rfl⟩

def thirds : Fin 3 ≃ Kind where
  toFun := ![.vertical,.middle,.horizontal]
  invFun | .vertical => 0 | .middle => 1 | .horizontal => 2
  left_inv j := by fin_cases j <;> rfl
  right_inv k := by cases k <;> rfl

theorem cell_inner (hp : 2≤p) (s : Bool) (i j : Fin p) :
    (∑ k : Kind,(meters (.inl (s,i,j,k))-1))=cellNew p j := by
  rw [←Equiv.sum_comp thirds]
  simp only [Fin.sum_univ_three]
  change (2*j.val+1-1)+(2-1)+(2*p-2-1)=_
  dsimp [cellNew]; omega

theorem cardinality (hp : 2≤p) : Fintype.card (Nodes (mesh p hp))=11*p^3+6*p^2+2*p := by
  rw [←expanded_size p hp]
  change Fintype.card ((Bool × Menu p) ⊕ (Σ e : Id p,Fin (length e-1)))=Fintype.card (Expanded p)
  have eq := Fintype.card_congr (Equiv.ofBijective (nameInner hp) (correspondence hp))
  simp only [Fintype.card_sum,Expanded,←eq]
  congr 1
  simp only [Fintype.card_sigma,Fintype.card_fin,Label,Fintype.sum_sum_type,Fintype.sum_prod_type,cell_inner hp,
    Fintype.card_prod,Fintype.card_bool,Finset.sum_const,Finset.card_univ,nsmul_eq_mul]
  congr 1

end
end DisjointnessDraft.Applications.UnitLabels
