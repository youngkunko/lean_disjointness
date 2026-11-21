import DisjointnessDraft.Applications.WeightedMatching

/-! The genuine maximum-weight matching objective on arbitrary weighted
bipartite edges, including partial matchings and isolated padding vertices. -/
namespace DisjointnessDraft.Applications.BipartiteOptimum
open WeightedMatching Classical
noncomputable section
variable {L R V : Type} [Fintype V] [DecidableEq V]
structure Candidate (E : L → ℤ → R → Prop) where
  dom : Finset L
  target : L → R
  cost : L → ℤ
  injective : Set.InjOn target dom
  valid : ∀u∈dom,E u (cost u) (target u)
def value {E : L → ℤ → R → Prop} (m : Candidate E) := ∑ u∈m.dom,m.cost u
def maximum (E : L → ℤ → R → Prop) : ℤ :=
  if h : ∃ z,IsGreatest (Set.range (value (E:=E))) z then h.choose else 0
def padded (E : V → ℤ → V → Prop) (a b : V) (K : ℤ) (u : Option V) (k : ℤ) :
    Option V ⊕ Fin pad → Prop
  | .inl v => allowed E a b u (K-k) v
  | .inr _ => False

theorem transfer {V : Type} [Fintype V] [DecidableEq V] {pad : ℕ} {E : V → ℤ → V → Prop} {a b : V} {K ans : ℤ}
    (someMatch : ∃ m : Matching E a b,weight E K m=ans)
    (upper : ∀ m : Matching E a b,weight E K m≤ans) :
    maximum (padded (pad:=pad) E a b K)=ans := by
  have mx : IsGreatest (Set.range (value (E:=padded (pad:=pad) E a b K))) ans := by
    constructor
    · obtain ⟨m,hm⟩ := someMatch
      let actual : Candidate (padded (pad:=pad) E a b K) := {
        dom := m.dom, target := fun u => .inl (m.target u), cost := fun u => K-m.gap u
        injective := fun _ hu _ hv eq => m.injective hu hv (Sum.inl.inj eq)
        valid := fun u hu => by
          change allowed E a b u (K-(K-m.gap u)) (m.target u)
          simpa only [sub_sub_cancel] using m.edges u hu }
      exact ⟨actual,hm⟩
    · rintro z ⟨m,rfl⟩
      let erase : Option V ⊕ Fin pad → Option V := Sum.elim id fun _ => none
      have embedded (u) (hu : u∈m.dom) : Sum.inl (erase (m.target u))=m.target u := by
        have h := m.valid u hu
        cases eq : m.target u with
        | inl v => rfl
        | inr v => rw [eq] at h; exact False.elim h
      let core : Matching E a b := {
        dom := m.dom, target := fun u => erase (m.target u), gap := fun u => K-m.cost u
        injective := fun u hu v hv eq => m.injective hu hv ((embedded u hu).symm.trans
          ((congrArg Sum.inl eq).trans (embedded v hv)))
        edges := fun u hu => by
          have h := m.valid u hu
          rw [←embedded u hu] at h
          exact h }
      have h := upper core
      simpa only [weight,core,sub_sub_cancel,value] using h
  have existsMax := Exists.intro ans mx
  rw [maximum,dif_pos existsMax]
  exact existsMax.choose_spec.unique mx
end
end DisjointnessDraft.Applications.BipartiteOptimum
