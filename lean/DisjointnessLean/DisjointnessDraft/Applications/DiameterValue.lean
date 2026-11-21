import DisjointnessDraft.Applications.DiameterLower

namespace DisjointnessDraft.Applications.DiameterGraph
open WeightedWalk PlanarPadding
open Classical
noncomputable section
variable {Z : Type} [Fintype Z] [Nonempty Z]

/-- Every legal finite connected weighted graph has a numeric diameter. -/
theorem exists_diameter {E : Net Z} (pos : ∀ u k v,E u k v → 0 ≤ k)
    (connected : ∀ u v, ∃ k, Path E u k v) : ∃ d, Diameter.HasDiameter E d := by
  let P (t : Z×Z) (m : ℕ) := Path E t.1 (m:ℤ) t.2
  have paths (t : Z×Z) : ∃m, P t m := by
    obtain ⟨k,w⟩ := connected t.1 t.2
    refine ⟨k.toNat,?_⟩
    simpa [P,Int.toNat_of_nonneg (w.nonneg pos)] using w
  let d (t : Z×Z) := Nat.find (paths t)
  obtain ⟨t,_,largest⟩ := Finset.exists_max_image Finset.univ d Finset.univ_nonempty
  refine ⟨d t,⟨t.1,t.2,Nat.find_spec (paths t),?_⟩,?_⟩
  · intro k w
    have eq := Int.toNat_of_nonneg (w.nonneg pos)
    have le : d t ≤ k.toNat := Nat.find_min' (paths t) (by simpa [P,eq] using w)
    exact_mod_cast (show (d t:ℤ)≤k by omega)
  · intro u v
    have le := largest (u,v) (Finset.mem_univ _)
    exact ⟨d (u,v),by exact_mod_cast le,Nat.find_spec (paths (u,v))⟩

theorem legal_value {F : Net Z} {h} {bound : ℤ} (ok : legal bound F h) :
    ∃ d, diameter (history F h) = some d := by
  obtain ⟨d,hd⟩ := exists_diameter (E:=sym (history F h)) (fun u k v e => by
    rcases e with e|e <;> exact (ok.2.2.1 _ _ _ e).1.le) ok.2.2.2.2
  exact ⟨d,value_eq hd⟩
end
end DisjointnessDraft.Applications.DiameterGraph
