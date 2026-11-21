import DisjointnessDraft.Applications.FiniteDiameter
import DisjointnessDraft.Applications.FanDrawing

/-! Padding at an extremal vertex increases the diameter by exactly one
when at least one leaf is added. -/
namespace DisjointnessDraft.Applications.PaddedDiameter
open WeightedWalk PlanarPadding
noncomputable section
variable {W : Type}

theorem symmetry {E : W→ℤ→W→Prop} {u v k} (w : Path (sym E) u k v) : Path (sym E) v k u :=
  FiniteDiameter.reversed (fun _ _ _ e => e.symm) w

theorem pendant (E : W→ℤ→W→Prop) (s t : W) (d : ℤ) {pad : ℕ} (hn : 0<pad) (d1 : 1≤d)
    (pair : Path (sym E) s d t) (least : ∀k,Path (sym E) s k t → d≤k)
    (diam : ∀u v,∃k,k≤d ∧ Path (sym E) u k v) :
    Diameter.HasDiameter (sym (extend (pad:=pad) E s)) (d+1) := by
  let i : Fin pad := ⟨0,hn⟩
  let F := extend (pad:=pad) E s
  have hop (j : Fin pad) : sym F (.inl s) 1 (.inr j) := Or.inl ⟨rfl,rfl⟩
  refine ⟨⟨.inl t,.inr i,(upper_path s (symmetry pair)).snoc (hop i),?_⟩,?_⟩
  · intro k w; cases w with
    | snoc prior edge =>
      rename_i a m c
      cases a with
      | inr j => rcases edge with h|h <;> contradiction
      | inl a =>
        rcases edge with h|h
        · obtain ⟨rfl,rfl⟩ := h
          obtain ⟨l,small,path⟩ := lower_path prior
          have lb := least l (symmetry path); omega
        · contradiction
  · rintro (a|i) (b|j)
    · obtain ⟨k,le,w⟩ := diam a b; exact ⟨k,by omega,upper_path _ w⟩
    · obtain ⟨k,le,w⟩ := diam a s; exact ⟨k+1,by omega,(upper_path s w).snoc (hop j)⟩
    · obtain ⟨k,le,w⟩ := diam b s; exact ⟨k+1,by omega,symmetry ((upper_path s w).snoc (hop i))⟩
    · exact ⟨1+1,by omega,(Diameter.one (hop i).symm).snoc (hop j)⟩

end
end DisjointnessDraft.Applications.PaddedDiameter
