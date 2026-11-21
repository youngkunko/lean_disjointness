import DisjointnessDraft.Applications.FiniteSubdivision

namespace DisjointnessDraft.Applications.FiniteSubdivision
open Subdivision WeightedWalk PlanarPadding Planarity Classical
noncomputable section
variable {V E : Type} (G : Graph V E)
def unit (live : E → Prop) (a : Nodes G) (k : ℤ) (b : Nodes G) := k=1 ∧ Dart G live a b
theorem unit_paths (live : E → Prop) (s t : Node (withLive G live)) (k : ℕ)
    (p : UnitWalk (withLive G live) s k t) : Path (sym (unit G live)) (move G live s) k (move G live t) := by
  induction p with
  | nil => exact .nil _
  | snoc _ e ih =>
    rw [Nat.cast_add,Nat.cast_one]
    exact ih.snoc (e.elim (fun a => Or.inl ⟨rfl,(unit_step G live ..).mp a⟩)
      (fun a => Or.inr ⟨rfl,(unit_step G live ..).mp a⟩))
theorem from_paths {a b k} (live : E → Prop) (p : Path (sym (unit G live)) a k b) :
    ∃ d : ℕ,(d:ℤ)=k ∧ UnitWalk (withLive G live) ((move G live).symm a) d ((move G live).symm b) := by
  induction p with
  | nil => exact ⟨0,rfl,.nil _⟩
  | snoc _ ed ih =>
    obtain ⟨d,rfl,pre⟩ := ih
    rcases ed with ⟨rfl,e⟩|⟨rfl,e⟩
    · exact ⟨d+1,by simp,pre.snoc (Or.inl ((unit_step G live ..).mpr (by simpa using e)))⟩
    · exact ⟨d+1,by simp,pre.snoc (Or.inr ((unit_step G live ..).mpr (by simpa using e)))⟩

theorem same_segment (D : Drawing (underlying G)) (unique : Function.Injective (fun e => (G.src e,G.dst e)))
    {e f : E} {k l : ℕ} (hk : k<G.len e) (hl : l<G.len f)
    (a : atNode G e k = atNode G f l) (b : atNode G e (k+1)=atNode G f (l+1)) :
    e=f ∧ k=l := by
  have h : interpolate (location G D (atNode G e k)) (location G D (atNode G e (k+1))) (1/2)=
      interpolate (location G D (atNode G f l)) (location G D (atNode G f (l+1))) (1/2) := by rw [a,b]
  rw [subsegment G D e k hk,subsegment G D f l hl] at h
  have t0 : (0:ℝ)<1/2 := by norm_num
  have t1 : (1/2:ℝ)<1 := by norm_num
  obtain ⟨rfl,eq⟩ := owner G D unique e f (interior G e k hk t0 t1.le (Or.inr t1))
    (interior G f l hl t0 t1.le (Or.inr t1)) h
  have pos : (G.len e:ℝ)≠0 := by exact_mod_cast (G.positive e).ne'
  exact ⟨rfl,by exact_mod_cast (add_right_cancel ((div_left_inj' pos).mp eq) : (k:ℝ)=l)⟩

end
end DisjointnessDraft.Applications.FiniteSubdivision
