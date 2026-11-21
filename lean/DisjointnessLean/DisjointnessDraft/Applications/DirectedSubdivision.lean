import DisjointnessDraft.Applications.SubdivisionPaths
import DisjointnessDraft.Applications.GirthOrient

/-! Homogeneously oriented integer subdivision. Rational interpolation is a
strict topological rank even when a long weighted edge is replaced by unit darts. -/
namespace DisjointnessDraft.Applications.DirectedSubdivision
open Subdivision FiniteSubdivision WeightedWalk PlanarPadding Classical
noncomputable section
variable {V E : Type} (G : Graph V E) (r : V → ℚ)
def level : Nodes G → ℚ
  | .inl v => r v
  | .inr ⟨e,i⟩ => r (G.src e)+((i.val+1:ℚ)/G.len e)*(r (G.dst e)-r (G.src e))

theorem level_at (e : E) (k : ℕ) (fit : k≤G.len e) :
    level G r (atNode G e k)=r (G.src e)+(k/G.len e:ℚ)*(r (G.dst e)-r (G.src e)) := by
  have pos := G.positive e
  by_cases zero : k=0
  · subst k; simp [level,atNode]
  · by_cases h : k<G.len e
    · simp only [atNode,dif_neg zero,dif_pos h,level]
      have z : ((k-1:ℕ):ℚ)+1=k := by exact_mod_cast (show k-1+1=k by omega)
      rw [z]
    · obtain rfl := le_antisymm fit (by omega)
      simp [atNode,zero,level,show ((G.len e):ℚ)≠0 by exact_mod_cast pos.ne']

theorem level_step (e : E) (k : ℕ) (fit : k<G.len e) :
    level G r (atNode G e (k+1))-level G r (atNode G e k)=(r (G.dst e)-r (G.src e))/G.len e := by
  rw [level_at _ _ _ _ fit,level_at _ _ _ _ fit.le]
  push_cast; ring

def arc (live : E → Prop) (a : Nodes G) (k : ℤ) (b : Nodes G) :=
  sym (unit G live) a k b ∧ level G r a<level G r b

theorem strand (live : E → Prop) (e : E) (on : live e) :
    (r (G.src e)<r (G.dst e) →
      Path (arc G r live) (.inl (G.src e)) (G.len e) (.inl (G.dst e))) ∧
    (r (G.dst e)<r (G.src e) →
      Path (arc G r live) (.inl (G.dst e)) (G.len e) (.inl (G.src e))) := by
  have pos := G.positive e
  have exacts (k : ℕ) (fit : k≤G.len e) :
      (r (G.src e)<r (G.dst e) → Path (arc G r live) (atNode G e 0) k (atNode G e k)) ∧
      (r (G.dst e)<r (G.src e) → Path (arc G r live) (atNode G e k) k (atNode G e 0)) := by
    induction k with
    | zero => exact ⟨fun _ => .nil _,fun _ => .nil _⟩
    | succ k ih =>
      have sk : k<G.len e := fit
      have delta := level_step G r e k sk
      have posq : 0<(G.len e:ℚ) := by exact_mod_cast pos
      have dart : unit G live (atNode G e k) 1 (atNode G e (k+1)) := ⟨rfl,e,k,sk,Or.inl on,rfl,rfl⟩
      obtain ⟨fw,bw⟩ := ih sk.le
      constructor
      · intro h
        have rnk := div_pos (sub_pos.mpr h) posq
        simpa using (fw h).snoc (show arc G r live _ (1:ℤ) _ from ⟨Or.inl dart,by linarith only [delta,rnk]⟩)
      · intro h
        have rnk := div_neg_of_neg_of_pos (sub_neg.mpr h) posq
        have e' : arc G r live (atNode G e (k+1)) 1 (atNode G e k) := ⟨Or.inr dart,by linarith only [delta,rnk]⟩
        have single : Path (arc G r live) (atNode G e (k+1)) 1 (atNode G e k) := by simpa using (Path.nil _).snoc e'
        simpa [add_comm] using single.append (bw h)
  simpa [atNode,pos.ne'] using exacts (G.len e) le_rfl

end
end DisjointnessDraft.Applications.DirectedSubdivision
