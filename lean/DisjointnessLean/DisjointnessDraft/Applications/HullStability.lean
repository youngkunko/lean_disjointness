import DisjointnessDraft.Applications.Hull
import Mathlib.Analysis.NormedSpace.HahnBanach.Separation
import Mathlib.Analysis.Convex.Topology

/-! Robust convex-hull certificates in a real normed space. Both the tested
point and every hull generator can move. The conclusions are Mathlib's
extreme-point and interior predicates for the actual perturbed convex hull. -/
namespace DisjointnessDraft.Applications.HullStability
open Set Metric
noncomputable section
variable {E I : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem extreme_of_exposed (v : I → E) (x : I) (L : E →L[ℝ] ℝ)
    (better : ∀ i,i≠x → L (v i)<L (v x)) : v x∈(convexHull ℝ (range v)).extremePoints ℝ := by
  let C : Set E := {z | z=v x ∨ L z<L (v x)}
  have bound {z : E} (m : z∈C) : L z≤L (v x) := m.elim (fun e => by rw [e]) le_of_lt
  have bounded : convexHull ℝ (range v) ⊆ C := by
    apply convexHull_min
    · rintro _ ⟨i,rfl⟩; by_cases e : i=x
      · exact Or.inl (congrArg v e)
      · exact Or.inr (better i e)
    · apply convex_iff_forall_pos.2
      intro u hu w hw a b ha hb sum
      change a • u + b • w=v x ∨ L (a • u + b • w)<L (v x)
      have id : a*L (v x)+b*L (v x)=L (v x) := by rw [←add_mul,sum,one_mul]
      rcases hu with h|h
      · subst u; rcases hw with g|g
        · subst w; exact Or.inl (by rw [←add_smul,sum,one_smul])
        · right; simp only [map_add,map_smul,smul_eq_mul]; linarith only [mul_lt_mul_of_pos_left g hb,id]
      · right; simp only [map_add,map_smul,smul_eq_mul]
        linarith only [mul_lt_mul_of_pos_left h ha,mul_le_mul_of_nonneg_left (bound hw) hb.le,id]
  apply mem_extremePoints_iff_left.2
  refine ⟨subset_convexHull ℝ _ ⟨x,rfl⟩,?_⟩
  rintro u hu w hw ⟨a,b,ha,hb,sum,eq⟩
  rcases bounded hu with e|h
  · exact e
  · have Lval := congrArg L eq
    simp only [map_add,map_smul,smul_eq_mul] at Lval
    have id : a*L (v x)+b*L (v x)=L (v x) := by rw [←add_mul,sum,one_mul]
    linarith only [mul_lt_mul_of_pos_left h ha,mul_le_mul_of_nonneg_left (bound (bounded hw)) hb.le,id,Lval]

theorem variation (L : E →L[ℝ] ℝ) (u v : E) {eps : ℝ} (move : ‖u-v‖≤eps) :
    |L u-L v|≤‖L‖*eps := by
  rw [←map_sub,←Real.norm_eq_abs]
  exact (L.le_opNorm _).trans (mul_le_mul_of_nonneg_left move (norm_nonneg _))

theorem stable_vertex (f g : I → E) (x : I) (L : E →L[ℝ] ℝ) {eps : ℝ}
    (motion : ∀ i,‖g i-f i‖≤eps)
    (margin : ∀ i,i≠x → 2*(‖L‖*eps)<L (f x)-L (f i)) :
    g x∈(convexHull ℝ (range g)).extremePoints ℝ :=
  extreme_of_exposed g x L (Hull.stable_exposure (L ∘ f) (L ∘ g) x _
    (fun i => variation L _ _ (motion i)) margin)

theorem stable_ball [Finite I] [Nonempty I] (f g : I → E) (x y : E) {eps radius : ℝ}
    (move : ∀ i,‖g i-f i‖≤eps) (point : ‖y-x‖≤eps)
    (margin : ∀ L : E →L[ℝ] ℝ, L≠0 → ∃ i,‖L‖*(2*eps+radius) ≤ L (f i)-L x) :
    closedBall y radius ⊆ convexHull ℝ (range g) := by
  classical
  intro z hz
  by_contra outside
  obtain ⟨L,t,less,gt⟩ := geometric_hahn_banach_closed_point (convex_convexHull ℝ (range g))
    (Set.finite_range g).isClosed_convexHull outside
  have all i := less (g i) (subset_convexHull ℝ _ (mem_range_self i))
  have nz : L≠0 := by
    intro eq; subst L
    have a := all (Classical.choice (inferInstance : Nonempty I))
    simp only [ContinuousLinearMap.zero_apply] at a gt; linarith
  obtain ⟨i,mg⟩ := margin L nz
  have p := abs_le.mp (variation L y x point)
  have m := abs_le.mp (variation L (g i) (f i) (move i))
  have d := abs_le.mp (variation L z y (by simpa [dist_eq_norm] using hz))
  nlinarith only [all i,gt,mg,p.2,m.1,d.2]

theorem stable_interior [Finite I] [Nonempty I] (f g : I → E) (x y : E) {eps radius : ℝ}
    (rpos : 0<radius) (move : ∀ i,‖g i-f i‖≤eps) (point : ‖y-x‖≤eps)
    (margin : ∀ L : E →L[ℝ] ℝ, L≠0 → ∃ i,‖L‖*(2*eps+radius) ≤ L (f i)-L x) :
    y∈interior (convexHull ℝ (range g)) := by
  exact mem_interior_iff_mem_nhds.mpr (Filter.mem_of_superset (Metric.closedBall_mem_nhds y rpos)
    (stable_ball f g x y move point margin))
end
end DisjointnessDraft.Applications.HullStability
