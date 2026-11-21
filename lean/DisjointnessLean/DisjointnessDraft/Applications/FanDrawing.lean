import DisjointnessDraft.Applications.PlanarPadding
import DisjointnessDraft.Applications.Diameter

/-! Two exterior fans over disjoint intervals of the boundary line of a
straight-line drawing. The rays in either fan meet only at their common tip. -/
namespace DisjointnessDraft.Applications.FanDrawing
open Planarity PlanarPadding
noncomputable section
variable {V : Type}

def wire (E : V→ℤ→V→Prop) (fan : Bool→V→ℤ→Prop) : Diameter.Node V→ℤ→Diameter.Node V→Prop
  | .inl u,k,.inl v => E u k v
  | .inr side,k,.inl v => fan side v k
  | _,_,_ => False

def point (P : V→Plane) (middle : ℝ) : Diameter.Node V→Plane
  | .inl v => ((P v).1,(P v).2+1)
  | .inr false => (middle-1,0)
  | .inr true => (middle+1,0)

set_option maxHeartbeats 800000 in
theorem diagram (E : V→ℤ→V→Prop) (fan : Bool→V→ℤ→Prop) (D : Drawing (plain E)) (m : ℝ)
    (up : ∀v,0≤(D.point v).2) (onLine : ∀s v k,fan s v k → (D.point v).2=0)
    (bank : ∀s v k,fan s v k → if s then m<(D.point v).1 else (D.point v).1<m) :
    ∃ d : Drawing (plain (wire E fan)),d.point=point D.point m := by
  let P := point D.point m
  have core (u v : V) (t : ℝ) : interpolate (P (.inl u)) (P (.inl v)) t=
      ((interpolate (D.point u) (D.point v) t).1,(interpolate (D.point u) (D.point v) t).2+1) := by
    apply Prod.ext <;> dsimp [P,point,interpolate]
    ring
  have baseY (u v : V) (t : ℝ) (a : 0<t) (b : t<1) : 1≤(interpolate (P (.inl u)) (P (.inl v)) t).2 := by
    rw [core]; dsimp [interpolate]
    linarith only [mul_nonneg (by linarith : 0≤1-t) (up u),mul_nonneg a.le (up v)]
  have fanY {s v k} (ok : fan s v k) (t : ℝ) :
      (interpolate (P (.inr s)) (P (.inl v)) t).2=t := by
    cases s <;> simp [P,point,interpolate,onLine _ _ _ ok]
  have undo {a b : Plane} (eq : (a.1,a.2+1)=(b.1,b.2+1)) : a=b := by
    have x := congrArg Prod.fst eq
    have y := congrArg Prod.snd eq
    exact Prod.ext x (add_right_cancel y)
  have inj : Function.Injective P := by
    rintro (u|s) (v|t) eq
    · have x := congrArg Prod.fst eq; have y := congrArg Prod.snd eq
      apply congrArg Sum.inl; apply D.injective; apply Prod.ext
      · exact x
      · change (D.point u).2+1=(D.point v).2+1 at y; linarith
    · have y := congrArg Prod.snd eq; cases t <;> change (D.point u).2+1=0 at y <;> linarith [up u]
    · have y := congrArg Prod.snd eq; cases s <;> change 0=(D.point v).2+1 at y <;> linarith [up v]
    · have x := congrArg Prod.fst eq; cases s <;> cases t <;> first | rfl | (dsimp [P,point] at x; linarith only [x])
  refine ⟨⟨P,inj,?_,?_⟩,rfl⟩
  · rintro (u|s) (v|j) ⟨k,e⟩ z t t0 t1 eq <;> try contradiction
    · cases z with
      | inl w =>
        apply D.miss ⟨k,e⟩ w t t0 t1
        rw [core] at eq
        exact undo eq
      | inr b =>
        have y := congrArg Prod.snd eq; have h := baseY u v t t0 t1
        cases b <;> change _ =0 at y <;> linarith
    · have y := congrArg Prod.snd eq; rw [fanY e] at y
      cases z with
      | inl w => change t=(D.point w).2+1 at y; linarith [up w]
      | inr b => cases b <;> change t=0 at y <;> linarith
  · rintro (u|i) (v|j) (a|s) (b|l) ⟨k,e⟩ ⟨m',f⟩ t y t0 t1 y0 y1 eq <;> try contradiction
    · have eq' : interpolate (D.point u) (D.point v) t=interpolate (D.point a) (D.point b) y := by
        rw [core,core] at eq; exact undo eq
      obtain ⟨rfl,rfl⟩ := D.apart ⟨k,e⟩ ⟨m',f⟩ _ _ t0 t1 y0 y1 eq'; exact ⟨rfl,rfl⟩
    · have z := congrArg Prod.snd eq; rw [fanY f] at z; linarith [baseY u v t t0 t1]
    · have z := congrArg Prod.snd eq; rw [fanY e] at z; linarith [baseY a b y y0 y1]
    · have z := congrArg Prod.snd eq; rw [fanY e,fanY f] at z; subst y
      have x := congrArg Prod.fst eq
      have F := bank _ _ _ e; have G := bank _ _ _ f
      have Y := onLine _ _ _ e; have Y' := onLine _ _ _ f
      cases i <;> cases s <;> dsimp [P,point,interpolate] at x <;> simp only [Bool.false_eq_true,if_false,if_true] at F G
      all_goals first
        | (refine ⟨rfl,congrArg Sum.inl (D.injective (Prod.ext ?_ (Y.trans Y'.symm)))⟩
           exact mul_left_cancel₀ t0.ne' (add_left_cancel x))
        | (exfalso; nlinarith only [x,mul_pos t0 (sub_pos.mpr F),mul_pos t0 (sub_pos.mpr G),t1])

end
end DisjointnessDraft.Applications.FanDrawing
