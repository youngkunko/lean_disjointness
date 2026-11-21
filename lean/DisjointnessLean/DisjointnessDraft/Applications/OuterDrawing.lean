import DisjointnessDraft.Applications.PlanarPadding

/-! Two distinguished external leaves at boundary points, and an arbitrary
number of isolated vertices, have a common straight-line drawing. -/
namespace DisjointnessDraft.Applications.OuterDrawing
open Planarity PlanarPadding
noncomputable section
inductive Host (W : Type) (pad : ℕ) where | old (u : W) | source | sink | isolate (i : Fin pad)
inductive Edge {W : Type} (E : W → W → Prop) (a b : W) : Host W pad → Host W pad → Prop
  | base {u v} (e : E u v) : Edge E a b (.old u) (.old v)
  | left : Edge E a b .source (.old a)
  | right : Edge E a b (.old b) .sink

variable {W : Type} {E : W → W → Prop}
def point (D : Drawing E) (a b : W) : Host W pad → Plane
  | .old u => D.point u
  | .source => ((D.point a).1,-1)
  | .sink => ((D.point b).1,-1)
  | .isolate i => ((i.val:ℝ),-2)

def drawing (D : Drawing E) (up : ∀v,0≤(D.point v).2) (a b : W) (different : a≠b)
    (ax : (D.point a).2=0) (bx : (D.point b).2=0) : Drawing (Edge (pad:=pad) E a b) := by
  let pt := point (pad:=pad) D a b
  have diff : (D.point a).1≠(D.point b).1 := fun h => different (D.injective (Prod.ext h (ax.trans bx.symm)))
  have inj : Function.Injective pt := by
    intro x y eq
    have fx := congrArg Prod.fst eq; have fy := congrArg Prod.snd eq
    cases x <;> cases y <;> dsimp [pt,point] at fx fy
    all_goals first
      | rfl
      | exact congrArg Host.old (D.injective (Prod.ext fx fy))
      | exact congrArg Host.isolate (Fin.ext (by exact_mod_cast fx))
      | contradiction
      | exact False.elim (diff fx)
      | exact False.elim (diff fx.symm)
      | (exfalso; norm_num at fy <;> try linarith)
    all_goals first | (rename_i u i; linarith [up u]) | (rename_i u; linarith [up u])
  have high (u v : W) (t : ℝ) (t0 : 0<t) (t1 : t<1) :
      0≤(interpolate (D.point u) (D.point v) t).2 :=
    add_nonneg (mul_nonneg (by linarith) (up u)) (mul_nonneg t0.le (up v))
  have left (t : ℝ) : interpolate (pt .source) (pt (.old a)) t=((D.point a).1,t-1) := by
    apply Prod.ext <;> dsimp [pt,point,interpolate]
    all_goals try rw [ax]
    all_goals ring
  have right (t : ℝ) : interpolate (pt (.old b)) (pt .sink) t=((D.point b).1,-t) := by
    apply Prod.ext <;> dsimp [pt,point,interpolate]
    all_goals try rw [bx]
    all_goals ring
  refine ⟨pt,inj,?_,?_⟩
  · intro u v e z t t0 t1 eq
    cases e with
    | @base u v e =>
      cases z with
      | old z => exact D.miss e z t t0 t1 eq
      | _ =>
        have y := congrArg Prod.snd eq
        change (interpolate (D.point u) (D.point v) t).2=_ at y
        dsimp [pt,point] at y
        linarith [high u v t t0 t1]
    | left =>
      rw [left] at eq
      have y := congrArg Prod.snd eq
      cases z <;> dsimp [pt,point] at y <;> try linarith
      rename_i u; linarith [up u]
    | right =>
      rw [right] at eq
      have y := congrArg Prod.snd eq
      cases z <;> dsimp [pt,point] at y <;> try linarith
      rename_i u; linarith [up u]
  · intro u v i j e f t s t0 t1 s0 s1 eq
    cases e with
    | @base u v e =>
      cases f with
      | base f =>
        obtain ⟨rfl,rfl⟩ := D.apart e f t s t0 t1 s0 s1 eq
        exact ⟨rfl,rfl⟩
      | left =>
        rw [left] at eq; have y := congrArg Prod.snd eq
        change (interpolate (D.point u) (D.point v) t).2=s-1 at y
        linarith [high u v t t0 t1]
      | right =>
        rw [right] at eq; have y := congrArg Prod.snd eq
        change (interpolate (D.point u) (D.point v) t).2= -s at y
        linarith [high u v t t0 t1]
    | left =>
      cases f with
      | @base u v e =>
        rw [left] at eq; have y := congrArg Prod.snd eq
        change t-1=(interpolate (D.point u) (D.point v) s).2 at y
        linarith [high u v s s0 s1]
      | left => exact ⟨rfl,rfl⟩
      | right =>
        rw [left,right] at eq; exact False.elim (diff (Prod.mk.inj eq).1)
    | right =>
      cases f with
      | @base u v e =>
        rw [right] at eq; have y := congrArg Prod.snd eq
        change -t=(interpolate (D.point u) (D.point v) s).2 at y
        linarith [high u v s s0 s1]
      | left =>
        rw [right,left] at eq; exact False.elim (diff (Prod.mk.inj eq.symm).1)
      | right => exact ⟨rfl,rfl⟩

def pull {V : Type} {G : V → V → Prop} (D : Drawing E) (f : V → W)
    (inj : Function.Injective f) (sub : ∀{u v},G u v → E (f u) (f v)) : Drawing G where
  point v := D.point (f v)
  injective := D.injective.comp inj
  miss e z := D.miss (sub e) (f z)
  apart e e' t s t0 t1 s0 s1 eq :=
    let h := D.apart (sub e) (sub e') t s t0 t1 s0 s1 eq
    ⟨inj h.1,inj h.2⟩
end
end DisjointnessDraft.Applications.OuterDrawing
