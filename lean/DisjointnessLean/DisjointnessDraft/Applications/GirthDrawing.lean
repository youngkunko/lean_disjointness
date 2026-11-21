import DisjointnessDraft.Applications.PlanarPadding
import Mathlib.Topology.Instances.Real.Lemmas

/-! Explicit continuous plane arcs for the directed graph. The top terminals are joined by
a parabola below all straight edges. Padding leaves are placed to the left of the core. -/
namespace DisjointnessDraft.Applications.GirthDrawing
open Planarity PlanarPadding Classical
noncomputable section
variable {V : Type}

structure Tracing (E : V → V → Prop) where
  point : V → Plane
  distinct : Function.Injective point
  curve : V → V → ℝ → Plane
  continuous : ∀ u v,E u v → Continuous (curve u v)
  ends : ∀ u v,E u v → curve u v 0=point u ∧ curve u v 1=point v
  simple : ∀ u v,E u v → Function.Injective (curve u v)
  misses : ∀ u v,E u v → ∀ z t,0<t → t<1 → curve u v t≠point z
  apart : ∀ u v a b,E u v → E a b → ∀ t s,0<t → t<1 → 0<s → s<1 →
    curve u v t=curve a b s → (u=a ∧ v=b) ∨ (u=b ∧ v=a)

theorem Tracing.mono {E F : V → V → Prop} (d : Tracing E) (h : ∀ u v,F u v → E u v) : Nonempty (Tracing F) :=
  ⟨⟨d.point,d.distinct,d.curve,fun _ _ e => d.continuous _ _ (h _ _ e),fun _ _ e => d.ends _ _ (h _ _ e),
    fun _ _ e => d.simple _ _ (h _ _ e),fun _ _ e => d.misses _ _ (h _ _ e),
    fun _ _ _ _ e f => d.apart _ _ _ _ (h _ _ e) (h _ _ f)⟩⟩

def swapPoint (p : Plane) : Plane := (p.2,p.1)
private theorem interpolate_swap (a b : Plane) (t : ℝ) :
    interpolate (swapPoint a) (swapPoint b) t=swapPoint (interpolate a b t) := rfl
private theorem swap_inj : Function.Injective swapPoint := fun _ _ h => Prod.ext (congrArg Prod.snd h) (congrArg Prod.fst h)

def swapDraw {E : V → V → Prop} (D : Drawing E) : Drawing E where
  point v := swapPoint (D.point v)
  injective := swap_inj.comp D.injective
  miss e z t t0 t1 h := D.miss e z t t0 t1 (swap_inj h)
  apart e f t s t0 t1 s0 s1 h := D.apart e f t s t0 t1 s0 s1 (swap_inj h)

def shift (r : ℝ) (p : Plane) : Plane := (p.1-r,p.2)
private theorem shift_inj (r : ℝ) : Function.Injective (shift r) := by
  intro a b h; have x := congrArg Prod.fst h; have y := congrArg Prod.snd h
  exact Prod.ext (sub_left_inj.mp x) y
private theorem interpolate_shift (r : ℝ) (a b : Plane) (t : ℝ) :
    interpolate (shift r a) (shift r b) t=shift r (interpolate a b t) := by
  apply Prod.ext
  · dsimp [shift,interpolate]; ring
  · rfl

def shiftDraw {E : V → V → Prop} (D : Drawing E) (r : ℝ) : Drawing E where
  point v := shift r (D.point v)
  injective := (shift_inj r).comp D.injective
  miss e z t t0 t1 h := by rw [interpolate_shift] at h; exact D.miss e z t t0 t1 (shift_inj r h)
  apart e f t s t0 t1 s0 s1 h := by
    rw [interpolate_shift,interpolate_shift] at h; exact D.apart e f t s t0 t1 s0 s1 (shift_inj r h)

/-- The padded drawing stays in the upper half-plane, even with arbitrarily many leaves. -/
theorem pad_left (E : V → ℤ → V → Prop) (D : Drawing (plain E)) (root : V)
    (left : ∀v,(D.point root).1≤(D.point v).1) (up : ∀v,0≤(D.point v).2) :
    ∃ F : Drawing (plain (extend (pad:=pad) E root)),(∀v,0≤(F.point v).2) ∧
      ∀v,F.point (.inl v)=D.point v := by
  let r := (D.point root).1
  let d := swapDraw (shiftDraw D r)
  obtain ⟨d',hd⟩ := drawing_at (pad:=pad) E root d (fun v => sub_nonneg.mpr (left v)) (sub_self r)
  let fin := shiftDraw (swapDraw d') (-r)
  have core (v : V) : fin.point (.inl v)=D.point v := by
    change shift (-r) (swapPoint (d'.point (.inl v)))=D.point v
    rw [hd]; apply Prod.ext <;> simp [d,shiftDraw,swapDraw,shift,swapPoint,extendPoint]
  refine ⟨fin,?_,core⟩
  rintro (v|i)
  · rw [core]; exact up v
  · change 0≤(d'.point (.inr i)).1
    rw [hd]; change 0≤(D.point root).2+i.val+1; linarith [up root,Nat.cast_nonneg (α:=ℝ) i.val]

private theorem reverse (p q : Plane) (t : ℝ) :
    interpolate p q t=interpolate q p (1-t) := by apply Prod.ext <;> dsimp [interpolate] <;> ring
private theorem interp_inj {u v : Plane} (n : u≠v) : Function.Injective (interpolate u v) := by
  intro a b e
  by_cases x : u.1=v.1
  · have y := congrArg Prod.snd e
    have ne : u.2≠v.2 := fun eq => n (Prod.ext x eq)
    dsimp [interpolate] at y
    exact sub_eq_zero.mp ((mul_eq_zero.mp (show (a-b)*(u.2-v.2)=0 by linarith only [y])).resolve_right (sub_ne_zero.mpr ne))
  · have y := congrArg Prod.fst e; dsimp [interpolate] at y
    exact sub_eq_zero.mp ((mul_eq_zero.mp (show (a-b)*(u.1-v.1)=0 by linarith only [y])).resolve_right (sub_ne_zero.mpr x))

def bend (u v : Plane) (t : ℝ) : Plane := ((interpolate u v t).1,-t*(1-t))

theorem with_return {base arc : V → V → Prop} (d : Drawing base) (up : ∀ v,0≤(d.point v).2)
    (orient : ∀ u v,arc u v → base u v ∨ base v u) (loop : ∀u,¬arc u u)
    (src dst : V) (src0 : (d.point src).2=0) (dst0 : (d.point dst).2=0) (ne : src≠dst) :
    Nonempty (Tracing (fun u v => arc u v ∨ u=dst ∧ v=src)) := by
  classical
  let c := fun u v t => if u=dst ∧ v=src then bend (d.point dst) (d.point src) t else interpolate (d.point u) (d.point v) t
  have nx : (d.point dst).1≠(d.point src).1 := fun h => ne (d.injective (Prod.ext h (dst0.trans src0.symm))).symm
  have ok {u v} (e : arc u v ∨ u=dst ∧ v=src) (h : ¬(u=dst ∧ v=src)) := e.resolve_right h
  have route {u v} (e : arc u v) (t : ℝ) (a : 0<t) (b : t<1) :
      ∃ x y s,base x y ∧ 0<s ∧ s<1 ∧ ((u=x ∧ v=y) ∨ (u=y ∧ v=x)) ∧
        interpolate (d.point u) (d.point v) t=interpolate (d.point x) (d.point y) s := by
    rcases orient _ _ e with uv|vu
    · exact ⟨u,v,t,uv,a,b,Or.inl ⟨rfl,rfl⟩,rfl⟩
    · exact ⟨v,u,1-t,vu,by linarith,by linarith,Or.inr ⟨rfl,rfl⟩,reverse ..⟩
  have sep {t s : ℝ} (t0 : 0<t) (t1 : t<1) (s0 : 0<s) (s1 : s<1) (u v : V) :
      bend (d.point dst) (d.point src) t≠interpolate (d.point u) (d.point v) s := by
    intro h; have y := congrArg Prod.snd h
    dsimp [bend,interpolate] at y
    nlinarith only [y,mul_pos t0 (sub_pos.mpr t1),mul_nonneg (sub_nonneg.mpr s1.le) (up u),mul_nonneg s0.le (up v)]
  refine ⟨⟨d.point,d.injective,c,?_,?_,?_,?_,?_⟩⟩
  · intro u v _; dsimp only [c]; split_ifs <;> dsimp [bend,interpolate] <;> fun_prop
  · intro u v _; dsimp only [c]; split_ifs with e
    · obtain ⟨rfl,rfl⟩ := e; exact ⟨by ext <;> simp [bend,interpolate,dst0],by ext <;> simp [bend,interpolate,src0]⟩
    · simp [interpolate]
  · intro u v e; dsimp only [c]; split_ifs with h
    · intro a b eq; have x := congrArg Prod.fst eq; dsimp [bend,interpolate] at x
      exact sub_eq_zero.mp ((mul_eq_zero.mp (show (a-b)*((d.point dst).1-(d.point src).1)=0 by linarith only [x])).resolve_right (sub_ne_zero.mpr nx))
    · apply interp_inj; intro eq; obtain rfl := d.injective eq; exact loop _ (ok e h)
  · intro u v e z t t0 t1; dsimp only [c]; split_ifs with h
    · intro eq; have y := congrArg Prod.snd eq; dsimp [bend] at y
      nlinarith only [y,mul_pos t0 (sub_pos.mpr t1),up z]
    · obtain ⟨a,b,s,ed,s0,s1,_,eq⟩ := route (ok e h) t t0 t1
      rw [eq]; exact d.miss ed z s s0 s1
  · intro u v a b e f t s t0 t1 s0 s1; dsimp only [c]; split_ifs with h l l
    · rintro _; exact Or.inl ⟨h.1.trans l.1.symm,h.2.trans l.2.symm⟩
    · exact fun eq => (sep t0 t1 s0 s1 _ _ eq).elim
    · exact fun eq => (sep s0 s1 t0 t1 _ _ eq.symm).elim
    · obtain ⟨u',v',r,ed,r0,r1,p,hr⟩ := route (ok e h) t t0 t1
      obtain ⟨a',b',t',fd,l0,l1,q,hl⟩ := route (ok f l) s s0 s1
      rw [hr,hl]; intro eq
      obtain ⟨rfl,rfl⟩ := d.apart ed fd r t' r0 r1 l0 l1 eq
      rcases p with ⟨rfl,rfl⟩|⟨rfl,rfl⟩ <;> rcases q with ⟨rfl,rfl⟩|⟨rfl,rfl⟩ <;> simp

end
end DisjointnessDraft.Applications.GirthDrawing
