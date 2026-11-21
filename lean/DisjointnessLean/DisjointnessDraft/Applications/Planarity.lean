import DisjointnessDraft.Applications.PlanarCore
import Mathlib.Data.Real.Basic

/-! Explicit straight-line drawing for the grid. The interior of every edge
lies in a half-open cell that identifies its two grid indices uniquely. Within
one cell all six possible segments have disjoint interiors and miss every
vertex. Reflection and a channel outside the grids join facing terminals. -/
namespace DisjointnessDraft.Applications.Planarity
open OriginalGrid
abbrev XY := ℤ × ℤ
def coord : Vertex → XY
  | .corner (r,c) => (4*c,4*r)
  | .inside r c .v => (4*c,4*r-2)
  | .inside r c .w => (4*c+2,4*r)
  | .inside r c .x => (4*c+1,4*r-1)

theorem distinct : Function.Injective coord := by
  intro u v h
  have hx := congrArg Prod.fst h
  have hy := congrArg Prod.snd h
  clear h
  cases u with
  | corner p =>
    obtain ⟨r,c⟩ := p
    cases v with
    | corner q => obtain ⟨s,t⟩ := q; simp_all [coord]
    | inside s t k => cases k <;> simp_all [coord] <;> omega
  | inside r c k =>
    cases v with
    | corner q => obtain ⟨s,t⟩ := q; cases k <;> simp_all [coord] <;> omega
    | inside s t other => cases k <;> cases other <;> simp_all [coord] <;> omega

abbrev Plane := ℝ × ℝ
def point (u : Vertex) : Plane := ((coord u).1,(coord u).2)
def interpolate (u v : Plane) (t : ℝ) : Plane := ((1-t)*u.1+t*v.1,(1-t)*u.2+t*v.2)
def delta : Local → Plane
  | .a => (0,-4) | .b => (0,0) | .c => (4,0)
  | .inside .v => (0,-2) | .inside .w => (2,0) | .inside .x => (1,-1)

theorem localDrawing (r c : ℤ) (u : Local) :
    point (embed r c u)=(4*(c:ℝ)+(delta u).1,4*(r:ℝ)+(delta u).2) := by
  cases u with
  | inside i => cases i <;> simp [point,coord,embed,delta] <;> ring_nf
  | _ => simp [point,coord,embed,delta] <;> ring_nf

private theorem atCell (r c : ℤ) (u v : Local) (t : ℝ) :
    interpolate (point (embed r c u)) (point (embed r c v)) t=
    (4*(c:ℝ)+(interpolate (delta u) (delta v) t).1,4*(r:ℝ)+(interpolate (delta u) (delta v) t).2) := by
  rw [localDrawing,localDrawing]; apply Prod.ext <;> dsimp [interpolate] <;> ring

private theorem box {p c m u v w} (e : Edge p c m u w v) (t : ℝ) (t0 : 0<t) (t1 : t<1) :
    let a := interpolate (delta u) (delta v) t
    0≤a.1 ∧ a.1<4 ∧ -4<a.2 ∧ a.2≤0 := by
  cases e <;> dsimp [interpolate,delta] <;> constructor <;> first | linarith | (constructor <;> first | linarith | (constructor <;> linarith))

private theorem localDisjoint {p c m u v w src dst d} (e : Edge p c m u w v) (e' : Edge p c m src d dst)
    (t s : ℝ) (t0 : 0<t) (t1 : t<1) (s0 : 0<s) (s1 : s<1)
    (eq : interpolate (delta u) (delta v) t = interpolate (delta src) (delta dst) s) :
    u=src ∧ v=dst := by
  have hx := congrArg Prod.fst eq
  have hy := congrArg Prod.snd eq
  cases e <;> cases e' <;> dsimp [interpolate,delta] at hx hy <;> first | exact ⟨rfl,rfl⟩ | exfalso; linarith

private theorem unique_axis {c k : ℤ} {a b : ℝ} (a0 : 0≤a) (a4 : a<4) (b0 : 0≤b) (b4 : b<4)
    (eq : 4*(c:ℝ)+a=4*(k:ℝ)+b) : c=k := by
  by_contra ne
  rcases lt_or_gt_of_ne ne with z|z
  · have one : (c:ℝ)+1≤(k:ℝ) := by exact_mod_cast (show c+1≤k by omega)
    linarith
  · have one : (k:ℝ)+1≤(c:ℝ) := by exact_mod_cast (show k+1≤c by omega)
    linarith

private theorem unique_row {r k : ℤ} {a b : ℝ} (a4 : -4<a) (a0 : a≤0) (b4 : -4<b) (b0 : b≤0)
    (eq : 4*(r:ℝ)+a=4*(k:ℝ)+b) : r=k := by
  have z : -r = -k := unique_axis (neg_nonneg.mpr a0) (by linarith) (neg_nonneg.mpr b0) (by linarith)
    (by push_cast; linarith only [eq])
  omega

theorem segments_disjoint {p M u v a b w d} (e : Step p M u w v) (e' : Step p M a d b)
    (t s : ℝ) (t0 : 0<t) (t1 : t<1) (s0 : 0<s) (s1 : s<1)
    (eq : interpolate (point u) (point v) t=interpolate (point a) (point b) s) : u=a ∧ v=b := by
  cases e with
  | cell r c r1 rp c1 cp e =>
    cases e' with
    | cell k l k1 kp l1 lp f =>
      rw [atCell,atCell] at eq
      have ⟨hx,hy⟩ := Prod.mk.inj eq
      have ⟨x0,x4,y4,y0⟩ := box e t t0 t1
      have ⟨a0,a4,b4,b0⟩ := box f s s0 s1
      have co := unique_axis x0 x4 a0 a4 hx
      have ro := unique_row y4 y0 b4 b0 hy
      subst k; subst l
      obtain ⟨rfl,rfl⟩ := localDisjoint e f t s t0 t1 s0 s1 (Prod.ext (by linarith only [hx]) (by linarith only [hy]))
      exact ⟨rfl,rfl⟩

private theorem localMiss {p c m u v w} (e : Edge p c m u w v) (z : Local) (t : ℝ) (t0 : 0<t) (t1 : t<1) :
    interpolate (delta u) (delta v) t ≠ delta z := by
  intro eq
  have hx := congrArg Prod.fst eq
  have hy := congrArg Prod.snd eq
  cases z with
  | inside i => cases i <;> cases e <;> dsimp [interpolate,delta] at hx hy <;> linarith
  | _ => cases e <;> dsimp [interpolate,delta] at hx hy <;> linarith

private theorem represented (z : Vertex) : ∃ r c k, z=embed r c k ∧
    0≤(delta k).1 ∧ (delta k).1<4 ∧ -4<(delta k).2 ∧ (delta k).2≤0 := by
  cases z with
  | corner q => obtain ⟨r,c⟩ := q; exact ⟨r,c,.b,rfl,by norm_num [delta]⟩
  | inside r c i => refine ⟨r,c,.inside i,rfl,?_⟩; cases i <;> norm_num [delta]

theorem segments_miss_vertices {p M u v w} (e : Step p M u w v) (z : Vertex) (t : ℝ) (t0 : 0<t) (t1 : t<1) :
    interpolate (point u) (point v) t ≠ point z := by
  intro eq
  obtain ⟨k,l,z,rfl,a0,a4,b4,b0⟩ := represented z
  cases e with
  | cell r c r1 rp c1 cp e =>
    rw [atCell,localDrawing] at eq
    have ⟨hx,hy⟩ := Prod.mk.inj eq
    have ⟨x0,x4,y4,y0⟩ := box e t t0 t1
    have co := unique_axis x0 x4 a0 a4 hx
    have ro := unique_row y4 y0 b4 b0 hy
    subst k; subst l
    exact localMiss e z t t0 t1 (Prod.ext (by linarith only [hx]) (by linarith only [hy]))

def boundary (p : ℤ) : ℝ := 4*((p:ℝ)+1)
def reflect (p : ℤ) (x : Plane) : Plane := (2*boundary p+1-x.1,x.2)
def draw (p : ℤ) : PlanarCore.T → Plane
  | .left v => point v | .right v => reflect p (point v)
inductive CoreEdge (p : ℤ) (M : ℤ → ℤ → Bool) (A : ℤ → Prop) : PlanarCore.T → PlanarCore.T → Prop
  | left {u v w} (e : Step p M u w v) : CoreEdge p M A (.left u) (.left v)
  | right {u v w} (e : Step p PlanarCore.Zmat u w v) : CoreEdge p M A (.right u) (.right v)
  | connect (j : ℤ) (enabled : A j) : CoreEdge p M A (.left (PlanarCore.side p j)) (.right (PlanarCore.side p j))

private theorem refl_inj {p} : Function.Injective (reflect p) := by
  intro u v e; apply Prod.ext
  · have h := congrArg Prod.fst e; dsimp [reflect] at h; linarith
  · have h := congrArg Prod.snd e; exact h
private theorem reflection (p : ℤ) (a b : Plane) (t : ℝ) :
    interpolate (reflect p a) (reflect p b) t=reflect p (interpolate a b t) := by
  apply Prod.ext
  · dsimp [reflect,interpolate]; ring
  · rfl
private theorem rod (p j : ℤ) (t : ℝ) :
    interpolate (point (PlanarCore.side p j)) (reflect p (point (PlanarCore.side p j))) t
      =(boundary p+t,4*(j:ℝ)) := by
  apply Prod.ext <;> dsimp [PlanarCore.side,point,coord,reflect,interpolate,boundary] <;> push_cast <;> ring

private theorem slab {p M u v w} (e : Step p M u w v) (t : ℝ) (t0 : 0<t) (t1 : t<1) :
    (interpolate (point u) (point v) t).1<boundary p := by
  cases e with
  | cell r c r1 rp c1 cp e =>
    rw [atCell]
    have b := (box e t t0 t1).2.1
    have cp' : (c:ℝ)≤p := by exact_mod_cast cp
    dsimp [boundary]; linarith

theorem core_segments {p M A u v a b} (e : CoreEdge p M A u v) (e' : CoreEdge p M A a b)
    (t s : ℝ) (t0 : 0<t) (t1 : t<1) (s0 : 0<s) (s1 : s<1)
    (eq : interpolate (draw p u) (draw p v) t=interpolate (draw p a) (draw p b) s) : u=a ∧ v=b := by
  cases e <;> cases e' <;> simp only [draw,reflection,rod] at eq
  case left.left e _ _ _ f => obtain ⟨rfl,rfl⟩ := segments_disjoint e f t s t0 t1 s0 s1 eq; exact ⟨rfl,rfl⟩
  case right.right e _ _ _ f => obtain ⟨rfl,rfl⟩ := segments_disjoint e f t s t0 t1 s0 s1 (refl_inj eq); exact ⟨rfl,rfl⟩
  case connect.connect i _ j _ =>
    have y := congrArg Prod.snd eq
    have equ : (i:ℝ)=j := by dsimp at y; linarith
    have h : i=j := by exact_mod_cast equ
    subst j; exact ⟨rfl,rfl⟩
  all_goals exfalso; have h := congrArg Prod.fst eq; dsimp only [reflect,Prod.fst] at h
  case left.right e _ _ _ f => linarith only [h,slab e t t0 t1,slab f s s0 s1]
  case right.left e _ _ _ f => linarith only [h,slab e t t0 t1,slab f s s0 s1]
  case left.connect e j _ => linarith only [h,slab e t t0 t1,s0]
  case right.connect e j _ => linarith only [h,slab e t t0 t1,s1]
  case connect.left j _ f => linarith only [h,slab f s s0 s1,t0]
  case connect.right j _ f => linarith only [h,slab f s s0 s1,t1]

def displayed (p : ℤ) : PlanarCore.T → Prop
  | .left v | .right v => (point v).1≤boundary p

private theorem vertex_bounds {p M u v w} (e : Step p M u w v) :
    (point u).1≤boundary p ∧ (point v).1≤boundary p := by
  cases e with
  | cell r c r1 rp c1 cp e =>
    rw [localDrawing,localDrawing]
    have cp' : (c:ℝ)≤p := by exact_mod_cast cp
    cases e <;> dsimp [boundary,delta] <;> constructor <;> linarith

theorem endpoints_displayed {p M A u v} (e : CoreEdge p M A u v) : displayed p u ∧ displayed p v := by
  cases e with
  | left e => exact vertex_bounds e
  | right e => exact vertex_bounds e
  | connect j _ => simp [displayed,PlanarCore.side,point,boundary,coord]

private theorem point_inj : Function.Injective point := by
  intro u v h
  have a := congrArg Prod.fst h
  have b := congrArg Prod.snd h
  dsimp only [point,Prod.fst,Prod.snd] at a b
  apply distinct
  exact Prod.ext (by exact_mod_cast a) (by exact_mod_cast b)

theorem core_vertices {p a b} (ha : displayed p a) (hb : displayed p b) (eq : draw p a=draw p b) : a=b := by
  have hx := congrArg Prod.fst eq
  cases a <;> cases b <;> simp only [displayed,draw,reflect,Prod.fst] at ha hb hx
  case left.left => exact congrArg _ (point_inj eq)
  case right.right => exact congrArg _ (point_inj (refl_inj eq))
  all_goals exfalso; linarith

theorem core_misses_vertices {p M A u v z} (e : CoreEdge p M A u v) (hz : displayed p z)
    (t : ℝ) (t0 : 0<t) (t1 : t<1) :
    interpolate (draw p u) (draw p v) t ≠ draw p z := by
  intro eq
  cases e <;> cases z <;> simp only [draw,reflection,rod] at eq
  case left.left e _ => exact segments_miss_vertices e _ t t0 t1 eq
  case right.right e _ => exact segments_miss_vertices e _ t t0 t1 (refl_inj eq)
  all_goals have h := congrArg Prod.fst eq; dsimp only [reflect,Prod.fst] at h; dsimp only [displayed] at hz
  case left.right e _ => linarith only [slab e t t0 t1,h,hz]
  case right.left e _ => linarith only [slab e t t0 t1,h,hz]
  all_goals linarith

private theorem above {p M u v w} (e : Step p M u w v) :
    0≤(point u).2 ∧ 0≤(point v).2 := by
  cases e with
  | cell r c r1 rp c1 cp e =>
    rw [localDrawing,localDrawing]
    have rr : (1:ℝ)≤r := by exact_mod_cast r1
    cases e <;> dsimp [delta] <;> constructor <;> linarith

theorem above_line {p M A u v} (rows : ∀ j,A j → 1≤j) (e : CoreEdge p M A u v) : 0≤(draw p u).2 ∧ 0≤(draw p v).2 := by
  cases e with
  | left e => exact above e
  | right e => exact above e
  | connect j on => have h := rows j on; simp [draw,reflect,point,PlanarCore.side,coord]; omega

/-- An outer-face arc for the girth selector, parametrized from the right
top terminal to the left one. Its interior lies strictly below the drawing. -/
def backArc (p q : ℤ) (t : ℝ) : Plane :=
  let a := draw p (.right (PlanarCore.top (p-q+1)))
  let b := draw p (.left (PlanarCore.top q))
  ((interpolate a b t).1,-t*(1-t))

theorem backArc_ends (p q : ℤ) : backArc p q 0=draw p (.right (PlanarCore.top (p-q+1))) ∧
    backArc p q 1=draw p (.left (PlanarCore.top q)) := by
  simp [backArc,draw,point,reflect,PlanarCore.top,coord,interpolate]
theorem backArc_simple (p q : ℤ) (q1 : 1≤q) (qp : q≤p) : Function.Injective (backArc p q) := by
  intro a b eq
  have hx := congrArg Prod.fst eq
  dsimp [backArc,draw,point,reflect,PlanarCore.top,coord,interpolate,boundary] at hx
  push_cast at hx
  have h : (q:ℝ)≤p := by exact_mod_cast qp
  have z : (1:ℝ)≤q := by exact_mod_cast q1
  have factor : (4*(p:ℝ)+5)*(a-b)=0 := by linarith only [hx]
  exact sub_eq_zero.mp ((mul_eq_zero.mp factor).resolve_left (by linarith))
theorem backArc_disjoint {p M A u v} (rows : ∀ j,A j → 1≤j) (edge : CoreEdge p M A u v) (q : ℤ)
    (t s : ℝ) (t0 : 0<t) (t1 : t<1) (s0 : 0≤s) (s1 : s≤1) :
    backArc p q t≠interpolate (draw p u) (draw p v) s := by
  intro eq
  have hy := congrArg Prod.snd eq
  have ⟨u0,v0⟩ := above_line rows edge
  have h := add_nonneg (mul_nonneg (sub_nonneg.mpr s1) u0) (mul_nonneg s0 v0)
  dsimp [backArc,interpolate] at hy
  nlinarith only [hy,h,mul_pos t0 (sub_pos.mpr t1)]
end DisjointnessDraft.Applications.Planarity
