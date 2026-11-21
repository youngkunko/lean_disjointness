import DisjointnessDraft.Applications.PlanarMatching
import DisjointnessDraft.Applications.Planarity

/-! A straight-line drawing for the split grid. One horizontal unit separates
the in/out copies on a sixteen-unit grid. The unconnected shortcut leaf in
the right-hand grid lies above its parent. -/
namespace DisjointnessDraft.Applications.SplitGrid
open OriginalGrid Planarity Classical
noncomputable section
abbrev Node := Vertex×Bool
abbrev Site := Local×Bool
inductive Template where | av | vb | bw | wc | vx | xw | b | v | w | x deriving DecidableEq

def addBit (b : Bool) : ℝ := if b then 1 else 0
def offset (right : Bool) (z : Site) : Plane :=
  let a := addBit z.2
  match z.1 with
  | .a => (a,-16) | .b => (a,0) | .c => (16+a,0)
  | .inside .v => (a,-8) | .inside .w => (8+a,0)
  | .inside .x => (4+a,if right then -12 else -4)
def center : Vertex → ℤ×ℤ | .corner p => p | .inside r c _ => (r,c)
def kind : Vertex → Local | .corner _ => .b | .inside _ _ k => .inside k
def pt (right : Bool) (v : Node) : Plane :=
  (16*((center v.1).2:ℝ)+(offset right (kind v.1,v.2)).1,
   16*((center v.1).1:ℝ)+(offset right (kind v.1,v.2)).2)
def siteNode (r c : ℤ) (z : Site) : Node := (embed r c z.1,z.2)
def diagonal (right : Bool) (u : Local) : Site×Site := ((u,!right),(u,right))
def ends (right : Bool) : Template → Site×Site
  | .av => if right then ((.inside .v,false),(.a,true)) else ((.a,true),(.inside .v,false))
  | .vb => if right then ((.b,false),(.inside .v,true)) else ((.inside .v,true),(.b,false))
  | .bw => if right then ((.inside .w,false),(.b,true)) else ((.b,true),(.inside .w,false))
  | .wc => if right then ((.c,false),(.inside .w,true)) else ((.inside .w,true),(.c,false))
  | .vx => ((.inside .v,!right),(.inside .x,right))
  | .xw => ((.inside .x,true),(.inside .w,false))
  | .b => diagonal right .b | .v => diagonal right (.inside .v)
  | .w => diagonal right (.inside .w) | .x => diagonal right (.inside .x)
def usable (right : Bool) (k : Template) := right=true → k≠.xw

def edge (right : Bool) (u v : Node) := ∃r c k,usable right k ∧
  u=siteNode r c (ends right k).1 ∧ v=siteNode r c (ends right k).2

theorem atSite (right : Bool) (r c : ℤ) (z : Site) : pt right (siteNode r c z)=
    (16*(c:ℝ)+(offset right z).1,16*(r:ℝ)+(offset right z).2) := by
  rcases z with ⟨k,b⟩
  cases k <;> simp [pt,siteNode,embed,center,kind,offset] <;> ring_nf

theorem atCell (right : Bool) (r c : ℤ) (u v : Site) (t : ℝ) :
    interpolate (pt right (siteNode r c u)) (pt right (siteNode r c v)) t =
      (16*(c:ℝ)+(interpolate (offset right u) (offset right v) t).1,
       16*(r:ℝ)+(interpolate (offset right u) (offset right v) t).2) := by
  rw [atSite,atSite]; apply Prod.ext <;> dsimp [interpolate] <;> ring

def along (d : Bool) (k : Template) (t : ℝ) := interpolate (offset d (ends d k).1) (offset d (ends d k).2) t
macro "local_calc" : tactic => `(tactic| (norm_num [along,ends,diagonal,offset,addBit,interpolate,usable] at * <;> first | contradiction | linarith))
theorem inside (d : Bool) (k : Template) (t : ℝ) (h : usable d k) (t0 : 0<t) (t1 : t<1) :
    0≤(along d k t).1 ∧ (along d k t).1<16 ∧ -16<(along d k t).2 ∧ (along d k t).2≤0 := by
  cases d <;> cases k <;> repeat' apply And.intro
  all_goals local_calc

set_option maxHeartbeats 3000000 in
theorem local_apart (d : Bool) (a k : Template) (u : usable d a) (v : usable d k)
    (t s : ℝ) (t0 : 0<t) (t1 : t<1) (s0 : 0<s) (s1 : s<1) (eq : along d a t=along d k s) : a=k := by
  have x := congrArg Prod.fst eq; have y := congrArg Prod.snd eq
  clear eq
  cases d <;> cases a <;> cases k <;> first | rfl | (exfalso; local_calc)

set_option maxHeartbeats 3000000 in
theorem local_miss (d : Bool) (k : Template) (z : Site) (u : usable d k) (t : ℝ) (t0 : 0<t) (t1 : t<1) :
    along d k t≠offset d z := by
  rcases z with ⟨z,b⟩
  intro eq
  have x := congrArg Prod.fst eq; have y := congrArg Prod.snd eq; clear eq
  cases z with
  | inside i => cases d <;> cases k <;> cases i <;> cases b <;> local_calc
  | _ => cases d <;> cases k <;> cases b <;> local_calc

theorem unique_axis {a b : ℤ} {x y : ℝ} (lx : 0≤x) (hx : x<16) (ly : 0≤y) (hy : y<16)
    (eq : 16*(a:ℝ)+x=16*(b:ℝ)+y) : a=b := by
  by_contra ne
  rcases lt_or_gt_of_ne ne with lt|lt
  · have h : (a:ℝ)+1≤b := by exact_mod_cast (show a+1≤b by omega)
    linarith
  · have h : (b:ℝ)+1≤a := by exact_mod_cast (show b+1≤a by omega)
    linarith

theorem unique_row {a b : ℤ} {x y : ℝ} (lx : -16<x) (hx : x≤0) (ly : -16<y) (hy : y≤0)
    (eq : 16*(a:ℝ)+x=16*(b:ℝ)+y) : a=b := by
  apply neg_inj.mp
  apply unique_axis (neg_nonneg.mpr hx) (by linarith : -x<16) (neg_nonneg.mpr hy) (by linarith : -y<16)
  push_cast; linarith

private theorem rep (z : Node) : siteNode (center z.1).1 (center z.1).2 (kind z.1,z.2)=z := by
  rcases z with ⟨v,d⟩; cases v <;> rfl
private theorem canonical (d : Bool) (z : Node) : let v:=offset d (kind z.1,z.2)
    0≤v.1 ∧ v.1<16 ∧ -16<v.2 ∧ v.2≤0 := by
  rcases z with ⟨v,s⟩
  cases v with
  | corner z => cases d <;> cases s <;> norm_num [kind,offset,addBit]
  | inside r c i => cases d <;> cases i <;> cases s <;> norm_num [kind,offset,addBit]

private theorem kinds {d : Bool} (u v : Node) (eq : offset d (kind u.1,u.2)=offset d (kind v.1,v.2)) :
    (kind u.1,u.2)=(kind v.1,v.2) := by
  rcases u with ⟨v₁,b⟩; rcases v with ⟨v₂,a⟩
  have ex := congrArg Prod.fst eq
  have ey := congrArg Prod.snd eq
  clear eq
  cases v₁ with
  | corner x => cases v₂ with
                | corner y => cases d <;> cases b <;> cases a <;> norm_num [kind,offset,addBit] at ex ey ⊢
                | inside s t j => cases j <;> cases d <;> cases b <;> cases a <;> norm_num [kind,offset,addBit] at ex ey ⊢
  | inside r c i => cases v₂ with
                    | corner y => cases i <;> cases d <;> cases b <;> cases a <;> norm_num [kind,offset,addBit] at ex ey ⊢
                    | inside s t j => cases i <;> cases j <;> cases d <;> cases b <;> cases a <;> norm_num [kind,offset,addBit] at ex ey ⊢

theorem pt_inj (d : Bool) : Function.Injective (pt d) := by
  intro u v eq
  obtain ⟨ux,ux',uy,uy'⟩ := canonical d u
  obtain ⟨vx,vx',vy,vy'⟩ := canonical d v
  have ex := congrArg Prod.fst eq; have ey := congrArg Prod.snd eq
  have cx := unique_axis ux ux' vx vx' ex
  have cy := unique_row uy uy' vy vy' ey
  simp only [pt,cx,cy,Prod.mk.injEq,add_right_inj] at eq
  rw [←rep u,←rep v,cx,cy,kinds u v (Prod.ext eq.1 eq.2)]

theorem apart (d : Bool) {u v a b : Node} (e : edge d u v) (f : edge d a b)
    (t s : ℝ) (t0 : 0<t) (t1 : t<1) (s0 : 0<s) (s1 : s<1)
    (eq : interpolate (pt d u) (pt d v) t=interpolate (pt d a) (pt d b) s) : u=a ∧ v=b := by
  obtain ⟨r,c,k,ok,rfl,rfl⟩ := e; obtain ⟨m,l,j,oj,rfl,rfl⟩ := f
  rw [atCell,atCell] at eq
  obtain ⟨x,y⟩ := Prod.mk.inj eq
  obtain ⟨lx,hx,ly,hy⟩ := inside d k t ok t0 t1; obtain ⟨lu,hu,lv,hv⟩ := inside d j s oj s0 s1
  have ec := unique_axis lx hx lu hu x; have er := unique_row ly hy lv hv y
  subst l; subst m
  have eq := local_apart d k j ok oj t s t0 t1 s0 s1 (Prod.ext (add_left_cancel x) (add_left_cancel y))
  subst j; exact ⟨rfl,rfl⟩

theorem misses (d : Bool) {u v : Node} (e : edge d u v) (z : Node)
    (t : ℝ) (t0 : 0<t) (t1 : t<1) : interpolate (pt d u) (pt d v) t≠pt d z := by
  obtain ⟨r,c,k,ok,rfl,rfl⟩ := e
  intro eq; rw [atCell] at eq
  obtain ⟨x,y⟩ := Prod.mk.inj eq
  obtain ⟨lx,hx,ly,hy⟩ := inside d k t ok t0 t1
  obtain ⟨lu,hu,lv,hv⟩ := canonical d z
  have ec := unique_axis lx hx lu hu x; have er := unique_row ly hy lv hv y
  rw [ec] at x; rw [er] at y
  exact local_miss d k (kind z.1,z.2) ok t t0 t1 (Prod.ext (add_left_cancel x) (add_left_cancel y))

end
end DisjointnessDraft.Applications.SplitGrid
