import DisjointnessDraft.Applications.SplitGrid
import DisjointnessDraft.Applications.PlanarEncoding

/-! The two split grids occupy disjoint half planes. A horizontal strip joins
facing row terminals, and each possible connector has its own ordinate. -/
namespace DisjointnessDraft.Applications.SplitCore
open OriginalGrid PlanarCore CoreSize Planarity PlanarPadding Classical
noncomputable section
variable {p : ℕ}
abbrev Chart (p : ℕ) := Bool × Menu p × Bool
def wall (p : ℕ) : ℝ := 16*((p:ℝ)+1)+1
def mirror (p : ℕ) (u : Plane) : Plane := (2*wall p+2-u.1,u.2)
def raw (d : Bool) (v : Menu p × Bool) := SplitGrid.pt d (vertex v.1,v.2)
def point (p : ℕ) (v : Chart p) : Plane := if v.1 then mirror p (raw true v.2) else raw false v.2

def line (p : ℕ) (u v : Chart p) : Prop :=
  match u.1,v.1 with
  | false,false => SplitGrid.edge false (vertex u.2.1,u.2.2) (vertex v.2.1,v.2.2)
  | true,true => SplitGrid.edge true (vertex u.2.1,u.2.2) (vertex v.2.1,v.2.2)
  | false,true => ∃ j : Fin p, u.2=(.right j,true) ∧ v.2=(.right j,true)
  | true,false => False

private theorem raw_inj (d : Bool) : Function.Injective (@raw p d) := by
  rintro ⟨u,b⟩ ⟨v,c⟩ e
  obtain ⟨eq,rfl⟩ := Prod.mk.inj ((SplitGrid.pt_inj d) e)
  exact Prod.ext (vertex_injective eq) rfl

theorem box (d : Bool) (v : Menu p×Bool) : (raw d v).1≤wall p ∧ 0≤(raw d v).2 := by
  obtain ⟨m,b⟩ := v
  cases m with
  | top c =>
    have z : (c.val:ℝ)+1≤p := by exact_mod_cast c.isLt
    cases d <;> cases b <;> dsimp [raw,vertex,SplitGrid.pt,SplitGrid.center,SplitGrid.kind,SplitGrid.offset,SplitGrid.addBit,wall,pos] <;> push_cast <;> constructor <;> linarith
  | right r =>
    have z := Nat.cast_nonneg (α:=ℝ) r.val
    cases d <;> cases b <;> dsimp [raw,vertex,SplitGrid.pt,SplitGrid.center,SplitGrid.kind,SplitGrid.offset,SplitGrid.addBit,wall,pos] <;> push_cast <;> constructor <;> linarith
  | site r c k =>
    have cr : (c.val:ℝ)+1≤p := by exact_mod_cast c.isLt
    have rr := Nat.cast_nonneg (α:=ℝ) r.val
    cases d <;> cases k <;> cases b <;> dsimp [raw,vertex,SplitGrid.pt,SplitGrid.center,SplitGrid.kind,SplitGrid.offset,SplitGrid.addBit,wall,pos] <;> push_cast <;> constructor <;> linarith

theorem high (v : Chart p) : 0≤(point p v).2 := by
  obtain ⟨b,v⟩ := v; cases b <;> exact (box _ v).2
private theorem refl_inj : Function.Injective (mirror p) := by
  intro a b h
  have x := congrArg Prod.fst h
  apply Prod.ext
  · dsimp [mirror] at x; linarith
  · have y := congrArg Prod.snd h
    exact y
private theorem map_line (a b : Plane) (s : ℝ) :
    interpolate (mirror p a) (mirror p b) s = mirror p (interpolate a b s) := by
  apply Prod.ext <;> dsimp [mirror,interpolate]
  ring

theorem pt_inj : Function.Injective (point p) := by
  rintro ⟨b,u⟩ ⟨d,v⟩ e
  have l := (box false u).1; have r := (box true v).1
  have l' := (box false v).1; have r' := (box true u).1
  cases b <;> cases d
  · exact congrArg (Prod.mk false) (raw_inj false e)
  · have x := congrArg Prod.fst e; change (raw false u).1=2*wall p+2-(raw true v).1 at x; linarith
  · have x := congrArg Prod.fst e; change 2*wall p+2-(raw true u).1=(raw false v).1 at x; linarith
  · exact congrArg (Prod.mk true) (raw_inj true (refl_inj e))

private theorem mono_slab (d : Bool) (u v : Menu p×Bool) (t : ℝ) (t0 : 0<t) (t1 : t<1) :
    (interpolate (raw d u) (raw d v) t).1≤wall p := by
  have a := mul_le_mul_of_nonneg_left (box d u).1 (show 0≤1-t by linarith)
  have b := mul_le_mul_of_nonneg_left (box d v).1 t0.le
  dsimp [interpolate]; nlinarith only [a,b]

theorem rod (j : Fin p) (t : ℝ) : interpolate (point p (false,.right j,true)) (point p (true,.right j,true)) t =
    (wall p+2*t,16*(pos j:ℝ)) := by
  apply Prod.ext <;> dsimp [interpolate,point,mirror,raw,vertex,SplitGrid.pt,SplitGrid.center,SplitGrid.kind,
    SplitGrid.offset,SplitGrid.addBit,wall] <;> push_cast <;> ring

private theorem miss_mono (d : Bool) {u v z : Menu p×Bool}
    (e : SplitGrid.edge d (vertex u.1,u.2) (vertex v.1,v.2)) (t : ℝ) (t0 : 0<t) (t1 : t<1) :
    interpolate (raw d u) (raw d v) t ≠ raw d z :=
  SplitGrid.misses d e _ t t0 t1

private theorem apart_mono (d : Bool) {u v a b : Menu p×Bool}
    (e : SplitGrid.edge d (vertex u.1,u.2) (vertex v.1,v.2))
    (f : SplitGrid.edge d (vertex a.1,a.2) (vertex b.1,b.2)) (t s : ℝ)
    (t0 : 0<t) (t1 : t<1) (s0 : 0<s) (s1 : s<1)
    (eq : interpolate (raw d u) (raw d v) t=interpolate (raw d a) (raw d b) s) : u=a ∧ v=b := by
  obtain ⟨x,y⟩ := SplitGrid.apart d e f t s t0 t1 s0 s1 eq
  obtain ⟨x₁,x₂⟩ := Prod.mk.inj x
  obtain ⟨y₁,y₂⟩ := Prod.mk.inj y
  exact ⟨Prod.ext (vertex_injective x₁) x₂,Prod.ext (vertex_injective y₁) y₂⟩

private theorem miss {a b : Chart p} (e : line p a b) (z : Chart p) (t : ℝ) (t0 : 0<t) (t1 : t<1) :
    interpolate (point p a) (point p b) t≠point p z := by
  rcases a with ⟨s,a⟩; rcases b with ⟨w,b⟩; rcases z with ⟨d,z⟩
  cases s <;> cases w
  · cases d
    · exact miss_mono false e t t0 t1
    · intro eq; have x := congrArg Prod.fst eq
      change (interpolate (raw false a) (raw false b) t).1=2*wall p+2-(raw true z).1 at x
      linarith [mono_slab false a b t t0 t1,(box true z).1]
  · obtain ⟨j,rfl,rfl⟩ := e
    rw [rod]; intro eq
    have x := congrArg Prod.fst eq
    cases d <;> dsimp [point,mirror] at x <;> linarith [(box false z).1,(box true z).1]
  · contradiction
  · change interpolate (mirror p _) (mirror p _) t ≠ _; rw [map_line]
    cases d
    · intro eq; have x := congrArg Prod.fst eq
      change 2*wall p+2-(interpolate (raw true a) (raw true b) t).1=(raw false z).1 at x
      linarith [mono_slab true a b t t0 t1,(box false z).1]
    · exact fun eq => miss_mono true e t t0 t1 (refl_inj eq)

private theorem apart {u v a b : Chart p} (e : line p u v) (f : line p a b) (t s : ℝ)
    (t0 : 0<t) (t1 : t<1) (s0 : 0<s) (s1 : s<1)
    (eq : interpolate (point p u) (point p v) t = interpolate (point p a) (point p b) s) : u=a ∧ v=b := by
  obtain ⟨l,u⟩ := u; obtain ⟨m,v⟩ := v; obtain ⟨j,a⟩ := a; obtain ⟨k,b⟩ := b
  cases l <;> cases m <;> cases j <;> cases k <;> try contradiction
  case false.false.false.false =>
    obtain ⟨rfl,rfl⟩ := apart_mono false e f t s t0 t1 s0 s1 eq; exact ⟨rfl,rfl⟩
  case false.false.false.true =>
    obtain ⟨h,rfl,rfl⟩ := f; rw [rod] at eq; have x := congrArg Prod.fst eq
    change (interpolate (raw false u) (raw false v) t).1=wall p+2*s at x
    linarith [mono_slab false u v t t0 t1]
  case false.true.false.false =>
    obtain ⟨h,rfl,rfl⟩ := e; rw [rod] at eq; have x := congrArg Prod.fst eq
    change wall p+2*t=(interpolate (raw false a) (raw false b) s).1 at x
    linarith [mono_slab false a b s s0 s1]
  case false.false.true.true =>
    change _=interpolate (mirror p _) (mirror p _) s at eq; rw [map_line] at eq
    have x := congrArg Prod.fst eq
    change (interpolate (raw false u) (raw false v) t).1=2*wall p+2-(interpolate (raw true a) (raw true b) s).1 at x
    linarith [mono_slab false u v t t0 t1,mono_slab true a b s s0 s1]
  case true.true.false.false =>
    change interpolate (mirror p _) (mirror p _) t=_ at eq; rw [map_line] at eq
    have x := congrArg Prod.fst eq
    change 2*wall p+2-(interpolate (raw true u) (raw true v) t).1=(interpolate (raw false a) (raw false b) s).1 at x
    linarith [mono_slab false a b s s0 s1,mono_slab true u v t t0 t1]
  case true.true.false.true =>
    obtain ⟨h,rfl,rfl⟩ := f; rw [rod] at eq
    change interpolate (mirror p _) (mirror p _) t=_ at eq; rw [map_line] at eq
    have x := congrArg Prod.fst eq
    change 2*wall p+2-(interpolate (raw true u) (raw true v) t).1=wall p+2*s at x
    linarith [mono_slab true u v t t0 t1]
  case false.true.true.true =>
    obtain ⟨h,rfl,rfl⟩ := e; rw [rod] at eq
    change _=interpolate (mirror p _) (mirror p _) s at eq; rw [map_line] at eq
    have x := congrArg Prod.fst eq
    change wall p+2*t=2*wall p+2-(interpolate (raw true a) (raw true b) s).1 at x
    linarith [mono_slab true a b s s0 s1]
  case false.true.false.true =>
    obtain ⟨i,rfl,rfl⟩ := e; obtain ⟨j,rfl,rfl⟩ := f
    rw [rod,rod] at eq
    have y := congrArg Prod.snd eq; change 16*(pos i:ℝ)=16*(pos j:ℝ) at y
    have h : (pos i:ℝ)=pos j := by linarith
    have same := PlanarEncoding.pos_inj (by exact_mod_cast h)
    subst j; exact ⟨rfl,rfl⟩
  case true.true.true.true =>
    change interpolate (mirror p _) (mirror p _) t=interpolate (mirror p _) (mirror p _) s at eq
    rw [map_line,map_line] at eq
    obtain ⟨rfl,rfl⟩ := apart_mono true e f t s t0 t1 s0 s1 (refl_inj eq)
    exact ⟨rfl,rfl⟩

def drawing (p : ℕ) : Drawing (line p) := ⟨point p,pt_inj,miss,apart⟩

end
end DisjointnessDraft.Applications.SplitCore
