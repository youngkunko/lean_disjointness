import DisjointnessDraft.Applications.PlanarMatching
import DisjointnessDraft.Model

/-! A finite literal undirected weighted graph. Its core consists of the two
copies of the displayed grid vertices. Each edge has a fixed orientation for
storage; traversals and distances permit both directions. -/
namespace DisjointnessDraft.Applications.FinitePlanarDistance
open CoreSize OriginalGrid PlanarCore WeightedWalk PlanarMatching Classical
noncomputable section
abbrev V := PlanarMatching.V
abbrev place := @PlanarMatching.place
inductive Wire (p : ℤ) (M : ℤ → ℤ → Bool) (A : ℤ → Prop) : T → ℤ → T → Prop
  | l {u v t} (e : Step p M u t v) : Wire p M A (.left u) t (.left v)
  | r {u v t} (e : Step p Zmat u t v) : Wire p M A (.right u) t (.right v)
  | link (j) (on : A j) : Wire p M A (.left (side p j)) (PlanarCore.link p j) (.right (side p j))
def wire (M : ℤ → ℤ → Bool) (A : ℤ → Prop) (u : V p) (k : ℤ) (v : V p) :=
  Wire p M A (PlanarMatching.place u) k (PlanarMatching.place v)
def edge (M : ℤ → ℤ → Bool) (A : ℤ → Prop) (u : V p) (k : ℤ) (v : V p) :=
  wire M A u k v ∨ wire M A v k u

def start (q : Fin p) : V p := (false,.top q)
def finishLine (q : Fin p) : V p := (true,.top (Fin.rev q))
theorem project {p M A u d v} (w : Path (edge (p:=p) M A) u d v) :
    Walk p M A (PlanarMatching.place u) d (PlanarMatching.place v) := by
  have forward {u v t s d} (h : Wire p M A u t v) (pre : Walk p M A s d u) : Walk p M A s (d+t) v := by
    cases h with
    | l e => exact pre.left (OriginalGrid.one (Or.inl e))
    | r e => exact pre.right (OriginalGrid.one (Or.inl e))
    | link j on => exact pre.cross on
  have backward {u v t s d} (h : Wire p M A v t u) (pre : Walk p M A s d u) : Walk p M A s (d+t) v := by
    cases h with
    | l e => exact pre.left (OriginalGrid.one (Or.inr e))
    | r e => exact pre.right (OriginalGrid.one (Or.inr e))
    | link j on => exact pre.back on
  induction w with
  | nil => exact .nil _
  | snoc _ e ih => exact e.elim (fun s => forward s ih) (fun s => backward s ih)

theorem directed_sub {p M A u k v} (arc : PlanarMatching.mapped (p:=p) M A u k v) : edge M A u k v := by
  have h {a b t} (e : DirectedCore.Physical (p:ℤ) M A a t b) : Wire p M A a t b ∨ Wire p M A b t a := by
    cases e with
    | l e => exact e.elim (fun x => Or.inl (.l x)) (fun x => Or.inr (.l x))
    | r e => exact e.elim (fun x => Or.inl (.r x)) (fun x => Or.inr (.r x))
    | cross j on => exact Or.inl (.link j on)
  exact h arc.1

theorem distance (p : ℕ) (q : Fin p) (M : ℤ → ℤ → Bool) (A : ℤ → Prop) (p2 : 2≤p)
    (range : ∀ j,A j → 1≤j ∧ j≤(p:ℤ)) (dummy : A p) (blank : M p (pos q)=false) :
    let d := 2*H (p:ℤ) - (if ∃ j,A j ∧ M j (pos q)=true then 1 else 0)
    Path (edge M A) (start q) d (finishLine q) ∧ ∀ t,Path (edge M A) (start q) t (finishLine q) → d≤t := by
  intro d
  have q1 : 1≤pos q := by dsimp [pos]; omega
  have qp : pos q≤p := by have := q.isLt; dsimp [pos]; omega
  have ip : 2≤(p:ℤ) := by exact_mod_cast p2
  have rev : pos (Fin.rev q)=(p:ℤ)-pos q+1 := by dsimp [pos,Fin.rev]; have := q.isLt; omega
  have dst : PlanarMatching.place (finishLine q)=.right (top ((p:ℤ)-pos q+1)) := by
    dsimp [finishLine,PlanarMatching.place,UnitCore.layer,vertex,top]; rw [rev]
  have src : PlanarMatching.place (start q)=.left (top (pos q)) := rfl
  have shortest := (PlanarCore.distance p (pos q) M A ip q1 qp range dummy blank).2
  rw [←src,←dst] at shortest
  refine ⟨?_,fun t w => shortest t (project w)⟩
  have path := (DirectedCore.directed_distance p (pos q) M A ip q1 qp range dummy blank).1
  rw [←src,←dst] at path
  obtain ⟨v,eq,walk⟩ := PlanarMatching.lift (start q) range path
  obtain rfl := PlanarMatching.inj eq
  exact walk.mono (fun _ _ _ => directed_sub)

theorem drawn {p M A u w v} (f : wire (p:=p) M A u w v) :
    Planarity.CoreEdge p M A (PlanarMatching.place u) (PlanarMatching.place v) := by
  have h {a b t} (e : Wire (p:ℤ) M A a t b) : Planarity.CoreEdge p M A a b := by
    cases e with
    | l e => exact .left e
    | r e => exact .right e
    | link j on => exact .connect j on
  exact h f

theorem displayed (u : V p) : Planarity.displayed p (PlanarMatching.place u) := by
  rcases u with ⟨s,v⟩
  have bound : (Planarity.point (vertex v)).1≤Planarity.boundary p := by
    cases v with
    | top c => have h := c.isLt; dsimp [Planarity.point,Planarity.coord,Planarity.boundary,vertex,pos]; push_cast; exact_mod_cast (by omega : 4*((c.val:ℤ)+1)≤4*((p:ℤ)+1))
    | right r => simp [Planarity.point,Planarity.coord,Planarity.boundary,vertex]
    | site r c k =>
      have bound : (c:ℤ)+1≤p := by have := c.isLt; omega
      have bc : ((c:ℕ):ℝ)+1≤(p:ℝ) := by exact_mod_cast bound
      cases k <;> dsimp [Planarity.point,Planarity.coord,Planarity.boundary,vertex,pos] <;> push_cast <;> linarith
  cases s <;> exact bound

theorem upper_half (u : V p) : 0≤(Planarity.draw p (PlanarMatching.place u)).2 := by
  rcases u with ⟨s,v⟩
  have bound : 0≤(Planarity.point (vertex v)).2 := by
    cases v with
    | top c => simp [Planarity.point,Planarity.coord,vertex]
    | right r => dsimp [Planarity.point,Planarity.coord,vertex,pos]; positivity
    | site r c k => cases k <;> dsimp [Planarity.point,Planarity.coord,vertex,pos] <;> push_cast <;> linarith [Nat.cast_nonneg (α:=ℝ) r.val]
  cases s <;> exact bound

def localWeight (p : ℤ) : Vertex → Vertex → ℤ
  | .corner (r,_),.inside i j .v => if r=i then 1 else 2*j-1
  | .corner (_,c),.inside _ j .w => if c=j then 2 else 2*p-2
  | _,_ => 1
def wireWeight (p : ℤ) : T → T → ℤ
  | .left a,.left b | .right a,.right b => localWeight p a b
  | .left a,.right _ => match a with | .corner (r,_) => PlanarCore.link p r | _ => 0
  | _,_ => 0

theorem weight_eq {p M A u k v} (e : Wire p M A u k v) : k=wireWeight p u v := by
  have local_eq {N a b t} (ed : Step p N a t b) : t=localWeight p a b := by
    cases ed with
    | cell r c _ _ _ _ ed => cases ed <;> simp [localWeight,embed]
  cases e with
  | l a => exact local_eq a
  | r a => exact local_eq a
  | link j h => rfl

theorem weight_bounds {p : ℕ} {M A u k v} (p2 : 2≤p)
    (rows : ∀ j,A j → 1≤j ∧ j≤(p:ℤ)) (e : Wire p M A u k v) :
    0<k ∧ k≤8*(p:ℤ)*(p+1) := by
  have hp : (2:ℤ)≤p := by exact_mod_cast p2
  have slab : 2*(p:ℤ)≤8*(p:ℤ)*(p+1) := by nlinarith [sq_nonneg (p:ℤ)]
  have step {N u k v} (a : Step (p:ℤ) N u k v) : 0<k ∧ k≤8*(p:ℤ)*(p+1) := by
    cases a with | cell r c r1 rp c1 cp ed => cases ed <;> omega
  cases e with
  | l a => exact step a
  | r a => exact step a
  | link j h =>
    obtain ⟨lo,hi⟩ := rows j h
    have nn := mul_nonneg (by omega : 0≤2*((p:ℤ)+1)) (by omega : 0≤(p:ℤ)-j)
    have top := mul_le_mul_of_nonneg_left (show (p:ℤ)-j≤p by omega) (by omega : 0≤2*((p:ℤ)+1))
    dsimp [PlanarCore.link,H]; constructor <;> nlinarith [sq_nonneg (p:ℤ)]

end
end DisjointnessDraft.Applications.FinitePlanarDistance
