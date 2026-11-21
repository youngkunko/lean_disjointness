import DisjointnessDraft.Applications.Grid

/-! The six-edge cell before compression. Corner potentials are extended by
local shortest-path envelopes. The upper bound expands every compressed step
to a walk using only the listed edges of the manuscript's original graph. -/
namespace DisjointnessDraft.Applications.OriginalGrid
open Grid
inductive Inner where | v | w | x
inductive Local where | a | b | c | inside (i : Inner)
inductive Vertex where | corner (z : GridPoint) | inside (r c : ℤ) (i : Inner)
def embed (r c : ℤ) : Local → Vertex
  | .a => .corner (r-1,c) | .b => .corner (r,c) | .c => .corner (r,c+1)
  | .inside i => .inside r c i
inductive Edge (p c : ℤ) (m : Bool) : Local → ℤ → Local → Prop
  | av : Edge p c m .a (2*c-1) (.inside .v)
  | bv : Edge p c m .b 1 (.inside .v)
  | bw : Edge p c m .b 2 (.inside .w)
  | cw : Edge p c m .c (2*p-2) (.inside .w)
  | vx : Edge p c m (.inside .v) 1 (.inside .x)
  | xw (present : m=true) : Edge p c m (.inside .x) 1 (.inside .w)
inductive Step (p : ℤ) (M : ℤ → ℤ → Bool) : Vertex → ℤ → Vertex → Prop
  | cell (r c) (r1 : 1≤r) (rp : r≤p) (c1 : 1≤c) (cp : c≤p) {u v t}
      (edge : Edge p c (M r c) u t v) : Step p M (embed r c u) t (embed r c v)
inductive Walk (p : ℤ) (M : ℤ → ℤ → Bool) : Vertex → ℤ → Vertex → Prop
  | nil (u) : Walk p M u 0 u
  | snoc {u v z d t} : Walk p M u d v → (Step p M v t z ∨ Step p M z t v) → Walk p M u (d+t) z

def fromA (p c : ℤ) (m : Bool) : Local → ℤ
  | .a => 0 | .b => 2*c | .c => 2*c+2*p-bit m
  | .inside .v => 2*c-1 | .inside .w => 2*c+2-bit m | .inside .x => 2*c

def fromB (p c : ℤ) : Local → ℤ
  | .a => 2*c | .b => 0 | .c => 2*p
  | .inside .v => 1 | .inside .w => 2 | .inside .x => 2

def fromC (p c : ℤ) (m : Bool) : Local → ℤ
  | .a => 2*c+2*p-bit m | .b => 2*p | .c => 0
  | .inside .v => 2*p+1-bit m | .inside .w => 2*p-2 | .inside .x => if m then 2*p-1 else 2*p+2

def localF (p r c : ℤ) (m : Bool) (f : GridPoint → ℤ) (u : Local) :=
  min (f (r-1,c)+fromA p c m u) (min (f (r,c)+fromB p c u) (f (r,c+1)+fromC p c m u))

private theorem near {a b d : ℤ} : a-b≤d ∧ b-a≤d ↔ a≤b+d ∧ b≤a+d := by omega

private theorem min_near {a b a' b' d : ℤ} (ha : a-a'≤d ∧ a'-a≤d) (hb : b-b'≤d ∧ b'-b≤d) :
    min a b-min a' b'≤d ∧ min a' b'-min a b≤d := by
  simp only [min_def]; split_ifs <;> omega

private theorem local_near {p r c m u t v} (f : GridPoint → ℤ) (hP : 2≤p) (hC : 1≤c)
    (e : Edge p c m u t v) :
    localF p r c m f u-localF p r c m f v≤t ∧ localF p r c m f v-localF p r c m f u≤t := by
  unfold localF
  apply min_near _ (min_near _ _)
  all_goals cases e <;> cases m <;> simp_all [fromA,fromB,fromC,bit] <;> omega

def extend (p : ℤ) (M : ℤ → ℤ → Bool) (F : GridPoint → ℤ) : Vertex → ℤ
  | .corner z => F z | .inside r c i => localF p r c (M r c) F (.inside i)

private theorem consistent {p q j r c} (M : ℤ → ℤ → Bool) (p2 : 2≤p) (q1 : 1≤q) (jp : j≤p)
    (r1 : 1≤r) (rp : r≤p) (c1 : 1≤c) (cp : c≤p) (u : Local) :
    let F := potential p q j (bit (M j q))
    extend p M F (embed r c u)=localF p r c (M r c) F u := by
  intro F
  have v := Grid.lipschitz M p2 q1 jp (.vert r c r1 rp c1 cp)
  have h := Grid.lipschitz M p2 q1 jp (.hor r c r1 rp c1 cp)
  have d := Grid.lipschitz M p2 q1 jp (.diag r c r1 rp c1 cp)
  change F (r,c)-F (r-1,c)≤_ ∧ F (r-1,c)-F (r,c)≤_ at v
  change F (r,c+1)-F (r,c)≤_ ∧ F (r,c)-F (r,c+1)≤_ at h
  change F (r,c+1)-F (r-1,c)≤_ ∧ F (r-1,c)-F (r,c+1)≤_ at d
  cases u <;> try rfl
  all_goals simp only [embed,extend,localF,fromA,fromB,fromC,add_zero,min_def]
  all_goals split_ifs <;> omega

theorem bound {p q j u d v} (M : ℤ → ℤ → Bool) (p2 : 2≤p) (q1 : 1≤q) (jp : j≤p)
    (path : Walk p M u d v) :
    let F := extend p M (potential p q j (bit (M j q)))
    F v-F u≤d := by
  let F := potential p q j (bit (M j q))
  have lip {a t b} (e : Step p M a t b) :
      extend p M F a-extend p M F b≤t ∧ extend p M F b-extend p M F a≤t := by
    cases e with
    | cell r c r1 rp c1 cp e =>
      rw [consistent M p2 q1 jp r1 rp c1 cp _,consistent M p2 q1 jp r1 rp c1 cp _]
      exact local_near F p2 c1 e
  change extend p M F v-extend p M F u≤d
  induction path with
  | nil => simp
  | snoc _ e ih => rcases e with e|e <;> have h := lip e <;> omega

theorem Walk.append {p M u d v t z} (a : Walk p M u d v) (b : Walk p M v t z) : Walk p M u (d+t) z := by
  induction b with
  | nil => simpa using a
  | snoc _ e ih => simpa only [add_assoc] using ih.snoc e

theorem one {p M u t v} (e : Step p M u t v ∨ Step p M v t u) : Walk p M u t v := by
  simpa using (Walk.nil u).snoc e

theorem Walk.reverse {p M u d v} (a : Walk p M u d v) : Walk p M v d u := by
  induction a with
  | nil => exact .nil _
  | snoc _ e ih => simpa only [add_comm] using (one e.symm).append ih

theorem expand_step {p M u t v} (e : Grid.Step p M u t v) :
    Walk p M (.corner u) t (.corner v) := by
  cases e with
  | vert r c r1 rp c1 cp =>
    let edge := @Step.cell p M r c r1 rp c1 cp
    have a := one (Or.inl (edge .av))
    have b := a.snoc (Or.inr (edge .bv))
    (convert b using 1; dsimp [embed]; ring)
  | hor r c r1 rp c1 cp =>
    let edge := @Step.cell p M r c r1 rp c1 cp
    have a := one (Or.inl (edge .bw))
    have b := a.snoc (Or.inr (edge .cw))
    (convert b using 1; dsimp [embed]; ring)
  | diag r c r1 rp c1 cp =>
    let edge := @Step.cell p M r c r1 rp c1 cp
    have a := one (Or.inl (edge .av))
    cases m : M r c with
    | false =>
      have b := ((a.snoc (Or.inr (edge .bv))).snoc (Or.inl (edge .bw))).snoc (Or.inr (edge .cw))
      (convert b using 1; dsimp [embed,bit]; ring)
    | true =>
      have b := ((a.snoc (Or.inl (edge .vx))).snoc (Or.inl (edge (.xw m)))).snoc (Or.inr (edge .cw))
      (convert b using 1; dsimp [embed,bit]; ring)

theorem expand_walk {p M u d v} (w : Grid.Walk p M u d v) : Walk p M (.corner u) d (.corner v) := by
  induction w with
  | nil => exact .nil _
  | snoc _ e ih =>
    rcases e with e|e
    · exact ih.append (expand_step e)
    · exact ih.append (expand_step e).reverse

theorem grid_distance (p q j : ℤ) (M : ℤ → ℤ → Bool) (p2 : 2≤p) (q1 : 1≤q) (qp : q≤p) (j1 : 1≤j) (jp : j≤p) :
    let d := 2*p*(p-q+1)+2*q*j-bit (M j q)
    Walk p M (.corner (0,q)) d (.corner (j,p+1)) ∧ ∀ e,Walk p M (.corner (0,q)) e (.corner (j,p+1)) → d≤e := by
  intro d
  refine ⟨expand_walk (Grid.grid_distance p q j M p2 q1 qp j1 jp).1,?_⟩
  intro e path
  have h := bound (q:=q) (j:=j) M p2 q1 jp path
  dsimp [extend,potential,eta] at h
  rw [min_eq_right (by omega : q≤p+1),min_self,max_eq_left (by omega : 0≤j-0)] at h
  simp [show ¬j<j by omega,show q<p+1 by omega,show (0:ℤ)<j by omega] at h
  dsimp [d]; linarith
end DisjointnessDraft.Applications.OriginalGrid
