import DisjointnessDraft.Applications.FinitePlanarDistance

/-! Adding pendant unit edges below an exterior vertex preserves every
old distance. Straight segments to distinct points on the line y = -1
give an explicit drawing on the full padded vertex set. -/
namespace DisjointnessDraft.Applications.PlanarPadding
open Planarity WeightedWalk Classical
noncomputable section
variable {W : Type}

structure Drawing (E : W → W → Prop) where
  point : W → Plane
  injective : Function.Injective point
  miss : ∀ {u v},E u v → ∀ z t,0<t → t<1 → interpolate (point u) (point v) t≠point z
  apart : ∀ {u v a b},E u v → E a b → ∀ t s,0<t → t<1 → 0<s → s<1 →
    interpolate (point u) (point v) t=interpolate (point a) (point b) s → u=a ∧ v=b

theorem Drawing.mono {E G : W → W → Prop} (d : Drawing E) (sub : ∀ a b,G a b → E a b) : Nonempty (Drawing G) :=
  ⟨⟨d.point,d.injective,fun h => d.miss (sub _ _ h),fun h e => d.apart (sub _ _ h) (sub _ _ e)⟩⟩

def extend {W : Type} (E : W → ℤ → W → Prop) (root : W) : W ⊕ Fin pad → ℤ → W ⊕ Fin pad → Prop
  | .inl a,t,.inl b => E a t b
  | .inl a,t,.inr _ => a=root ∧ t=1
  | _,_,_ => False
def plain (E : W → ℤ → W → Prop) (a b : W) := ∃ t,E a t b
def sym (E : W → ℤ → W → Prop) (a : W) (t : ℤ) (b : W) := E a t b ∨ E b t a

def extendPoint (point : W → Plane) (root : W) : W ⊕ Fin pad → Plane
  | .inl u => point u
  | .inr i => ((point root).1+i.val+1,-1)

theorem drawing_at (E : W → ℤ → W → Prop) (root : W) (D : Drawing (plain E))
    (up : ∀v,0≤(D.point v).2) (onLine : (D.point root).2=0) :
    ∃ d : Drawing (plain (extend (pad:=pad) E root)), d.point=extendPoint D.point root := by
  let pt := extendPoint (pad:=pad) D.point root
  have hi {u v : W} {t : ℝ} (t0 : 0<t) (t1 : t<1) : 0≤(interpolate (D.point u) (D.point v) t).2 :=
    add_nonneg (mul_nonneg (by linarith) (up u)) (mul_nonneg t0.le (up v))
  have edgeY (i : Fin pad) (t : ℝ) :
      (interpolate (pt (.inl root)) (pt (.inr i)) t).2= -t := by
    dsimp [pt,extendPoint,interpolate]; rw [onLine]; ring
  have edgeX (i : Fin pad) (t : ℝ) :
      (interpolate (pt (.inl root)) (pt (.inr i)) t).1=(D.point root).1+t*(i.val+1) := by
    dsimp [pt,extendPoint,interpolate]; ring
  refine ⟨⟨pt,?_,?_,?_⟩,rfl⟩
  · rintro (a|i) (b|j) eq
    · exact congrArg Sum.inl (D.injective eq)
    · have e := congrArg Prod.snd eq; change (D.point a).2= -1 at e; linarith [up a]
    · have e := congrArg Prod.snd eq; change -1=(D.point b).2 at e; linarith [up b]
    · have e := congrArg Prod.fst eq; dsimp [pt,extendPoint] at e
      have same : (i.val:ℝ)=j.val := by linarith
      exact congrArg Sum.inr (Fin.ext (by exact_mod_cast same))
  · rintro (u|i) (v|j) ⟨k,e⟩ z t t0 t1 eq
    · cases z with
      | inl a => exact D.miss ⟨k,e⟩ a t t0 t1 eq
      | inr a => have h := congrArg Prod.snd eq
                 change (interpolate (D.point u) (D.point v) t).2= -1 at h
                 linarith [hi (u:=u) (v:=v) t0 t1]
    · obtain ⟨rfl,rfl⟩ := e
      have h := congrArg Prod.snd eq
      rw [edgeY] at h
      cases z with
      | inl v => change -t=(D.point v).2 at h; linarith [up v]
      | inr a => change -t= -1 at h; linarith
    · contradiction
    · contradiction
  · rintro (u|i) (v|j) (a|s) (b|l) ⟨k,e⟩ ⟨m,f⟩ t y t0 t1 y0 y1 eq <;> try contradiction
    · obtain ⟨rfl,rfl⟩ := D.apart ⟨k,e⟩ ⟨m,f⟩ t y t0 t1 y0 y1 eq; exact ⟨rfl,rfl⟩
    · obtain ⟨rfl,rfl⟩ := f
      have h := congrArg Prod.snd eq; rw [edgeY] at h
      change (interpolate (D.point u) (D.point v) t).2= -y at h
      linarith [hi (u:=u) (v:=v) t0 t1]
    · obtain ⟨rfl,rfl⟩ := e
      have h := congrArg Prod.snd eq; rw [edgeY] at h
      change -t=(interpolate (D.point a) (D.point b) y).2 at h
      linarith [hi (u:=a) (v:=b) y0 y1]
    · obtain ⟨rfl,rfl⟩ := e; obtain ⟨rfl,rfl⟩ := f
      have same := congrArg Prod.snd eq; rw [edgeY,edgeY] at same
      have ty : t=y := by linarith
      subst y
      have x := congrArg Prod.fst eq; rw [edgeX,edgeX] at x
      have id : (j.val:ℝ)=l.val := by nlinarith [mul_left_cancel₀ t0.ne' (add_left_cancel x)]
      exact ⟨rfl,congrArg Sum.inr (Fin.ext (by exact_mod_cast id))⟩

theorem drawing (E : W → ℤ → W → Prop) (root : W) (D : Drawing (plain E))
    (up : ∀v,0≤(D.point v).2) (onLine : (D.point root).2=0) :
    Nonempty (Drawing (plain (extend (pad:=pad) E root))) :=
  ⟨(drawing_at E root D up onLine).choose⟩

def erase (root : W) : W ⊕ Fin pad → W | .inl a => a | .inr _ => root
theorem lower_path {E : W → ℤ → W → Prop} {root s} {v : W ⊕ Fin pad} {k}
    (p : Path (sym (extend E root)) (.inl s) k v) :
    ∃ d,d≤k ∧ Path (sym E) s d (erase root v) := by
  induction p with
  | nil => exact ⟨0,le_rfl,.nil _⟩
  | @snoc a b d t _ e ih =>
    obtain ⟨k,le,w⟩ := ih
    cases a <;> cases b <;> rcases e with e|e <;> try contradiction
    · exact ⟨k+t,by omega,w.snoc (Or.inl e)⟩
    · exact ⟨k+t,by omega,w.snoc (Or.inr e)⟩
    · obtain ⟨rfl,rfl⟩ := e; exact ⟨k,by omega,w⟩
    · obtain ⟨rfl,rfl⟩ := e; exact ⟨k,by omega,w⟩
theorem upper_path {E : W → ℤ → W → Prop} (root : W) {s t d} (p : Path (sym E) s d t) :
    Path (sym (extend (pad:=pad) E root)) (.inl s) d (.inl t) := by
  induction p with
  | nil => exact .nil _
  | snoc _ e ih => exact ih.snoc e

end
end DisjointnessDraft.Applications.PlanarPadding
