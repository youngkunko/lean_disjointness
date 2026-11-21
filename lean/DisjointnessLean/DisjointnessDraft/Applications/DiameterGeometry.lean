import DisjointnessDraft.Applications.DiameterGraph

namespace DisjointnessDraft.Applications.DiameterGraph
open PlanarEncoding FinitePlanarDistance CoreSize Planarity WeightedWalk PlanarPadding
open Classical
noncomputable section
variable {n pad : ℕ}

def baseDraw (F : Family n) (xs : List (Fin n)) : Drawing (plain (core F xs)) where
  point u := draw (dim n) (PlanarMatching.place u)
  injective a b eq := PlanarMatching.inj (core_vertices (FinitePlanarDistance.displayed a) (FinitePlanarDistance.displayed b) eq)
  miss := fun ⟨_,e⟩ z t t0 t1 => core_misses_vertices (drawn e) (FinitePlanarDistance.displayed z) t t0 t1
  apart := fun ⟨_,e⟩ ⟨_,f⟩ t s t0 t1 s0 s1 eq =>
    let same := core_segments (drawn e) (drawn f) t s t0 t1 s0 s1 eq
    ⟨PlanarMatching.inj same.1,PlanarMatching.inj same.2⟩

theorem boundary_tip (s : Bool) (q : Fin (dim n)) :
    let pt := draw (dim n) (PlanarMatching.place (visitor s q))
    pt.2=0 ∧ (if s then boundary (dim n)+1/2<pt.1 else pt.1<boundary (dim n)+1/2) := by
  intro pt
  have bound (c : Fin (dim n)) : (c.val:ℝ)+1≤(dim n:ℝ) := by exact_mod_cast c.isLt
  have br : ((dim n-(q.val+1):ℕ):ℝ)+1 ≤ (dim n:ℝ) := bound (Fin.rev q)
  cases s <;> dsimp [pt,visitor,start,finishLine,PlanarMatching.place,UnitCore.layer,vertex,pos,Planarity.point,coord,draw,reflect,boundary] <;>
    push_cast <;> constructor <;> first | rfl | linarith only [bound q,br]

theorem planar (F : Family n) (a : List (Act n)) : Nonempty (Drawing (plain (graph (pad:=pad) F a))) := by
  let D := baseDraw F (links a)
  let m := boundary (dim n)+1/2
  have geom s v k (h : fan a s v k) : (D.point v).2=0 ∧ (if s then m<(D.point v).1 else (D.point v).1<m) := by
    rcases h with ⟨rfl,_⟩|⟨q,_,rfl,_⟩
    · exact boundary_tip s (Fin.last n)
    · exact boundary_tip s q.castSucc
  obtain ⟨d,decl⟩ := FanDrawing.diagram _ (fan a) D m upper_half (fun s v k h => (geom s v k h).1) (fun s v k h => (geom s v k h).2)
  apply PlanarPadding.drawing _ (center false) d
  · rintro (v|s); rw [decl]; change 0≤(D.point v).2+1; exact add_nonneg (upper_half v) (by norm_num)
    rw [decl]; cases s <;> rfl
  · rw [decl]; rfl

theorem core_short (F : Family n) (xs : List (Fin n)) (hn : 1≤n) (u v : Base n) :
    ∃ k,k<span n ∧ Path (sym (core F xs)) u k v := by
  have h : 2≤dim n := by dsimp [dim]; omega
  obtain ⟨k,small,z⟩ := DiameterRoutes.cheap_paths h (table F) (enabled xs) (Or.inl rfl) u v
  exact ⟨k,by dsimp [span,FiniteDiameter.L]; omega,FiniteDiameter.expand h (rows xs) u v z⟩

theorem connected (F : Family n) (a : List (Act n)) (hn : 1≤n) (u v : W n pad) :
    ∃ k,Path (sym (graph F a)) u k v := by
  let D := middle F a
  let r := anchor (n:=n) false
  have lift {u v : Base n} {k} (w : Path (sym (core F (links a))) u k v) :
      Path (sym D) (.inl u) k (.inl v) := by induction w with | nil => exact .nil _ | snoc _ e ih => exact ih.snoc e
  have get (v : Diameter.Node (Base n)) : ∃ k,Path (sym D) (.inl r) k v := by
    cases v with
    | inl v => obtain ⟨k,_,w⟩ := core_short F (links a) hn r v; exact ⟨_,lift w⟩
    | inr s =>
      obtain ⟨k,_,w⟩ := core_short F (links a) hn r (anchor s)
      exact ⟨_,(lift w).snoc (Or.inr (show fan a s (anchor s) (3*span n) from Or.inl ⟨rfl,rfl⟩))⟩
  have all (v : W n pad) : ∃ k,Path (sym (graph F a)) (.inl (.inl r)) k v := by
    cases v with
    | inl v => obtain ⟨k,w⟩ := get v; exact ⟨_,upper_path _ w⟩
    | inr i =>
      obtain ⟨k,w⟩ := get (center false)
      exact ⟨_,(upper_path (center false) w).snoc (Or.inl (show extend D (center false) (.inl (center false)) 1 (.inr i) from ⟨rfl,rfl⟩))⟩
  obtain ⟨i,x⟩ := all u; obtain ⟨j,y⟩ := all v
  exact ⟨_,(PaddedDiameter.symmetry x).append y⟩

theorem bounded (F : Family n) (a : List (Act n)) (hn : 1≤n) {u v : W n pad} {k} (h : graph F a u k v) :
    0<k ∧ k≤3*span n := by
  have p : (2:ℤ)≤dim n := by dsimp [dim]; omega
  have P : 1≤span n := by
    have c : (1:ℤ)≤(dim n:ℤ)^3 := one_le_pow₀ (by omega)
    dsimp [span,FiniteDiameter.L]; omega
  rcases u with (u|s)|i <;> rcases v with (v|t)|j <;> try contradiction
  · have H := weight_bounds (show 2≤dim n by dsimp [dim]; omega) (rows (links a)) h
    have z := mul_nonneg (show 0≤(dim n:ℤ)-2 by omega) (sq_nonneg (dim n:ℤ))
    refine ⟨H.1,H.2.trans ?_⟩; unfold span FiniteDiameter.L; nlinarith only [z,p,sq_nonneg (dim n:ℤ)]
  · obtain ⟨_,rfl⟩ := h; omega
  · rcases h with ⟨_,rfl⟩|⟨_,_,_,rfl⟩ <;> omega
  · obtain ⟨_,rfl⟩ := h; omega

def full (xs : List (Fin n)) (q : Fin n) := xs.map Act.attach ++ [Act.select false q,Act.select true q]
theorem links_full (xs : List (Fin n)) (q : Fin n) : links (full xs q)=xs := by
  simp [links,full,List.filterMap_append,List.filterMap_map,Function.comp_def]

theorem fan_full (xs : List (Fin n)) (q : Fin n) (s : Bool) (v : Base n) (k : ℤ) :
    fan (full xs q) s v k ↔ (bulk s v ∧ k=3*span n) ∨ (v=visitor s q.castSucc ∧ k=span n) := by
  cases s <;> simp [fan,full]

theorem edge_full (F : Family n) (xs : List (Fin n)) (q : Fin n) :
    sym (middle F (full xs q)) =
      Diameter.Edge (sym (core F xs)) bulk (start q.castSucc) (finishLine q.castSucc) (span n) := by
  funext u k v; apply propext
  constructor
  · rintro (e|e)
    all_goals rcases u with u|s <;> rcases v with v|t <;> try contradiction
    · apply Diameter.Edge.base; apply Or.inl; simpa [middle,FanDrawing.wire,links_full] using e
    · rcases (fan_full xs q s v k).mp e with ⟨h,rfl⟩|⟨rfl,rfl⟩
      · exact .old _ _ h
      · cases s <;> exact .short _
    · apply Diameter.Edge.base; apply Or.inr; simpa [middle,FanDrawing.wire,links_full] using e
    · rcases (fan_full xs q t u k).mp e with ⟨h,rfl⟩|⟨rfl,rfl⟩
      · exact .oldRev _ _ h
      · cases t
        · exact Diameter.Edge.shortRev (a:=start q.castSucc) (b:=finishLine q.castSucc) false
        · exact Diameter.Edge.shortRev (a:=start q.castSucc) (b:=finishLine q.castSucc) true
  · intro e; cases e with
    | base e => simpa [middle,PlanarPadding.sym,FanDrawing.wire,links_full] using e
    | old s v h => exact Or.inl ((fan_full xs q s v _).mpr (Or.inl ⟨h,rfl⟩))
    | oldRev s v h => exact Or.inr ((fan_full xs q s v _).mpr (Or.inl ⟨h,rfl⟩))
    | short s => apply Or.inl; apply (fan_full xs q _ _ _).mpr; cases s <;> exact Or.inr ⟨rfl,rfl⟩
    | shortRev s => apply Or.inr; apply (fan_full xs q _ _ _).mpr; cases s <;> exact Or.inr ⟨rfl,rfl⟩

def val (f : Family n) (xs : List (Fin n)) (q : Fin n) : ℤ :=
  2*PlanarCore.H (dim n)-(if ∃x∈xs,x∈f q then 1 else 0)

theorem answer_diameter (F : Family n) (xs : List (Fin n)) (q : Fin n) (hn : 1≤n) (pad1 : 0<pad) :
    Diameter.HasDiameter (sym (graph (pad:=pad) F (full xs q))) (2*span n+val F xs q+1) := by
  have eq := PlanarEncoding.encoded_distance (pad:=0) F xs q
  obtain ⟨p,w⟩ := eq
  obtain ⟨l,le,path⟩ := lower_path p
  let d := val F xs q
  have least (k : ℤ) (x : Path (sym (core F xs)) (start q.castSucc) k (finishLine q.castSucc)) : d≤k := w k (upper_path _ x)
  have same : l=d := le_antisymm le (least l path); subst l
  have nonneg u k v (e : sym (core F xs) u k v) : 0≤k := by
    have sz : 2≤dim n := by dsimp [dim]; omega
    rcases e with e|e <;> exact (weight_bounds sz (rows xs) e).1.le
  have result := Diameter.selector_pair (sym (core F xs)) bulk (start q.castSucc) (finishLine q.castSucc) (span n) d nonneg
    (core_short F xs hn) path (PaddedDiameter.symmetry path) least
  rw [←edge_full F xs q] at result
  have dd := path.nonneg nonneg
  have sz : (1:ℤ)≤dim n := by dsimp [dim]; omega
  have ten : (1:ℤ)≤(dim n:ℤ)^3 := one_le_pow₀ sz
  apply PaddedDiameter.pendant _ (center false) (center true) _ pad1 _ result.1.1 result.1.2 result.2
  change 1≤2*(64*(dim n:ℤ)^3)+d; omega

end
end DisjointnessDraft.Applications.DiameterGraph
