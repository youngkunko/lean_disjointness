import DisjointnessDraft.Applications.GirthPadding
import DisjointnessDraft.Applications.WeightedPlanarLower
import DisjointnessDraft.Applications.UnitEncoding

/-! Weighted, directed planar girth on the complete finite grid, including physical
initialization, connector updates, the return arc, and arbitrarily many directed leaves. -/
namespace DisjointnessDraft.Applications.WeightedGirth
open PlanarEncoding FinitePlanarDistance Planarity UnitEncoding CoreSize OriginalGrid PlanarCore
open GirthTarget GirthOrient GirthPadding PlanarPadding WeightedWalk PlanarMatching ShortTransfer Filter Classical
noncomputable section
abbrev Base (n : ℕ) := FinitePlanarDistance.V (dim n)
def height (v : Base n) : ℚ := DirectedCore.rank (dim n) (PlanarMatching.place v)
def put (x : Fin n) : Base n × Base n := ((false,.right x.castSucc),(true,.right x.castSucc))
def before (f : Family n) (xs : List (Fin n)) := wire (p:=dim n) (table f) (enabled xs)

theorem crossing (x : Fin n) : height (put x).1 < height (put x).2 := by
  unfold height; exact_mod_cast (show DirectedCore.rank (dim n) (PlanarMatching.place (put x).1) <
    DirectedCore.rank (dim n) (PlanarMatching.place (put x).2) by
    have := x.isLt
    dsimp [put,PlanarMatching.place,UnitCore.layer,vertex,DirectedCore.rank,DirectedCore.level,pos,dim]; omega)

theorem terminal_order (q : Fin n) : height (start q.castSucc) < height (finishLine q.castSucc) := by
  unfold height; exact_mod_cast (show DirectedCore.rank (dim n) (PlanarMatching.place (start q.castSucc)) <
    DirectedCore.rank (dim n) (PlanarMatching.place (finishLine q.castSucc)) by
    have := q.isLt; have := (Fin.rev q.castSucc).isLt
    dsimp [start,finishLine,PlanarMatching.place,UnitCore.layer,vertex,DirectedCore.rank,DirectedCore.level,pos,dim] at *; omega)

def storage (hn : 0<n) : Storage n (Base n) where
  stored := before
  potential := plain (potential (dim n))
  strength u v := wireWeight (dim n) (PlanarMatching.place u) (PlanarMatching.place v)
  rank := height
  put := put
  src q := start q.castSucc
  dst q := finishLine q.castSucc
  inside := fun _ _ _ _ _ e => ⟨_,potential_of e⟩
  asymmetric := by
    intro u v e h
    let meshD := coreDrawing (dim n) (sourceDim hn)
    exact no_flip meshD u v ⟨⟨(u,v),e⟩,rfl,rfl⟩ ⟨⟨(v,u),h⟩,rfl,rfl⟩
  canonical := fun _ _ _ _ _ e => weight_eq e
  activity := by
    intro f xs u k v
    have z := connector f xs (.inl u : W n 0) (.inl v) k
    simpa [input,PlanarPadding.extend,ends,put,before,PlanarEncoding.weight,Prod.mk.injEq] using z
  fresh := fun f x h => missing (pad:=0) f x h
  injective := by intro x y h; exact ends_injective (pad:=0) (congrArg (GirthPadding.pair (pad:=0)) h)
  inserted := fun x => (bridge x).property
  forward := crossing
  order := fun q => (terminal_order q).le

theorem zero_row (f : Family n) (q : Fin n) : table f (dim n) (pos q.castSucc)=false := by
  simp only [table,decide_eq_false_iff_not]
  rintro ⟨x,i,e,_,_⟩; have := x.isLt; dsimp [pos,dim] at e; omega

theorem hit (f : Family n) (xs : List (Fin n)) (q : Fin n) :
    (∃j,enabled xs j ∧ table f j (pos q.castSucc)=true) ↔ ∃x∈xs,x∈f q := by
  constructor
  · rintro ⟨j,on,mem⟩
    obtain ⟨x,i,r,c,m⟩ := of_decide_eq_true mem
    have ii : i=q := pos_inj (show pos i=pos q from c)
    rcases on with rfl|⟨y,hy,ey⟩
    · rw [zero_row] at mem; contradiction
    · obtain rfl := pos_inj (r.trans ey.symm); exact ⟨x,hy,ii▸m⟩
  · rintro ⟨x,h,m⟩; exact ⟨pos x,Or.inr ⟨x,h,rfl⟩,decide_eq_true ⟨x,q,rfl,rfl,m⟩⟩

theorem distances (hn : 0<n) (f : Family n) (xs : List (Fin n)) (q : Fin n) :
    let d := PlanarTarget.normal n-(if ∃x∈xs,x∈f q then (1:ℤ) else 0)
    Path (oriented (storage hn) f xs) (start q.castSucc) d (finishLine q.castSucc) ∧
    ∀k,Path (oriented (storage hn) f xs) (start q.castSucc) k (finishLine q.castSucc) → d≤k := by
  intro d
  let p := dim n
  let i : Fin p := q.castSucc
  have q1 : 1≤pos i := by dsimp [pos]; omega
  have qp : pos i≤p := by have := i.isLt; change (q.val:ℤ)+1≤(n:ℤ)+1; have := q.isLt; omega
  have pp : 2≤(p:ℤ) := by exact_mod_cast sourceDim hn
  have rev : pos (Fin.rev i)=(p:ℤ)-pos i+1 := by have hi : i.val<p := i.isLt; change ((p-(i.val+1):ℕ):ℤ)+1=(p:ℤ)-((i.val:ℤ)+1)+1; omega
  have dest : PlanarMatching.place (finishLine i)=.right (top ((p:ℤ)-pos i+1)) := by
    dsimp [finishLine,PlanarMatching.place,UnitCore.layer,vertex,top]; rw [rev]
  have src : PlanarMatching.place (start i)=.left (top (pos i)) := rfl
  have path := (DirectedCore.directed_distance p (pos i) (table f) (enabled xs) pp q1 qp (rows xs) (Or.inl rfl) (zero_row f q)).1
  rw [←src,←dest,hit f xs q] at path
  obtain ⟨v,eq,w⟩ := PlanarMatching.lift (start i) (rows xs) path
  obtain rfl := PlanarMatching.inj eq
  have shortest := (encoded_distance (pad:=0) f xs q).2
  have walk : Path (mapped (table f) (enabled xs)) (start q.castSucc) d (finishLine q.castSucc) := by
    by_cases h : ∃x∈xs,x∈f q <;> simpa [d,i,p,PlanarTarget.normal,h] using w
  refine ⟨walk.mono (fun u k v e => ⟨directed_sub e,by change (↑(DirectedCore.rank _ (PlanarMatching.place u)):ℚ)<↑(DirectedCore.rank _ (PlanarMatching.place v)); exact_mod_cast e.2⟩),?_⟩
  intro k walk
  exact shortest k (upper_path (root n) (walk.mono (fun _ _ _ e => e.1)))

theorem leftmost (hn : 0<n) (v : Base n) : 4≤(draw (dim n) (PlanarMatching.place v)).1 := by
  rcases v with ⟨s,v⟩
  have bounds : 4≤(Planarity.point (vertex v)).1 ∧ (Planarity.point (vertex v)).1≤boundary (dim n) := by
    cases v with
    | top c => have := c.isLt; dsimp [Planarity.point,coord,vertex,boundary,pos,dim] at *; push_cast; constructor <;> exact_mod_cast (by omega)
    | right r => dsimp [Planarity.point,coord,vertex,boundary,pos,dim]; push_cast; constructor <;> linarith [Nat.cast_nonneg (α:=ℝ) n]
    | site r c k =>
      have lo : (0:ℝ)≤c.val := by positivity
      have hi : (c.val:ℝ)+1≤dim n := by exact_mod_cast c.isLt
      cases k <;> dsimp [Planarity.point,coord,vertex,boundary,pos] <;> push_cast <;> constructor <;> linarith
  cases s
  · exact bounds.1
  · change 4≤2*boundary (dim n)+1-(Planarity.point (vertex v)).1
    have nPos : (0:ℝ)<n := by exact_mod_cast hn
    have wall : 4≤boundary (dim n) := by simp [boundary,dim]; linarith only [nPos]
    linarith only [bounds.2,wall]

theorem top_y (q : Fin (dim n)) : (draw (dim n) (PlanarMatching.place (start q))).2=0 ∧
    (draw (dim n) (PlanarMatching.place (finishLine q))).2=0 := by
  simp [start,finishLine,PlanarMatching.place,UnitCore.layer,vertex,draw,reflect,Planarity.point,coord]

def drawing (f : Family n) (xs : List (Fin n)) : Drawing (plain (before f xs)) where
  point v := draw (dim n) (PlanarMatching.place v)
  injective := fun _ _ eq => PlanarMatching.inj (core_vertices (FinitePlanarDistance.displayed _) (FinitePlanarDistance.displayed _) eq)
  miss := fun ⟨_,e⟩ z t a b => core_misses_vertices (drawn e) (FinitePlanarDistance.displayed z) t a b
  apart := fun ⟨_,e⟩ ⟨_,h⟩ t u a b c d eq =>
    let z := core_segments (drawn e) (drawn h) t u a b c d eq
    ⟨PlanarMatching.inj z.1,PlanarMatching.inj z.2⟩

def geometry (hn : 0<n) : Geometry (storage hn) (root n) (PlanarTarget.limit n) (PlanarTarget.normal n) where
  diagram := drawing
  leftmost _ _ v := by change (4:ℝ)≤_; exact leftmost hn v
  above _ _ := upper_half
  top _ _ q := top_y q.castSucc
  distinct _ := fun eq => Bool.noConfusion (congrArg Prod.fst eq)
  weights _ xs _ _ _ e := weight_bounds (sourceDim hn) (rows xs) e
  positive := by dsimp [PlanarTarget.limit,dim]; push_cast; nlinarith [sq_nonneg (n:ℤ)]
  distance := distances hn

theorem lower (lo hi : ℝ) (lp : 0<lo) (lh : lo≤hi) :
    ∃c : ℝ,0<c ∧ ∀ᶠ N : ℕ in atTop,
      let n := stringSize N
      let pad := PlanarTarget.padding N
      Fintype.card (W n pad)=N ∧ Bound lo hi c N true (GirthTarget.legal (V:=W n pad) (PlanarTarget.limit n)) exactSpec ∧
      Bound lo hi c N true (GirthTarget.legal (V:=W n pad) (PlanarTarget.limit n)) (testSpec (PlanarTarget.normal n)) := by
  obtain ⟨c,cp,e⟩ := ShortTransfer.eventual lo hi lp lh
  obtain ⟨k,b⟩ := eventually_atTop.mp e
  refine ⟨c,cp,?_⟩
  filter_upwards [string_geometry (max k 32)] with N g
  let n := stringSize N
  let pad := PlanarTarget.padding N
  have ns : 32≤n := (le_max_right ..).trans g.1
  have hn : 0<n := by omega
  have cap : PlanarTarget.vertexCount n≤N := by
    have fit : 9*(n*n)≤N := g.2.2.1
    dsimp [PlanarTarget.vertexCount,dim]; nlinarith [Nat.mul_le_mul_left n ns]
  have card : Fintype.card (W n pad)=N := by rw [PlanarTarget.vertex_count]; exact Nat.add_sub_of_le cap
  exact ⟨card,GirthTarget.physical _ (certificate _ _ (geometry hn) pad) lo hi c N (b n ((le_max_left ..).trans g.1) N g.2.2.2.1 g.2.2.2.2)⟩

end
end DisjointnessDraft.Applications.WeightedGirth
