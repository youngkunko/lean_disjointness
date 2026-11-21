import DisjointnessDraft.Applications.WeightedMatching
import DisjointnessDraft.Applications.DirectedCore
import DisjointnessDraft.Applications.CoreSize

/-! Exact maximum weight in the finite vertex-splitting reduction on the
directed two-grid core. Every candidate matching is quantified over, including
partial matchings. There are 8p²+4p unsplit vertices. -/
namespace DisjointnessDraft.Applications.PlanarMatching
open OriginalGrid DirectedCore PlanarCore CoreSize WeightedWalk WeightedMatching Classical
noncomputable section
abbrev V (p : ℕ) := Bool × Menu p
def place {p : ℕ} (v : V p) : T := UnitCore.layer v.1 (vertex v.2)

theorem inj {p} : Function.Injective (@place p) := by
  rintro ⟨i,a⟩ ⟨j,b⟩ h
  cases i <;> cases j <;> simp_all [place,UnitCore.layer,vertex_injective.eq_iff]

def mapped {p : ℕ} (M : ℤ → ℤ → Bool) (A : ℤ → Prop) (u : V p) (k : ℤ) (v : V p) :=
  DirectedCore.arc (p:ℤ) M A (place u) k (place v)

private theorem in_menu {p : ℕ} {M A u t v} (range : ∀ j,A j → 1≤j ∧ j≤(p:ℤ)) (a : DirectedCore.arc p M A u t v) :
    ∃ z : V p, place z=v := by
  have pair {B u k v} (e : OriginalGrid.Step (p:ℤ) B u k v) :
      (∃ i : Menu p,vertex i=u) ∧ (∃ i : Menu p,vertex i=v) := by
    cases e with | cell r c r1 rp c1 cp e => exact ⟨local_vertices r1 rp c1 cp _,local_vertices r1 rp c1 cp _⟩
  cases a.1 with
  | l ed => rcases ed with e|e
            · obtain ⟨z,eq⟩ := (pair e).2; exact ⟨(false,z),congrArg T.left eq⟩
            · obtain ⟨z,eq⟩ := (pair e).1; exact ⟨(false,z),congrArg T.left eq⟩
  | r ed => rcases ed with e|e
            · obtain ⟨z,eq⟩ := (pair e).2; exact ⟨(true,z),congrArg T.right eq⟩
            · obtain ⟨z,eq⟩ := (pair e).1; exact ⟨(true,z),congrArg T.right eq⟩
  | cross j aj =>
    have r := range j aj
    have e : ((j-1).toNat:ℤ)=j-1 := Int.toNat_of_nonneg (by omega)
    let i : Fin p := ⟨(j-1).toNat,by omega⟩
    refine ⟨(true,.right i),?_⟩
    dsimp [place,UnitCore.layer,vertex,side,pos,i]; rw [e]; simp

theorem lift {p M A} (s : V p) {d v} (range : ∀ j,A j → 1≤j ∧ j≤(p:ℤ))
    (w : Path (DirectedCore.arc p M A) (place s) d v) :
    ∃ i,place i=v ∧ Path (mapped M A) s d i := by
  induction w with
  | nil => exact ⟨s,rfl,.nil _⟩
  | snoc _ e ih =>
    obtain ⟨u,rfl,pr⟩ := ih
    obtain ⟨b,rfl⟩ := in_menu range e
    exact ⟨b,rfl,pr.snoc e⟩

private theorem proj {p M A u d v} (w : Path (mapped (p:=p) M A) u d v) : Path (DirectedCore.arc p M A) (place u) d (place v) := by
  induction w with | nil => exact .nil _ | snoc _ e ih => exact ih.snoc e

theorem maximum (p : ℕ) (q : Fin p) (M : ℤ → ℤ → Bool) (A : ℤ → Prop) (p2 : 2≤p)
    (range : ∀ j,A j → 1≤j ∧ j≤(p:ℤ)) (dummy : A p) (empty : M p (pos q)=false) :
    let src : V p := (false,.top q)
    let dst : V p := (true,.top (Fin.rev q))
    let edges := mapped M A
    let hit := if ∃ j,A j ∧ M j (pos q)=true then (1:ℤ) else 0
    let K := 2*H p+1
    let result := (8*(p:ℤ)^2+4*p)*K+1+hit
    (∃ m : Matching edges src dst,weight edges K m=result) ∧
    ∀ m : Matching edges src dst,weight edges K m≤result := by
  intro src dst edges hit K result
  have q1 : 1≤pos q := by dsimp [pos]; omega
  have qp : pos q≤p := by have := q.isLt; dsimp [pos]; omega
  have p2' : (2:ℤ)≤p := by exact_mod_cast p2
  have rev : pos (Fin.rev q)=(p:ℤ)-pos q+1 := by dsimp [pos,Fin.rev]; have := q.isLt; omega
  have dsteq : place dst=.right (top ((p:ℤ)-pos q+1)) := by dsimp [dst,place,UnitCore.layer,vertex,top]; rw [rev]
  have srcEq : place src=.left (top (pos q)) := rfl
  obtain ⟨w,min⟩ := directed_distance p (pos q) M A p2' q1 qp range dummy empty
  rw [←srcEq,←dsteq] at w min
  obtain ⟨last,eq,walk⟩ := lift src range w
  obtain rfl := inj eq
  have nnCore {u k v} (edge : DirectedCore.arc (p:ℤ) M A u k v) : 0≤k := by
    have step {B a t b} (h : OriginalGrid.Step (p:ℤ) B a t b) : 0≤t := by
      cases h with | cell _ _ r1 rp c1 cp e => cases e <;> omega
    cases edge.1 with
    | l e => exact e.elim step step
    | r e => exact e.elim step step
    | cross j on =>
      have jj := (range j on).2
      have h := mul_nonneg (show 0≤2*((p:ℤ)+1) by omega) (show 0≤(p:ℤ)-j by omega)
      have h' : 0≤4*(p:ℤ)*(p+1) := by positivity
      dsimp [link,H]; omega
  have nn (u : V p) k (v : V p) (e : edges u k v) : 0≤k := nnCore e
  have all := WeightedMatching.maximum edges (fun v => rank p (place v)) (fun _ _ _ h => h.2) nn walk
    (fun k r => min _ (proj r)) (K:=K) (by dsimp [K]; split <;> omega)
  have card := CoreSize.paired_size p
  have e : ((Fintype.card (V p):ℕ):ℤ)=8*(p:ℤ)^2+4*p := by exact_mod_cast card
  have id : ((Fintype.card (V p):ℤ)+1)*K-(2*H p-hit)=result := by rw [e]; dsimp [K,result]; ring
  exact id ▸ all

end
end DisjointnessDraft.Applications.PlanarMatching
