import DisjointnessDraft.Applications.SplitCore

/-! Every positive-rank arc of the directed finite grid occurs in the split
drawing; the diagonal and the row links have their prescribed endpoints. -/
namespace DisjointnessDraft.Applications.SplitArcs
open OriginalGrid PlanarCore DirectedCore PlanarMatching CoreSize SplitGrid
noncomputable section
def tag (out : Bool) (v : V p) : SplitCore.Chart p :=
  (v.1,v.2,if v.1 then !out else out)

private theorem self (d : Bool) (v : Vertex) : edge d (v,!d) (v,d) := by
  cases v with
  | corner rc => exact ⟨rc.1,rc.2,.b,by simp [usable],rfl,rfl⟩
  | inside r c i =>
    cases i
    · exact ⟨r,c,.v,by simp [usable],rfl,rfl⟩
    · exact ⟨r,c,.w,by simp [usable],rfl,rfl⟩
    · exact ⟨r,c,.x,by simp [usable],rfl,rfl⟩

theorem diagonal (v : V p) : SplitCore.line p (tag true v) (tag false v) := by
  obtain ⟨d,v⟩ := v
  cases d <;> exact self _ _

macro "shape_cell" : tactic => `(tactic| first
  | exact ⟨_,_,.av,by simp [usable],rfl,rfl⟩
  | exact ⟨_,_,.vb,by simp [usable],rfl,rfl⟩
  | exact ⟨_,_,.bw,by simp [usable],rfl,rfl⟩
  | exact ⟨_,_,.wc,by simp [usable],rfl,rfl⟩
  | exact ⟨_,_,.vx,by simp [usable],rfl,rfl⟩
  | exact ⟨_,_,.xw,by simp [usable],rfl,rfl⟩
  | (exfalso; dsimp [level,embed] at *; omega))

private theorem left_cell {p M u k v} (e : OriginalGrid.Step p M u k v) :
    (level false u<level false v → edge false (u,true) (v,false)) ∧
    (level false v<level false u → edge false (v,true) (u,false)) := by
  cases e with
  | cell r c r1 rp c1 cp e =>
    cases e <;> constructor <;> intro h <;> shape_cell

private theorem right_cell {p u k v} (e : OriginalGrid.Step p Zmat u k v) :
    (level true v<level true u → edge true (u,false) (v,true)) ∧
    (level true u<level true v → edge true (v,false) (u,true)) := by
  cases e with
  | cell r c r1 rp c1 cp e =>
    cases e <;> constructor <;> intro h <;> first | contradiction | shape_cell

private theorem shape {p M A u t v} (e : arc p M A u t v) :
    match u,v with
    | .left a,.left b => edge false (a,true) (b,false)
    | .right a,.right b => edge true (a,false) (b,true)
    | .left a,.right b => ∃j,A j ∧ a=side p j ∧ b=side p j
    | _,_ => False := by
  obtain ⟨h,inc⟩ := e
  cases h with
  | l h => exact h.elim (fun k => (left_cell k).1 inc) (fun k => (left_cell k).2 inc)
  | r h =>
    dsimp [rank] at inc
    exact h.elim (fun k => (right_cell k).1 (by omega)) (fun k => (right_cell k).2 (by omega))
  | cross j on => exact ⟨j,on,rfl,rfl⟩

theorem drawing_edges {p : ℕ} {M A} (range : ∀j,A j → 1≤j ∧ j≤(p:ℤ))
    {u v : V p} {k : ℤ} (e : mapped M A u k v) : SplitCore.line p (tag true u) (tag false v) := by
  obtain ⟨a,u⟩ := u
  obtain ⟨b,v⟩ := v
  have h := shape e
  cases a <;> cases b
  · exact h
  · obtain ⟨j,on,lu,rv⟩ := h
    obtain ⟨j1,jp⟩ := range j on
    have jval : ((j-1).toNat:ℤ)=j-1 := Int.toNat_of_nonneg (by omega)
    let i : Fin p := ⟨(j-1).toNat,by omega⟩
    have hv : vertex (.right i)=side (p:ℤ) j := by
      dsimp [vertex,pos,i,side]; rw [jval]; simp
    exact ⟨i,Prod.ext (vertex_injective (lu.trans hv.symm)) rfl,
      Prod.ext (vertex_injective (rv.trans hv.symm)) rfl⟩
  · exact h
  · exact h

theorem top_y (d out : Bool) (q : Fin p) : (SplitCore.point p (tag out (d,.top q))).2=0 := by
  cases d <;> cases out <;> simp [tag,SplitCore.point,SplitCore.mirror,SplitCore.raw,vertex,pt,offset,kind,center,addBit]

end
end DisjointnessDraft.Applications.SplitArcs
