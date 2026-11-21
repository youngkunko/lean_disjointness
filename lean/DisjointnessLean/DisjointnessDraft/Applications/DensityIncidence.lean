import DisjointnessDraft.Applications.DensityHost
import Mathlib.Algebra.BigOperators.Fin

/-! The bills used in the density proof are ordinary induced edge and
vertex counts. Each non-loop unordered pair occurs in at most one host slot. -/
namespace DisjointnessDraft.Applications.DensityIncidence
open DensityHost Density Finset Classical
open scoped BigOperators
noncomputable section
variable {n p : ℕ}

def edgeEquiv (n : ℕ) : Edge n ≃ ((Fin n×Fin 3)⊕((Fin n×Fin 3)⊕((Fin n×Fin n)⊕((Fin n×Fin n)⊕((Fin n×Fin n)×Fin (6*n-1)))))) where
  toFun | .row i a => .inl (i,a) | .col j a => .inr (.inl (j,a))
        | .left i j => .inr (.inr (.inl (i,j))) | .right i j => .inr (.inr (.inr (.inl (i,j))))
        | .middle i j t => .inr (.inr (.inr (.inr ((i,j),t))))
  invFun | .inl (i,a) => .row i a | .inr (.inl (j,a)) => .col j a
         | .inr (.inr (.inl (i,j))) => .left i j | .inr (.inr (.inr (.inl (i,j)))) => .right i j
         | .inr (.inr (.inr (.inr ((i,j),t)))) => .middle i j t
  left_inv v := by cases v <;> rfl
  right_inv v := by rcases v with ⟨i,a⟩|(⟨j,a⟩|(⟨i,j⟩|(⟨i,j⟩|⟨⟨i,j⟩,t⟩))) <;> rfl

theorem verts_ofFn {k : ℕ} (f : Fin k→Bool) : verts (List.ofFn f)=∑i,bit (f i) := by
  induction k with
  | zero => simp [verts]
  | succ k ih => rw [List.ofFn_succ,verts,Fin.sum_univ_succ,ih]

def vertexTotal (z : Choose n p) : ℤ := ∑v,bit (z v)
def contribution (g : Edge n→Bool) (z : Choose n p) (e : Edge n) := bit (g e && z (pair e).1 && z (pair e).2)
def edgeTotal (g : Edge n→Bool) (z : Choose n p) : ℤ := ∑e,contribution g z e

theorem vertex_total (z : Choose n p) : vertexBill z=vertexTotal z := by
  unfold vertexTotal
  rw [←Equiv.sum_comp (hostEquiv n p).symm]
  simp only [Fintype.sum_sum_type,Fintype.sum_prod_type,hostEquiv,Equiv.coe_fn_symm_mk]
  simp [vertexBill,countV,subset,flags,v₃,verts_ofFn,Fin.sum_univ_three,Fintype.sum_prod_type,add_assoc]

private theorem chain {k : ℕ} (g : ℕ→Bool) (last r : Bool) (f : Fin (k+1)→Bool) (t : ℕ) :
    interior g last r t (f 0) (List.ofFn fun i : Fin k => f i.succ)=
      bit (last && f (Fin.last k) && r)+ ∑i : Fin k,bit (g (t+i.val) && f i.castSucc && f i.succ) := by
  induction k generalizing t with
  | zero => simp [DensityHost.interior]
  | succ k ih =>
    rw [List.ofFn_succ,DensityHost.interior,Fin.sum_univ_succ]
    have b := ih (fun i => f i.succ) (t+1)
    simp only [Fin.succ_last,Fin.val_zero,Nat.add_zero,Fin.castSucc_zero] at b ⊢
    rw [b]
    simp [Fin.succ_castSucc,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm,add_left_comm,add_comm,add_assoc]

private theorem expanded (hn : 0<n) (g : Edge n→Bool) (z : Choose n p) (ij : Fin n×Fin n) :
    blockPath (g (.left ij.1 ij.2)) (g (.right ij.1 ij.2)) (internalAt hn g ij.1 ij.2)
      ((subset z).rows ij.1).1 ((subset z).cols ij.2).1 ((subset z).paths ij)=
      contribution g z (.left ij.1 ij.2)+contribution g z (.right ij.1 ij.2)+
      ∑t,contribution g z (.middle ij.1 ij.2 t) := by
  let k := 6*n-1
  have eq : k+1=6*n := by dsimp [k]; omega
  let f := fun t : Fin (k+1) => z (.site ij.1 ij.2 (Fin.cast eq t))
  have paths : (subset z).paths ij=List.ofFn f := by
    apply List.ext_getElem
    · simp [subset,eq]
    · intro j _ _; simp only [subset,List.getElem_ofFn,f]; rfl
  rw [paths,List.ofFn_succ,blockPath,chain]
  simp only [zero_add]
  have first : bit (g (.left ij.1 ij.2) && ((subset z).rows ij.1).1 && f 0)=contribution g z (.left ij.1 ij.2) := rfl
  have last : bit (g (.right ij.1 ij.2) && f (Fin.last k) && ((subset z).cols ij.2).1)=contribution g z (.right ij.1 ij.2) := rfl
  rw [first,last,add_assoc]
  congr 2
  apply sum_congr rfl
  intro t _
  have tlt : t.val<6*n-1 := t.isLt
  simp only [contribution,pair,internalAt,f,Nat.mod_eq_of_lt tlt]; rfl

theorem edge_total (hn : 0<n) (g : Edge n→Bool) (z : Choose n p) : edgeBill hn g z=edgeTotal g z := by
  unfold edgeBill edgeTotal
  simp_rw [expanded hn g z]
  rw [←Equiv.sum_comp (edgeEquiv n).symm]
  simp only [Fintype.sum_sum_type,Fintype.sum_prod_type,edgeEquiv,Equiv.coe_fn_symm_mk,Finset.sum_add_distrib]
  have triR (i : Fin n) : triangle (g ∘ Edge.row i) ((subset z).rows i)=∑a,contribution g z (.row i a) := by
    simp [triangle,subset,flags,contribution,pair,Fin.sum_univ_three]
  have triC (j : Fin n) : triangle (g ∘ Edge.col j) ((subset z).cols j)=∑a,contribution g z (.col j a) := by
    simp [triangle,subset,flags,contribution,pair,Fin.sum_univ_three]
  simp [triR,triC,add_assoc]

theorem selected_vertices (z : Choose n p) :
    vertexBill z=((univ.filter (fun v => z v=true)).card:ℤ) := by
  rw [vertex_total]; simp [vertexTotal,bit,Finset.sum_boole]

theorem selected_edges (hn : 0<n) (g : Edge n→Bool) (z : Choose n p) :
    edgeBill hn g z=((univ.filter (fun e => g e=true ∧ z (pair e).1=true ∧ z (pair e).2=true)).card:ℤ) := by
  rw [edge_total]; simp [edgeTotal,contribution,bit,Finset.sum_boole,and_assoc]

end
end DisjointnessDraft.Applications.DensityIncidence
