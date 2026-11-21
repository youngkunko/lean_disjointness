import DisjointnessDraft.Applications.Density
import DisjointnessDraft.Applications.ShortTransfer
import Mathlib.Tactic.DeriveFintype

/-! A simple undirected host with individually insertable triangle edges,
endpoint attachments and consecutive internal path edges. A Boolean assignment
selects an arbitrary subset of its vertices, including the isolated padding. -/
namespace DisjointnessDraft.Applications.DensityHost
open Density Finset Classical
open scoped BigOperators
noncomputable section
variable {n p : ℕ}
inductive Vertex (n p : ℕ) where
  | row (i : Fin n) (a : Fin 3) | col (j : Fin n) (a : Fin 3)
  | site (i j : Fin n) (t : Fin (6*n)) | isolated (t : Fin p)
  deriving Fintype,DecidableEq
inductive Edge (n : ℕ) where
  | row (i : Fin n) (a : Fin 3) | col (j : Fin n) (a : Fin 3)
  | left (i j : Fin n) | right (i j : Fin n) | middle (i j : Fin n) (t : Fin (6*n-1))
  deriving Fintype,DecidableEq

def pair (e : Edge n) : Vertex n p × Vertex n p :=
  match e with
  | .row i a => (.row i a,.row i (a+1))
  | .col j a => (.col j a,.col j (a+1))
  | .left i j => (.row i 0,.site i j ⟨0,by have := i.isLt; omega⟩)
  | .right i j => (.site i j ⟨6*n-1,by have := i.isLt; omega⟩,.col j 0)
  | .middle i j t => (.site i j ⟨t.val,by have := t.isLt; omega⟩,
                        .site i j ⟨t.val+1,by have := t.isLt; omega⟩)

theorem simple (e : Edge n) : (pair (p:=p) e).1≠(pair (p:=p) e).2 := by
  cases e with
  | row i a => simp [pair]
  | col j a => simp [pair]
  | left i j => simp [pair]
  | right i j => simp [pair]
  | middle i j t => simp [pair,Fin.ext_iff]
theorem unique (e e' : Edge n) (h : pair (p:=p) e=pair e' ∨ pair (p:=p) e=(pair e').swap) : e=e' := by
  rcases h with h|h
  · have a := congrArg Prod.fst h
    have b := congrArg Prod.snd h
    cases e <;> cases e' <;> simp [pair] at a b <;> simp_all
    all_goals aesop
  · have a := congrArg Prod.fst h
    have b := congrArg Prod.snd h
    cases e <;> cases e' <;> simp [pair] at a b
    all_goals omega

def hostEquiv (n p : ℕ) : Vertex n p ≃ ((Fin n×Fin 3)⊕((Fin n×Fin 3)⊕((Fin n×Fin n×Fin (6*n))⊕Fin p))) where
  toFun | .row i a => .inl (i,a) | .col j a => .inr (.inl (j,a))
        | .site i j t => .inr (.inr (.inl (i,j,t))) | .isolated a => .inr (.inr (.inr a))
  invFun | .inl (i,a) => .row i a | .inr (.inl (j,a)) => .col j a
         | .inr (.inr (.inl (i,j,t))) => .site i j t | .inr (.inr (.inr a)) => .isolated a
  left_inv v := by cases v <;> rfl
  right_inv v := by rcases v with ⟨i,a⟩|(⟨j,a⟩|(⟨i,j,t⟩|z)) <;> rfl
theorem vertex_count (n p : ℕ) : Fintype.card (Vertex n p)=6*n^3+6*n+p := by
  rw [Fintype.card_congr (hostEquiv n p)]; simp [Fintype.card_sum,Fintype.card_prod]; ring

abbrev Choose (n p : ℕ) := Vertex n p → Bool
def flags (f : Fin 3→Bool) : Tri := (f 0,f 1,f 2)
def subset (z : Choose n p) : Subset n where
  rows i := flags (fun a => z (.row i a))
  cols j := flags (fun a => z (.col j a))
  paths ij := List.ofFn (fun t => z (.site ij.1 ij.2 t))
  size _ := List.length_ofFn
def atFlag (s : Tri) (a : Fin 3) : Bool := ![s.1,s.2.1,s.2.2] a
def lift (s : Subset n) : Choose n p
  | .row i a => atFlag (s.rows i) a | .col j a => atFlag (s.cols j) a
  | .site i j t => (s.paths (i,j)).get ⟨t.val,by rw [s.size]; exact t.isLt⟩
  | .isolated _ => false

theorem recover (s : Subset n) : subset (lift (p:=p) s)=s := by
  cases s with
  | mk rows cols paths lengths =>
    unfold subset
    congr 1
    · funext ij; rcases ij with ⟨i,j⟩
      apply List.ext_getElem
      · exact (List.length_ofFn ..).trans (lengths (i,j)).symm
      · intro t a b; simp [subset,lift]

def vertexBill (z : Choose n p) := countV (subset z)+ ∑i : Fin p, bit (z (.isolated i))
def triangle (active : Fin 3→Bool) (s : Tri) : ℤ :=
  bit (active 0 && s.1 && s.2.1) + bit (active 1 && s.2.1 && s.2.2) + bit (active 2 && s.2.2 && s.1)
theorem constant_triangle (a : Bool) (s : Tri) : triangle (fun _ => a) s=e₃ a s := by
  cases a <;> simp [triangle,e₃,bit]

/-- The current flag tests the edge between the previous vertex and the next
one in the channel. Reaching the end tests the separate right attachment. -/
def interior (edge : ℕ→Bool) (endpoint : Bool) (r : Bool) : ℕ→Bool→List Bool→ℤ
  | _,l,[] => bit (endpoint && l && r)
  | t,l,b::bs => bit (edge t && l && b)+interior edge endpoint r (t+1) b bs

def blockPath (left right : Bool) (edge : ℕ→Bool) (l r : Bool) : List Bool→ℤ
  | [] => 0
  | b::bs => bit (left && l && b)+interior edge right r 0 b bs

theorem constant_block (m l r : Bool) (s : List Bool) (nonempty : s≠[]) :
    blockPath true true (fun _ => m) l r s=channel m l r s := by
  have on (bs : List Bool) (a : Bool) (t : ℕ) : interior (fun _ => true) true r t a bs=path a r bs := by
    induction bs generalizing a t with
    | nil => simp [interior,path]
    | cons b bs ih => simp [interior,path,ih]
  have off (bs : List Bool) (a : Bool) (t : ℕ) : interior (fun _ => false) true r t a bs=bit (r && (a::bs).getLast!) := by
    induction bs generalizing a t with
    | nil => cases a <;> cases r <;> rfl
    | cons b bs ih => simpa [interior,bit] using ih b (t+1)
  obtain ⟨b,bs,rfl⟩ := List.exists_cons_of_ne_nil nonempty
  cases m <;> simp [blockPath,channel,off,on,path]

def internalAt (hn : 0<n) (g : Edge n→Bool) (i j : Fin n) (t : ℕ) :=
  g (.middle i j ⟨t%(6*n-1),Nat.mod_lt _ (by omega)⟩)
def edgeBill (hn : 0<n) (g : Edge n→Bool) (z : Choose n p) : ℤ :=
  (∑i,triangle (g ∘ Edge.row i) ((subset z).rows i))+
  (∑j,triangle (g ∘ Edge.col j) ((subset z).cols j))+
  ∑ij : Fin n×Fin n,blockPath (g (.left ij.1 ij.2)) (g (.right ij.1 ij.2)) (internalAt hn g ij.1 ij.2)
      ((subset z).rows ij.1).1 ((subset z).cols ij.2).1 ((subset z).paths ij)

def hard (M : Fin n→Fin n→Bool) (X : Fin n→Bool) (q : Fin n) : Edge n→Bool
  | .row i _ => decide (i=q) | .col j _ => X j | .middle i j _ => M i j
  | .left _ _ | .right _ _ => true

theorem hard_edges (hn : 0<n) (M : Fin n→Fin n→Bool) (X : Fin n→Bool) (q : Fin n) (z : Choose n p) :
    edgeBill hn (hard M X q) z=countE M X q (subset z) := by
  have positive (ij : Fin n×Fin n) : (subset z).paths ij ≠ [] := by
    intro h; have a := (subset z).size ij; rw [h] at a; simp at a; omega
  simp only [edgeBill,hard,Function.comp_def,hard,internalAt,constant_triangle,countE]
  congr 1; apply sum_congr rfl; intro ij _; exact constant_block _ _ _ _ (positive ij)

def score (hn : 0<n) (g : Edge n→Bool) (z : Choose n p) : ℚ := (edgeBill hn g z:ℚ)/(vertexBill z:ℚ)
def maximum (hn : 0<n) (g : Edge n→Bool) (p : ℕ) : ℚ :=
  univ.sup' univ_nonempty (score (p:=p) hn g)
def threshold (n : ℕ) : ℚ := (6*(n:ℚ)+7)/(6*(n:ℚ)+6)

theorem edge_control (hn : 0<n) (M : Fin n→Fin n→Bool) (X : Fin n→Bool) (q : Fin n) (s : Subset n) :
    countE M X q s≤2*countV s := by
  have tri (a : Bool) (v : Tri) : e₃ a v≤2*v₃ v := by
    obtain ⟨b,c,d⟩ := v; cases a <;> cases b <;> cases c <;> cases d <;> decide
  have bp (ij : Fin n×Fin n) :
      channel (M ij.1 ij.2) (s.rows ij.1).1 (s.cols ij.2).1 (s.paths ij)≤2*verts (s.paths ij) := by
    have v := channel_bound (M ij.1 ij.2) (s.rows ij.1).1 (s.cols ij.2).1 (s.paths ij) (by rw [s.size]; omega)
    have w := path_vertices (s.paths ij)
    cases wh : whole (M ij.1 ij.2) (s.rows ij.1).1 (s.cols ij.2).1 (s.paths ij)
    · rw [wh] at v; change _≤_+0 at v; omega
    · have all : (s.paths ij).all id=true := by
        simp only [whole,Bool.and_eq_true] at wh; exact wh.2
      have k := w.2 all; rw [s.size] at k
      rw [wh] at v; change _≤_+1 at v; omega
  have r := sum_le_sum (s:=univ) (fun i _ => tri (decide (i=q)) (s.rows i))
  have c := sum_le_sum (s:=univ) (fun j _ => tri (X j) (s.cols j))
  have b := sum_le_sum (s:=univ) (fun ij _ => bp ij)
  simp only [←Finset.mul_sum] at r c b
  unfold countE countV; linarith

theorem threshold_iff (hn : 0<n) (M : Fin n→Fin n→Bool) (X : Fin n→Bool) (q : Fin n) :
    threshold n≤maximum hn (hard M X q) p ↔ ∃ j,M q j=true ∧ X j=true := by
  rw [←density_iff M X q,maximum,Finset.le_sup'_iff]
  have den : (0:ℚ)<6*(n:ℚ)+6 := by positivity
  have th : 0<threshold n := by unfold threshold; positivity
  have cp (z : Subset n) : 0≤countV z :=
    add_nonneg (add_nonneg (sum_nonneg fun i _ => (triangle_bound true (z.rows i)).2)
      (sum_nonneg fun j _ => (triangle_bound true (z.cols j)).2)) (sum_nonneg fun ij _ => (path_vertices _).1)
  have addpos (z : Choose n p) : 0≤∑i : Fin p,bit (z (.isolated i)) := sum_nonneg (fun i _ => by cases z (.isolated i) <;> decide)
  constructor
  · rintro ⟨z,_,le⟩
    have nonneg : 0≤vertexBill z := add_nonneg (cp _) (addpos z)
    have pos : 0<vertexBill z := by
      by_contra! nil
      have eq := le_antisymm nil nonneg
      simp [score,eq] at le; linarith
    have v : (0:ℚ)<(vertexBill z:ℚ) := by exact_mod_cast pos
    have e := (div_le_div_iff₀ den v).mp le
    rw [hard_edges] at e
    have base : 0<countV (subset z) := by
      by_contra! bad
      have zero := le_antisymm bad (cp _)
      have ctrl := edge_control hn M X q (subset z)
      rw [zero] at ctrl
      have hw : (countE M X q (subset z):ℚ)≤0 := by exact_mod_cast (by omega : countE M X q (subset z)≤0)
      have bound := mul_nonpos_of_nonpos_of_nonneg hw den.le
      have numerator : (0:ℚ)<(6*(n:ℚ)+7)*(vertexBill z:ℚ) := mul_pos (by positivity) v
      linarith only [e,bound,numerator]
    refine ⟨subset z,base,?_⟩
    have sm : countV (subset z)≤vertexBill z := by unfold vertexBill; linarith [addpos z]
    have ineq : (6*(n:ℚ)+7)*(countV (subset z):ℚ)≤(countE M X q (subset z):ℚ)*(6*(n:ℚ)+6) :=
      (mul_le_mul_of_nonneg_left (by exact_mod_cast sm) (by positivity)).trans e
    exact_mod_cast (by nlinarith only [ineq] : (6*(n:ℚ)+7)*(countV (subset z):ℚ)≤(6*(n:ℚ)+6)*(countE M X q (subset z):ℚ))
  · rintro ⟨s,hv,ok⟩
    refine ⟨lift s,mem_univ _,?_⟩
    have bill : vertexBill (lift (p:=p) s)=countV s := by simp [vertexBill,recover,lift,bit]
    change (6*(n:ℚ)+7)/(6*(n:ℚ)+6)≤(edgeBill hn (hard M X q) (lift s):ℚ)/(vertexBill (lift (p:=p) s):ℚ)
    rw [bill,hard_edges,recover,div_le_div_iff₀ den (by exact_mod_cast hv)]
    have c : (6*(n:ℚ)+7)*(countV s:ℚ)≤(6*(n:ℚ)+6)*(countE M X q s:ℚ) := by exact_mod_cast ok
    linarith

end
end DisjointnessDraft.Applications.DensityHost
