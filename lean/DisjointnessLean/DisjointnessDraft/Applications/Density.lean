import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Fintype.Fin
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.Positivity
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Finset.Card
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-! Vertex-subset accounting in the density gadget. A selector for a candidate
induced subgraph gives three Boolean flags per triangle and one flag per path
vertex. Edge counts include both endpoint attachments. -/
namespace DisjointnessDraft.Applications.Density
open Classical Finset
open scoped BigOperators
set_option maxHeartbeats 900000
noncomputable section
def bit (b : Bool) : ℤ := if b then 1 else 0
def verts : List Bool → ℤ | [] => 0 | h::t => bit h + verts t
def path (l r : Bool) : List Bool → ℤ
  | [] => bit (l && r)
  | h::t => bit (l && h)+path h r t

theorem path_bound (l r : Bool) (s : List Bool) :
    path l r s ≤ verts s + bit (l && r && s.all id) := by
  induction s generalizing l with
  | nil => simp [path,verts]
  | cons h t ih =>
    have H := ih h
    cases l <;> cases r <;> cases h <;> cases e : t.all id <;> simp [path,verts,bit,e] at H ⊢ <;> omega

def Tri := Bool × Bool × Bool
def v₃ (s : Tri) : ℤ := bit s.1+bit s.2.1+bit s.2.2
def e₃ (active : Bool) (s : Tri) : ℤ := if active then bit (s.1 && s.2.1)+bit (s.2.1 && s.2.2)+bit (s.2.2 && s.1) else 0
def inactive (a : Bool) (s : Tri) := bit (!a && s.1)

theorem triangle_bound (a : Bool) (s : Tri) : e₃ a s ≤ v₃ s-inactive a s ∧ 0≤v₃ s := by
  rcases s with ⟨i,j,k⟩; cases i <;> cases j <;> cases k <;> cases a <;> decide

def channel (m l r : Bool) (s : List Bool) := if m then path l r s else bit (l && s.head!) + bit (r && s.getLast!)
def whole (m l r : Bool) (s : List Bool) := m && l && r && s.all id

theorem ends_le (l r : Bool) (h j : Bool) (tail : List Bool) :
    bit (l && h)+bit (r && (h::j::tail).getLast!) ≤ verts (h::j::tail) := by
  have E (b : Bool) (xs : List Bool) : bit (r && (b::xs).getLast!)≤verts (b::xs) := by
    induction xs generalizing b with
    | nil => cases b <;> cases r <;> decide
    | cons x xs ih =>
      have H := ih x
      change _ ≤ bit b + verts (x::xs)
      change bit (r && (x::xs).getLast!) ≤ verts (x::xs) at H
      change bit (r && (x::xs).getLast!) ≤ _
      cases b <;> simp [bit] at * <;> omega
  have H := E j tail
  have e : (h::j::tail).getLast! =(j::tail).getLast! := rfl
  rw [e]; change _ ≤ bit h+verts (j::tail)
  exact add_le_add (by cases l <;> cases h <;> decide) H

theorem channel_bound (m l r : Bool) (s : List Bool) (size : 2≤s.length) :
    channel m l r s ≤ verts s+bit (whole m l r s) := by
  cases m with
  | true => simpa [channel,whole] using path_bound l r s
  | false =>
    cases s with
    | nil => simp at size
    | cons h s =>
      cases s with
      | nil => simp at size
      | cons j s => simpa [channel,whole,bit] using ends_le l r h j s

theorem path_vertices (s : List Bool) : 0≤verts s ∧ (s.all id=true → verts s=(s.length:ℤ)) := by
  induction s with
  | nil => simp [verts]
  | cons h t ih =>
    obtain ⟨pos,eq⟩ := ih
    cases h <;> simp [verts,bit] <;> first | exact pos | (constructor <;> first | omega | (intro H; rw [eq (by simpa using H)]; omega))

structure Subset (n : ℕ) where
  rows : Fin n → Tri
  cols : Fin n → Tri
  paths : Fin n × Fin n → List Bool
  size : ∀ ij,(paths ij).length=6*n

def countV {n} (z : Subset n) : ℤ := (∑ i,v₃ (z.rows i))+(∑ j,v₃ (z.cols j))+(∑ ij,verts (z.paths ij))
def countE {n} (M : Fin n → Fin n → Bool) (X : Fin n → Bool) (q : Fin n) (z : Subset n) : ℤ :=
  (∑ i,e₃ (i=q) (z.rows i)) + (∑ j,e₃ (X j) (z.cols j)) +
    ∑ ij,channel (M ij.1 ij.2) (z.rows ij.1).1 (z.cols ij.2).1 (z.paths ij)
def full {n} (M : Fin n → Fin n → Bool) (z : Subset n) (ij : Fin n × Fin n) :=
  whole (M ij.1 ij.2) (z.rows ij.1).1 (z.cols ij.2).1 (z.paths ij)

theorem absent {n} (hn : 0<n) (M : Fin n → Fin n → Bool) (X : Fin n → Bool) (q : Fin n)
    (nohit : ∀ j,M q j=true → X j=false) (z : Subset n) (positive : 0<countV z) :
    (6*(n:ℤ)+6)*countE M X q z < (6*(n:ℤ)+7)*countV z := by
  let f := fun ij => bit (full M z ij)
  let ar := fun i => inactive (decide (i=q)) (z.rows i)
  let ac := fun j => inactive (X j) (z.cols j)
  let π := ∑ ij,f ij
  let δ := (∑ i,ar i)+(∑ j,ac j)
  have fv ij : 0≤f ij := by dsimp [f,bit]; split <;> decide
  have da i : 0≤ar i := by dsimp [ar,inactive,bit]; split <;> decide
  have db j : 0≤ac j := by dsimp [ac,inactive,bit]; split <;> decide
  have dpos : 0≤δ := add_nonneg (sum_nonneg fun i _ => da i) (sum_nonneg fun j _ => db j)
  have locate (ij : Fin n × Fin n) : f ij ≤ ar ij.1 + ac ij.2 := by
    obtain ⟨i,j⟩ := ij
    by_cases here : full M z (i,j)=true
    · have val : M i j=true ∧ (z.rows i).1=true ∧ (z.cols j).1=true := by
        have h := here
        simp only [full,whole,Bool.and_eq_true,and_assoc] at h
        exact ⟨h.1,h.2.1,h.2.2.1⟩
      obtain ⟨m,r,c⟩ := val
      by_cases eq : i=q
      · subst i
        simp [f,ar,ac,here,inactive,bit,nohit j m,r,c]
      · simp [f,ar,ac,here,inactive,bit,eq,r,c]
        split <;> decide
    · have zero : full M z (i,j)=false := Bool.eq_false_iff.mpr here
      simpa [f,zero,bit] using add_nonneg (da i) (db j)
  have occupy : π≤(n:ℤ)*δ := by
    have b := sum_le_sum (s:=univ) (fun ij _ => locate ij)
    calc π ≤ ∑ ij : Fin n × Fin n, (ar ij.1+ac ij.2) := b
         _ = _ := by simp [Fintype.sum_prod_type,Finset.sum_add_distrib,δ,← Finset.mul_sum]; ring
  have er := sum_le_sum (s:=univ) (fun i _ => (triangle_bound (decide (i=q)) (z.rows i)).1)
  have ec := sum_le_sum (s:=univ) (fun j _ => (triangle_bound (X j) (z.cols j)).1)
  have ep := sum_le_sum (s:=univ) (fun (ij : Fin n × Fin n) _ => channel_bound (M ij.1 ij.2)
    (z.rows ij.1).1 (z.cols ij.2).1 (z.paths ij) (by rw [z.size]; omega))
  have e : countE M X q z≤countV z+π-δ := by
    simp only [Finset.sum_sub_distrib] at ec er
    simp only [Finset.sum_add_distrib] at ep
    dsimp [countE,countV,π,δ,f,ar,ac,full]; linarith only [ec,er,ep]
  have vp (ij) : 6*(n:ℤ)*f ij≤verts (z.paths ij) := by
    cases a : full M z ij with
    | false => simpa [f,a,bit] using (path_vertices (z.paths ij)).1
    | true =>
      have all : (z.paths ij).all id=true := by
        simp only [full,whole,Bool.and_eq_true,and_assoc] at a
        exact a.2.2.2
      rw [(path_vertices _).2 all,z.size]; simp [f,a,bit]
  have floor : 6*(n:ℤ)*π≤countV z := by
    have b := sum_le_sum (s:=univ) (fun ij _ => vp ij)
    rw [←Finset.mul_sum] at b
    have h₁ := sum_nonneg (s:=univ) (fun i _ => (triangle_bound true (z.rows i)).2)
    have h₂ := sum_nonneg (s:=univ) (fun j _ => (triangle_bound true (z.cols j)).2)
    dsimp only [countV,π]; linarith only [h₁,h₂,b]
  have lp : 0<6*(n:ℤ)+6 := by positivity
  by_cases d : δ=0
  · have y : π≤0 := by simpa [d] using occupy
    have ge : countE M X q z≤countV z := by linarith
    nlinarith only [mul_le_mul_of_nonneg_left ge lp.le,positive]
  · nlinarith only [mul_le_mul_of_nonneg_left e lp.le,floor,occupy,lt_of_le_of_ne dpos (Ne.symm d)]

def witness {n} (q x : Fin n) : Subset n where
  rows i := if i=q then (true,true,true) else (false,false,false)
  cols j := if j=x then (true,true,true) else (false,false,false)
  paths ij := List.replicate (6*n) (decide (ij=(q,x)))
  size _ := List.length_replicate

private theorem replicate_verts (b : Bool) (k : ℕ) :
    verts (List.replicate k b) = if b then (k:ℤ) else 0 := by
  induction k with
  | zero => cases b <;> rfl
  | succ k ih => cases b <;> simp [List.replicate_succ,verts,bit] at ih ⊢ <;> omega

private theorem off_path (k : ℕ) (l r : Bool) : path l r (List.replicate (k+1) false)=0 := by
  induction k generalizing l with
  | zero => cases l <;> cases r <;> decide
  | succ k ih => change bit (l && false)+path false r (List.replicate (k+1) false)=0
                 rw [ih false]; cases l <;> decide

private theorem on_path (k : ℕ) : path true true (List.replicate k true)=(k:ℤ)+1 := by
  induction k with
  | zero => decide
  | succ k ih => simp [List.replicate_succ,path,bit,ih]; omega

private theorem off_channel (m l r : Bool) (k : ℕ) (pos : 0<k) :
    channel m l r (List.replicate k false)=0 := by
  cases k with
  | zero => omega
  | succ k =>
    cases m
    · have lz : (List.replicate (k+1) false).getLast! = false := by
        induction k with
        | zero => rfl
        | succ k ih => exact ih (by omega)
      have hz : (List.replicate (k+1) false).head! = false := rfl
      change bit (l && (List.replicate (k+1) false).head!) + bit (r && (List.replicate (k+1) false).getLast!) = 0
      rw [lz,hz]; simp [bit]
    · exact off_path k l r

theorem attained {n} (M : Fin n → Fin n → Bool) (X : Fin n → Bool) (q x : Fin n)
    (edge : M q x=true) (active : X x=true) :
    countV (witness q x)=6*(n:ℤ)+6 ∧ countE M X q (witness q x)=6*(n:ℤ)+7 := by
  classical
  let z := witness q x
  have row i : v₃ (z.rows i) = if i=q then 3 else 0 := by by_cases e : i=q <;> simp [z,witness,v₃,bit,e]
  have col j : v₃ (z.cols j) = if j=x then 3 else 0 := by by_cases e : j=x <;> simp [z,witness,v₃,bit,e]
  have rowe i : e₃ (decide (i=q)) (z.rows i) = if i=q then 3 else 0 := by
    by_cases e : i=q <;> simp [z,witness,e₃,bit,e]
  have cole j : e₃ (X j) (z.cols j) = if j=x then 3 else 0 := by
    by_cases e : j=x
    · subst j; simp [z,witness,e₃,bit,active]
    · cases a : X j <;> simp [z,witness,e₃,bit,e,a]
  have pathv ij : verts (z.paths ij)=if ij=(q,x) then 6*(n:ℤ) else 0 := by
    simp [z,witness,replicate_verts]
  have pathe (ij : Fin n × Fin n) :
      channel (M ij.1 ij.2) (z.rows ij.1).1 (z.cols ij.2).1 (z.paths ij)
        =if ij=(q,x) then 6*(n:ℤ)+1 else 0 := by
    by_cases eq : ij=(q,x)
    · subst ij; simp [z,witness,edge,channel,on_path]
    · have pos : 0<6*n := by have := q.isLt; omega
      simp only [if_neg eq]
      change channel _ _ _ (List.replicate _ (decide (ij=(q,x)))) = 0
      simpa only [decide_eq_false eq] using off_channel (M ij.1 ij.2) (z.rows ij.1).1 (z.cols ij.2).1 (6*n) pos
  change countV z=_ ∧ countE M X q z=_
  simp [countV,countE,row,col,rowe,cole,pathv,pathe]
  constructor <;> ring

theorem density_iff {n} (M : Fin n → Fin n → Bool) (X : Fin n → Bool) (q : Fin n) :
    (∃ z : Subset n, 0<countV z ∧ (6*(n:ℤ)+7)*countV z ≤ (6*(n:ℤ)+6)*countE M X q z)
       ↔ ∃ j,M q j=true ∧ X j=true := by
  constructor
  · rintro ⟨z,hv,h⟩
    by_contra! nohit
    have a : ∀ j,M q j=true → X j=false := by
      intro j hj; cases e : X j <;> simp_all
    have bad := absent (by have := q.isLt; omega) M X q a z hv
    omega
  · rintro ⟨x,m,y⟩
    obtain ⟨v,e⟩ := attained M X q x m y
    refine ⟨witness q x, ?_, ?_⟩
    · rw [v]; positivity
    · rw [v,e]; exact le_of_eq (mul_comm _ _)

end
end DisjointnessDraft.Applications.Density
