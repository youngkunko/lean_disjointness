import Mathlib.LinearAlgebra.Matrix.SchurComplement
import Mathlib.Algebra.Field.ZMod
import Mathlib.Algebra.BigOperators.Group.Finset.Indicator

/-! The two matrix reductions on the concrete (2n+1)-dimensional matrix.
Its inverse and the determinant after the one selector edit are computed over
any field. In the prime field of the reduction neither test wraps around. -/
namespace DisjointnessDraft.Applications.Matrices
open Classical Finset Matrix
open scoped BigOperators
noncomputable section
variable {Q U K : Type} [Fintype Q] [Fintype U] [DecidableEq Q] [DecidableEq U] [Field K]
abbrev Ix (Q U : Type) := (Q ⊕ U) ⊕ Unit

def upper (M : Matrix Q U K) : Matrix (Q ⊕ U) (Q ⊕ U) K := fromBlocks 1 M 0 1
def column (x : U → K) : Matrix (Q ⊕ U) Unit K := fun i _ => i.elim (fun _ => 0) x

def A (M : Matrix Q U K) (x : U → K) : Matrix (Ix Q U) (Ix Q U) K :=
  fromBlocks (upper M) (column x) 0 1

theorem upper_inv (M : Matrix Q U K) : upper (-M)*upper M=1 := by simp [upper,fromBlocks_multiply,fromBlocks_one]

theorem det_A (M : Matrix Q U K) (x : U → K) : (A M x).det=1 := by
  simp [A,upper,Matrix.det_fromBlocks_zero₂₁]

theorem inverse (M : Matrix Q U K) (x : U → K) :
    (A M x)⁻¹ = fromBlocks (upper (-M)) (-(upper (-M)*column x)) 0 1 := by
  apply Matrix.inv_eq_left_inv
  simp [A,fromBlocks_multiply,upper_inv,fromBlocks_one]

theorem inverse_entry (M : Matrix Q U K) (x : U → K) (q : Q) :
    (A M x)⁻¹ (.inl (.inl q)) (.inr ()) = ∑ j,M q j*x j := by
  rw [inverse]
  simp [fromBlocks,Matrix.mul_apply,Fintype.sum_sum_type,upper,column]

def selRow (q : Q) : Matrix Unit (Ix Q U) K := fun _ j => if j=.inl (.inl q) then 1 else 0
def selCol : Matrix (Ix Q U) Unit K := fun i _ => if i=.inr () then 1 else 0

theorem selected_entries {Q U K : Type} [Fintype Q] [Fintype U] [DecidableEq Q] [DecidableEq U] [Field K] (q : Q) (a b : Ix Q U) :
    ((selCol : Matrix (Ix Q U) Unit K)*(selRow q : Matrix Unit (Ix Q U) K)) a b =
      if a=.inr () ∧ b=.inl (.inl q) then 1 else 0 := by
  simp [Matrix.mul_apply,selRow,selCol]; split_ifs <;> simp_all

theorem selected_det (M : Matrix Q U K) (x : U → K) (q : Q) :
    (A M x+selCol*selRow q).det=1+∑ j,M q j*x j := by
  rw [Matrix.det_add_mul _ _ (show IsUnit (A M x).det by rw [det_A]; exact isUnit_one),det_A,one_mul,Matrix.det_unique]
  simp [Matrix.mul_apply,selRow,selCol,Matrix.one_apply,inverse_entry]

def incidence (S : Q → Finset U) : Matrix Q U K := fun q j => if j∈S q then 1 else 0
def flags (X : Finset U) : U → K := fun j => if j∈X then 1 else 0

theorem product {Q U K : Type} [Fintype Q] [Fintype U] [DecidableEq Q] [DecidableEq U] [Field K] (S : Q → Finset U) (X : Finset U) (q : Q) :
    (∑ j,incidence (K:=K) S q j * flags X j)=((S q∩X).card:K) := by
  calc _ = ∑ j : U, if j∈S q∩X then (1:K) else 0 := by
         apply sum_congr rfl; intro j _; by_cases hj : j∈S q <;> by_cases hx : j∈X <;> simp [incidence,flags,hj,hx]
       _ = _ := by
         rw [Finset.sum_ite,Finset.sum_const_zero,add_zero,Finset.sum_const,nsmul_eq_mul,mul_one]
         congr 2; ext; simp

theorem new_entry {Q U K : Type} [Fintype Q] [Fintype U] [DecidableEq Q] [DecidableEq U] [Field K] (S : Q → Finset U) (X : Finset U) (j : U) (a b : Ix Q U) :
    A (incidence (K:=K) S) (flags (insert j X)) a b =
    if a=.inl (.inr j) ∧ b=.inr () then 1 else A (incidence S) (flags X) a b := by
  rcases a with (q|u)|i <;> rcases b with (r|v)|t <;> simp [A,fromBlocks,column,flags]
  split_ifs <;> simp_all

theorem prime_tests {p : ℕ} [Fact p.Prime] (hp : Fintype.card U+1<p)
    (S : Q → Finset U) (X : Finset U) (q : Q) :
    let B := A (incidence (K:=ZMod p) S) (flags X)
    ((B⁻¹ (.inl (.inl q)) (.inr ())=0) ↔ Disjoint (S q) X) ∧
    (((B+selCol*selRow q).det=1) ↔ Disjoint (S q) X) ∧ (B+selCol*selRow q).det≠0 := by
  intro B
  let c := (S q∩X).card
  have small : c+1<p := lt_of_le_of_lt (Nat.succ_le_succ (card_le_univ _)) hp
  have nonwrap (z : ℕ) (hz : z<p) : ((z:ZMod p)=0) ↔ z=0 := by
    rw [ZMod.natCast_zmod_eq_zero_iff_dvd]; exact ⟨fun h => Nat.eq_zero_of_dvd_of_lt h hz,by rintro rfl; exact dvd_zero _⟩
  have zero : ((c:ZMod p)=0) ↔ Disjoint (S q) X := by
    rw [nonwrap c (by omega),Finset.disjoint_iff_inter_eq_empty]; exact Finset.card_eq_zero
  have v : B⁻¹ (.inl (.inl q)) (.inr ())=(c:ZMod p) := (inverse_entry _ _ _).trans (product S X q)
  have d : (B+selCol*selRow q).det=1+(c:ZMod p) := (selected_det _ _ _).trans (congrArg (1+·) (product S X q))
  rw [v,d]
  refine ⟨zero,by simpa using zero,?_⟩
  have h : ((c+1:ℕ):ZMod p)≠0 := fun e => Nat.succ_ne_zero c ((nonwrap _ small).mp e)
  simpa [add_comm] using h

end
end DisjointnessDraft.Applications.Matrices
