import DisjointnessDraft.Applications.AlgebraicCosts
import DisjointnessDraft.Applications.StringCosts
import DisjointnessDraft.Applications.StringAlignment
import DisjointnessDraft.Applications.ShortTransfer

/-! Appendix lower bounds for nonsingular matrices and dynamic strings on
all sufficiently large target sizes, including value-returning variants. -/
namespace DisjointnessDraft.Applications.MatrixStringLower
open Transfer.Compiler ShortTransfer Filter
noncomputable section

open AlgebraicCosts in
theorem matrices (lo hi : ℝ) (lp : 0<lo) (lh : lo≤hi) (K : ℕ) :
    ∃ c : ℝ, 0<c ∧ ∀ᶠ N : ℕ in atTop, ∀ (p : ℕ) [Fact p.Prime], N≤K*p →
      Bound lo hi c N false nonsingular (invSpec (N:=N) (p:=p)) ∧
      Bound lo hi c N false nonsingular (invValue (N:=N) (p:=p)) ∧
      Bound lo hi c N true nonsingular (detSpec (N:=N) (p:=p)) ∧
      Bound lo hi c N true nonsingular (detValue (N:=N) (p:=p)) := by
  obtain ⟨c,cp,low⟩ := ShortTransfer.eventual lo hi lp lh
  obtain ⟨k,hk⟩ := eventually_atTop.mp low
  refine ⟨c,cp,?_⟩
  filter_upwards [matrix_geometry k K] with N params
  intro p _ field
  obtain ⟨big,fit,fp,nN,pow⟩ := params p field
  have low : Realizes lo hi c _ N := @hk _ big N nN pow
  exact ⟨low (invSchedule fit) false (inverse_valid fit fp) (by simp [invSchedule])
      (by simp [invSchedule]) (by simp [invSchedule]),
    low (invValueSchedule fit) false (inverse_value_valid fit fp) (by simp [invValueSchedule,invSchedule])
      (by simp [invValueSchedule,invSchedule]) (by simp [invValueSchedule,invSchedule]),
    low (detSchedule fit) true (determinant_valid fit fp) (by simp [detSchedule])
      (by simp [detSchedule]) (by simp),
    low (detValueSchedule fit) true (determinant_value_valid fit fp) (by simp [detValueSchedule,detSchedule])
      (by simp [detValueSchedule,detSchedule]) (by simp)⟩

open StringCosts StringAlignment in
theorem strings (lo hi : ℝ) (lp : 0<lo) (lh : lo≤hi) :
    ∃ c : ℝ, 0<c ∧ ∀ᶠ N : ℕ in atTop,
      Bound lo hi c N false (dictLegal (n:=stringSize N) N) dictQuery ∧
      Bound lo hi c N false (docLegal (n:=stringSize N) N) docQuery ∧
      Bound lo hi c N false (docOneLegal (n:=stringSize N) N) docOneQuery ∧
      Bound lo hi c N false (legal N) (spec (threshold (stringSize N))) ∧
      Bound lo hi c N false (legal N) distance := by
  obtain ⟨c,cp,low⟩ := ShortTransfer.eventual lo hi lp lh
  obtain ⟨k,hk⟩ := eventually_atTop.mp low
  refine ⟨c,cp,?_⟩
  filter_upwards [string_geometry k] with N params
  obtain ⟨big,one,fit,nN,pow⟩ := params
  let n := stringSize N
  have low : Realizes lo hi c _ N := @hk _ big N nN pow
  have nsq : n≤n*n := Nat.le_mul_of_pos_right n one
  have dict : n*n+2*n+1≤N := by dsimp only [n] at *; omega
  have docs : n*(n+1)+2≤N := by dsimp only [n] at *; rw [Nat.mul_succ]; omega
  exact ⟨low (dictSchedule n) false (dictionary_valid dict) (by simp [dictSchedule])
      (by simp [dictSchedule]) (by simp [dictSchedule]),
    low (docSchedule n) false (documents_valid docs) (by simp [docSchedule])
      (by simp [docSchedule]) (by simp [docSchedule]),
    low (docOneSchedule n) false (documents_one_valid (n:=n) (N:=N) (by omega)) (by simp [docOneSchedule])
      (by simp [docOneSchedule]) (by simp [docOneSchedule]),
    low (schedule n) false (valid fit) (by simp [schedule,edits]) (by simp [schedule]) (by simp [schedule]),
    low (distanceSchedule n) false (distance_valid fit) (by simp [distanceSchedule,edits])
      (by simp [distanceSchedule,schedule]) (by simp [distanceSchedule,schedule])⟩

end
end DisjointnessDraft.Applications.MatrixStringLower
