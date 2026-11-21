import DisjointnessDraft.Applications.DensitySchedule
import Mathlib.Data.Nat.Find

/-! Identity of the target vertex count and the physical all-size bounds for
both forms of the exact densest-subgraph query. -/
namespace DisjointnessDraft.Applications.DensitySchedule
open DensityHost ShortTransfer Transfer.Compiler Filter Real MeasureTheory
noncomputable section

def coreSize (n : ℕ) := 6*n^3+6*n
def sourceSize (N : ℕ) := Nat.findGreatest (fun n => coreSize n≤N) N
def extra (N : ℕ) := N-coreSize (sourceSize N)
theorem fits (N : ℕ) : coreSize (sourceSize N)≤N :=
  Nat.findGreatest_spec (P:=fun n => coreSize n≤N) (Nat.zero_le _) (by simp [coreSize])
theorem cardinality (N : ℕ) : Fintype.card (Vertex (sourceSize N) (extra N))=N := by
  rw [vertex_count]; change coreSize (sourceSize N)+(N-coreSize (sourceSize N))=N
  exact Nat.add_sub_of_le (fits N)
theorem positive (N : ℕ) (bound : 12≤N) : 0<sourceSize N :=
  Nat.le_findGreatest (by omega : 1≤N) (by simpa [coreSize] using bound : coreSize 1≤N)

theorem geometry (k : ℕ) : ∀ᶠ N : ℕ in atTop, k≤sourceSize N ∧ 12≤N ∧ N≤sourceSize N^4 := by
  let b := max k 100
  filter_upwards [eventually_ge_atTop (coreSize b)] with N big
  have bN : b≤N := by dsimp [coreSize] at big; omega
  have bn : b≤sourceSize N := Nat.le_findGreatest bN big
  have b1 : 100≤sourceSize N := (le_max_right ..).trans bn
  have kN : k≤sourceSize N := (le_max_left ..).trans bn
  have fit := fits N
  let n := sourceSize N
  have hfit : 6*n^3+6*n≤N := fit
  have sn : n+1≤N := by change 100≤n at b1; omega
  have bigger : ¬ coreSize (n+1)≤N := Nat.findGreatest_is_greatest (P:=fun r => coreSize r≤N) (Nat.lt_succ_self n) sn
  have hsize : coreSize (n+1)≤100*n^3 := by
    unfold coreSize
    have nn : 100≤n := b1
    nlinarith only [nn,Nat.mul_le_mul_right n nn,Nat.mul_le_mul_right (n^2) nn]
  have pow : 100*n^3≤n^4 := by
    calc 100*n^3 ≤ n*n^3 := Nat.mul_le_mul_right _ b1
         _ = n^4 := by ring
  exact ⟨kN,by omega,by change N≤n^4; omega⟩

theorem lower (lo hi : ℝ) (lp : 0<lo) (lh : lo≤hi) :
    ∃c : ℝ,0<c ∧ ∀ᶠ N : ℕ in atTop, ∀ hn : 0<sourceSize N,
      Fintype.card (Vertex (sourceSize N) (extra N))=N ∧
      Bound lo hi c N true (legal (n:=sourceSize N)) (valueSpec hn (extra N)) ∧
      Bound lo hi c N true (legal (n:=sourceSize N)) (decisionSpec hn (extra N)) := by
  obtain ⟨c,cp,large⟩ := Transfer.Compiler.lower lo hi lp lh 3 4 4 (by norm_num)
  obtain ⟨k,L⟩ := eventually_atTop.mp large
  refine ⟨c,cp,?_⟩
  filter_upwards [geometry k] with N h
  intro hn
  obtain ⟨above,big,pow⟩ := h
  have nN := Nat.findGreatest_le (P:=fun n => coreSize n≤N) N
  have npos : (0:ℝ)<N := by exact_mod_cast (by omega : 0<N)
  have logle := logb_le_logb_of_le (b:=2) (by norm_num) npos (by exact_mod_cast pow : (N:ℝ)≤(sourceSize N:ℝ)^4)
  rw [logb_pow] at logle
  refine ⟨cardinality N,?_,?_⟩
  · intro w tu tq tu1 tq1 wl wh Ω _ μ _ D gu
    let S := plan ℚ (fun a => !(decide (threshold (sourceSize N)≤a))) 0 (sourceSize N)
    exact L _ above N w tu nN (by simpa using logle) tu1 wl wh _ _ _ _ Ω μ S (initialized D (init _)) _ _ true tq tq1
      (init_guarantees μ D _ gu) (value_valid hn (extra N)) (by simp [S,plan,tri]) (by simp [S,plan,tri]) (by simp)
  · intro w tu tq tu1 tq1 wl wh Ω _ μ _ D gu
    let S := plan Bool (!·) false (sourceSize N)
    exact L _ above N w tu nN (by simpa using logle) tu1 wl wh _ _ _ _ Ω μ S (initialized D (init _)) _ _ true tq tq1
      (init_guarantees μ D _ gu) (decision_valid hn (extra N)) (by simp [S,plan,tri]) (by simp [S,plan,tri]) (by simp)

end
end DisjointnessDraft.Applications.DensitySchedule
