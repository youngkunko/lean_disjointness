import DisjointnessDraft.Transfer.Lower
import Mathlib.Data.Nat.Sqrt

/-! Common physical lower bounds for constant-length application reductions
at every sufficiently large target size. -/
namespace DisjointnessDraft.Applications.ShortTransfer
open DisjointnessFoundations Transfer.Compiler MeasureTheory Filter Real
noncomputable section

/-- Both the update/query tradeoff and its minimax consequence, on the actual
physical target. All allowed word sizes, coin laws and target machines are
quantified here. -/
def Bound (lo hi c : ℝ) (N : ℕ) (sel : Bool) {F U Q A : Type}
    (legal : F → List (Instr U Q) → Prop) (spec : F → List (Instr U Q) → Q → A) :=
  ∀ (w tu : ℕ) (tq : ℝ), 1≤tu → 1≤tq → lo*logb 2 N≤w → (w:ℝ)≤hi*logb 2 N →
    ∀ (Ω : Type) [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
      (D : Target F U Q A w Ω), Guarantees μ D legal spec tu tq →
      c*(Tradeoff.ratio N w tu)^2≤Transfer.charge sel tu tq ∧
      c*(FixedFamilySizes.logRatio N)^2≤max (tu:ℝ) tq

def Realizes (lo hi c : ℝ) (n N : ℕ) :=
  ∀ {F U Q A : Type} (S : Schedule n F U Q A)
    {legal : F → List (Instr U Q) → Prop} {spec : F → List (Instr U Q) → Q → A}
    (sel : Bool), Valid S legal spec →
    (∀x,(S.insert x).length≤8) → (∀q,(S.finish q).length≤8) →
    (∀q u,.inl u∈S.finish q → sel=true) → Bound lo hi c N sel legal spec

theorem eventual (lo hi : ℝ) (lp : 0<lo) (lh : lo≤hi) :
    ∃c : ℝ, 0<c ∧ ∀ᶠ n : ℕ in atTop, ∀ N, n≤N → N≤n^3 → Realizes lo hi c n N := by
  obtain ⟨c,cp,large⟩ := Transfer.Compiler.lower lo hi lp lh 8 8 3 (by norm_num)
  refine ⟨c,cp,?_⟩
  filter_upwards [large,eventually_ge_atTop 1] with n good h
  intro N nN dist F U Q A S legal spec sel valid up fit gate w tu tq tu1 tq1 wl wh Ω _ μ _ D gu
  have hn : (0:ℝ)<N := by exact_mod_cast (by omega : 0<N)
  have le := logb_le_logb_of_le (b:=2) (by norm_num) hn (by exact_mod_cast dist : (N:ℝ)≤(n:ℝ)^3)
  rw [logb_pow] at le
  exact good N w tu nN (by simpa using le) tu1 wl wh F U Q A Ω μ S D legal spec sel tq tq1 gu valid up fit gate

/-- The largest source fitting the length-nine quadratic string encoding. -/
def stringSize (N : ℕ) := (N/9).sqrt

theorem string_geometry (k : ℕ) : ∀ᶠ N : ℕ in atTop, k≤stringSize N ∧ 1≤stringSize N ∧
    9*(stringSize N*stringSize N)≤N ∧ stringSize N≤N ∧ N≤stringSize N^3 := by
  let b := max k 40
  filter_upwards [eventually_ge_atTop (9*(b*b):ℕ)] with N hN
  let n := stringSize N
  have h : b≤n := Nat.le_sqrt.mpr (by omega)
  have h40 : 40≤n := (le_max_right ..).trans h
  have kh : k≤n := (le_max_left ..).trans h
  have fits := Nat.sqrt_le (N/9)
  have above := Nat.lt_succ_sqrt (N/9)
  change n*n≤N/9 at fits
  change N/9<(n+1)*(n+1) at above
  have fit : 9*(n*n)≤N := by omega
  have prev : N<9*((n+1)*(n+1)) := by omega
  have small : (n+1)*(n+1)≤4*(n*n) := by nlinarith [Nat.mul_le_mul_left n (by omega : 1≤n)]
  have cube : 36*(n*n)≤n^3 := by
    simpa [pow_succ,Nat.mul_assoc,Nat.mul_comm,Nat.mul_left_comm] using Nat.mul_le_mul_right (n*n) (by omega : 36≤n)
  exact ⟨kh,by omega,fit,(Nat.sqrt_le_self (N/9)).trans (Nat.div_le_self ..),by change N≤n^3; omega⟩

/-- The largest dimension satisfying both manuscript matrix constraints. -/
def fieldSize (N p : ℕ) := min ((N-1)/2) (p-2)

theorem matrix_geometry (k K : ℕ) : ∀ᶠ N : ℕ in atTop, ∀p : ℕ, N≤K*p →
    k≤fieldSize N p ∧ 2*fieldSize N p+1≤N ∧ fieldSize N p+1<p ∧
    fieldSize N p≤N ∧ N≤fieldSize N p^3 := by
  let b := max k (K+4)
  filter_upwards [eventually_ge_atTop ((2*b+3)*(K+2):ℕ)] with N big p hp
  have left : 2*b+3≤N := (Nat.le_mul_of_pos_right _ (by omega : 0<K+2)).trans big
  have right : b+2≤p := by
    by_contra! contra
    have bad := Nat.mul_le_mul_left K (by omega : p≤b+1)
    nlinarith [hp,big]
  let n := fieldSize N p
  have bn : b≤n := le_min (by omega) (by omega)
  have nk : k≤n := (le_max_left ..).trans bn
  have large : K+4≤n := (le_max_right ..).trans bn
  have na : n≤(N-1)/2 := min_le_left ..
  have nb : n≤p-2 := min_le_right ..
  have nbounds : 2*n+1≤N ∧ n+1<p := by omega
  have cube : n*n≤n^3 := by
    simpa [pow_succ,Nat.mul_assoc] using Nat.le_mul_of_pos_right (n*n) (by omega : 0<n)
  have Nsq : N≤n*n := by
    by_cases c : (N-1)/2≤p-2
    · have a : n=(N-1)/2 := min_eq_left c
      nlinarith [show N≤2*n+2 by omega,Nat.mul_le_mul_right n (show 4≤n by omega)]
    · have a : n=p-2 := min_eq_right (by omega)
      have eq : p=n+2 := by omega
      rw [eq] at hp
      nlinarith [Nat.mul_le_mul_right (n+2) (show K+2≤n by omega)]
  exact ⟨nk,nbounds.1,nbounds.2,by omega,Nsq.trans cube⟩

end
end DisjointnessDraft.Applications.ShortTransfer
