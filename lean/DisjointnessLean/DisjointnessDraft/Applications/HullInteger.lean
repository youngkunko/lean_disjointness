import DisjointnessDraft.Applications.HullRounding
import DisjointnessDraft.Applications.HullExposure

/-! The snapped grid is injective on every guard, data point, blocker and
selector. For each pair of labels one can choose a legal configuration exposing
one of them while the other is present. -/
namespace DisjointnessDraft.Applications.HullInteger
open HullConfig HullRounding HullCosts HullExposure Finset ShortTransfer Filter
open Classical
noncomputable section
variable {n : ℕ}

theorem perturbed_injective (f : Label n → Point) (n5 : 5≤n)
    (motion : ∀v i,|f v i-coords n v i|≤1/(Hull.radius n)^2) : Function.Injective f := by
  intro v u eq
  by_contra ne
  let All : Family n := fun _ => univ
  have clash (v u : Label n) (e : f v=f u) (different : v≠u)
      (X : Finset (Fin n)) (T : Finset (Fin (n+1))) (av : v∈present All X T) (au : u∈visible All X T) : False := by
    have h := perturbed_gap n5 _ motion All X T u au v av different
    rw [e] at h; exact lt_irrefl _ h
  have against (p : Label n) (a : Fin (n+1)) (e : f p=f (.sel a)) (d : p≠.sel a)
      (m : p∈present All univ {a}) : False :=
    clash _ _ e d univ {a} m (by simp [visible])
  cases v <;> cases u
  case guard.guard a b c d =>
    exact clash (.guard a b) (.guard c d) eq ne ∅ ∅ (by simp [All,present]) (by simp [All,visible])
  case guard.datum a b c d =>
    exact clash (.guard a b) (.datum c d) eq ne ∅ ∅ (by simp [All,present]) (by simp [All,visible])
  case guard.block a b c =>
    exact clash (.guard a b) (.block c) eq ne univ univ (by simp [All,present]) (by simp [visible])
  case guard.sel a b c =>
    exact against (.guard a b) c eq ne (by simp [All,present])
  case datum.guard a b c d =>
    exact clash (.datum a b) (.guard c d) eq ne ∅ ∅ (by simp [All,present]) (by simp [All,visible])
  case datum.datum a b c d =>
    exact clash (.datum a b) (.datum c d) eq ne ∅ ∅ (by simp [All,present]) (by simp [All,visible])
  case datum.block a b c =>
    exact clash (.datum a b) (.block c) eq ne univ univ (by simp [All,present]) (by simp [visible])
  case datum.sel a b c =>
    exact against (.datum a b) c eq ne (by simp [All,present])
  case block.guard a c d =>
    exact clash (.guard c d) (.block a) eq.symm (Ne.symm ne) univ univ (by simp [All,present]) (by simp [visible])
  case block.datum a c d =>
    exact clash (.datum c d) (.block a) eq.symm (Ne.symm ne) univ univ (by simp [All,present]) (by simp [visible])
  case block.block a c =>
    exact clash (.block a) (.block c) eq ne univ univ (by simp [All,present]) (by simp [visible])
  case block.sel a c =>
    exact clash (.sel c) (.block a) eq.symm (Ne.symm ne) univ univ (by simp [All,present]) (by simp [visible])
  case sel.guard a c d =>
    exact against (.guard c d) a eq.symm (Ne.symm ne) (by simp [All,present])
  case sel.datum a c d =>
    exact against (.datum c d) a eq.symm (Ne.symm ne) (by simp [All,present])
  case sel.block a c =>
    exact clash (.sel a) (.block c) eq ne univ univ (by simp [All,present]) (by simp [visible])
  case sel.sel a c =>
    rcases le_total a c with ac|ca
    · exact clash (.sel c) (.sel a) eq.symm (Ne.symm ne) univ {a,c} (by simp [present]) (by simp [visible,ac])
    · exact clash (.sel a) (.sel c) eq ne univ {a,c} (by simp [present]) (by simp [visible,ca])

theorem snapped_injective (n5 : 5≤n) : Function.Injective (snapped n) :=
  perturbed_injective _ n5 (small_error n5)

theorem integer_injective (n5 : 5≤n) : Function.Injective (realPoint ∘ integer n) := by
  rw [←dilate_snapped (by omega : 0<n)]
  exact (dilation (by omega : 0<n)).injective.comp (snapped_injective n5)

/-- Physical specialization after the rounded finite classification. Rounding,
dilation, word size, injectivity, operation scripts and costs are discharged. -/
theorem lower_of_snapped (lo hi : ℝ) (lp : 0<lo) (lh : lo≤hi)
    (classified : ∀ n : ℕ,5≤n → ∀S X T,classification (snapped n) S X T) :
    ∃c : ℝ,0<c ∧ ∀ᶠ N : ℕ in atTop,Bound lo hi c N true (legal N) spec := by
  apply lower_of_realization lo hi lp lh
  filter_upwards [string_geometry 5] with N p
  let m := stringSize N+stringSize N
  have m5 : 5≤m := by dsimp [m]; omega
  have dim : m≤N := (GeometricCosts.sizes (by omega : 4≤stringSize N) p.2.2.1).2
  exact ⟨integer m,integer_injective m5,fun S X T => integer_classification m5 S X T (classified m m5 S X T),within_limit m5 dim⟩

end
end DisjointnessDraft.Applications.HullInteger
