import DisjointnessDraft.Information.Leakage

/-! Average conditional min-entropy via the optimal guessing probability of a
finite joint-mass table. Tables need no division by a zero-mass observation. -/
namespace DisjointnessDraft.Information.MinEntropy
open Finset Real
open scoped BigOperators
open Classical
noncomputable section
variable {X Y Z : Type*} [Fintype X] [Nonempty X] [Fintype Y] [Fintype Z]

def best (p : X→ℝ) := p (guessAtom p)
def guess (p : Y→X→ℝ) := ∑y,best (p y)
def bits (p : ℝ) := -log p / log 2
def average (p : Y→X→ℝ) := bits (guess p)

theorem best_mono {p q : X→ℝ} (h : ∀x,p x≤q x) : best p ≤ best q :=
  (h _).trans (guess_max q _)

theorem best_scale (p : X→ℝ) {r : ℝ} (hr : 0≤r) :
    best (fun x => r*p x)=r*best p := by
  apply le_antisymm
  · exact mul_le_mul_of_nonneg_left (guess_max p _) hr
  · exact guess_max (fun x => r*p x) (guessAtom p)

theorem guess_pos (p : Y→X→ℝ) (nn : ∀y x,0≤p y x) (total : ∑y,∑x,p y x=1) :
    0<guess p := by
  have someAtom : ∃ y x, 0<p y x := by
    by_contra! no
    have all y x := le_antisymm (no y x) (nn y x)
    simp [all] at total
  obtain ⟨y,x,px⟩ := someAtom
  exact (px.trans_le (guess_max (p y) x)).trans_le
    (single_le_sum (f:=fun j => best (p j)) (fun j _ => nn j _) (mem_univ y))

theorem entropy_bound {u v r : ℝ} (up : 0<u) (vp : 0<v) (rp : 0<r) (h : u≤r*v) :
    bits v - log r / log 2 ≤ bits u := by
  have le := log_le_log up h
  rw [log_mul rp.ne' vp.ne'] at le
  unfold bits
  rw [←sub_div]
  exact (div_le_div_iff_of_pos_right (log_pos (by norm_num))).mpr (by linarith)

/-- Revealing an extra observation can multiply guessing probability by at
most the number of its possible values (Fact on average min-entropy, part a). -/
theorem reveal (p : Z→Y→X→ℝ) (nn : ∀z y x,0≤p z y x) :
    (∑z,guess (p z)) ≤ Fintype.card Z * guess (fun y x => ∑z,p z y x) := by
  calc _ ≤ ∑_z : Z,guess (fun y x => ∑z,p z y x) := by
          apply sum_le_sum; intro z _
          apply sum_le_sum; intro y _
          exact best_mono fun x => single_le_sum (fun t _ => nn t y x) (mem_univ z)
       _ = _ := by simp

/-- Any deterministic coarsening of the observed variable can only decrease
its guessing probability (part c). -/
theorem coarsen (p : Y→X→ℝ) (f : Y→Z) :
    guess (fun z x => ∑y with f y=z,p y x) ≤ guess p := by
  let coarse := fun (z : Z) (x : X) => ∑y with f y=z,p y x
  calc guess coarse ≤ ∑z,∑y with f y=z,best (p y) := by
         apply sum_le_sum; intro z _
         unfold best; dsimp [coarse]
         apply sum_le_sum; intro y _
         exact guess_max (p y) _
       _ = _ := by simp [sum_filter,Finset.sum_comm,guess]

/-- A subevent of probability mass costs at most log₂(1/mass) in average
conditional min-entropy. The table s consists of the joint masses on E. -/
theorem event (p s : Y→X→ℝ) (mass : ℝ) (massPos : 0<mass) (inc : ∀y x,s y x≤p y x) :
    guess (fun y x => s y x/mass) ≤ mass⁻¹*guess p := by
  calc _ = mass⁻¹*guess s := by
         unfold guess; rw [mul_sum]; apply sum_congr rfl; intro y _
         simpa only [div_eq_inv_mul] using best_scale (s y) (inv_nonneg.mpr massPos.le)
       _ ≤ _ := mul_le_mul_of_nonneg_left (sum_le_sum fun y _ => best_mono (inc y)) (inv_nonneg.mpr massPos.le)

/-- At most a 1/R fraction of observations have posterior guessing chance
above R times the average. Setting R=2^r gives part (b) in bits. -/
theorem tail (m : Y→ℝ) (b : Y→ℝ) (nn : ∀y,0≤m y) (bn : ∀y,0≤b y)
    (norm : ∑y,m y=1) (positive : 0<∑y,m y*b y) (R : ℝ) (rp : 0<R) :
    let g := ∑y,m y*b y
    1-1/R ≤ ∑y with b y≤R*g,m y := by
  intro g
  let E := univ.filter fun y => b y≤R*g
  have h : (∑y∈Eᶜ,m y)*(R*g) ≤ ∑y∈Eᶜ,m y*b y := by
    rw [sum_mul]; apply sum_le_sum; intro y hy
    exact mul_le_mul_of_nonneg_left (le_of_lt (by simpa [E] using hy)) (nn y)
  have sub : (∑y∈Eᶜ,m y*b y) ≤ g := sum_le_sum_of_subset_of_nonneg (subset_univ _) (fun y _ _ => mul_nonneg (nn y) (bn y))
  have prob : (∑y∈Eᶜ,m y)≤1/R := by
    apply (le_div_iff₀ rp).mpr
    apply (mul_le_mul_right positive).mp
    simpa [mul_assoc,g] using h.trans sub
  have total := (sum_add_sum_compl E m).trans norm
  linarith only [prob,total]
end
end DisjointnessDraft.Information.MinEntropy
