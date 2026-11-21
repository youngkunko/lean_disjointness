import DisjointnessDraft.Applications.HullCosts
import DisjointnessDraft.Applications.HullAngles
import Mathlib.Algebra.Order.Round

/-! Rounding the manuscript's three coordinates, translating the
extreme-point classification under dilation, and bounding the output words. -/
namespace DisjointnessDraft.Applications.HullRounding
open Hull HullConfig HullCosts HullAngles Real Finset Classical
noncomputable section
variable {n N : ℕ}
def scale (n : ℕ) : ℝ := 2*(radius n)^2
def integer (n : ℕ) (v : Label n) : Grid := fun i => round (scale n * coords n v i)
def snapped (n : ℕ) (v : Label n) : Point := fun i => (integer n v i:ℝ) / scale n

theorem scale_pos (hn : 0<n) : 0<scale n := by unfold scale radius; positivity

theorem coordinate_error (n5 : 5≤n) (v : Label n) (i : Fin 3) :
    |snapped n v i-coords n v i| ≤ 1/(4*(radius n)^2) := by
  have pos := scale_pos (by omega : 0<n)
  have raw := abs_sub_round (scale n * coords n v i)
  have eq : snapped n v i-coords n v i = ((integer n v i:ℝ)-scale n*coords n v i)/scale n := by
    unfold snapped; field_simp
  rw [eq,abs_div,abs_of_pos pos,le_div_iff₀ (by unfold radius; positivity : 0<4*(radius n)^2)]
  have one : |(integer n v i:ℝ)-scale n*coords n v i|≤1/2 := by simpa only [integer,abs_sub_comm] using raw
  have eq' : |(integer n v i:ℝ)-scale n*coords n v i|/scale n*(4*(radius n)^2)=
      2*|(integer n v i:ℝ)-scale n*coords n v i| := by
    rw [show 4*(radius n)^2=2*scale n by unfold scale; ring]; field_simp; ring
  rw [eq']; linarith

/-- Squared Euclidean displacement is strictly smaller than the squared
manuscript radius. -/
theorem euclidean_error (n5 : 5≤n) (v : Label n) :
    ∑i : Fin 3,(snapped n v i-coords n v i)^2 < (1/(radius n)^2)^2 := by
  have pos : 0<radius (n:ℝ) := by unfold radius; positivity
  have bp (i : Fin 3) : (snapped n v i-coords n v i)^2≤(1/(4*(radius n)^2))^2 := by
    simpa only [sq_abs] using pow_le_pow_left₀ (abs_nonneg _) (coordinate_error n5 v i) 2
  have summed := sum_le_sum (s:=univ) (fun i _ => bp i)
  have lt : 3*(1/(4*(radius n)^2))^2 < (1/(radius n)^2)^2 := by
    rw [show 1/(4*(radius n)^2)=(1/(radius n)^2)/4 by ring]
    nlinarith [sq_pos_of_pos (one_div_pos.mpr (sq_pos_of_pos pos))]
  exact summed.trans_lt (by simpa using lt)

theorem small_error (n5 : 5≤n) (v : Label n) (i : Fin 3) : |snapped n v i-coords n v i|≤1/(radius n)^2 := by
  apply (coordinate_error n5 v i).trans
  have p : 0<(radius (n:ℝ))^2 := by unfold radius; positivity
  exact one_div_le_one_div_of_le p (by linarith)

private theorem column_bound (j : Fin n) (a h R : ℝ) (a0 : 0≤a) (ar : a≤R) (h0 : 0≤h) (hr : h≤R)
    (i : Fin 3) : |column j a h i|≤R := by
  fin_cases i
  · simpa [column,abs_mul,abs_of_nonneg a0] using (mul_le_of_le_one_right a0 (abs_cos_le_one (angle j))).trans ar
  · simpa [column,abs_mul,abs_of_nonneg a0] using (mul_le_of_le_one_right a0 (abs_sin_le_one (angle j))).trans ar
  · simpa [column,abs_of_nonneg h0] using hr

theorem coordinate_size (n5 : 5≤n) (v : Label n) (i : Fin 3) : |coords n v i|≤radius n := by
  have bn : (5:ℝ)≤n := by exact_mod_cast n5
  have H := parameters bn
  have rn := (numbers bn).1
  have hh : 1≤height (n:ℝ) := by unfold height; linarith [Nat.cast_nonneg (α:=ℝ) n]
  have smallh : height (n:ℝ)+1≤radius n := by nlinarith [sq_nonneg (height (n:ℝ)-1)]
  have level (j : Fin n) (h : ℝ) (hg : 0≤h) (hr : h≤height n) :
      |column j (radius n-h^2) h i|≤radius n := by
    have relation := pow_le_pow_left₀ hg hr 2
    exact column_bound j _ _ _ (by nlinarith) (by nlinarith [sq_nonneg h]) hg (by linarith) i
  cases v with
  | guard k j =>
    have kN : (k.val:ℝ)≤n := by exact_mod_cast (show k.val≤n by have := k.isLt; omega)
    apply level <;> dsimp only [height] <;> linarith [Nat.cast_nonneg (α:=ℝ) k.val]
  | datum k j =>
    have kN : (k.val:ℝ)+1≤n := by exact_mod_cast k.isLt
    apply level <;> dsimp only [height] <;> linarith [Nat.cast_nonneg (α:=ℝ) k.val]
  | block j => exact column_bound j _ _ _ (by linarith) (by linarith) (by linarith) smallh i
  | sel a =>
    let s := 2*(a.val:ℝ)+1
    have aN : (a.val:ℝ)≤n := by exact_mod_cast (show a.val≤n by have := a.isLt; omega)
    have s1 : 1≤s := by dsimp [s]; linarith [Nat.cast_nonneg (α:=ℝ) a.val]
    have sH : s≤height n := by dsimp [s,height]; linarith
    have upper := selector_order (R:=radius n) (H:=height n) le_rfl s1 sH H.2
    have rp : 0<radius (n:ℝ) := by linarith
    have sp : 0<s := by linarith
    have pos : 0≤selector (radius n) s := by unfold selector; positivity
    have top : selector (radius n) 1=(radius n+1)/2 := by simp [selector]
    rw [top] at upper
    change |(![0,0,selector (radius n) s] : Point) i|≤radius n
    fin_cases i <;> simp [abs_of_nonneg pos] <;> linarith

theorem integer_size (n5 : 5≤n) (v : Label n) (i : Fin 3) :
    |(integer n v i:ℝ)|≤2*(radius n)^3+1 := by
  have sp := scale_pos (by omega : 0<n)
  have raw := abs_sub_round (scale n * coords n v i)
  have tri := abs_add_le ((integer n v i:ℝ)-scale n*coords n v i) (scale n*coords n v i)
  rw [sub_add_cancel,abs_mul,abs_of_pos sp] at tri
  have diff : |(integer n v i:ℝ)-scale n*coords n v i|≤1/2 := by simpa only [integer,abs_sub_comm] using raw
  have large := mul_le_mul_of_nonneg_left (coordinate_size n5 v i) sp.le
  unfold scale at large tri diff
  nlinarith

theorem within_limit (n5 : 5≤n) (leN : n≤N) (v : Label n) : fit N (integer n v) := by
  intro i
  have h := integer_size n5 v i
  have cube : 2*(radius (n:ℝ))^3+1=128*(n:ℝ)^12+1 := by unfold radius; ring
  rw [cube] at h
  have c : (n:ℝ)≤N := by exact_mod_cast leN
  have nn : (n:ℝ)≤(N:ℝ)+1 := by linarith
  have p := pow_le_pow_left₀ (by positivity : 0≤(n:ℝ)) nn 12
  have one : (1:ℝ)≤((N:ℝ)+1)^12 := one_le_pow₀ (by linarith [Nat.cast_nonneg (α:=ℝ) N])
  have z : |(integer n v i:ℝ)|≤1000*((N:ℝ)+1)^12 := by linarith
  unfold limit; exact_mod_cast z

def dilation (hn : 0<n) : Point ≃ₗ[ℝ] Point := LinearEquiv.smulOfNeZero ℝ Point (scale n) (scale_pos hn).ne'
theorem dilate_snapped (hn : 0<n) : (⇑(dilation hn)) ∘ snapped n = realPoint ∘ integer n := by
  funext v i
  change scale n*((integer n v i:ℝ)/scale n)=_
  field_simp [realPoint,(scale_pos hn).ne']

theorem integer_classification (n5 : 5≤n) (S : Family n) (X : Finset (Fin n)) (T : Finset (Fin (n+1)))
    (h : classification (snapped n) S X T) : classification (realPoint ∘ integer n) S X T := by
  have hn : 0<n := by omega
  let L := dilation hn
  unfold classification at *
  rw [←dilate_snapped hn]
  simp only [Set.image_comp]
  have c := L.toLinearMap.image_convexHull (snapped n '' (↑(present S X T) : Set (Label n)))
  change L '' (convexHull ℝ _) = convexHull ℝ (L '' _) at c
  rw [←c,←image_extremePoints L,h]

end
end DisjointnessDraft.Applications.HullRounding
