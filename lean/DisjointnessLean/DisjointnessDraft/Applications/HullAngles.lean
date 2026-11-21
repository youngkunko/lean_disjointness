import DisjointnessDraft.Applications.HullConfig

/-! Cyclic angular separation and scalar margins for all four kinds of
exposing planes (bottom guard, blocker, selector, and surviving data level). -/
namespace DisjointnessDraft.Applications.HullAngles
open Hull HullConfig Real
noncomputable section
def dot {n} (j k : Fin n) := cos (angle j-angle k)
theorem angular {n} (n5 : 5≤n) {j k : Fin n} (ne : j≠k) : 8/(n:ℝ)^2≤1-dot j k := by
  have np : 0<(n:ℝ) := by exact_mod_cast (show 0<n by omega)
  have nh : (5:ℝ)≤n := by exact_mod_cast n5
  have ordered (a b : Fin n) (h : a.val<b.val) : cos (angle b-angle a)≤cos (2*π/n) := by
    have bounds : 1≤(b.val:ℝ)-a.val ∧ (b.val:ℝ)-a.val≤n-1 := by
      have ab := a.isLt; have bb := b.isLt
      have ab1 : a.val+1≤b.val := by omega
      have ab2 : b.val+1≤n+a.val := by omega
      have z1 : (a.val:ℝ)+1≤b.val := by exact_mod_cast ab1
      have z2 : (b.val:ℝ)+1≤n+a.val := by exact_mod_cast ab2
      constructor <;> linarith
    let unit := 2*π/(n:ℝ)
    have pos : 0<unit := by dsimp [unit]; positivity
    have full : unit*n=2*π := by dsimp [unit]; field_simp
    have de : angle b-angle a=unit*((b.val:ℝ)-a.val) := by dsimp [angle,unit]; ring
    have lo : unit≤angle b-angle a := by rw [de]; simpa using mul_le_mul_of_nonneg_left bounds.1 pos.le
    have hi : angle b-angle a≤2*π-unit := by rw [de,←full]; nlinarith only [mul_le_mul_of_nonneg_left bounds.2 pos.le]
    by_cases first : angle b-angle a≤π
    · exact cos_le_cos_of_nonneg_of_le_pi pos.le first lo
    · rw [←cos_two_pi_sub (angle b-angle a)]
      exact cos_le_cos_of_nonneg_of_le_pi pos.le (by linarith) (by linarith)
  have diff : j.val≠k.val := fun h => ne (Fin.ext h)
  have bound : dot j k≤cos (2*π/n) := by
    rcases lt_or_gt_of_ne diff with a|a
    · rw [dot,←cos_neg,neg_sub]; exact ordered j k a
    · exact ordered k j a
  linarith [angular_gap n nh]

theorem numbers {n : ℝ} (n5 : 5≤n) :
    1<radius n/2 ∧ height n+3<selector (radius n) (height n) ∧
    (radius n-1)*(8/n^2)>(height n+1)^2+2 ∧
    (radius n/2)*(8/n^2)>1 ∧ 2*(2*height n+3)/(radius n)^2<1/2 := by
  have np : 0<n := by linarith
  have n2 : 25≤n^2 := by nlinarith [mul_nonneg (show 0≤n-5 by linarith) (show 0≤n+5 by linarith)]
  have n4 : 25*n^2≤n^4 := by nlinarith only [mul_nonneg (show 0≤n^2-25 by linarith) (sq_nonneg n)]
  have n1 : n≤n^2 := by nlinarith only [mul_nonneg np.le (show 0≤n-1 by linarith)]
  have n8 : n^4≤n^8 := by nlinarith only [mul_nonneg (show 0≤n^4-1 by nlinarith) (show 0≤n^4 by positivity)]
  have z := parameters n5
  have h0 : 0<height n := by dsimp [height]; linarith
  have r0 : 0<radius n := by dsimp [radius]; positivity
  refine ⟨?_,?_,?_,?_,?_⟩
  · dsimp [radius]; nlinarith
  · dsimp [selector]; apply (lt_div_iff₀ (show 0<2*height n by positivity)).2
    dsimp [height,radius]; nlinarith
  · rw [←mul_div_assoc]; apply (lt_div_iff₀ (sq_pos_of_pos np)).2
    have v := mul_nonneg (show 0≤n-5 by linarith) (show 0≤n^3 by positivity)
    dsimp [height,radius]; nlinarith
  · rw [←mul_div_assoc]; apply (lt_div_iff₀ (sq_pos_of_pos np)).2
    dsimp [radius]; nlinarith
  · apply (div_lt_iff₀ (sq_pos_of_pos r0)).2
    dsimp [height,radius]; nlinarith

theorem selector_order {R H s t : ℝ} (s1 : 1≤s) (st : s≤t) (tH : t≤H) (room : H^2≤R/2) :
    selector R t≤selector R s := by
  have s0 : 0<s := by linarith
  have t0 : 0<t := by linarith
  have p : s*t≤H^2 := by nlinarith only [mul_le_mul_of_nonneg_right st t0.le,mul_nonneg (sub_nonneg.mpr tH) (show 0≤H+t by linarith)]
  have e := heights (R:=R) s0 t0
  have ge : 0≤(t-s)*(R-s*t)/(2*s*t) := div_nonneg (mul_nonneg (sub_nonneg.mpr st) (by nlinarith [sq_nonneg H])) (by positivity)
  linarith

theorem stage_gap {R H s t : ℝ} (s1 : 1≤s) (gap : 2≤t-s) (tH : t≤H) (room : H^2≤R/2) :
    1≤selector R s-selector R t := by
  have s0 : 0<s := by linarith
  have t0 : 0<t := by linarith
  have p : s*t≤H^2 := by nlinarith only [mul_le_mul_of_nonneg_right (show s≤t by linarith) t0.le,mul_nonneg (sub_nonneg.mpr tH) (show 0≤H+t by linarith)]
  rw [heights s0 t0]
  apply (le_div_iff₀ (by positivity : 0<2*s*t)).2
  nlinarith [mul_le_mul_of_nonneg_right gap (show 0≤R-s*t by nlinarith [sq_nonneg H])]

/-- A surviving level strictly beats every foreign-column blocker. -/
theorem foreign_block {n h : ℝ} (n5 : 5≤n) (hH : h≤height n) {c : ℝ} (angleGap : 8/n^2≤1-c) :
    1/2 ≤ value (radius n) h h 1-((radius n-1)*c+(2*h-1/2)*(height n+1)) := by
  obtain ⟨r,_,large,_,_⟩ := numbers n5
  have g := mul_le_mul_of_nonneg_left angleGap (show 0≤radius n-1 by linarith)
  dsimp [value]
  nlinarith only [large,g,hH,sq_nonneg (height n+1-h)]

theorem level_selector {n h s : ℝ} (n5 : 5≤n) (h1 : 1≤h) (hs : h≤s) (sH : s≤height n) :
    1/2≤value (radius n) h h 1-(2*h-1/2)*selector (radius n) s := by
  have p := parameters n5
  have T := selector_order (R:=radius n) (H:=height n) (show 1≤s by linarith) sH le_rfl p.2
  have s0 : 0<s := by linarith
  have a : 0≤radius n/s-h := by
    have sm : h*s≤(height n)^2 := by nlinarith only [mul_le_mul_of_nonneg_right hs s0.le,mul_nonneg (sub_nonneg.mpr sH) (show 0≤height n+s by linarith)]
    have := (le_div_iff₀ s0).2 (show h*s≤radius n by nlinarith [sq_nonneg (height n)])
    linarith
  rw [selector_deficit s0]
  linarith only [mul_nonneg (sub_nonneg.mpr hs) a,T,p.1,hs,sH]
end
end DisjointnessDraft.Applications.HullAngles
