import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Analysis.Convex.Extreme
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-! Quantitative certificates for the paraboloid columns, blocker tetrahedron,
and selector cone in the convex-hull reduction. The exposure and containment
identities use the manuscript's radii, heights, normals, and barycentric weights. -/
namespace DisjointnessDraft.Applications.Hull
open Real
noncomputable section
def radius (n : ℝ) := 4*n^4
def height (n : ℝ) := 2*n+1
def selector (R s : ℝ) := (R+s^2)/(2*s)
def value (R h z cosine : ℝ) := (R-z^2)*cosine + (2*h-1/2)*z

theorem angular_gap (n : ℝ) (n5 : 5≤n) : 8/n^2 ≤ 1-cos (2*π/n) := by
  have np : 0<n := by linarith
  have a : 0≤π/n := by positivity
  have b : π/n≤π/2 := by apply (div_le_iff₀ np).2; nlinarith [pi_pos,mul_nonneg (show 0≤n-2 by linarith) pi_pos.le]
  have hs := mul_le_sin a b
  have e : 2/π*(π/n)=2/n := by field_simp
  rw [e] at hs
  have hsq : (2/n)^2≤sin (π/n)^2 := by nlinarith only [mul_nonneg (sub_nonneg.mpr hs) (add_nonneg (sin_nonneg_of_nonneg_of_le_pi a (by linarith [pi_pos])) (by positivity : 0≤2/n))]
  rw [show 2*π/n=2*(π/n) by ring,cos_two_mul]
  have id := sin_sq_add_cos_sq (π/n)
  have eq : 8/n^2=2*(2/n)^2 := by ring
  rw [eq]; linarith

theorem parameters {n : ℝ} (n5 : 5≤n) :
    height n+1 < selector (radius n) (height n) ∧ (height n)^2 ≤ radius n/2 := by
  have np : 0≤n := by linarith
  have s : 0<height n := by unfold height; linarith
  have n2 : 5*n≤n^2 := by nlinarith [mul_nonneg np (show 0≤n-5 by linarith)]
  have n4 : 25*n^2≤n^4 := by nlinarith [mul_nonneg (show 0≤n^2-25 by nlinarith) (sq_nonneg n)]
  constructor
  · unfold selector; apply (lt_div_iff₀ (by positivity : 0<2*height n)).2
    unfold height radius; nlinarith
  · unfold radius height; nlinarith

theorem heights {R s t : ℝ} (s0 : 0<s) (t0 : 0<t) :
    selector R s-selector R t=(t-s)*(R-s*t)/(2*s*t) := by
  unfold selector; field_simp; ring

theorem level_deficit (R h z c : ℝ) :
    value R h h 1-value R h z c=(z-h)^2+(z-h)/2+(R-z^2)*(1-c) := by
  unfold value; ring

theorem integer_gap (h z : ℤ) (hz : h≠z) :
    (1:ℝ)/2 ≤ ((z:ℝ)-h)^2+((z:ℝ)-h)/2 := by
  by_cases hlt : h<z
  · have e : (h:ℝ)+1≤z := by exact_mod_cast (show h+1≤z by omega)
    nlinarith only [e,sq_nonneg ((z:ℝ)-h-1)]
  · have e : (z:ℝ)+1≤h := by exact_mod_cast (show z+1≤h by omega)
    have a := mul_nonneg (show 0≤(h:ℝ)-z-1 by linarith) (show 0≤(h:ℝ)-z by linarith)
    nlinarith only [e,a]

theorem selector_deficit {R h s : ℝ} (s0 : 0<s) :
    value R h h 1-(2*h-1/2)*selector R s=(s-h)*(R/s-h)+(selector R s-h)/2 := by
  unfold value selector; field_simp; ring

theorem cone_section (R s h : ℝ) :
    R+s^2-2*s*h=R-h^2+(h-s)^2 := by ring

theorem cone_margin {R s h c dot : ℝ} (rad : 0≤R-h^2) (side : dot≤c)
    (c0 : 0≤c) (gap : s+1≤h) :
    c≤c*(R+s^2)-(R-h^2)*dot-2*s*c*h := by
  have e := mul_le_mul_of_nonneg_left side rad
  have a : 1≤(h-s)^2 := by nlinarith only [mul_nonneg (show 0≤h-s-1 by linarith) (show 0≤h-s+1 by linarith)]
  have b := mul_le_mul_of_nonneg_left a c0
  nlinarith only [e,b]

def D (R H c : ℝ) := R-1-c*(R-H^2)
def lam (R H c h : ℝ) := (h^2-1)/D R H c
def wtBlock (H h l : ℝ) := (h-1-l*(H-1))/H
def wtBase (H h l : ℝ) := (H+1-h-l)/H

theorem tetra (R H c h d : ℝ) (h2 : 2≤h) (hH : h≤H) (wide : H^2-1<D R H c) :
    let l := lam R H c h
    let a := wtBase H h l
    let b := wtBlock H h l
    0<l/2 ∧ 0<a ∧ 0<b ∧ a+b+l/2+l/2=1 ∧
      (a+b)*(R-1)+l/2*(c*(R-H^2))+l/2*(c*(R-H^2))=R-h^2 ∧
      l/2*d+l/2*(-d)=0 ∧ a+b*(H+1)+l/2*H+l/2*H=h := by
  intro l a b
  have h0 : 0<H := by linarith
  have h1 : 0<H-1 := by linarith
  have w : 0<D R H c := by nlinarith [sq_nonneg (H-2)]
  have l0 : 0<l := by apply div_pos _ w; nlinarith [sq_nonneg (h-2)]
  have l1 : l<1 := by apply (div_lt_one w).2; nlinarith only [wide,mul_nonneg (sub_nonneg.mpr hH) (show 0≤H+h by linarith)]
  have s : (h+1)*(H-1)<D R H c := by nlinarith only [mul_nonneg (sub_nonneg.mpr hH) h1.le,wide]
  have bound := mul_lt_mul_of_pos_left s (show 0<h-1 by linarith)
  have exactD : l*D R H c=h^2-1 := div_mul_cancel₀ _ w.ne'
  have small : l*(H-1)<h-1 := by
    apply (mul_lt_mul_right w).mp
    calc l*(H-1)*D R H c = (l*D R H c)*(H-1) := by ring
         _ < _ := by rw [exactD]; linarith only [bound]
  have weights : a+b+l=1 := by dsimp [a,b,wtBase,wtBlock]; field_simp; ring
  refine ⟨by linarith,div_pos (by linarith) h0,div_pos (by linarith) h0,by linarith,?_,by ring,?_⟩
  · have t : a+b=1-l := by linarith
    rw [t]; dsimp [D] at exactD; linarith only [exactD]
  · dsimp [a,b,wtBase,wtBlock]; field_simp; ring

/-- Each support value changes by at most epsilon. A strict witness with
margin exceeding twice epsilon therefore survives moving every point. -/
theorem stable_exposure {I : Type} (f g : I → ℝ) (x : I) (eps : ℝ)
    (motion : ∀ i, |g i-f i|≤eps) (clear : ∀ i,i≠x → 2*eps<f x-f i) :
    ∀ i,i≠x → g i<g x := by
  intro i h
  have p := abs_le.mp (motion i)
  have q := abs_le.mp (motion x)
  linarith [clear i h]

end
end DisjointnessDraft.Applications.Hull
