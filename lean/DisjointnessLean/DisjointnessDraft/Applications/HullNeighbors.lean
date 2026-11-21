import DisjointnessDraft.Applications.HullHidden

/-! Adjacent columns in a regular polygon, including wraparound. The common
barycentric lower bound is chosen for the allowed rounding radius. -/
namespace DisjointnessDraft.Applications.HullNeighbors
open Hull HullConfig HullAngles HullHidden Real Classical
noncomputable section
def turn (n : ℕ) : ℝ := 2*π/n
def next {n} (j : Fin n) : Fin n :=
  if h : j.val+1<n then ⟨j.val+1,h⟩ else ⟨0,by have := j.isLt; omega⟩
def prev {n} (j : Fin n) : Fin n :=
  if h : j.val=0 then ⟨n-1,by have := j.isLt; omega⟩ else ⟨j.val-1,by have := j.isLt; omega⟩

theorem next_angle {n} (j : Fin n) : angle (next j)=angle j+turn n ∨ angle (next j)=angle j+turn n-2*π := by
  have pos : (n:ℝ)≠0 := by have := j.isLt; exact_mod_cast (show n≠0 by omega)
  by_cases h : j.val+1<n
  · left; simp [angle,next,h,turn]; ring
  · right; have e : (j.val:ℝ)+1=n := by have := j.isLt; exact_mod_cast (show j.val+1=n by omega)
    simp [angle,next,h,turn]; rw [e]; field_simp; ring

private theorem prev_angle {n} (j : Fin n) : angle (prev j)=angle j-turn n ∨ angle (prev j)=angle j-turn n+2*π := by
  have pos : (n:ℝ)≠0 := by have := j.isLt; exact_mod_cast (show n≠0 by omega)
  by_cases h : j.val=0
  · right; have n1 : 1≤n := by have := j.isLt; omega
    simp [angle,prev,h,turn,Nat.cast_sub n1]; field_simp
  · left; have j1 : 1≤j.val := by omega
    simp [angle,prev,h,turn,Nat.cast_sub j1]; ring

theorem next_frame {n} (j : Fin n) (r z : ℝ) :
    column (next j) r z=frame j (r*cos (turn n)) (r*sin (turn n)) z := by
  rcases next_angle j with h|h <;> ext i <;> fin_cases i <;>
    simp [column,frame,h,cos_add,sin_add] <;> ring
theorem prev_frame {n} (j : Fin n) (r z : ℝ) :
    column (prev j) r z=frame j (r*cos (turn n)) (-(r*sin (turn n))) z := by
  rcases prev_angle j with h|h <;> ext i <;> fin_cases i <;>
    simp [column,frame,h,cos_sub,sin_sub] <;> ring

def mass (n : ℕ) : ℝ := 1/(4*(n:ℝ)*radius n)
def eps (n : ℕ) : ℝ := 1/(radius n)^2
theorem scales {n : ℕ} (h5 : 5≤n) :
    24*eps n<mass n ∧ 0<mass n ∧ mass n≤1/4 ∧ 16*(height n)^2≤radius n := by
  have nr : (5:ℝ)≤n := by exact_mod_cast h5
  have h : 0<(n:ℝ) := by linarith
  have R : 0<radius n := by dsimp [radius]; positivity
  have s : 25≤(n:ℝ)^2 := by nlinarith [mul_nonneg (show 0≤(n:ℝ)-5 by linarith) (show 0≤(n:ℝ)+5 by linarith)]
  have q : 25*(n:ℝ)^2≤(n:ℝ)^4 := by nlinarith only [mul_nonneg (sq_nonneg (n:ℝ)) (show 0≤(n:ℝ)^2-25 by linarith)]
  have t : 5*(n:ℝ)≤(n:ℝ)^2 := by nlinarith only [mul_nonneg h.le (show 0≤(n:ℝ)-5 by linarith)]
  have main : 96*(n:ℝ)<radius n := by dsimp [radius]; linarith
  refine ⟨?_,by dsimp [mass]; positivity,?_,?_⟩
  · dsimp [eps,mass]; rw [mul_one_div,div_lt_div_iff₀ (sq_pos_of_pos R) (by positivity)]
    nlinarith only [mul_lt_mul_of_pos_right main R]
  · dsimp [mass]; apply (div_le_div_iff₀ (by positivity) (by norm_num)).2
    nlinarith [mul_nonneg (show 0≤(n:ℝ)-1 by linarith) R.le]
  · dsimp [height,radius]; nlinarith

theorem spread_bounds {n : ℕ} (n5 : 5≤n) {s : ℝ} (s1 : 1≤s) (sH : s≤height n) :
    let R := radius n
    let C := R-s^2
    let D := C*(1-cos (turn n))
    let d := C*sin (turn n)
    16*(n:ℝ)^2≤D ∧ D≤2*R ∧ 1≤d ∧ 2*s+1≤D ∧ C≥R/2 := by
  intro R C D d
  have h : (5:ℝ)≤n := by exact_mod_cast n5
  have np : 0<(n:ℝ) := by linarith
  have rp : 0<radius n := by dsimp [radius]; positivity
  have r := (parameters h).2
  have cs : R/2≤C := by dsimp [C,R]; nlinarith only [r,mul_nonneg (sub_nonneg.mpr sH) (show 0≤height n+s by linarith)]
  have c0 : 0≤C := (div_nonneg rp.le (by norm_num)).trans cs
  have a := angular_gap (n:=(n:ℝ)) h
  have nrare : ((radius n)/2)*(8/(n:ℝ)^2)=16*(n:ℝ)^2 := by dsimp [radius]; field_simp; ring
  have Dl : 16*(n:ℝ)^2≤D := by
    rw [←nrare]; exact mul_le_mul cs a (by positivity) c0
  have Dh : D≤2*R := by
    have co := neg_one_le_cos (turn n)
    dsimp [D]; nlinarith only [mul_nonneg c0 (show 0≤1+cos (turn n) by linarith),show C≤R by dsimp [C]; linarith [sq_nonneg s]]
  have ang0 : 0≤turn n := by dsimp [turn]; positivity
  have ang1 : turn n≤π/2 := by dsimp [turn]; apply (div_le_iff₀ np).2; nlinarith only [mul_nonneg (show 0≤(n:ℝ)-4 by linarith) pi_pos.le]
  have sn := mul_le_sin ang0 ang1
  have eq : 2/π*turn n=4/(n:ℝ) := by dsimp [turn]; field_simp; ring
  rw [eq] at sn
  have rare : ((radius n)/2)*(4/(n:ℝ))=8*(n:ℝ)^3 := by dsimp [radius]; field_simp; ring
  have dt : 8*(n:ℝ)^3≤d := by rw [←rare]; exact mul_le_mul cs sn (by positivity) c0
  have n2 := mul_nonneg np.le (show 0≤(n:ℝ)-1 by linarith)
  have n3 := mul_nonneg (sq_nonneg (n:ℝ)) (show 0≤(n:ℝ)-1 by linarith)
  exact ⟨Dl,Dh,by nlinarith,by dsimp [height] at sH; nlinarith,cs⟩
end
end DisjointnessDraft.Applications.HullNeighbors
