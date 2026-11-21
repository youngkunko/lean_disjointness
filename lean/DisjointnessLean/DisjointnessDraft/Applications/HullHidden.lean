import DisjointnessDraft.Applications.HullExposure

/-! Affine-support tests for hidden points. A positively weighted enclosing
family with sufficiently large directional width continues to contain its
test point when all coordinates move. -/
namespace DisjointnessDraft.Applications.HullHidden
open Hull HullConfig HullAngles Finset Real Classical
open scoped BigOperators
noncomputable section
abbrev LForm := Point →L[ℝ] ℝ
def frame {n} (j : Fin n) (x y z : ℝ) : Point :=
  ![cos (angle j)*x-sin (angle j)*y,sin (angle j)*x+cos (angle j)*y,z]
def alpha {n} (j : Fin n) (L : LForm) := L (frame j 1 0 0)
def beta {n} (j : Fin n) (L : LForm) := L (frame j 0 1 0)
def gamma (L : LForm) := L ![0,0,1]
def size {n} (j : Fin n) (L : LForm) := |alpha j L| + |beta j L| + |gamma L|

theorem frame_apply {n} (j : Fin n) (L : LForm) (x y z : ℝ) :
    L (frame j x y z)=x*alpha j L+y*beta j L+z*gamma L := by
  have eq : frame j x y z=x • frame j 1 0 0+y • frame j 0 1 0+z • ![0,0,1] := by
    ext i; fin_cases i <;> simp [frame] <;> ring
  rw [eq]; simp only [map_add,map_smul,smul_eq_mul,alpha,beta,gamma]
theorem same {n} (j : Fin n) (r z : ℝ) : column j r z=frame j r 0 z := by
  ext i; fin_cases i <;> simp [frame,column] <;> ring

private theorem frame_inv {n} (j : Fin n) (x : Point) :
    x=frame j (cos (angle j)*x 0+sin (angle j)*x 1) (-sin (angle j)*x 0+cos (angle j)*x 1) (x 2) := by
  have a := sin_sq_add_cos_sq (angle j)
  ext i
  fin_cases i <;> simp [frame]
  all_goals first | nlinarith only [congrArg (fun a => a*x 0) a] | nlinarith only [congrArg (fun a => a*x 1) a]

theorem point_variation {n} (j : Fin n) (L : LForm) {eps : ℝ} (x y : Point) (within : ∀ i,|x i-y i|≤eps) :
    |L x-L y|≤2*eps*size j L := by
  have ep : 0≤eps := (abs_nonneg _).trans (within 0)
  let d := x-y
  have dx (i : Fin 3) : |d i|≤eps := within i
  have bound (a b : ℝ) (aa : |a|≤1) (bb : |b|≤1) : |a*d 0+b*d 1|≤2*eps := by
    calc _ ≤ |a*d 0| + |b*d 1| := abs_add_le _ _
         _ ≤ 1*eps+1*eps := by simp only [abs_mul]; exact add_le_add (mul_le_mul aa (dx 0) (abs_nonneg _) zero_le_one) (mul_le_mul bb (dx 1) (abs_nonneg _) zero_le_one)
         _ = _ := by ring
  let a := cos (angle j)*d 0+sin (angle j)*d 1
  let b := -sin (angle j)*d 0+cos (angle j)*d 1
  have ax : |a|≤2*eps := bound _ _ (abs_cos_le_one _) (abs_sin_le_one _)
  have bx : |b|≤2*eps := bound _ _ (by simpa using abs_sin_le_one (angle j)) (abs_cos_le_one _)
  have cz : |d 2|≤2*eps := (dx 2).trans (by linarith)
  have le := abs_add_le (a*alpha j L+b*beta j L) (d 2*gamma L)
  have lt := abs_add_le (a*alpha j L) (b*beta j L)
  rw [←L.map_sub]
  change |L d|≤_
  rw [frame_inv j d,frame_apply]
  change |a*alpha j L+b*beta j L+d 2*gamma L|≤_
  simp only [abs_mul] at le lt
  unfold size
  linarith only [le,lt,mul_le_mul_of_nonneg_right ax (abs_nonneg (alpha j L)),mul_le_mul_of_nonneg_right bx (abs_nonneg (beta j L)),mul_le_mul_of_nonneg_right cz (abs_nonneg (gamma L))]

theorem size_pos {n} (j : Fin n) (L : LForm) (nz : L≠0) : 0<size j L := by
  by_contra! h
  have a : alpha j L=0 := abs_nonpos_iff.mp (by unfold size at h; linarith [abs_nonneg (beta j L),abs_nonneg (gamma L)])
  have b : beta j L=0 := abs_nonpos_iff.mp (by unfold size at h; linarith [abs_nonneg (alpha j L),abs_nonneg (gamma L)])
  have c : gamma L=0 := abs_nonpos_iff.mp (by unfold size at h; linarith [abs_nonneg (alpha j L),abs_nonneg (beta j L)])
  apply nz; ext x
  rw [frame_inv j x,frame_apply,a,b,c]; simp

theorem unscale {q a W : ℝ} (one : 1≤q) (x : |q*a|≤W) : |a|≤W := by
  rw [abs_mul,abs_of_nonneg (by linarith : 0≤q)] at x
  have h : |a|≤q*|a| := by simpa using mul_le_mul_of_nonneg_right one (abs_nonneg a)
  exact h.trans x

/-- If every score is at most B above its weighted mean, and each weight is
at least m, then the full score range is at most B/m. -/
theorem spread {I : Type} [Fintype I] (a score : I → ℝ) {m B avg : ℝ} (m0 : 0<m)
    (a1 : ∑ i,a i=1) (ma : ∀ i,m≤a i) (mean : ∑ i,a i*score i=avg) (cap : ∀ i,score i-avg≤B) :
    ∀ i j,|score i-score j|≤B/m := by
  let defic := fun i => B+avg-score i
  have d0 i : 0≤defic i := by dsimp [defic]; linarith [cap i]
  have total : ∑ i,a i*defic i=B := by
    simp only [defic,mul_sub,Finset.sum_sub_distrib,←Finset.sum_mul,a1,mean,one_mul]; ring
  have one i : defic i≤B/m := by
    apply (le_div_iff₀ m0).2
    have e := Finset.single_le_sum (f:=fun i => a i*defic i) (s:=univ)
      (fun j _ => mul_nonneg (m0.le.trans (ma j)) (d0 j)) (mem_univ i)
    rw [total] at e
    exact (mul_comm _ _).le.trans ((mul_le_mul_of_nonneg_right (ma i) (d0 i)).trans e)
  intro i j
  have lo := one i; have hi := one j
  dsimp [defic] at lo hi
  exact abs_le.2 ⟨by linarith [cap j],by linarith [cap i]⟩

theorem stays_in_hull {I : Type} [Fintype I] [Nonempty I] {n} (j : Fin n)
    (y y' : Point) (P P' : I → Point) (p : I → ℝ) {m eps : ℝ} (room : 24*eps<m) (ep : 0≤eps)
    (unit : ∑ i,p i=1) (weights : ∀ i,m≤p i)
    (center : ∀ L : LForm,∑ i,p i*L (P i)=L y)
    (wide : ∀ (L : LForm) (W : ℝ), (∀ i k,|L (P i)-L (P k)|≤W) → size j L≤6*W)
    (yp : ∀ i,|y' i-y i|≤eps) (pp : ∀ v i,|P' v i-P v i|≤eps) :
    y'∈convexHull ℝ (Set.range P') := by
  by_contra out
  obtain ⟨L,t,low,high⟩ := geometric_hahn_banach_closed_point (convex_convexHull ℝ (Set.range P'))
    (Set.finite_range P').isClosed_convexHull out
  have lt i := (low _ (subset_convexHull ℝ _ (Set.mem_range_self i))).trans high
  have nz : L≠0 := by
    intro z
    subst L
    have h := lt (Classical.choice (inferInstance : Nonempty I))
    simp at h
  have sp := size_pos j L nz
  have m0 : 0<m := by linarith
  let B := 4*eps*size j L
  have cap i : L (P i)-L y≤B := by
    have a := abs_le.mp (point_variation j L y' y yp)
    have b := abs_le.mp (point_variation j L (P' i) (P i) (pp i))
    dsimp [B]; nlinarith only [lt i,a.2,b.1]
  have w := wide L _ (spread p (fun i => L (P i)) m0 unit weights (center L) cap)
  have e : size j L*m≤6*B := by
    have z := mul_le_mul_of_nonneg_right w m0.le
    calc size j L*m ≤ 6*(B/m)*m := z
         _ = _ := by field_simp
  dsimp [B] at e; nlinarith only [e,mul_lt_mul_of_pos_right room sp]

end
end DisjointnessDraft.Applications.HullHidden
