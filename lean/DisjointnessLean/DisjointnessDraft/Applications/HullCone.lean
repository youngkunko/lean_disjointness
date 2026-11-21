import DisjointnessDraft.Applications.HullNeighbors

/-! Robust hiding of every level strictly above the selected cutoff. Four
ordinary vertices suffice: the selector and three guards on the ring at its
base, in the same column and the two adjacent columns. -/
namespace DisjointnessDraft.Applications.HullCone
open Hull HullConfig HullAngles HullHidden HullNeighbors Real Classical
open scoped BigOperators
noncomputable section
def witnesses {n} (j : Fin n) (a : Fin (n+1)) : Fin 4 → Label n :=
  ![.guard a j,.sel a,.guard a (next j),.guard a (prev j)]

theorem enclosed {n : ℕ} (n5 : 5≤n) (j : Fin n) (a : Fin (n+1)) (h : ℝ)
    (after : 2*(a.val:ℝ)+2≤h) (hH : h≤height n)
    (y' : Point) (P' : Fin 4 → Point)
    (ym : ∀ i,|y' i-column j (radius n-h^2) h i|≤eps n)
    (pm : ∀ k i,|P' k i-coords n (witnesses j a k) i|≤eps n) :
    y'∈convexHull ℝ (Set.range P') := by
  let R := radius n
  let H := height n
  let s := 2*(a.val:ℝ)+1
  let C := R-s^2
  let T := selector R s
  let c := cos (turn n)
  let d := C*sin (turn n)
  let D := C*(1-c)
  let b := (h-s)/(T-s)
  let l := (h-s)^2/D
  let k := 1-b-l
  let p : Fin 4 → ℝ := ![k,b,l/2,l/2]
  let P := coords n ∘ witnesses j a
  let y := column j (R-h^2) h
  have nr : (5:ℝ)≤n := by exact_mod_cast n5
  have s1 : 1≤s := by dsimp [s]; linarith [show (0:ℝ)≤a.val by positivity]
  have sh : s+1≤h := by dsimp [s]; linarith
  have sH : s≤H := by linarith
  have sp : 0<s := by linarith
  have npos : 0<(n:ℝ) := by linarith
  have R0 : 0<R := by dsimp [R,radius]; positivity
  have r := spread_bounds n5 s1 sH
  have hnum := numbers nr
  have Hn : H≤(5/2)*(n:ℝ) := by dsimp [H,height]; linarith
  have M := scales n5
  have cm : C≥R/2 := r.2.2.2.2
  have hp : 0<H := by linarith
  have q : 16*(n:ℝ)^2≤D := r.1
  have D0 : 0<D := by have h1 := r.2.2.2.1; change 2*s+1≤D at h1; linarith
  have Tdef : (T-s)*(2*s)=C := by dsimp [T,selector,C]; field_simp; ring
  have Ts : 4*H≤T-s := by
    apply (le_of_mul_le_mul_right _ (show 0<2*s by linarith))
    have z := mul_le_mul_of_nonneg_left sH hp.le
    have Rlarge : 16*H^2≤R := M.2.2.2
    calc 4*H*(2*s)≤8*H^2 := by nlinarith only [z]
         _ ≤ R/2 := by linarith only [Rlarge]
         _ ≤ C := cm
         _ = _ := Tdef.symm
  have T0 : 0<T-s := by linarith
  have exactB : b*(T-s)=h-s := div_mul_cancel₀ _ T0.ne'
  have exactL : l*D=(h-s)^2 := div_mul_cancel₀ _ D0.ne'
  have b4 : b≤1/4 := by
    apply (div_le_iff₀ T0).2; linarith
  have l2 : l≤1/2 := by
    apply (div_le_iff₀ D0).2
    have z : (h-s)^2≤H^2 := by nlinarith only [mul_nonneg (show 0≤H-(h-s) by linarith) (show 0≤H+(h-s) by linarith)]
    have z' := mul_nonneg (show 0≤5/2*(n:ℝ)-H by linarith) (show 0≤5/2*(n:ℝ)+H by linarith)
    calc (h-s)^2≤H^2 := z
         _ ≤ ((5/2:ℝ)*n)^2 := by nlinarith only [z']
         _ ≤ (1/2:ℝ)*(16*(n:ℝ)^2) := by nlinarith only [sq_nonneg (n:ℝ)]
         _ ≤ _ := by linarith only [q]
  have mR : mass n*(4*(n:ℝ)*R)=1 := div_mul_cancel₀ _ (by positivity)
  have mb : mass n≤b := by
    apply (le_div_iff₀ T0).2
    have TR : T-s≤R := by
      apply (le_of_mul_le_mul_right _ (show 0<2*s by linarith))
      dsimp [C] at Tdef; nlinarith only [Tdef,sq_nonneg s,mul_nonneg R0.le (show 0≤2*s-1 by linarith)]
    have Rn : R≤4*(n:ℝ)*R := by nlinarith only [mul_nonneg (show 0≤4*(n:ℝ)-1 by linarith) R0.le]
    have z := mul_le_mul_of_nonneg_left (TR.trans Rn) M.2.1.le
    linarith
  have ml : mass n≤l/2 := by
    apply (le_of_mul_le_mul_right _ D0)
    have dsmall : D≤2*R := r.2.1
    have m2 : 2*D≤4*(n:ℝ)*R := by nlinarith only [dsmall,mul_nonneg (show 0≤(n:ℝ)-1 by linarith) R0.le]
    have z := mul_le_mul_of_nonneg_left m2 M.2.1.le
    nlinarith only [z,mR,exactL,mul_nonneg (show 0≤h-s-1 by linarith) (show 0≤h-s+1 by linarith)]
  have mk : mass n≤k := by dsimp [k]; linarith [M.2.2.1]
  have raw : P=![frame j C 0 s,frame j 0 0 T,frame j (C*c) d s,frame j (C*c) (-d) s] := by
    funext i; fin_cases i
    · simp [P,witnesses,coords,same,C,s,R]
    · simp [P,witnesses,coords,frame,T,s,R]
    · simp [P,witnesses,coords,next_frame,C,s,R,c,d]
    · simp [P,witnesses,coords,prev_frame,C,s,R,c,d]
  refine stays_in_hull j y y' P P' p M.1 (by dsimp [eps]; positivity) ?_ ?_ ?_ ?_ ym pm
  · simp [p,Fin.sum_univ_four,k]; ring
  · intro i; fin_cases i
    · exact mk
    · exact mb
    · exact ml
    · exact ml
  · intro L
    rw [raw]; simp [p,Fin.sum_univ_four,y,same,frame_apply]
    have Z : k*s+b*T+l*s=h := by dsimp [k]; linarith only [exactB]
    have X : k*C+l*(C*c)=R-h^2 := by
      have e : b*C=2*s*(h-s) := by linear_combination (2*s)*exactB-b*Tdef
      dsimp [D] at exactL; dsimp [k]; nlinarith only [exactL,e,show C=R-s^2 from rfl]
    linear_combination (alpha j L)*X+(gamma L)*Z
  · intro L W bound
    rw [raw] at bound
    have nb i k := abs_le.mp (bound i k)
    have bys := nb 2 3
    have ac := nb 0 2
    have ad := nb 0 3
    have za := nb 1 0
    simp [frame_apply] at bys ac ad za
    have d1 : 1≤d := r.2.2.1
    have d2 : 2*s+1≤D := r.2.2.2.1
    have ds1 : 1≤D := by linarith
    have ww : 0≤W := (abs_nonneg _).trans (bound 0 0)
    have AC : |D*alpha j L|≤W := by dsimp [D]; exact abs_le.mpr ⟨by linarith only [ac.1,ad.1],by linarith only [ac.2,ad.2]⟩
    have Aw := unscale ds1 AC
    have Bw : |beta j L|≤W := unscale (by linarith : 1≤2*d)
      (abs_le.2 ⟨by linarith only [bys.1],by linarith only [bys.2]⟩)
    have AC' : |(2*s)*alpha j L|≤W := by
      rw [abs_mul,abs_of_nonneg (by positivity : 0≤2*s)]
      rw [abs_mul,abs_of_nonneg D0.le] at AC
      nlinarith only [AC,mul_nonneg (show 0≤D-2*s by linarith) (abs_nonneg (alpha j L))]
    have wideG : |gamma L-2*s*alpha j L|≤W := by
      apply unscale (show 1≤T-s by linarith)
      have id : (T-s)*(gamma L-2*s*alpha j L)=T*gamma L-s*gamma L-C*alpha j L := by
        linear_combination -(alpha j L)*Tdef
      rw [id]
      exact abs_le.mpr ⟨by linarith only [za.1],by linarith only [za.2]⟩
    have Gw : |gamma L|≤2*W := by
      have z := abs_add_le (gamma L-2*s*alpha j L) (2*s*alpha j L)
      rw [sub_add_cancel] at z
      linarith only [z,wideG,AC']
    unfold size; linarith only [Aw,Bw,Gw,ww]

end
end DisjointnessDraft.Applications.HullCone
