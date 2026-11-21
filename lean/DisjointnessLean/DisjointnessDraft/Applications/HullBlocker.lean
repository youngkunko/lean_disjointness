import DisjointnessDraft.Applications.HullNeighbors

/-! Robust containment in the blocker tetrahedron. The four concrete
generators are the bottom guard, blocker, and the two neighboring top guards.
The argument uses barycentric weights and the directional width of this
tetrahedron. -/
namespace DisjointnessDraft.Applications.HullBlocker
open Hull HullConfig HullAngles HullHidden HullNeighbors Real Classical
open scoped BigOperators
noncomputable section
def witnesses {n} (j : Fin n) : Fin 4 → Label n :=
  ![.guard 0 j,.block j,.guard (Fin.last n) (next j),.guard (Fin.last n) (prev j)]

theorem enclosed {n : ℕ} (n5 : 5≤n) (j : Fin n) (h : ℝ) (h2 : 2≤h) (hH : h≤height n)
    (y' : Point) (P' : Fin 4 → Point)
    (ym : ∀ i,|y' i-column j (radius n-h^2) h i|≤eps n)
    (pm : ∀ k i,|P' k i-coords n (witnesses j k) i|≤eps n) :
    y'∈convexHull ℝ (Set.range P') := by
  let H := height n
  let R := radius n
  let c := cos (turn n)
  let d := (R-H^2)*sin (turn n)
  let D := Hull.D R H c
  let l := lam R H c h
  let a := wtBase H h l
  let b := wtBlock H h l
  let p : Fin 4 → ℝ := ![a,b,l/2,l/2]
  let y := column j (R-h^2) h
  let P := coords n ∘ witnesses j
  have nr : (5:ℝ)≤n := by exact_mod_cast n5
  have m := scales n5
  have nonnegN : 0≤(n:ℝ) := by positivity
  have hp : 0<H := by dsimp [H,height]; linarith
  have rp : 0<R := by dsimp [R,radius]; positivity
  have rr := spread_bounds n5 (s:=H) (by dsimp [H,height]; linarith) le_rfl
  have Dident : D=(H^2-1)+(R-H^2)*(1-c) := by dsimp [D,Hull.D]; ring
  have gap : 2≤D-(H^2-1) := by rw [Dident]; nlinarith only [rr.1,sq_nonneg ((n:ℝ)-5),nr]
  have big : H^2-1<D := by linarith
  have D0 : 0<D := by nlinarith only [big,hH,h2,sq_nonneg (H-2)]
  have small : D≤2*R := by
    have cc := neg_one_le_cos (turn n)
    have ch : 0≤R-H^2 := by linarith [rr.2.2.2.2]
    dsimp [D,Hull.D]; nlinarith only [mul_nonneg ch (by dsimp [c]; linarith : 0≤1+c),sq_nonneg H]
  have tetra := Hull.tetra R H c h d h2 hH big
  change 0<l/2 ∧ 0<a ∧ 0<b ∧ a+b+l/2+l/2=1 ∧ _ at tetra
  obtain ⟨_,_,_,unit,X,Y,Z⟩ := tetra
  have mr : mass n*(4*(n:ℝ)*R)=1 := div_mul_cancel₀ _ (by positivity)
  have hle : H≤4*(n:ℝ) := by dsimp [H,height]; linarith
  have mH : mass n*H*D≤2 := by
    calc _ ≤ (mass n*(4*(n:ℝ)))*(2*R) := mul_le_mul (mul_le_mul_of_nonneg_left hle m.2.1.le) small D0.le (mul_nonneg m.2.1.le (by positivity))
         _ = 2 := by nlinarith only [mr]
  have mD : mass n*D≤1 := by
    have sm := mul_le_mul_of_nonneg_left small m.2.1.le
    have nR : 2*R≤4*(n:ℝ)*R := by nlinarith only [mul_nonneg (show 0≤4*(n:ℝ)-2 by linarith) rp.le]
    exact (sm.trans (mul_le_mul_of_nonneg_left nR m.2.1.le)).trans_eq mr
  have exactL : l*D=h^2-1 := div_mul_cancel₀ _ D0.ne'
  have exactA : a*H=H+1-h-l := div_mul_cancel₀ _ hp.ne'
  have exactB : b*H=h-1-l*(H-1) := div_mul_cancel₀ _ hp.ne'
  have ma : mass n≤a := by
    apply (le_of_mul_le_mul_right _ (mul_pos hp D0))
    have z := mul_nonneg (show 0≤H-h by linarith) D0.le
    have zz := mul_nonneg (show 0≤H-h by linarith) (show 0≤H+h by linarith)
    nlinarith only [congrArg (·*D) exactA,exactL,mH,gap,z,zz]
  have mb : mass n≤b := by
    apply (le_of_mul_le_mul_right _ (mul_pos hp D0))
    have hf : (h+1)*(H-1)≤H^2-1 := by nlinarith only [mul_nonneg (show 0≤H-h by linarith) (show 0≤H-1 by linarith)]
    have factor : (h-1)*(D-(h+1)*(H-1))≥2 := by
      have g : 2≤D-(h+1)*(H-1) := by linarith
      nlinarith only [g,mul_nonneg (show 0≤h-2 by linarith) (show 0≤D-(h+1)*(H-1) by linarith)]
    nlinarith only [congrArg (·*D) exactB,congrArg (·*(H-1)) exactL,mH,factor]
  have ml : mass n≤l/2 := by
    apply (le_of_mul_le_mul_right _ D0)
    nlinarith only [mD,exactL,h2,sq_nonneg (h-2)]
  have raw : P=![frame j (R-1) 0 1,frame j (R-1) 0 (H+1),frame j (c*(R-H^2)) d H,frame j (c*(R-H^2)) (-d) H] := by
    funext i; fin_cases i
    · simp [P,witnesses,coords,same,R]
    · simp [P,witnesses,coords,same,R,H]
    · simp [P,witnesses,coords,next_frame,R,H,height,c,d,mul_comm]
    · simp [P,witnesses,coords,prev_frame,R,H,height,c,d,mul_comm]
  refine stays_in_hull j y y' P P' p m.1 (by dsimp [eps]; positivity) ?_ ?_ ?_ ?_ ym pm
  · simpa only [p,Fin.sum_univ_four,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_three] using unit
  · intro i; fin_cases i
    · exact ma
    · exact mb
    · exact ml
    · exact ml
  · intro L
    rw [raw]; simp [p,Fin.sum_univ_four,y,same,frame_apply]
    linear_combination (alpha j L)*X+(beta j L)*Y+(gamma L)*Z
  · intro L W bound
    rw [raw] at bound
    let A := alpha j L
    let B := beta j L
    let C := gamma L
    have bounds (i k : Fin 4) := abs_le.mp (bound i k)
    have cz := bounds 1 0
    have bys := bounds 2 3
    have ac := bounds 0 2
    have ad := bounds 0 3
    simp [frame_apply] at cz bys ac ad
    have h1 : 1≤H := by linarith
    have d1 : 1≤d := rr.2.2.1
    have d2 : 1≤D := by nlinarith only [gap,sq_nonneg H]
    have ww : 0≤W := (abs_nonneg _).trans (bound 0 0)
    have HC : |H*gamma L|≤W := abs_le.2 ⟨by linarith only [cz.1],by linarith only [cz.2]⟩
    have Cw : |gamma L|≤W := unscale h1 HC
    have Bw : |beta j L|≤W := unscale (by linarith : 1≤2*d)
      (abs_le.2 ⟨by linarith only [bys.1],by linarith only [bys.2]⟩)
    have hc' : |(H-1)*gamma L|≤W := by
      rw [abs_mul,abs_of_nonneg (by linarith : 0≤H-1)]
      rw [abs_mul,abs_of_nonneg hp.le] at HC
      nlinarith only [HC,abs_nonneg (gamma L)]
    have Aw : |alpha j L|≤2*W := by
      apply unscale d2
      have cc := abs_le.mp hc'
      dsimp [D,Hull.D]
      exact abs_le.mpr ⟨by linarith only [ac.1,ad.1,cc.1],by linarith only [ac.2,ad.2,cc.2]⟩
    unfold size; linarith

end
end DisjointnessDraft.Applications.HullBlocker
