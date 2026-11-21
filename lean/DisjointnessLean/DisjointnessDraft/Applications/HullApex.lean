import DisjointnessDraft.Applications.HullCone

/-! A lower selector is surrounded by the highest selector and the bottom
regular polygon. Uniform averaging of the base directions follows from
rotation by one column. This works for odd and even column counts. -/
namespace DisjointnessDraft.Applications.HullApex
open Hull HullConfig HullAngles HullHidden HullNeighbors Real Classical Finset
open scoped BigOperators
noncomputable section

private def rotate (n : ℕ) : Fin n ≃ Fin n where
  toFun := next
  invFun := prev
  left_inv j := by
    have hh := j.isLt
    by_cases h : j.val+1<n
    · rw [next,dif_pos h,prev,dif_neg (by simp)]
      apply Fin.ext; simp
    · rw [next,dif_neg h,prev,dif_pos rfl]
      apply Fin.ext; simp only; omega
  right_inv j := by
    have hh := j.isLt
    by_cases h : j.val=0
    · rw [prev,dif_pos h,next,dif_neg (by change ¬(n-1)+1<n; omega)]
      apply Fin.ext; exact h.symm
    · rw [prev,dif_neg h,next,dif_pos (by change j.val-1+1<n; omega)]
      apply Fin.ext; change j.val-1+1=j.val; omega

theorem centered {n : ℕ} (n5 : 5≤n) :
    (∑ j : Fin n,cos (angle j))=0 ∧ (∑ j : Fin n,sin (angle j))=0 := by
  let A := ∑ j : Fin n,cos (angle j)
  let B := ∑ j : Fin n,sin (angle j)
  let c := cos (turn n)
  let d := sin (turn n)
  have ca j : cos (angle ((rotate n) j))=cos (angle j)*c-sin (angle j)*d := by
    change cos (angle (next j))=_
    rcases next_angle j with h|h <;> simp [h,cos_add,c,d]
  have sn j : sin (angle ((rotate n) j))=sin (angle j)*c+cos (angle j)*d := by
    change sin (angle (next j))=_
    rcases next_angle j with h|h <;> simp [h,sin_add,c,d]
  have ax := Equiv.sum_comp (rotate n) (fun j => cos (angle j))
  have bx := Equiv.sum_comp (rotate n) (fun j => sin (angle j))
  simp_rw [ca] at ax; simp_rw [sn] at bx
  rw [Finset.sum_sub_distrib,←Finset.sum_mul,←Finset.sum_mul] at ax
  rw [Finset.sum_add_distrib,←Finset.sum_mul,←Finset.sum_mul] at bx
  change A*c-B*d=A at ax; change B*c+A*d=B at bx
  have nr : (5:ℝ)≤n := by exact_mod_cast n5
  have gap : 0<1-c := lt_of_lt_of_le (by positivity : 0<8/(n:ℝ)^2) (angular_gap _ nr)
  have pos : 0<(1-c)^2+d^2 := add_pos_of_pos_of_nonneg (sq_pos_of_pos gap) (sq_nonneg d)
  have c1 : A*((1-c)^2+d^2)=0 := by linear_combination -(1-c)*ax+d*bx
  have c2 : B*((1-c)^2+d^2)=0 := by linear_combination -(1-c)*bx-d*ax
  exact ⟨(mul_eq_zero.mp c1).resolve_right pos.ne',(mul_eq_zero.mp c2).resolve_right pos.ne'⟩

def witnesses {n} (a : Fin (n+1)) : Option (Fin n) → Label n
  | none => .sel a | some k => .guard 0 k

theorem enclosed {n : ℕ} (n5 : 5≤n) (s t : Fin (n+1)) (earlier : s<t) (y' : Point)
    (P' : Option (Fin n) → Point)
    (ym : ∀ i,|y' i-coords n (.sel t) i|≤eps n)
    (pm : ∀ k i,|P' k i-coords n (witnesses s k) i|≤eps n) :
    y'∈convexHull ℝ (Set.range P') := by
  let R := radius n
  let H := height n
  let a := 2*(s.val:ℝ)+1
  let b := 2*(t.val:ℝ)+1
  let T := selector R a
  let z := selector R b
  let l := (z-1)/(T-1)
  let g := (1-l)/(n:ℝ)
  let p : Option (Fin n) → ℝ := fun i => i.elim l (fun _ => g)
  let P := coords n ∘ witnesses s
  let j : Fin n := ⟨0,by omega⟩
  let C := R-1
  let D := C*(1-cos (turn n))
  let d := C*sin (turn n)
  have bounds (i : Fin (n+1)) : 1≤2*(i.val:ℝ)+1 ∧ 2*(i.val:ℝ)+1≤H := by
    have h := i.isLt
    have hc : (i.val:ℝ)≤n := by exact_mod_cast (show i.val≤n by omega)
    dsimp [H,height]; constructor <;> linarith [show 0≤(i.val:ℝ) by positivity]
  have nr : (5:ℝ)≤n := by exact_mod_cast n5
  have np : 0<(n:ℝ) := by linarith
  have rp : 0<R := by dsimp [R,radius]; positivity
  have sh := (bounds s).2
  have bh := (bounds t).2
  have one := (bounds s).1
  have bt := (bounds t).1
  change a≤H at sh; change b≤H at bh; change 1≤a at one; change 1≤b at bt
  have ab : 2≤b-a := by
    have h : (s.val:ℝ)+1≤t.val := by exact_mod_cast (show s.val+1≤t.val by exact earlier)
    dsimp [b,a]; linarith
  have M := scales n5
  have room : H^2≤R/2 := (parameters nr).2
  have delta : 1≤T-z := stage_gap one ab bh room
  have zH : selector R H≤z := selector_order bt bh le_rfl room
  have z1 : 2≤z := by have e : H+3<selector R H := (numbers nr).2.1; linarith
  have T1 : 0<T-1 := by linarith
  have TR : T≤R := by
    have H := selector_order (R:=R) (H:=H) (s:=1) le_rfl one sh room
    change T≤selector R 1 at H
    have z := (numbers nr).1; change 1<R/2 at z
    simp only [selector,one_pow,mul_one] at H; linarith
  have exactL : l*(T-1)=z-1 := div_mul_cancel₀ _ T1.ne'
  have exactG : g*n=1-l := div_mul_cancel₀ _ np.ne'
  have mR : mass n*(4*(n:ℝ)*R)=1 := div_mul_cancel₀ _ (by positivity)
  have ml : mass n≤l := by
    apply (le_div_iff₀ T1).2
    have oneR : T-1≤4*(n:ℝ)*R := by nlinarith only [TR,mul_nonneg (show 0≤4*(n:ℝ)-1 by linarith) rp.le]
    have e := mul_le_mul_of_nonneg_left oneR M.2.1.le
    linarith
  have mg : mass n≤g := by
    apply (le_div_iff₀ np).2
    apply (le_of_mul_le_mul_right _ T1)
    have e := mul_le_mul_of_nonneg_left (show T-1≤R by linarith) (mul_nonneg M.2.1.le np.le)
    nlinarith only [e,mR,exactL,delta]
  have rare : (n:ℝ)^2≤T-1 := by
    have big : H+3<selector R H := (numbers nr).2.1
    have ar : 0<a := by linarith
    have h0 : T*(2*a)=R+a^2 := div_mul_cancel₀ _ (by positivity)
    have Hn : H≤(5/2)*(n:ℝ) := by dsimp [H,height]; linarith
    have r1 : 5*(n:ℝ)^3≤(n:ℝ)^4 := by nlinarith only [mul_nonneg (show 0≤(n:ℝ)-5 by linarith) (show 0≤(n:ℝ)^3 by positivity)]
    have r2 : (n:ℝ)≤(n:ℝ)^3 := by nlinarith only [mul_nonneg np.le (show 0≤(n:ℝ)^2-1 by nlinarith [sq_nonneg ((n:ℝ)-1)])]
    have ah := mul_le_mul_of_nonneg_right (sh.trans Hn) (show 0≤(n:ℝ)^2+1 by positivity)
    apply (le_of_mul_le_mul_right _ (show 0<2*a by linarith))
    have polybound : 2*a*((n:ℝ)^2+1)≤R := calc
      _ = 2*(a*((n:ℝ)^2+1)) := by ring
      _ ≤ 2*((5/2 : ℝ)*(n:ℝ)*((n:ℝ)^2+1)) := mul_le_mul_of_nonneg_left ah (by norm_num)
      _ = 5*(n:ℝ)^3+5*n := by ring
      _ ≤ R := by dsimp [R,radius]; nlinarith only [r1,r2,show 0≤(n:ℝ)^3 by positivity]
    calc (n:ℝ)^2*(2*a) ≤ R-2*a := by linarith only [polybound]
         _ ≤ _ := by linarith only [h0,sq_nonneg a]
  have rr := spread_bounds (s:=1) n5 le_rfl (show 1≤height n by dsimp [height]; linarith)
  have rrD : 2*(1:ℝ)+1≤D := by simpa only [one_pow] using rr.2.2.2.1
  have hD : 1≤D := by linarith only [rrD]
  have hd : 1≤d := by simpa only [one_pow] using rr.2.2.1
  have hC : 0≤C := by dsimp [C]; have z : 1<R/2 := (numbers nr).1; linarith
  have dominates : C≤(T-1)*D := by
    have a := angular_gap _ nr
    have c0 : 0≤1-cos (turn n) := by linarith [cos_le_one (turn n)]
    have mul := mul_le_mul rare a (show 0≤8/(n:ℝ)^2 by positivity) T1.le
    have eq : (n:ℝ)^2*(8/(n:ℝ)^2)=8 := by field_simp
    rw [eq] at mul
    have same : (1:ℝ)≤(T-1)*(1-cos (turn n)) := by change 8≤(T-1)*(1-cos (turn n)) at mul; linarith
    simpa only [D,mul_assoc,mul_left_comm,mul_one,one_mul] using mul_le_mul_of_nonneg_left same hC
  let base := fun k : Fin n => column k C 1
  have first : P none=frame j 0 0 T := by simp [P,witnesses,coords,frame,T,a,R]
  have on k : P (some k)=base k := by simp [P,witnesses,coords,base,C,R]
  have apex : coords n (.sel t)=frame j 0 0 z := by simp [coords,frame,z,b,R]
  refine stays_in_hull j _ y' P P' p M.1 (by dsimp [eps]; positivity) ?_ ?_ ?_ ?_ ym pm
  · simp [Fintype.sum_option,p]; linarith
  · intro i; cases i <;> first | exact ml | exact mg
  · intro L
    rw [Fintype.sum_option,first,apex]
    simp only [on,p,Option.elim,frame_apply,zero_mul,add_zero,zero_add,←Finset.mul_sum]
    have ringSum : ∑ i : Fin n,L (base i)=n*gamma L := by
      have basis k : base k=(C*cos (angle k)) • ![1,0,0]+(C*sin (angle k)) • ![0,1,0]+![0,0,1] := by
        ext i; fin_cases i <;> simp [base,column]
      simp_rw [basis]; simp only [map_add,map_smul,smul_eq_mul,sum_add_distrib,←Finset.sum_mul,←Finset.mul_sum]
      rw [(centered n5).1,(centered n5).2]; simp [gamma]
    rw [ringSum]
    nlinarith only [congrArg (·*gamma L) exactL,congrArg (·*gamma L) exactG]
  · intro L W cap
    have take (i k : Option (Fin n)) := abs_le.mp (cap i k)
    have bys := take (some (next j)) (some (prev j))
    have ac := take (some j) (some (next j))
    have ad := take (some j) (some (prev j))
    have za := take none (some j)
    simp only [first,on,base,next_frame,prev_frame,frame_apply] at bys ac ad za
    rw [same j C 1,frame_apply] at ac ad za
    simp only [zero_mul,one_mul,add_zero,zero_add] at bys ac ad za
    have AC : |D*alpha j L|≤W := by
      dsimp [D]; exact abs_le.mpr ⟨by linarith only [ac.1,ad.1],by linarith only [ac.2,ad.2]⟩
    have Aw := unscale hD AC
    have Bw : |beta j L|≤W := unscale (by linarith : 1≤2*d)
      (abs_le.2 ⟨by dsimp [d]; linarith only [bys.1],by dsimp [d]; linarith only [bys.2]⟩)
    have mag : |C*alpha j L|≤(T-1)*W := by
      rw [abs_mul,abs_of_nonneg hC]
      rw [abs_mul,abs_of_nonneg (by linarith : 0≤D)] at AC
      have a := mul_le_mul_of_nonneg_right dominates (abs_nonneg (alpha j L))
      have b := mul_le_mul_of_nonneg_left AC T1.le
      nlinarith only [a,b]
    have WW : 0≤W := (abs_nonneg _).trans (cap none none)
    have T2 : 1≤T-1 := by linarith
    have G : |gamma L|≤2*W := by
      apply (le_of_mul_le_mul_right _ T1)
      have q := abs_add_le ((T-1)*gamma L-C*alpha j L) (C*alpha j L)
      rw [sub_add_cancel,abs_mul,abs_of_nonneg T1.le] at q
      have m : |(T-1)*gamma L-C*alpha j L|≤W := abs_le.mpr ⟨by linarith only [za.1],by linarith only [za.2]⟩
      nlinarith only [q,m,mag,mul_nonneg (show 0≤T-1-1 by linarith) WW]
    unfold size; linarith only [Aw,Bw,G,WW]
end
end DisjointnessDraft.Applications.HullApex
