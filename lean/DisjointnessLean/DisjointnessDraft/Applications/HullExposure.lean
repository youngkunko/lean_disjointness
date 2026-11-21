import DisjointnessDraft.Applications.HullAngles
import Mathlib.Analysis.Normed.Operator.ContinuousLinearMap

/-! Every point declared visible by the finite selector classification has a
quantitatively separating linear functional. The margins include arbitrary
independent perturbations in each of the three coordinates. -/
namespace DisjointnessDraft.Applications.HullExposure
open Hull HullConfig HullAngles Real Finset Classical
noncomputable section
inductive Form (n : ℕ) where | level (h : ℤ) (j : Fin n) | blocker (j : Fin n) | apex (s : ℤ)
  deriving DecidableEq
def shape {n} : Label n → Form n
  | .guard i j => .level (2*(i.val:ℤ)+1) j
  | .datum i j => .level (2*((i.val:ℤ)+1)) j
  | .block j => .blocker j
  | .sel a => .apex (2*(a.val:ℤ)+1)
def coordForm {n} : Form n → Point
  | .level h j => column j (radius n-(h:ℝ)^2) h
  | .blocker j => column j (radius n-1) (height n+1)
  | .apex s => ![0,0,selector (radius n) s]
theorem represents {n} (v : Label n) : coords n v=coordForm (shape v) := by
  cases v <;> simp [coords,coordForm,shape]

private theorem inj {n} : Function.Injective (@shape n) := by
  intro u v eq
  cases u <;> cases v <;> simp_all [shape] <;> omega
def small {n} (f : Form n) := match f with
  | .level h _ | .apex h => (1≤h ∧ h≤2*(n:ℤ)+1)
  | .blocker _ => True
private theorem bounded {n} (v : Label n) : small (shape v) := by
  cases v with
  | guard i j => have := i.isLt; simp [small,shape]; omega
  | datum i j => have := i.isLt; simp [small,shape]; omega
  | block => trivial
  | sel a => have := a.isLt; simp [small,shape]; omega

def plane {n} (j : Fin n) (b : ℝ) : Point →L[ℝ] ℝ :=
  cos (angle j) • ContinuousLinearMap.proj (R:=ℝ) 0 +
  sin (angle j) • ContinuousLinearMap.proj (R:=ℝ) 1 + b • ContinuousLinearMap.proj (R:=ℝ) 2
def zplane : Point →L[ℝ] ℝ := ContinuousLinearMap.proj (R:=ℝ) 2

private theorem eval_col {n} (j k : Fin n) (b r h : ℝ) :
    plane j b (column k r h)=r*dot j k+b*h := by
  simp [plane,column,HullAngles.dot,Real.cos_sub]; ring
private theorem eval_apex {n} (j : Fin n) (s b : ℝ) :
    plane j b ![0,0,s]=b*s := by simp [plane]
private theorem self_dot {n} (j : Fin n) : dot j j=1 := by simp [dot]
private theorem dot_le {n} (j k : Fin n) : dot j k≤1 := cos_le_one _
private theorem num {n : ℕ} (n5 : 5≤n) : (5:ℝ)≤n := by exact_mod_cast n5
private theorem bounds_real {n : ℕ} {h : ℤ} (r : 1≤h ∧ h≤2*(n:ℤ)+1) : (1:ℝ)≤h ∧ (h:ℝ)≤height n := by
  dsimp [height]; constructor <;> exact_mod_cast (by omega : _)
private theorem radius_ok {n : ℕ} {h : ℝ} (n5 : 5≤n) (h1 : 1≤h) (hH : h≤height n) :
    radius n/2≤radius n-h^2 := by
  have a := (parameters (num n5)).2
  nlinarith only [a,mul_nonneg (sub_nonneg.mpr hH) (show 0≤height n+h by linarith)]
private theorem plane_level {n : ℕ} (j : Fin n) (h z : ℤ) (k : Fin n) (n5 : 5≤n)
    (zrange : 1≤z ∧ z≤2*(n:ℤ)+1) (ne : h≠z ∨ j≠k) :
    1/2 ≤ plane j (2*(h:ℝ)-1/2) (coordForm (.level h j))-
      plane j (2*(h:ℝ)-1/2) (coordForm (.level z k)) := by
  obtain ⟨z1,zH⟩ := bounds_real zrange
  have r := radius_ok n5 z1 zH
  have raw := numbers (num n5)
  simp only [coordForm,eval_col,self_dot]
  change _≤value (radius n) h h 1-value (radius n) h z (dot j k)
  rw [level_deficit]
  by_cases e : h=z
  · subst h
    have a := angular n5 (ne.resolve_left (by tauto))
    have p := mul_le_mul_of_nonneg_left a (show 0≤radius n-(z:ℝ)^2 by linarith [raw.1])
    have q := mul_le_mul_of_nonneg_right r (show 0≤8/(n:ℝ)^2 by positivity)
    linarith [raw.2.2.2.1]
  · have p := mul_nonneg (show 0≤radius n-(z:ℝ)^2 by linarith [raw.1]) (sub_nonneg.mpr (dot_le j k))
    linarith [integer_gap h z e]

private theorem base_gap {n : ℕ} (n5 : 5≤n) (j : Fin n) (v : Form n) (range : small v)
    (ne : v≠.level 1 j) : 1/2≤plane j (-1) (coordForm (.level 1 j))-plane j (-1) (coordForm v) := by
  have raw := numbers (num n5)
  cases v with
  | level z k =>
    obtain ⟨z1,zH⟩ := bounds_real range
    have r := radius_ok n5 z1 zH
    simp only [coordForm,eval_col,self_dot,Int.cast_one,one_pow,mul_one,neg_mul,one_mul]
    have score := mul_nonneg (show 0≤radius n-(z:ℝ)^2 by linarith [raw.1]) (sub_nonneg.mpr (dot_le j k))
    by_cases eq : z=1
    · subst z
      have neq : j≠k := fun h => ne (by rw [h])
      have g := angular n5 neq
      have hh := mul_le_mul_of_nonneg_right (show radius n/2≤radius n-1 by linarith [raw.1]) (show 0≤8/(n:ℝ)^2 by positivity)
      have gg := mul_le_mul_of_nonneg_left g (show 0≤radius n-1 by linarith [raw.1])
      norm_num at *; linarith [raw.2.2.2.1]
    · have z2 : (2:ℝ)≤z := by exact_mod_cast (show 2≤z by dsimp [small] at range; omega)
      nlinarith only [score,z2,sq_nonneg ((z:ℝ)-1)]
  | blocker k =>
    simp [coordForm,eval_col,self_dot]
    have h := mul_le_mul_of_nonneg_left (dot_le j k) (show 0≤radius n-1 by linarith [raw.1])
    unfold height; nlinarith only [h,num n5]
  | apex s =>
    obtain ⟨s1,sH⟩ := bounds_real range
    have z := selector_order (R:=radius n) s1 sH le_rfl (parameters (num n5)).2
    simp [coordForm,eval_col,eval_apex,self_dot]; linarith [raw.1,raw.2.1]

private theorem blocker_gap {n : ℕ} (n5 : 5≤n) (j : Fin n) (v : Form n) (range : small v)
    (ne : v≠.blocker j) : 1/2≤plane j (1/2) (coordForm (.blocker j))-plane j (1/2) (coordForm v) := by
  have raw := numbers (num n5)
  cases v with
  | level z k =>
    obtain ⟨z1,zH⟩ := bounds_real range
    have r := radius_ok n5 z1 zH
    have score := mul_nonneg (show 0≤radius n-(z:ℝ)^2 by linarith [raw.1]) (sub_nonneg.mpr (dot_le j k))
    simp [coordForm,eval_col,self_dot]
    nlinarith only [score,z1,zH,sq_nonneg ((z:ℝ)-1)]
  | blocker k =>
    have neq : j≠k := fun h => ne (by rw [h])
    have g := angular n5 neq
    have gg := mul_le_mul_of_nonneg_left g (show 0≤radius n-1 by linarith [raw.1])
    have hh := mul_le_mul_of_nonneg_right (show radius n/2≤radius n-1 by linarith [raw.1]) (show 0≤8/(n:ℝ)^2 by positivity)
    simp [coordForm,eval_col,self_dot]; linarith [raw.2.2.2.1]
  | apex s =>
    obtain ⟨s1,sH⟩ := bounds_real range
    have z := selector_order (R:=radius n) (H:=height n) (s:=1) le_rfl s1 sH (parameters (num n5)).2
    simp [coordForm,eval_col,eval_apex,self_dot]
    have zz : selector (radius n) s≤(radius n+1)/2 := by simpa only [selector,one_pow,mul_one] using z
    linarith [raw.1]

def choice {n} (v : Label n) : Point →L[ℝ] ℝ :=
  match shape v with
  | .level h j => plane j (if h=1 then -1 else 2*(h:ℝ)-1/2)
  | .blocker j => plane j (1/2)
  | .apex _ => zplane

private theorem present_block {n} (S : Family n) (X : Finset (Fin n)) (T : Finset (Fin (n+1))) (u : Label n)
    (m : u∈present S X T) {k} (e : shape u=.blocker k) : k∈X := by
  cases u <;> simp_all [shape,present]
private theorem present_apex {n} (S : Family n) (X : Finset (Fin n)) (T : Finset (Fin (n+1))) (u : Label n)
    (m : u∈present S X T) {s} (e : shape u=.apex s) : ∃ a∈T,s=2*(a.val:ℤ)+1 := by
  cases u <;> simp_all [shape,present]
  aesop

private theorem regular {n : ℕ} (S : Family n) (X : Finset (Fin n)) (T : Finset (Fin (n+1))) (n5 : 5≤n)
    (v : Label n) {h j} (shapev : shape v=.level h j) (block : j∉X)
    (cut : ∀ a∈T,h≤2*(a.val:ℤ)+1) (u : Label n) (mu : u∈present S X T) (ne : u≠v) :
    1/2≤plane j (2*(h:ℝ)-1/2) (coords n v)-plane j (2*(h:ℝ)-1/2) (coords n u) := by
  have hv := bounded v; rw [shapev] at hv
  obtain ⟨h1,hH⟩ := bounds_real hv
  have hu := bounded u
  rw [represents,represents,shapev]
  cases eu : shape u with
  | level z k =>
    rw [eu] at hu
    apply plane_level j h z k n5 hu
    by_cases same : h=z
    · right; intro jk; subst z; subst k; exact ne (inj (eu.trans shapev.symm))
    · exact Or.inl same
  | blocker k =>
    have neq : j≠k := fun eq => block (eq ▸ present_block S X T u mu eu)
    simpa only [value,coordForm,eval_col,self_dot] using foreign_block (h:=h) (num n5) hH (angular n5 neq)
  | apex s =>
    obtain ⟨a,atop,rfl⟩ := present_apex S X T u mu eu
    have ca : (h:ℝ)≤((2*(a.val:ℤ)+1:ℤ):ℝ) := by exact_mod_cast cut a atop
    rw [eu] at hu
    simpa only [value,coordForm,eval_col,self_dot,eval_apex] using level_selector (num n5) h1 ca (bounds_real hu).2

theorem visible_gap {n : ℕ} (n5 : 5≤n) (S : Family n) (X : Finset (Fin n)) (T : Finset (Fin (n+1)))
    (v : Label n) (mv : v∈visible S X T) (u : Label n) (mu : u∈present S X T) (ne : u≠v) :
    1/2≤choice v (coords n v)-choice v (coords n u) := by
  have distinct : shape u≠shape v := fun eq => ne (inj eq)
  cases v with
  | guard i j =>
    simp only [visible,mem_filter,mem_univ,true_and] at mv
    rcases mv with base|⟨block,live⟩
    · have eq : shape (.guard i j)=.level 1 j := by simp [shape,base]
      rw [eq] at distinct
      simpa only [choice,eq,if_pos rfl,represents,eq] using base_gap n5 j (shape u) (bounded u) distinct
    · by_cases base : i.val=0
      · have eq : shape (.guard i j)=.level 1 j := by simp [shape,base]
        rw [eq] at distinct
        simpa only [choice,eq,if_pos rfl,represents,eq] using base_gap n5 j (shape u) (bounded u) distinct
      · have nb : 2*(i.val:ℤ)+1≠1 := by omega
        exact (show 1/2≤plane j (if 2*(i.val:ℤ)+1=1 then -1 else 2*((2*(i.val:ℤ)+1:ℤ):ℝ)-1/2) _ -
             plane j (if 2*(i.val:ℤ)+1=1 then -1 else 2*((2*(i.val:ℤ)+1:ℤ):ℝ)-1/2) _ by
          rw [if_neg nb]; exact regular S X T n5 _ rfl block (fun a ha => by have h := live a ha; omega) u mu ne)
  | datum i j =>
    simp only [visible,mem_filter,mem_univ,true_and] at mv
    have nb : 2*((i.val:ℤ)+1)≠1 := by omega
    simp only [choice,shape,if_neg nb]
    exact regular S X T n5 _ rfl mv.2.1 (fun a ha => by have h := mv.2.2 a ha; omega) u mu ne
  | block j => simpa only [choice,represents,shape] using blocker_gap n5 j (shape u) (bounded u) distinct
  | sel a =>
    simp only [visible,mem_filter,mem_univ,true_and] at mv
    have sr := bounds_real (bounded (Label.sel a))
    have nums := numbers (num n5)
    have earliest := selector_order (R:=radius n) sr.1 sr.2 le_rfl (parameters (num n5)).2
    change 1/2≤selector (radius n) (2*(a.val:ℝ)+1)-zplane (coords n u)
    rw [represents u]
    cases h : shape u with
    | level z j =>
      have b := bounded u; rw [h] at b; have hz := (bounds_real b).2
      simp [zplane,coordForm,column]; push_cast at *; linarith [nums.2.1]
    | blocker j => simp [zplane,coordForm,column]; push_cast at *; linarith [nums.2.1]
    | apex s =>
      obtain ⟨b,bt,rfl⟩ := present_apex S X T u mu h
      have ab : a≤b := mv.2 b bt
      have neq : a≠b := by intro eq; subst b; exact distinct h
      have g : (2:ℝ)≤((2*(b.val:ℤ)+1:ℤ):ℝ)-((2*(a.val:ℤ)+1:ℤ):ℝ) := by
        have : a.val<b.val := (show a<b from lt_of_le_of_ne ab neq)
        exact_mod_cast (show (2:ℤ)≤(2*(b.val:ℤ)+1)-(2*(a.val:ℤ)+1) by omega)
      have z := stage_gap (R:=radius n) sr.1 g (bounds_real (bounded (Label.sel b))).2 (parameters (num n5)).2
      simp [coordForm,zplane]; push_cast at z; linarith

private theorem plane_variation {n} (j : Fin n) (b : ℝ) (x y : Point) (eps : ℝ) (_ep : 0≤eps)
    (move : ∀ i,|x i-y i|≤eps) : |plane j b x-plane j b y|≤(2+|b|)*eps := by
  have cos := abs_cos_le_one (angle j)
  have sin := abs_sin_le_one (angle j)
  have a := mul_le_mul cos (move 0) (abs_nonneg _) zero_le_one
  have c := mul_le_mul sin (move 1) (abs_nonneg _) zero_le_one
  have z := mul_le_mul_of_nonneg_left (move 2) (abs_nonneg b)
  calc |plane j b x-plane j b y| =
      |Real.cos (angle j)*(x 0-y 0)+Real.sin (angle j)*(x 1-y 1)+b*(x 2-y 2)| := by
        congr 1; simp [plane]; ring
    _ ≤ (|Real.cos (angle j)| * |x 0-y 0|+|Real.sin (angle j)| * |x 1-y 1|)+|b| * |x 2-y 2| := by
      simp only [←abs_mul]; exact (abs_add_le _ _).trans (add_le_add_right (abs_add_le _ _) _)
    _ ≤ _ := by linarith only [a,c,z]

private theorem variation {n} (v : Label n) (x y : Point) (eps : ℝ) (ep : 0≤eps)
    (move : ∀ i,|x i-y i|≤eps) : |choice v x-choice v y|≤(2*height n+3)*eps := by
  have npos : 1≤height n := by dsimp [height]; linarith [show (0:ℝ)≤n by positivity]
  have bound := bounded v
  unfold choice
  cases h : shape v with
  | level z j =>
    rw [h] at bound
    obtain ⟨z1,zH⟩ := bounds_real bound
    apply (plane_variation j _ x y _ ep move).trans
    apply mul_le_mul_of_nonneg_right _ ep
    by_cases e : z=1
    · simp [e]; linarith
    · rw [if_neg e,abs_of_nonneg (by linarith : 0≤2*(z:ℝ)-1/2)]; linarith
  | blocker j =>
    apply (plane_variation j _ x y _ ep move).trans
    apply mul_le_mul_of_nonneg_right _ ep; rw [abs_of_nonneg (by norm_num : (0:ℝ)≤1/2)]; linarith
  | apex s =>
    have h : eps≤(2*height n+3)*eps := by nlinarith only [mul_nonneg (show 0≤2*height n+2 by linarith) ep]
    exact (move 2).trans h

theorem visible_present {n} (S : Family n) (X : Finset (Fin n)) (T : Finset (Fin (n+1)))
    {v} (h : v∈visible S X T) : v∈present S X T := by cases v <;> simp_all [visible,present]

theorem perturbed_gap {n : ℕ} (n5 : 5≤n) (f : Label n → Point)
    (motion : ∀ v i,|f v i-coords n v i|≤1/(radius n)^2)
    (S : Family n) (X : Finset (Fin n)) (T : Finset (Fin (n+1))) (v : Label n) (mv : v∈visible S X T)
    (u : Label n) (mu : u∈present S X T) (ne : u≠v) : choice v (f u)<choice v (f v) := by
  have gap := visible_gap n5 S X T v mv u mu ne
  have ep : 0≤1/(radius n)^2 := by positivity
  have a := abs_le.mp (variation v (f u) (coords _ u) _ ep (motion u))
  have b := abs_le.mp (variation v (f v) (coords _ v) _ ep (motion v))
  have sm := (numbers (num n5)).2.2.2.2
  simp only [div_eq_mul_inv,one_mul] at a b sm
  linarith only [a.2,b.1,gap,sm]

theorem robust_vertex {n : ℕ} (n5 : 5≤n) (f : Label n → Point)
    (motion : ∀ v i,|f v i-coords n v i|≤1/(radius n)^2)
    (S : Family n) (X : Finset (Fin n)) (T : Finset (Fin (n+1))) (v : Label n) (mv : v∈visible S X T) :
    f v∈(convexHull ℝ (f '' (↑(present S X T) : Set (Label n)))).extremePoints ℝ := by
  let g := fun i : {u // u∈present S X T} => f i.val
  have eq : f '' (↑(present S X T) : Set (Label n))=Set.range g := by ext x; simp [g]
  rw [eq]
  apply HullStability.extreme_of_exposed g ⟨v,visible_present S X T mv⟩ (choice v)
  intro i neq
  exact perturbed_gap n5 f motion S X T v mv i i.property (fun e => neq (Subtype.ext e))

end
end DisjointnessDraft.Applications.HullExposure
