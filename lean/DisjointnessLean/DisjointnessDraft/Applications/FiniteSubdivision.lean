import DisjointnessDraft.Applications.PlanarPadding
import Mathlib.Data.Fintype.Sigma
import Mathlib.Data.Fintype.Sum

/-! A fixed finite subdivision has one physical vertex for each original
vertex and one for each strict integral position on an original edge.
Changing the first-edge switch never changes this address type. -/
namespace DisjointnessDraft.Applications.FiniteSubdivision
open Subdivision PlanarPadding Planarity Classical
noncomputable section
variable {V E : Type} (G : Graph V E)
abbrev Nodes := V ⊕ (Σ e : E,Fin (G.len e-1))
def withLive (live : E → Prop) : Graph V E := { G with enabled := live }
def move (live : E → Prop) : Node (withLive G live) ≃ Nodes G where
  toFun | .core v => .inl v | .inner e i => .inr ⟨e,i⟩
  invFun | .inl v => .core v | .inr ⟨e,i⟩ => .inner e i
  left_inv := by rintro (v|⟨e,i⟩) <;> rfl
  right_inv := by rintro (v|⟨e,i⟩) <;> rfl
def atNode (e : E) (k : ℕ) : Nodes G :=
  if z : k=0 then .inl (G.src e) else if h : k<G.len e then .inr ⟨e,⟨k-1,by omega⟩⟩ else .inl (G.dst e)
theorem move_at (live : E → Prop) (e : E) (k : ℕ) :
    move G live (atPos (withLive G live) e k)=atNode G e k := by
  simp only [atPos,atNode,withLive]; split_ifs <;> rfl
def Dart (live : E → Prop) (a b : Nodes G) :=
  ∃ e,∃ k : ℕ,k<G.len e ∧ (live e ∨ 0<k) ∧ a=atNode G e k ∧ b=atNode G e (k+1)

theorem dart_iff (live : E → Prop) (a b : Nodes G) :
    Dart G live a b ↔ ∃ e,∃ k : ℕ,k<G.len e ∧ (live e ∨ 0<k) ∧ a=atNode G e k ∧ b=atNode G e (k+1) := Iff.rfl

theorem unit_step (live : E → Prop) (a b : Node (withLive G live)) :
    UnitStep (withLive G live) a b ↔ Dart G live (move G live a) (move G live b) := by
  rw [dart_iff]
  constructor
  · rintro ⟨e,k,fit,on⟩; exact ⟨e,k,fit,on,move_at ..,move_at ..⟩
  · rintro ⟨e,k,fit,on,aa,bb⟩
    rw [←move_at G live] at aa bb
    obtain rfl := (move G live).injective aa; obtain rfl := (move G live).injective bb
    exact .along e k fit on

def underlying (a b : V) := ∃ e,G.src e=a ∧ G.dst e=b
def location (D : Drawing (underlying G)) : Nodes G → Plane
  | .inl v => D.point v
  | .inr ⟨e,i⟩ => interpolate (D.point (G.src e)) (D.point (G.dst e)) ((i.val+1:ℝ)/G.len e)

theorem along_position (D : Drawing (underlying G)) (e : E) (k : ℕ) (fit : k≤G.len e) :
    location G D (atNode G e k)=interpolate (D.point (G.src e)) (D.point (G.dst e)) (k/G.len e) := by
  have pos := G.positive e
  by_cases z : k=0
  · subst k; simp [atNode,location,interpolate]
  · by_cases h : k<G.len e
    · simp only [atNode,dif_neg z,dif_pos h,location]
      have same : ((k-1:ℕ):ℝ)+1=k := by exact_mod_cast (by omega : k-1+1=k)
      rw [same]
    · have endK : k=G.len e := by omega
      rw [endK]
      simp [atNode,Nat.ne_zero_of_lt pos,location,interpolate,show ((G.len e:ℕ):ℝ)≠0 by exact_mod_cast pos.ne']

theorem subsegment (D : Drawing (underlying G)) (e : E) (k : ℕ) (fit : k<G.len e) (t : ℝ) :
    interpolate (location G D (atNode G e k)) (location G D (atNode G e (k+1))) t=
      interpolate (D.point (G.src e)) (D.point (G.dst e)) ((k+t)/G.len e) := by
  rw [along_position _ _ _ _ fit.le,along_position _ _ _ _ fit]
  apply Prod.ext <;> dsimp [interpolate] <;> push_cast <;> ring

theorem interpolation_injective {a b : Plane} (ne : a≠b) : Function.Injective (interpolate a b) := by
  intro u v eq
  obtain x|y : a.1≠b.1 ∨ a.2≠b.2 := by by_contra! contra; exact ne (Prod.ext contra.1 contra.2)
  · have h := congrArg Prod.fst eq; dsimp [interpolate] at h
    exact sub_eq_zero.mp (Or.resolve_right (mul_eq_zero.mp (show (u-v)*(a.1-b.1)=0 by linarith only [h])) (sub_ne_zero.mpr x))
  · have h := congrArg Prod.snd eq; dsimp [interpolate] at h
    exact sub_eq_zero.mp (Or.resolve_right (mul_eq_zero.mp (show (u-v)*(a.2-b.2)=0 by linarith only [h])) (sub_ne_zero.mpr y))

theorem interior (e : E) (k : ℕ) (fit : k<G.len e) {t : ℝ} (zero : 0<t) (one : t≤1)
    (strict : k+1<G.len e ∨ t<1) : 0<(k+t)/(G.len e:ℝ) ∧ (k+t)/(G.len e:ℝ)<1 := by
  have pos : 0<(G.len e:ℝ) := by exact_mod_cast G.positive e
  refine ⟨div_pos (by positivity) pos,(div_lt_one pos).mpr ?_⟩
  rcases strict with left|right
  · have h : (k:ℝ)+1<G.len e := by exact_mod_cast left
    linarith
  · have h : (k:ℝ)+1≤G.len e := by exact_mod_cast fit
    linarith

private theorem inner_frac (e : E) (i : Fin (G.len e-1)) :
    0<(i.val+1:ℝ)/G.len e ∧ (i.val+1:ℝ)/G.len e<1 :=
  interior G e i.val (by have := i.isLt; omega) zero_lt_one le_rfl (Or.inl (by have := i.isLt; omega))

theorem separated (D : Drawing (underlying G)) (e : E) : D.point (G.src e)≠D.point (G.dst e) := by
  intro eq
  have bad := D.miss (show underlying G (G.src e) (G.dst e) from ⟨e,rfl,rfl⟩) (G.src e) (1/2) (by norm_num) (by norm_num)
  apply bad; rw [←eq]; apply Prod.ext <;> dsimp [interpolate] <;> ring

theorem owner (D : Drawing (underlying G)) (unique : Function.Injective (fun e => (G.src e,G.dst e)))
    (e f : E) {t s : ℝ} (ti : 0<t ∧ t<1) (si : 0<s ∧ s<1)
    (eq : interpolate (D.point (G.src e)) (D.point (G.dst e)) t=interpolate (D.point (G.src f)) (D.point (G.dst f)) s) :
    e=f ∧ t=s := by
  obtain ⟨a,b⟩ := D.apart ⟨e,rfl,rfl⟩ ⟨f,rfl,rfl⟩ t s ti.1 ti.2 si.1 si.2 eq
  obtain rfl := unique (Prod.ext a b)
  exact ⟨rfl,interpolation_injective (separated G D e) eq⟩

def drawing (D : Drawing (underlying G)) (unique : Function.Injective (fun e => (G.src e,G.dst e)))
    (live : E → Prop) : Drawing (Dart G live) where
  point := location G D
  injective := by
    rintro (u|⟨e,i⟩) (v|⟨f,j⟩) eq
    · exact congrArg Sum.inl (D.injective eq)
    · exact (D.miss ⟨f,rfl,rfl⟩ u _ (inner_frac G f j).1 (inner_frac G f j).2 eq.symm).elim
    · exact (D.miss ⟨e,rfl,rfl⟩ v _ (inner_frac G e i).1 (inner_frac G e i).2 eq).elim
    · obtain ⟨rfl,t⟩ := owner G D unique e f (inner_frac G e i) (inner_frac G f j) eq
      have pos : (G.len e:ℝ)≠0 := by exact_mod_cast (G.positive e).ne'
      have same : i=j := Fin.ext (by exact_mod_cast (add_right_cancel ((div_left_inj' pos).mp t) : (i.val:ℝ)=j.val))
      simp [same]
  miss := by
    intro a b ab z t t0 t1 eq
    obtain ⟨e,k,fit,_,rfl,rfl⟩ := (dart_iff ..).mp ab
    rw [subsegment G D e k fit] at eq
    have ti := interior G e k fit t0 t1.le (Or.inr t1)
    cases z with
    | inl v => exact D.miss ⟨e,rfl,rfl⟩ v _ ti.1 ti.2 eq
    | inr z =>
      obtain ⟨f,j⟩ := z
      obtain ⟨rfl,s⟩ := owner G D unique e f ti (inner_frac G f j) eq
      have pos : (G.len e:ℝ)≠0 := by exact_mod_cast (G.positive e).ne'
      have same := (div_left_inj' pos).mp s
      by_cases kj : k≤j
      · have le : (k:ℝ)≤j := by exact_mod_cast kj
        linarith
      · have le : (j:ℝ)+1≤k := by exact_mod_cast (by omega : j.val+1≤k)
        linarith
  apart := by
    intro a b u v ab uv t s t0 t1 s0 s1 eq
    obtain ⟨e,k,fit,_,rfl,rfl⟩ := (dart_iff ..).mp ab
    obtain ⟨f,l,fits,_,rfl,rfl⟩ := (dart_iff ..).mp uv
    rw [subsegment G D e k fit,subsegment G D f l fits] at eq
    obtain ⟨rfl,es⟩ := owner G D unique e f (interior G e k fit t0 t1.le (Or.inr t1)) (interior G f l fits s0 s1.le (Or.inr s1)) eq
    have pos : (G.len e:ℝ)≠0 := by exact_mod_cast (G.positive e).ne'
    have vals := (div_left_inj' pos).mp es
    have kl : k=l := by
      rcases lt_trichotomy k l with h|h|h
      · have le : (k:ℝ)+1≤l := by exact_mod_cast h
        linarith
      · exact h
      · have le : (l:ℝ)+1≤k := by exact_mod_cast h
        linarith
    simp [kl]

end
end DisjointnessDraft.Applications.FiniteSubdivision
