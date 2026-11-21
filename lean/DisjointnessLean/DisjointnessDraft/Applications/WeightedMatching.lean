import DisjointnessDraft.Applications.WeightedWalk
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Fintype.Option
import Mathlib.Data.Fintype.BigOperators
import Mathlib.GroupTheory.Perm.Basic
import Mathlib.Tactic.Positivity

/-! Vertex splitting and complementary edge weights. A source-to-sink path
gives a perfect matching via successive swaps. A shortest-path potential
bounds all perfect matchings by summing the dual inequalities. Smaller
matchings lose at least one full diagonal edge. -/
namespace DisjointnessDraft.Applications.WeightedMatching
open WeightedWalk Finset Classical
open scoped BigOperators
noncomputable section
variable {V : Type} [Fintype V] [DecidableEq V] (E : V → ℤ → V → Prop)
def allowed (s t : V) : Option V → ℤ → Option V → Prop
  | none,w,some v => v=s ∧ w=0
  | some v,w,none => v=t ∧ w=0
  | some u,w,some v => (u=v ∧ w=0) ∨ E u w v
  | _,_,_ => False

private theorem achieve (rank : V → ℤ) (inc : ∀ u k v,E u k v → rank u<rank v)
    {s t d} (w : Path E s d t) : ∃ (f : Option V ≃ Option V) (cost : Option V → ℤ),
      f none=some s ∧ f (some t)=none ∧ cost (some t)=0 ∧
      (∀ v,rank t<rank v → f (some v)=some v ∧ cost (some v)=0) ∧
      (∀ i,allowed E s t i (cost i) (f i)) ∧ ∑ i,cost i=d ∧ rank s≤rank t := by
  induction w with
  | nil =>
    refine ⟨Equiv.swap none (some s),fun _ => 0,by simp,by simp,rfl,?_,?_,by simp,le_rfl⟩
    · intro v hi
      have ne : v≠s := by intro h; subst v; omega
      simp [Equiv.swap_apply_def,ne]
    · intro i
      cases i with
      | none => simp [allowed]
      | some v => by_cases e : v=s <;> simp [allowed,Equiv.swap_apply_def,e]
  | @snoc a b d k _ edge ih =>
    obtain ⟨f,g,fs,ft,gt,upper,valid,total,start⟩ := ih
    have lt := inc _ _ _ edge
    have ba : b≠a := by intro eq; subst b; omega
    have bs : b≠s := by intro eq; subst b; omega
    obtain ⟨fb,gb⟩ := upper b lt
    let f' := f.trans (Equiv.swap none (some b))
    let g' := fun i => g i + if i=some a then k else 0
    have onA : f' (some a)=some b := by simp [f',ft]
    have onB : f' (some b)=none := by simp [f',fb]
    have away i (na : i≠some a) (nb : i≠some b) : f' i=f i := by
      have n : f i≠none := fun h => na (f.injective (h.trans ft.symm))
      have m : f i≠some b := fun h => nb (f.injective (h.trans fb.symm))
      simp [f',Equiv.swap_apply_def,n,m]
    refine ⟨f',g',(away none (by simp) (by simp)).trans fs,onB,by simp [g',gb,ba],?_,?_,?_,by omega⟩
    · intro v vb
      have ea : v≠a := by intro e; subst v; omega
      have eb : v≠b := by intro e; subst v; omega
      have hv := upper v (by omega)
      exact ⟨(away _ (by simpa) (by simpa)).trans hv.1,by simp [g',ea,hv.2]⟩
    · intro i
      by_cases ia : i=some a
      · subst i; rw [onA]; exact Or.inr (by simpa [g',gt] using edge)
      · by_cases ib : i=some b
        · subst i; rw [onB]; exact ⟨rfl,by simp [g',ba,gb]⟩
        · rw [away _ ia ib]
          have h := valid i
          have fn : f i≠none := fun e => ia (f.injective (e.trans ft.symm))
          have cost : g' i=g i := by simp [g',ia]
          rw [cost]
          cases i <;> cases v : f _ <;> simp_all [allowed]
    · simp [g',sum_add_distrib,total]

theorem dual {s t d} (w : Path E s d t) (min : ∀ k,Path E s k t → d≤k)
    (nonneg : ∀ u k v,E u k v → 0≤k) : ∃ P : V → ℤ,P s=0 ∧ P t=d ∧ ∀ u k v,E u k v → P v-P u≤k := by
  -- Retain the existing section parameters for this theorem interface.
  have _apiInstances := ((inferInstance : Fintype V), (inferInstance : DecidableEq V))
  let reach := fun v => ∃ j : ℕ,Path E s (j:ℤ) v
  let P := fun v => if h : reach v then Min.min d ((Nat.find h:ℕ):ℤ) else d
  have d0 := w.nonneg nonneg
  have rs : reach s := ⟨0,.nil _⟩
  have rt : reach t := ⟨d.toNat,by simpa [Int.toNat_of_nonneg d0] using w⟩
  have zero : Nat.find rs=0 := Nat.eq_zero_of_le_zero (Nat.find_min' _ (show Path E s ((0:ℕ):ℤ) s from .nil _))
  refine ⟨P,by simp [P,rs,zero,d0],by simp [P,rt,min_eq_left (min _ (Nat.find_spec rt))],?_⟩
  intro u k v e
  have pos := nonneg _ _ _ e
  by_cases ru : reach u
  · have p := (Nat.find_spec ru).snoc e
    have rv : reach v := ⟨Nat.find ru+k.toNat,by simpa [Int.toNat_of_nonneg pos] using p⟩
    have le : Nat.find rv ≤ Nat.find ru+k.toNat := Nat.find_min' _ (by simpa [Int.toNat_of_nonneg pos] using p)
    simp only [P,dif_pos ru,dif_pos rv,min_def]; split_ifs <;> omega
  · simp only [P,dif_neg ru]
    by_cases rv : reach v <;> simp [rv,min_def] <;> (try split_ifs) <;> omega

private theorem perfect_bound (s t : V) (f : Option V ≃ Option V) (g : Option V → ℤ)
    (valid : ∀ i,allowed E s t i (g i) (f i)) (P : V → ℤ) (bound : ∀ u k v,E u k v → P v-P u≤k) :
    P t-P s≤∑ i,g i := by
  have _apiInstance := (inferInstance : DecidableEq V)
  let left := fun i : Option V => i.elim (P s) P
  let right := fun i : Option V => i.elim (P t) P
  have h i : right (f i)-left i ≤ g i := by
    have a := valid i
    cases i with
    | none => cases e : f none with
              | none => simp [e,allowed] at a
              | some v => obtain ⟨eq,z⟩ := (show v=s ∧ g none=0 by simpa [e,allowed] using a)
                          simp [e,left,right,eq,z]
    | some u =>
      cases e : f (some u) with
      | none => obtain ⟨eq,z⟩ := (show u=t ∧ g (some u)=0 by simpa [e,allowed] using a); subst u; simp [e,left,right,z]
      | some v =>
        have a' : (u=v ∧ g (some u)=0) ∨ E u (g (some u)) v := by simpa [e,allowed] using a
        rcases a' with ⟨rfl,z⟩|arc
        · simp [e,left,right,z]
        · simpa [e,left,right] using bound _ _ _ arc
  have sum := sum_le_sum (s:=univ) (fun i _ => h i)
  rw [sum_sub_distrib,Equiv.sum_comp f right] at sum
  simpa [Fintype.sum_option,left,right] using sum

structure Matching (s t : V) where
  dom : Finset (Option V)
  target : Option V → Option V
  gap : Option V → ℤ
  injective : Set.InjOn target dom
  edges : ∀ i∈dom, allowed E s t i (gap i) (target i)
def weight {s t} (K : ℤ) (m : Matching E s t) := ∑ i∈m.dom,(K-m.gap i)

theorem maximum (rank : V → ℤ) (inc : ∀ u k v,E u k v → rank u<rank v)
    (pos : ∀ u k v,E u k v → 0≤k) {s t d K} (path : Path E s d t) (least : ∀ k,Path E s k t → d≤k) (cheap : d<K) :
    let result := (Fintype.card V+1:ℤ)*K-d
    (∃ m : Matching E s t,weight E K m=result) ∧ ∀ m : Matching E s t,weight E K m≤result := by
  intro result
  obtain ⟨f,g,_,_,_,_,ok,sum,_⟩ := achieve E rank inc path
  refine ⟨⟨⟨univ,f,g,f.injective.injOn,fun i _ => ok i⟩,?_⟩,?_⟩
  · simp [weight,sum_sub_distrib,sum,result]
  · intro m
    have total (i) (h : i∈m.dom) : 0≤m.gap i := by
      have e := m.edges i h
      have hh {i j : Option V} {k} (h : allowed E s t i k j) : 0≤k := by
        cases i <;> cases j <;> simp only [allowed] at h <;> first | contradiction | (obtain ⟨_,rfl⟩ := h; rfl)
        all_goals exact pos _ _ _ (by assumption)
      exact hh e
    by_cases full : m.dom=univ
    · have inj : Function.Injective m.target := by
        intro i j eq; exact m.injective (by simp [full]) (by simp [full]) eq
      let f := Equiv.ofBijective m.target ((Finite.injective_iff_bijective).mp inj)
      obtain ⟨P,s0,td,bound⟩ := dual E path least pos
      have cost := perfect_bound E s t f m.gap (fun i => m.edges i (by simp [full])) P bound
      rw [s0,td,sub_zero] at cost
      rw [weight,full,sum_sub_distrib]
      simp only [sum_const,card_univ,Fintype.card_option,nsmul_eq_mul,Nat.cast_add,Nat.cast_one]
      dsimp only [result]; omega
    · have missing : m.dom.card<Fintype.card (Option V) := card_lt_card (ssubset_univ_iff.mpr full)
      have card : (m.dom.card:ℤ)≤Fintype.card V := by simp only [Fintype.card_option] at missing; omega
      have kpos : 0<K := (path.nonneg pos).trans_lt cheap
      have nonneg := sum_nonneg (fun i hi => total i hi)
      unfold weight; rw [sum_sub_distrib]; simp only [sum_const,nsmul_eq_mul]
      dsimp [result]; nlinarith only [mul_le_mul_of_nonneg_right card kpos.le,nonneg,cheap]

end
end DisjointnessDraft.Applications.WeightedMatching
