import DisjointnessFoundations.FiniteRelativeEntropy
import Mathlib.Analysis.SpecialFunctions.Log.ENNRealLog
import Mathlib.MeasureTheory.Measure.Real

/-! The KL chain rule for finite probability kernels, including singular laws. -/
namespace DisjointnessDraft.Information.RelativeEntropy
open Finset Real ENNReal DisjointnessFoundations.FiniteSampling DisjointnessFoundations.InformationLoss
open scoped BigOperators ENNReal
open Classical
noncomputable section
variable {X Y : Type*} [Fintype X] [Fintype Y]

def AC (a b : InputLaw X) := ∀ x, b.weight x = 0 → a.weight x = 0

def divergence (a b : InputLaw X) : ℝ≥0∞ :=
  if AC a b then ENNReal.ofReal (klBits a.weight b.weight) else ⊤

def joint (a : InputLaw X) (p : X → InputLaw Y) : InputLaw (X × Y) where
  weight t := a.weight t.1 * (p t.1).weight t.2
  nonneg t := mul_nonneg (a.nonneg _) ((p _).nonneg _)
  total := by rw [Fintype.sum_prod_type]; simp_rw [←mul_sum,(p _).total,mul_one]; exact a.total

theorem support (a b : InputLaw X) (p q : X → InputLaw Y) :
    AC (joint a p) (joint b q) ↔ AC a b ∧ ∀ x, a.weight x ≠ 0 → AC (p x) (q x) := by
  constructor
  · intro h
    constructor
    · intro x zero
      by_contra non
      have all (y : Y) : (p x).weight y=0 :=
        (mul_eq_zero.mp (h (x,y) (by simp [joint,zero]))).resolve_left non
      have t := (p x).total
      simp [all] at t
    · intro x nx y zy
      exact (mul_eq_zero.mp (h (x,y) (by simp [joint,zy]))).resolve_left nx
  · rintro ⟨ab,h⟩ ⟨x,y⟩ e
    change b.weight x*(q x).weight y=0 at e
    change a.weight x*(p x).weight y=0
    rcases mul_eq_zero.mp e with z|z
    · exact mul_eq_zero_of_left (ab x z) _
    · by_cases az : a.weight x=0
      · simp [az]
      · simp [h x az y z]

theorem finite_chain (a b : InputLaw X) (p q : X → InputLaw Y)
    (h : AC (joint a p) (joint b q)) :
    klBits (joint a p).weight (joint b q).weight =
      klBits a.weight b.weight + ∑ x, a.weight x * klBits (p x).weight (q x).weight := by
  obtain ⟨ab,pq⟩ := (support ..).mp h
  have atom (x : X) (y : Y) :
      (joint a p).weight (x,y) * log ((joint a p).weight (x,y)/(joint b q).weight (x,y)) =
        a.weight x * log (a.weight x / b.weight x) * (p x).weight y +
        a.weight x * ((p x).weight y * log ((p x).weight y / (q x).weight y)) := by
    dsimp [joint]
    by_cases ax : a.weight x=0
    · simp [ax]
    by_cases py : (p x).weight y=0
    · simp [py]
    have bx := mt (ab x) ax
    have qy := mt (pq x ax y) py
    rw [mul_div_mul_comm,log_mul (div_ne_zero ax bx) (div_ne_zero py qy)]
    ring
  have nat_chain : kl (joint a p).weight (joint b q).weight =
      kl a.weight b.weight + ∑ x, a.weight x * kl (p x).weight (q x).weight := by
    unfold kl
    rw [Fintype.sum_prod_type]
    simp_rw [atom,sum_add_distrib,←mul_sum,(p _).total,mul_one]
  unfold klBits
  rw [nat_chain,add_div,Finset.sum_div]
  congr 1
  apply sum_congr rfl
  intro x _
  ring

theorem finite_nonneg (a b : InputLaw X) (h : AC a b) :
    0 ≤ klBits a.weight b.weight := div_nonneg (kl_nonneg a b h) (log_nonneg (by norm_num))

/-- Divergences are measured in bits. A positive atom outside the reference
support contributes infinity, and zero-mass rows contribute zero. -/
theorem chain (a b : InputLaw X) (p q : X → InputLaw Y) :
    divergence (joint a p) (joint b q) = divergence a b +
      ∑ x, ENNReal.ofReal (a.weight x) * divergence (p x) (q x) := by
  by_cases h : AC (joint a p) (joint b q)
  · obtain ⟨ab,pq⟩ := (support ..).mp h
    rw [divergence,if_pos h,finite_chain a b p q h,divergence,if_pos ab]
    have terms (x : X) : 0 ≤ a.weight x * klBits (p x).weight (q x).weight := by
      by_cases z : a.weight x=0
      · simp [z]
      · exact mul_nonneg (a.nonneg _) (finite_nonneg _ _ (pq x z))
    rw [ENNReal.ofReal_add (finite_nonneg _ _ ab) (sum_nonneg fun x _ => terms x),ENNReal.ofReal_sum_of_nonneg (fun x _ => terms x)]
    congr 1
    apply sum_congr rfl
    intro x _
    by_cases z : a.weight x=0
    · simp [z]
    · rw [ENNReal.ofReal_mul (a.nonneg _),divergence,if_pos (pq x z)]
  · rw [divergence,if_neg h]
    by_cases ab : AC a b
    · obtain ⟨x,ax,hx⟩ : ∃x,a.weight x≠0 ∧ ¬AC (p x) (q x) := by
        by_contra! no
        exact h ((support ..).mpr ⟨ab,no⟩)
      have hit : ENNReal.ofReal (a.weight x)*divergence (p x) (q x)=⊤ := by
        rw [divergence,if_neg hx,ENNReal.mul_top]
        simp [ENNReal.ofReal_ne_zero_iff.mpr (lt_of_le_of_ne (a.nonneg _) (Ne.symm ax))]
      have sumtop : (∑x,ENNReal.ofReal (a.weight x)*divergence (p x) (q x))=⊤ :=
        top_unique (hit ▸ (Finset.single_le_sum (f:=fun i => ENNReal.ofReal (a.weight i)*divergence (p i) (q i)) (fun _ _ => zero_le _) (mem_univ x)))
      simp [sumtop]
    · simp [divergence,ab]
end
end DisjointnessDraft.Information.RelativeEntropy
