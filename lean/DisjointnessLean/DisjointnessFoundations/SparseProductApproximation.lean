import DisjointnessFoundations.FiniteRelativeEntropy
import Mathlib.Analysis.Convex.Deriv
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Tactic.Positivity

namespace DisjointnessFoundations.ProductTransfer
open DisjointnessFoundations.FiniteSampling DisjointnessFoundations.InformationLoss
open Finset
noncomputable section
open Classical

variable {A : Type*} [Fintype A]

def tv (p q : InputLaw A) : ℝ := (∑ a, |p.weight a - q.weight a|) / 2

theorem tv_nonneg (p q : InputLaw A) : 0 ≤ tv p q :=
  div_nonneg (sum_nonneg fun _ _ => abs_nonneg _) (by norm_num)

theorem tv_symm (p q : InputLaw A) : tv p q = tv q p := by
  simp only [tv, abs_sub_comm]

private theorem tv_eq_imbalance (p q : InputLaw A) :
    tv p q = ∑ a ∈ univ.filter (fun a => q.weight a ≤ p.weight a),
      (p.weight a - q.weight a) := by
  let E := univ.filter (fun a => q.weight a ≤ p.weight a)
  let d := fun a => p.weight a - q.weight a
  have dp (a) (ha : a ∈ E) : 0 ≤ d a := sub_nonneg.mpr (Finset.mem_filter.mp ha).2
  have dn (a) (ha : a ∈ Eᶜ) : d a ≤ 0 := by
    have hh : ¬q.weight a ≤ p.weight a := by simpa [E] using ha
    exact sub_nonpos.mpr (le_of_lt (lt_of_not_ge hh))
  have absE : (∑ a ∈ E, |d a|) = ∑ a ∈ E, d a :=
    sum_congr rfl fun a ha => abs_of_nonneg (dp a ha)
  have absC : (∑ a ∈ Eᶜ, |d a|) = -(∑ a ∈ Eᶜ, d a) := by
    rw [← sum_neg_distrib]
    exact sum_congr rfl fun a ha => abs_of_nonpos (dn a ha)
  have zero : (∑ a, d a) = 0 := by simp [d, sum_sub_distrib, p.total, q.total]
  have tot := (sum_add_sum_compl E d).trans zero
  change (∑ a, |d a|) / 2 = _
  rw [← sum_add_sum_compl E (fun a => |d a|), absE, absC]
  linarith

/-- Binary Pinsker follows from the supporting line at the reference mass.
We retain the endpoints by expressing the binary entropy using continuous x log x. -/
private theorem binary_pin {u v : ℝ} (hvu : v ≤ u) (hu : u ≤ 1)
    (hv : 0 < v) (hv' : v < 1) :
    2 * (u-v)^2 ≤ u * Real.log (u/v) + (1-u) * Real.log ((1-u)/(1-v)) := by
  let f := fun x : ℝ =>
    x * Real.log x + (1-x) * Real.log (1-x) -
      x * Real.log v - (1-x) * Real.log (1-v) - 2 * (x-v)^2
  let df := fun x : ℝ =>
    Real.log x - Real.log (1-x) - Real.log v + Real.log (1-v) - 4 * (x-v)
  let ddf := fun x : ℝ => x⁻¹ + (1-x)⁻¹ - 4
  have hc : Continuous f := by
    dsimp only [f]
    exact (((Real.continuous_mul_log.add
      (Real.continuous_mul_log.comp (continuous_const.sub continuous_id))).sub
      (continuous_id.mul continuous_const)).sub
      ((continuous_const.sub continuous_id).mul continuous_const)).sub
      (continuous_const.mul ((continuous_id.sub continuous_const).pow 2))
  have hlin (x : ℝ) : HasDerivAt (fun t : ℝ => 1-t) (-1) x := by
    simpa using (hasDerivAt_const x (1:ℝ)).sub (hasDerivAt_id x)
  have hshift (x : ℝ) : HasDerivAt (fun t : ℝ => t-v) 1 x := by
    simpa using (hasDerivAt_id x).sub (hasDerivAt_const x v)
  have hdf (x) (hx : x ∈ Set.Ioo (0:ℝ) 1) : HasDerivAt f (df x) x := by
    have h1x : (1-x) ≠ 0 := by linarith [hx.2]
    have h := (((Real.hasDerivAt_mul_log (ne_of_gt hx.1)).add
      ((Real.hasDerivAt_mul_log h1x).comp x (hlin x))).sub
      ((hasDerivAt_id x).mul_const (Real.log v))).sub
      ((hlin x).mul_const (Real.log (1-v)))
    have h' := h.sub (((hshift x).pow 2).const_mul 2)
    convert h' using 1
    simp [f, df, Function.comp_def]
    ring
  have hddf (x) (hx : x ∈ Set.Ioo (0:ℝ) 1) : HasDerivAt df (ddf x) x := by
    have h1x : (1-x) ≠ 0 := by linarith [hx.2]
    have h := (((Real.hasDerivAt_log (ne_of_gt hx.1)).sub
      ((Real.hasDerivAt_log h1x).comp x (hlin x))).sub
      (hasDerivAt_const x (Real.log v))).add (hasDerivAt_const x (Real.log (1-v)))
    have h' := h.sub ((hshift x).const_mul 4)
    convert h' using 1
    simp [df, ddf, Function.comp_def]
  have hddf_nonneg (x) (hx : x ∈ Set.Ioo (0:ℝ) 1) : 0 ≤ ddf x := by
    have hp : 0 < x * (1-x) := mul_pos hx.1 (sub_pos.mpr hx.2)
    apply (le_of_mul_le_mul_right ?_ hp)
    have id : ddf x * (x * (1-x)) = (2*x-1)^2 := by
      dsimp only [ddf]
      field_simp [ne_of_gt hx.1, ne_of_gt (sub_pos.mpr hx.2)]
      ring
    rw [zero_mul, id]
    positivity
  have hconv : ConvexOn ℝ (Set.Icc (0:ℝ) 1) f := by
    apply convexOn_of_hasDerivWithinAt2_nonneg (f' := df) (f'' := ddf) (convex_Icc _ _) hc.continuousOn
    · rw [interior_Icc]
      exact fun x hx => (hdf x hx).hasDerivWithinAt
    · rw [interior_Icc]
      exact fun x hx => (hddf x hx).hasDerivWithinAt
    · rwa [interior_Icc]
  have zero : f v = 0 := by simp [f]
  have dfzero : df v = 0 := by simp [df]
  have hfu : 0 ≤ f u := by
    rcases eq_or_lt_of_le hvu with rfl | hlt
    · rw [zero]
    have slope_ge := hconv.le_slope_of_hasDerivAt ⟨hv.le,hv'.le⟩
      ⟨hv.le.trans hvu,hu⟩ hlt (hdf v ⟨hv,hv'⟩)
    rw [dfzero, slope_def_field, zero, sub_zero] at slope_ge
    exact (div_nonneg_iff.mp slope_ge).elim And.left fun h => False.elim ((not_le_of_gt (sub_pos.mpr hlt)) h.2)
  have logmul (x y : ℝ) (hy : y ≠ 0) :
      x * Real.log (x/y) = x * Real.log x - x * Real.log y := by
    by_cases h : x = 0
    · simp [h]
    · rw [Real.log_div h hy, mul_sub]
  rw [logmul _ _ hv.ne', logmul _ _ (sub_pos.mpr hv').ne']
  dsimp only [f] at hfu
  linarith

theorem pinsker_sq (p q : InputLaw A) (ac : ∀ a, q.weight a = 0 → p.weight a = 0) :
    2*(tv p q)^2 ≤ kl p.weight q.weight := by
  let E := univ.filter (fun a => q.weight a ≤ p.weight a)
  let u := ∑ a ∈ E, p.weight a
  let v := ∑ a ∈ E, q.weight a
  have hvu : v ≤ u := sum_le_sum (fun a ha => (mem_filter.mp ha).2)
  have cp : (∑ a ∈ Eᶜ, p.weight a) = 1-u :=
    eq_sub_of_add_eq (by rw [add_comm]; exact (sum_add_sum_compl E _).trans p.total)
  have cq : (∑ a ∈ Eᶜ, q.weight a) = 1-v :=
    eq_sub_of_add_eq (by rw [add_comm]; exact (sum_add_sum_compl E _).trans q.total)
  have hv : 0 ≤ v := sum_nonneg fun a _ => q.nonneg a
  have hu : u ≤ 1 := by
    have h := sum_nonneg (s := Eᶜ) (fun a _ => p.nonneg a)
    linarith
  have ht : tv p q = u-v := by rw [tv_eq_imbalance, sum_sub_distrib]
  have logsum (S : Finset A) :
      (∑ a ∈ S, p.weight a) * Real.log ((∑ a ∈ S, p.weight a) / (∑ a ∈ S, q.weight a))
        ≤ ∑ a ∈ S, p.weight a * Real.log (p.weight a / q.weight a) :=
    Real.sum_mul_log_div_leq (fun a _ => p.nonneg a) (fun a _ => q.nonneg a) (fun a _ => ac a)
  rcases eq_or_lt_of_le hv with hz | hpos
  · have zu : u = 0 := by
      apply sum_eq_zero
      intro a ha
      apply ac
      exact le_antisymm ((single_le_sum (fun b _ => q.nonneg b) ha).trans_eq hz.symm) (q.nonneg a)
    rw [ht, zu, ←hz]
    simpa using kl_nonneg p q ac
  · rcases eq_or_lt_of_le (hvu.trans hu) with h1 | hlt
    · have e : u = v := le_antisymm (hu.trans_eq h1.symm) hvu
      rw [ht, e, sub_self]
      simpa using kl_nonneg p q ac
    · have h := add_le_add (logsum E) (logsum Eᶜ)
      rw [cp, cq, sum_add_sum_compl] at h
      exact ht ▸ (binary_pin hvu hu hpos hlt).trans h

theorem pinsker_bits (p q : InputLaw A) (ac : ∀ a, q.weight a = 0 → p.weight a = 0) :
    tv p q ≤ Real.sqrt ((Real.log 2 / 2) * klBits p.weight q.weight) := by
  apply Real.le_sqrt_of_sq_le
  have lp : Real.log 2 ≠ 0 := (Real.log_pos (by norm_num)).ne'
  have eq : Real.log 2 / 2 * klBits p.weight q.weight = kl p.weight q.weight / 2 := by
    unfold klBits
    field_simp
    ring
  rw [eq]
  linarith only [pinsker_sq p q ac]

theorem expectation_transfer (p q : InputLaw A) (f : A → ℝ) (M : ℝ)
    (hf : ∀ a, 0 ≤ f a) (hM : ∀ a, f a ≤ M) :
    ∑ a, q.weight a * f a ≤ ∑ a, p.weight a * f a + M * tv p q := by
  let E := univ.filter (fun a => p.weight a ≤ q.weight a)
  have key :
      (∑ a, (q.weight a - p.weight a) * f a) ≤
      ∑ a, if a ∈ E then (q.weight a - p.weight a) * M else 0 := by
    apply sum_le_sum
    intro a _
    by_cases ha : a ∈ E
    · rw [if_pos ha]
      exact mul_le_mul_of_nonneg_left (hM a) (sub_nonneg.mpr (mem_filter.mp ha).2)
    · rw [if_neg ha]
      exact mul_nonpos_of_nonpos_of_nonneg
        (sub_nonpos.mpr (le_of_lt (lt_of_not_ge (by simpa [E] using ha)))) (hf a)
  rw [← sum_filter, ← sum_mul] at key
  simp only [filter_mem_eq_inter, univ_inter] at key
  rw [tv_symm p q, tv_eq_imbalance, mul_comm M]
  change _ ≤ _ + (∑ a ∈ E, (q.weight a - p.weight a)) * M
  simp_rw [sub_mul, sum_sub_distrib] at key
  rw [sum_sub_distrib]
  linarith

variable {B : Type*} [Fintype B]

def productMarginals (j : InputLaw (A × B)) : InputLaw (A × B) where
  weight p := (∑ b, j.weight (p.1,b)) * (∑ a, j.weight (a,p.2))
  nonneg p := mul_nonneg (sum_nonneg fun b _ => j.nonneg (p.1,b))
    (sum_nonneg fun a _ => j.nonneg (a,p.2))
  total := by
    have totalA := (Fintype.sum_prod_type _).symm.trans j.total
    have totalB := (Fintype.sum_prod_type_right _).symm.trans j.total
    rw [Fintype.sum_prod_type]
    simp_rw [← mul_sum, totalB, mul_one]
    exact totalA

theorem product_support (j : InputLaw (A × B)) (t : A × B)
    (h : (productMarginals j).weight t = 0) : j.weight t = 0 := by
  rcases t with ⟨a,b⟩
  rcases mul_eq_zero.mp h with h | h
  · exact le_antisymm ((single_le_sum (fun b _ => j.nonneg (a,b)) (mem_univ b)).trans_eq h)
      (j.nonneg _)
  · exact le_antisymm ((single_le_sum (fun a _ => j.nonneg (a,b)) (mem_univ a)).trans_eq h)
      (j.nonneg _)

def mutualBits (j : InputLaw (A × B)) : ℝ := klBits j.weight (productMarginals j).weight

end
end DisjointnessFoundations.ProductTransfer
