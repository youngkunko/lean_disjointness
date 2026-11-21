import DisjointnessDraft.Native.Operational

namespace DisjointnessDraft.Native
open DisjointnessFoundations HardDistribution PhysicalProtocol CellProbe
open scoped ENNReal BigOperators
noncomputable section
open Classical

variable {n ℓ g w : ℕ} {Ω C : Type}
abbrev Separated (n ℓ g : ℕ) (i : Fin ℓ) := Fin n × ((Fin n → Whole ℓ g) × (Block ℓ g i × Outside g i))

def separate (i : Fin ℓ) : Draw n ℓ g ≃ Separated n ℓ g i :=
  Equiv.prodCongr (Equiv.refl _) (Equiv.prodCongr (Equiv.refl _) (split g i))

theorem mean_mono {A : Type*} [Fintype A] {f g : A → ℝ} (h : ∀ x,f x≤g x) : mean f≤mean g :=
  div_le_div_of_nonneg_right (Finset.sum_le_sum (fun x _ => h x)) (Nat.cast_nonneg _)

def yes (fit : occupied ℓ g≤n) (z : Draw n ℓ g) := answer (rows fit z.2.1) (updates fit z.2.2) z.1=true

theorem mass (hl : 2≤ℓ) (hg : 0<g) (hn : 0<n) (fit : occupied ℓ g≤n) :
    (1/4:ℝ) ≤ mean (fun z : Draw n ℓ g => if yes fit z then 1 else 0) := by
  letI (i : Fin ℓ) : Nonempty (Block ℓ g i) := layer_nonempty (by omega) hg i
  letI : NeZero n := ⟨hn.ne'⟩
  let f (q : Fin n) (p : (Fin n → Whole ℓ g) × Whole ℓ g) : ℝ := if yes fit (q,p) then 1 else 0
  rw [mean_prod (fun q p => f q p),←mean_const (α:=Fin n) (1/4:ℝ)]
  apply mean_mono; intro q
  have eq := mean_equiv (Equiv.prodComm (Whole ℓ g) (Fin n → Whole ℓ g)) (f q)
  rw [←eq,←mean_const (α:=Whole ℓ g) (1/4:ℝ)]
  change _ ≤ mean (fun p : Whole ℓ g × (Fin n → Whole ℓ g) => f q (p.2,p.1))
  rw [mean_prod (fun x F => f q (F,x))]
  apply mean_mono
  intro x
  apply (true_frequency hl hg fit x q).trans
  apply mean_mono; intro F
  by_cases h : answer (rows fit F) (updates fit x) q=true <;> simp [f,yes,h]

theorem enough_mass (hl : 2≤ℓ) (hg : 0<g) (hn : 0<n) (fit : occupied ℓ g≤n)
    (D : Machine n w C) (R : RandomTape Ω C) (a : Ω) {tq : ℝ} (qp : 0<tq)
    (cheap : mean (fun z : Draw n ℓ g => (reads fit D R a z:ℝ))≤tq) :
    (1/8:ℝ) ≤ mean (fun z : Draw n ℓ g => if yes fit z ∧ reads fit D R a z≤⌊8*tq⌋₊ then 1 else 0) := by
  let c := fun z : Draw n ℓ g => reads fit D R a z
  let f := fun z : Draw n ℓ g => if yes fit z then (1:ℝ) else 0
  let ok := fun z : Draw n ℓ g => if yes fit z ∧ c z≤⌊8*tq⌋₊ then (1:ℝ) else 0
  have point (z : Draw n ℓ g) : f z ≤ ok z+(c z:ℝ)/(8*tq) := by
    by_cases h : yes fit z
    · by_cases k : c z≤⌊8*tq⌋₊
      · simp [f,ok,h,k,div_nonneg (Nat.cast_nonneg _) (by positivity : 0≤8*tq)]
      · have k' : 8*tq<(c z:ℝ) := (Nat.floor_lt (by positivity)).mp (lt_of_not_ge k)
        simp only [f,ok,h,true_and,k,ite_false,ite_true,zero_add]
        exact (one_le_div (by positivity)).mpr k'.le
    · simp [f,ok,h,div_nonneg (Nat.cast_nonneg _) (by positivity : 0≤8*tq)]
  have lin : mean (fun z => ok z+(c z:ℝ)/(8*tq))=mean ok +mean (fun z => (c z:ℝ))/(8*tq) := by
    unfold mean; rw [Finset.sum_add_distrib,←Finset.sum_div,add_div]; ring
  have fr := (mass hl hg hn fit).trans (mean_mono point)
  rw [lin] at fr
  have cap : mean (fun z => (c z:ℝ))/(8*tq)≤1/8 := (div_le_iff₀ (by positivity)).mpr (by linarith [cheap])
  change 1/8≤mean ok; linarith

theorem snapshot_mass (hl : 2≤ℓ) (hg : 2≤g) (hn : 0<n) (fit : occupied ℓ g≤n)
    (D : Machine n w C) (R : RandomTape Ω C) (a : Ω) {tu : ℕ} (hu : WorstUpdate D R (tu:ℝ≥0∞))
    (hz : FreshCorrect D R) {tq : ℝ} (qp : 0<tq) (i : Fin ℓ)
    (cheap : mean (fun z : Draw n ℓ g => (reads fit D R a z:ℝ))≤tq) :
    (1/8:ℝ) ≤ mean (fun v : Separated n ℓ g i => if ((snapshot fit hg D R hu a i).actual
      ⌊8*tq⌋₊ v.2.1 v.2.2.1 v.2.2.2 v.1).answer=some true then 1 else 0) := by
  let S := snapshot fit hg D R hu a i
  let ind (v : Separated n ℓ g i) := if (S.actual ⌊8*tq⌋₊ v.2.1 v.2.2.1 v.2.2.2 v.1).answer=some true then (1:ℝ) else 0
  change _≤mean ind
  rw [←mean_equiv (separate i) ind]
  apply (enough_mass hl (by omega) hn fit D R a qp cheap).trans
  apply mean_mono
  rintro ⟨q,F,x⟩
  have iv : join i ((split g i x).1) ((split g i x).2)=x := (split g i).symm_apply_apply x
  by_cases ok : yes fit (q,F,x) ∧ reads fit D R a (q,F,x)≤⌊8*tq⌋₊
  · have v := under_cap fit hg D R hu a hz i F ((split g i x).1) ((split g i x).2) q ⌊8*tq⌋₊ (by simpa only [iv] using ok.2)
    rw [iv,show answer (rows fit F) (updates fit x) q=true from ok.1] at v
    change (if _ then (1:ℝ) else 0) ≤ if (S.actual _ F _ _ q).answer=some true then 1 else 0
    change (if yes fit (q,F,x) ∧ reads fit D R a (q,F,x)≤⌊8*tq⌋₊ then (1:ℝ) else 0) ≤
      if ((snapshot fit hg D R hu a i).actual ⌊8*tq⌋₊ F ((split g i x).1) ((split g i x).2) q).answer=some true then 1 else 0
    rw [if_pos ok,if_pos v]
  · rw [if_neg ok]; unfold Function.comp ind; split <;> norm_num

end
end DisjointnessDraft.Native
