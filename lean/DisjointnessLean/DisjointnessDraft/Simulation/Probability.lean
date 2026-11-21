import DisjointnessDraft.Simulation.Game
import DisjointnessFoundations.BernoulliTailEstimates
import DisjointnessFoundations.IndependentMaskMeasure

/-! Independent Bernoulli cells cover a *fixed* distinct probe set with
exact probability p^k. Capping the packet removes at most a Chernoff tail,
even though the cap and the cover use the same sample. -/
namespace DisjointnessDraft.PhysicalProtocol
open DisjointnessFoundations FiniteSampling ProtocolInformation VerifierLaw MeasureTheory Real Finset
open scoped BigOperators
open Classical
noncomputable section

def chance (r : SamplingRate) (P : (Fin n → Bool) → Prop) :=
  ∑ b : Fin n → Bool, if P b then bitWeight r b else 0

theorem chance_measure (r : SamplingRate) (P : (Fin n → Bool) → Prop) :
    (masks r n).real {b | P b} = chance r P := by
  rw [masks,pmf_real]
  rfl

theorem chance_cover (r : SamplingRate) (S : Finset (Fin n)) :
    chance r (fun b => ∀ a∈S,b a=true) = r.p^S.card := by
  let d (a : Fin n) (b : Bool) : ℝ := if a∈S ∧ b=false then 0 else if b then r.p else 1-r.p
  have term (bits : Fin n → Bool) : (if ∀ a∈S,bits a=true then bitWeight r bits else 0) =
      ∏ i, d i (bits i) := by
    by_cases h : ∀ a∈S,bits a=true
    · rw [if_pos h]
      apply Finset.prod_congr rfl
      intro a _
      by_cases ha : a∈S <;> simp [d,ha,h]
    · rw [if_neg h]
      push_neg at h
      obtain ⟨a,ha,hb⟩ := h
      exact (Finset.prod_eq_zero (Finset.mem_univ a) (by simp [d,ha,hb])).symm
  have entry (a : Fin n) : (∑ b : Bool,d a b) = if a∈S then r.p else 1 := by
    by_cases ha : a∈S <;> simp [Fintype.sum_bool,d,ha]
  calc chance r (fun bits : Fin n → Bool => ∀a∈S,bits a=true) = ∑ bits : Fin n → Bool, ∏ i,d i (bits i) := by
         unfold chance; apply Finset.sum_congr rfl
         intro z _
         apply Eq.trans _ (term z)
         exact congrArg (fun inst => @ite ℝ (∀ a∈S,z a=true) inst (bitWeight r z) 0) (Subsingleton.elim _ _)
       _ = ∏ a, ∑ b,d a b := (Fintype.prod_sum d).symm
       _ = _ := by simp_rw [entry]; rw [Fintype.prod_ite_mem]; simp

theorem chance_cap (r : SamplingRate) (S : Finset (Fin n)) (K : ℕ) (small : S.card≤K) :
    chance r (fun bits => ⌊2*r.p*K⌋₊ < (S.filter (fun a => bits a)).card) ≤ exp (-(r.p*K)/3) := by
  let C := fun a : Fin n => decide (a∈S)
  have population : Acceptance.population C = S.card := by
    unfold Acceptance.population
    simp only [C,decide_eq_true_eq]
    rw [←Finset.sum_filter]
    simp
  have card (bits : Fin n → Bool) : Acceptance.sampledCount C (List.ofFn bits) =
      (S.filter (fun a => bits a)).card := by
    unfold Acceptance.sampledCount
    simp only [C,List.getElem?_ofFn,Fin.is_lt,dif_pos,decide_eq_true_eq,
      Option.some.injEq,Fin.eta]
    rw [←Finset.sum_filter]
    simp only [Finset.sum_const,smul_eq_mul,mul_one]
    congr 1
    ext a
    simp
  have tail := Acceptance.sample_cap_tail r n C K (by rw [population]; exact_mod_cast small)
  rw [bitMean_eq] at tail
  convert tail using 1
  apply Finset.sum_congr rfl
  intro bits _
  rw [card]
  have t : 0≤2*r.p*K := mul_nonneg (mul_nonneg (by norm_num) r.positive.le) (Nat.cast_nonneg _)
  by_cases h : 2*r.p*K < ((S.filter (fun a => bits a)).card:ℝ)
  · have hn := (Nat.floor_lt t).mpr h
    simp [chance,h,hn]
  · have hn : ¬⌊2*r.p*K⌋₊ < (S.filter (fun a => bits a)).card := fun z => h ((Nat.floor_lt t).mp z)
    simp [chance,h,hn]

theorem chance_difference (r : SamplingRate) (P Bad Good : (Fin n→Bool) → Prop)
    (accept : ∀ b,P b → ¬Bad b → Good b) :
    chance r P - chance r Bad ≤ chance r Good := by
  unfold chance
  rw [←Finset.sum_sub_distrib]
  apply Finset.sum_le_sum
  intro b _
  have pos := bitWeight_nonneg r b
  by_cases p : P b <;> by_cases c : Bad b <;> by_cases g : Good b <;> simp_all

namespace Snapshot
variable {m N s w ecap lcap : ℕ} {W O : Type} (S : Snapshot m N s w ecap lcap W O)

theorem point_mass (r : SamplingRate) (fuel : ℕ) (f : Families m W) (x : Information.Layer N s)
    (o : O) (q : Fin m) (yes : (S.actual fuel f x o q).answer = some true) :
    r.p ^ (S.required fuel f x o q).card - exp (-(r.p*ecap)/3) ≤
      chance r (fun b => (S.game ⌊2*r.p*ecap⌋₊ fuel).accepted q (f,x,o,b)=true) := by
  let needed := fun b : Cell w → Bool => ∀ a∈S.required fuel f x o q,b a=true
  let abort := fun b : Cell w → Bool => ⌊2*r.p*ecap⌋₊ < (S.touchedBits f x o b).card
  have bound := chance_difference r needed abort _ (fun b cover good =>
    S.success f x o q b _ fuel (Nat.le_of_not_gt good) cover yes)
  have c := chance_cover r (S.required fuel f x o q)
  have e : (S.early f x o).card≤ecap := by
    have p := (S.advice f x o).1.property
    simpa [advice] using p
  have small := chance_cap r (S.early f x o) ecap e
  exact (sub_le_sub (le_of_eq c.symm) small).trans bound

end Snapshot
end
end DisjointnessDraft.PhysicalProtocol
