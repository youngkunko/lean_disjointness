import DisjointnessDraft.Simulation.Probability
import DisjointnessFoundations.UniformAtomWeights
import DisjointnessFoundations.IndependentMaskMeasure

/-! Average over the independent uniform rows, target layer, outside updates,
and query. A tangent to p^x proves the Jensen step without dividing by any
individual atom of the disjoint/short-query event. -/
namespace DisjointnessDraft.PhysicalProtocol
open DisjointnessFoundations HardDistribution HardIndependence FiniteSampling VerifierLaw ActualAcceptance
  MeasureTheory Real
open scoped BigOperators
open Classical
noncomputable section

private theorem avg_mono {T : Type} [Fintype T] {f g : T → ℝ} (h : ∀ z,f z≤g z) :
    mean f ≤ mean g := div_le_div_of_nonneg_right (Finset.sum_le_sum (fun z _ => h z)) (Nat.cast_nonneg _)
private theorem avg_add {T : Type} [Fintype T] (f g : T→ℝ) :
    mean (fun z => f z+g z)=mean f + mean g := by simp only [mean,Finset.sum_add_distrib,add_div]
private theorem avg_sub {T : Type} [Fintype T] (f g : T→ℝ) :
    mean (fun z => f z-g z)=mean f - mean g := by simp only [mean,Finset.sum_sub_distrib,sub_div]
private theorem avg_scale {T : Type} [Fintype T] (a : ℝ) (f : T→ℝ) :
    mean (fun z => a*f z)=a*mean f := by simp [mean,←Finset.mul_sum,mul_div_assoc]

theorem averaging {T : Type} [Fintype T] [Nonempty T] (r : SamplingRate) (tail τ : ℝ)
    (good : T → Prop) (k : T → ℕ) (prob : T → ℝ)
    (nonnegative : ∀ x, 0≤prob x) (tp : 0≤tail)
    (point : ∀ x,good x → r.p^(k x)-tail≤prob x)
    (many : 1/8 ≤ mean (fun x => if good x then (1:ℝ) else 0))
    (hits : mean (fun x => (k x:ℝ)) ≤ τ) :
    (1/8)*r.p^(8*τ)-tail ≤ mean prob := by
  let b := 8*τ
  let a := r.p^b
  let flag := fun x => if good x then (1:ℝ) else 0
  have ap : 0≤a := Real.rpow_nonneg r.positive.le _
  have lp := Real.log_nonpos r.positive.le r.le_one
  have meanPositive : 0≤mean (fun x => (k x:ℝ)) := by
    simpa only [mean_const] using (avg_mono (f:=fun _ : T => (0:ℝ))
      (g:=fun x => (k x:ℝ)) (fun x => Nat.cast_nonneg _))
  have total : 0≤τ := meanPositive.trans hits
  have small : mean (fun x => flag x*(k x:ℝ)) ≤ mean (fun x => (k x:ℝ)) := by
    apply avg_mono; intro x; by_cases h : good x <;> simp [flag,h]
  have correction : mean (fun x => flag x*(k x:ℝ)) - b*mean flag ≤ 0 := by
    have v := mul_le_mul_of_nonneg_right many total
    dsimp [b,flag] at *; linarith only [v,small,hits]
  have tangent (x : T) : a+a*log r.p*((k x:ℝ)-b) ≤ r.p^(k x) := by
    have h := mul_le_mul_of_nonneg_left (Real.add_one_le_exp (log r.p*((k x:ℝ)-b))) ap
    have eq : a * exp (log r.p*((k x:ℝ)-b)) = r.p^(k x) := by
      rw [← Real.rpow_natCast, Real.rpow_def_of_pos r.positive]
      dsimp [a]
      rw [Real.rpow_def_of_pos r.positive,←Real.exp_add]; congr 1; ring
    rw [eq] at h; linarith only [h]
  have point' (x : T) : a*flag x+(a*log r.p)*(flag x*(k x:ℝ)-b*flag x)≤prob x+tail := by
    by_cases h : good x
    · simpa [flag,h] using (show a+a*log r.p*((k x:ℝ)-b)≤prob x+tail by linarith [point x h,tangent x])
    · simp [flag,h,add_nonneg (nonnegative x) tp]
  have estimate := avg_mono point'
  simp only [avg_add,avg_sub,avg_scale,mean_const] at estimate
  have sign := mul_nonneg_of_nonpos_of_nonpos (mul_nonpos_of_nonneg_of_nonpos ap lp) correction
  have lower := mul_le_mul_of_nonneg_left many ap
  change a*(1/8) ≤ a*mean flag at lower
  change (1/8)*a-tail ≤ mean prob
  linarith only [sign,lower,estimate]

abbrev Draw (m N s : ℕ) (W O : Type) := Fin m × (Families m W × (Information.Layer N s × O))

local instance layerMeasure : MeasurableSpace (Information.Layer N s) := ⊤
local instance layerSingleton : MeasurableSingletonClass (Information.Layer N s) := ⟨fun _ => trivial⟩

private theorem uniform_section {A B : Type} [Fintype A] [MeasurableSpace A] [MeasurableSingletonClass A]
    [Fintype B] [MeasurableSpace B] [MeasurableSingletonClass B] (μ : Measure B) [IsFiniteMeasure μ]
    (E : Set (A × B)) : ((unif A).prod μ).real E = mean (fun a => μ.real (Prod.mk a ⁻¹' E)) := by
  rw [prod_event _ _ _ (Set.toFinite _).measurableSet]
  simp only [real_unif_atom,mean,←Finset.mul_sum,div_eq_inv_mul]

private theorem mean_pair {A B : Type} [Fintype A] [Fintype B] (f : A × B → ℝ) :
    mean f = mean (fun a => mean fun b => f (a,b)) := mean_prod (fun a b => f (a,b))

namespace Snapshot
variable {m N s w ecap lcap : ℕ} {W O : Type} (S : Snapshot m N s w ecap lcap W O)
variable [Fintype W] [MeasurableSpace W] [MeasurableSingletonClass W]
  [Fintype O] [MeasurableSpace O] [MeasurableSingletonClass O]

def good (fuel : ℕ) (d : Draw m N s W O) := (S.actual fuel d.2.1 d.2.2.1 d.2.2.2 d.1).answer=some true
def hits (fuel : ℕ) (d : Draw m N s W O) := (S.required fuel d.2.1 d.2.2.1 d.2.2.2 d.1).card

theorem acceptance_eq (r : SamplingRate) (limit fuel : ℕ) :
    Information.acceptance (S.game limit fuel) (unif O) (masks r (2^w)) =
      mean (fun d : Draw m N s W O => chance r (fun b => (S.game limit fuel).accepted d.1
        (d.2.1,d.2.2.1,d.2.2.2,b)=true)) := by
  classical
  simp_rw [mean_pair]
  unfold Information.acceptance Information.experiment
  simp_rw [uniform_section,←chance_measure]
  simp only [mean,Fintype.card_fin]
  rfl

theorem acceptance_lower (r : SamplingRate) (fuel : ℕ) (τ : ℝ) [Nonempty (Draw m N s W O)]
    (many : 1/8≤mean (fun d : Draw m N s W O => if S.good fuel d then (1:ℝ) else 0))
    (budget : mean (fun d : Draw m N s W O => (S.hits fuel d:ℝ))≤τ) :
    (1/8)*r.p^(8*τ)-exp (-(r.p*ecap)/3) ≤
      Information.acceptance (S.game ⌊2*r.p*ecap⌋₊ fuel) (unif O) (masks r (2^w)) := by
  rw [S.acceptance_eq]
  apply averaging r _ τ (S.good fuel) (S.hits fuel) _ _ (Real.exp_pos _).le _ many budget
  · intro d
    apply Finset.sum_nonneg; intro b _
    split <;> first | exact le_rfl | exact DisjointnessFoundations.ProtocolInformation.bitWeight_nonneg r b
  · rintro ⟨q,f,x,o⟩ good; exact S.point_mass r fuel f x o q good

end Snapshot
end
end DisjointnessDraft.PhysicalProtocol
