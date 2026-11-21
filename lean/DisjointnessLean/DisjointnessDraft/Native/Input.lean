import DisjointnessDraft.Corruption.Counting
import DisjointnessDraft.Model
import DisjointnessFoundations.EpochSizesAndAverages
import Mathlib.Data.Finset.Sort

/-! Each row and the update input independently choose a fixed-size subset in each
epoch block. Updates within an epoch are sorted in the ambient universe. -/
namespace DisjointnessDraft.Native
open DisjointnessFoundations
open scoped BigOperators
noncomputable section
open Classical

abbrev epochSize {ℓ : ℕ} (g : ℕ) (i : Fin ℓ) := HardDistribution.epochSize g i
def blockSize (ℓ g : ℕ) (i : Fin ℓ) := ℓ*(epochSize g i)^2
abbrev Block (ℓ g : ℕ) (i : Fin ℓ) := ↥(Corruption.layer (blockSize ℓ g i) (epochSize g i))
abbrev Whole (ℓ g : ℕ) := (i : Fin ℓ) → Block ℓ g i
abbrev Outside {ℓ : ℕ} (g : ℕ) (i : Fin ℓ) := (j : {j : Fin ℓ // j ≠ i}) → Block ℓ g j
abbrev Point (ℓ g : ℕ) := (i : Fin ℓ) × Fin (blockSize ℓ g i)
def occupied (ℓ g : ℕ) := ∑ i : Fin ℓ,blockSize ℓ g i

variable {ℓ g n : ℕ}

open CellProbe MeasureTheory
open scoped ENNReal

/-- Only source histories with fresh insertions are used in the native experiment. -/
def FreshCorrect {Ω C : Type} (D : Machine n w C) (R : RandomTape Ω C) :=
  ∀ a f xs q, xs.Nodup → (finalRun D R a f xs q).map Prod.fst = some (answer f xs q)
def FreshMeasurable {Ω C : Type} [MeasurableSpace Ω] (D : Machine n w C) (R : RandomTape Ω C) :=
  ∀ f xs q, xs.Nodup → Measurable (fun a => cost (finalRun D R a f xs q))
def FreshQuery {Ω C : Type} [MeasurableSpace Ω] (μ : Measure Ω) (D : Machine n w C) (R : RandomTape Ω C) (tq : ℝ) :=
  ∀ f xs q, xs.Nodup → (∫⁻ a, cost (finalRun D R a f xs q) ∂μ) ≤ ENNReal.ofReal tq

def split (g : ℕ) (i : Fin ℓ) : Whole ℓ g ≃ Block ℓ g i × Outside g i := Equiv.piSplitAt i _
def join (i : Fin ℓ) (v : Block ℓ g i) (o : Outside g i) := (split g i).symm (v,o)

theorem join_same (i : Fin ℓ) (v : Block ℓ g i) (o : Outside g i) : join i v o i = v := by simp [join,split]
theorem join_other (i j : Fin ℓ) (h : j ≠ i) (v : Block ℓ g i) (o : Outside g i) :
    join i v o j = o ⟨j,h⟩ := by simp [join,split,h]

theorem point_card (ℓ g : ℕ) : Fintype.card (Point ℓ g)=occupied ℓ g := by simp [Point,occupied]
def embed (fit : occupied ℓ g≤n) : Point ℓ g ↪ Fin n :=
  (Fintype.equivFinOfCardEq (point_card ℓ g)).toEmbedding.trans (Fin.castLEEmb fit)

def tag (i : Fin ℓ) (fit : occupied ℓ g≤n) : Fin (blockSize ℓ g i) ↪ Fin n :=
  (Function.Embedding.sigmaMk i).trans (embed fit)

def epochElements (fit : occupied ℓ g≤n) (x : Whole ℓ g) (i : Fin ℓ) : List (Fin n) :=
  ((x i).val.map (tag i fit)).sort (·≤·)

def updates (fit : occupied ℓ g≤n) (x : Whole ℓ g) : List (Fin n) :=
  (List.finRange ℓ).reverse.flatMap (epochElements fit x)

def rows (fit : occupied ℓ g≤n) (F : Fin n → Whole ℓ g) : Family n := fun q =>
  ((Finset.univ : Finset (Point ℓ g)).filter (fun z => z.2 ∈ (F q z.1).val)).map (embed fit)

@[simp] theorem epoch_length (fit : occupied ℓ g≤n) (x : Whole ℓ g) (i : Fin ℓ) :
    (epochElements fit x i).length=epochSize g i := by
  simp [epochElements,Corruption.mem_layer.mp (x i).property]

@[simp] theorem mem_epoch (fit : occupied ℓ g≤n) (x : Whole ℓ g) (i : Fin ℓ) (a : Fin n) :
    a ∈ epochElements fit x i ↔ ∃ b ∈ (x i).val, tag i fit b=a := by simp [epochElements]

theorem updates_nodup (fit : occupied ℓ g≤n) (x : Whole ℓ g) : (updates fit x).Nodup := by
  apply List.nodup_flatMap.mpr
  refine ⟨fun i _ => Finset.sort_nodup _ _,?_⟩
  have distinct : (List.finRange ℓ).reverse.Nodup := List.nodup_reverse.mpr (List.nodup_finRange ℓ)
  apply distinct.imp
  intro i j different a l r
  obtain ⟨u,_,lu⟩ := (mem_epoch fit x i a).mp l
  obtain ⟨v,_,rv⟩ := (mem_epoch fit x j a).mp r
  have eq : (⟨i,u⟩ : Point ℓ g)=⟨j,v⟩ := (embed fit).injective (lu.trans rv.symm)
  exact different (congrArg Sigma.fst eq)

theorem mem_updates (fit : occupied ℓ g≤n) (x : Whole ℓ g) (a : Fin n) :
    a ∈ updates fit x ↔ ∃ i, ∃ b ∈ (x i).val, tag i fit b=a := by simp [updates,List.mem_flatMap]

theorem mem_row (fit : occupied ℓ g≤n) (F : Fin n → Whole ℓ g) (q : Fin n) (i : Fin ℓ) (j : Fin (blockSize ℓ g i)) :
    tag i fit j∈rows fit F q ↔ j∈(F q i).val := by
  change embed fit ⟨i,j⟩ ∈ _ ↔ _
  simp [rows]

theorem correct (fit : occupied ℓ g≤n) (F : Fin n → Whole ℓ g) (x : Whole ℓ g) (q : Fin n) :
    answer (rows fit F) (updates fit x) q=true ↔ ∀ i,Disjoint (F q i).val (x i).val := by
  simp only [answer,decide_eq_true_eq]
  constructor
  · intro h i
    apply Finset.disjoint_left.mpr
    intro j hj hx
    exact h _ ((mem_updates fit x _).mpr ⟨i,j,hx,rfl⟩) ((mem_row fit F q i j).mpr hj)
  · intro h a ha hrow
    obtain ⟨i,b,hb,rfl⟩ := (mem_updates fit x a).mp ha
    exact Finset.disjoint_left.mp (h i) ((mem_row fit F q i b).mp hrow) hb

theorem layer_nonempty (hl : 0<ℓ) (hg : 0<g) (i : Fin ℓ) : Nonempty (Block ℓ g i) := by
  let s := epochSize g i
  have p : 0<s := pow_pos hg _
  have bound : s≤blockSize ℓ g i :=
    (Nat.le_mul_of_pos_right s p).trans ((by simpa [blockSize,pow_two,s] using Nat.le_mul_of_pos_left (s*s) hl))
  exact Finset.Nonempty.to_subtype (Finset.card_pos.mp (by rw [Corruption.card_layer]; exact Nat.choose_pos bound))

end
end DisjointnessDraft.Native
