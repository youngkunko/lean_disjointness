import DisjointnessDraft.Native.Input
import DisjointnessFoundations.SegmentWriteConcatenation
import DisjointnessFoundations.GeometricEpochEstimates

/-! The three pieces of the native hard history and their physical writes,
recovered from the same fixed tape of the candidate data structure. -/
namespace DisjointnessDraft.Native
open DisjointnessFoundations CellProbe HardProtocol ProtocolRun Chronogram Execution Simulation
open scoped ENNReal BigOperators
noncomputable section
open Classical

variable {n ℓ g w : ℕ} {Ω C : Type}
def past (i : Fin ℓ) := (order ℓ).take ((order ℓ).idxOf i)
def newer (i : Fin ℓ) := (order ℓ).drop ((order ℓ).idxOf i+1)
theorem split_order (i : Fin ℓ) : past i ++ i::newer i=order ℓ := by
  have h := List.idxOf_lt_length_iff.mpr (show i∈order ℓ by simp [order])
  have eq := List.take_append_drop ((order ℓ).idxOf i) (order ℓ)
  rwa [List.drop_eq_getElem_cons h,List.getElem_idxOf h] at eq

theorem sorted_split (i : Fin ℓ) :
    (∀ j ∈ past i, i < j) ∧ (∀ j ∈ newer i, j < i) := by
  have k := List.pairwise_append.mp (show (past i++i::newer i).Pairwise (· > ·) by
    rw [split_order]; exact List.pairwise_reverse.mpr (List.pairwise_lt_finRange ℓ))
  exact ⟨fun j h => k.2.2 j h i (List.mem_cons_self ..),(List.pairwise_cons.mp k.2.1).1⟩

variable (fit : occupied ℓ g≤n)
def before (x : Whole ℓ g) (i : Fin ℓ) := (past i).flatMap (epochElements fit x)
def after (x : Whole ℓ g) (i : Fin ℓ) := (newer i).flatMap (epochElements fit x)

theorem history_split (x : Whole ℓ g) (i : Fin ℓ) :
    (before fit x i++epochElements fit x i)++after fit x i=updates fit x := by
  simpa [before,after,updates,List.append_assoc,order] using congrArg (List.flatMap (epochElements fit x)) (split_order i)

theorem before_independent (i : Fin ℓ) (u v : Block ℓ g i) (o : Outside g i) :
    before fit (join i u o) i = before fit (join i v o) i := by
  apply List.flatMap_congr
  intro j hj
  have ne := ((sorted_split i).1 j hj).ne'
  simp [epochElements,join_other i j ne]

theorem after_length (x : Whole ℓ g) (i : Fin ℓ) : (after fit x i).length ≤ Statement.problemSize i.val g := by
  let js := newer i
  have nd : js.Nodup := (List.drop_sublist _ _).nodup (List.nodup_reverse.mpr (List.nodup_finRange ℓ))
  have sum : (after fit x i).length = ∑ j ∈ js.toFinset, epochSize g j := by
    change (js.flatMap (epochElements fit x)).length = _
    rw [List.length_flatMap,List.sum_toFinset _ nd]; simp [Function.comp_def]
  rw [sum,←Finset.sum_coe_sort]
  let e : {j // j ∈ js.toFinset} ↪ Fin i.val :=
    ⟨fun j => ⟨j.val.val,(sorted_split i).2 j (List.mem_toFinset.mp j.property)⟩,
      fun a b h => Subtype.ext (Fin.ext (congrArg (fun k : Fin i.val => k.val) h))⟩
  have h := Finset.sum_le_univ_sum_of_nonneg (s:=Finset.univ.map e) (fun j => Nat.zero_le (epochSize g j))
  rw [Finset.sum_map] at h
  simpa only [e,epochSize,HardDistribution.epochSize,Statement.problemSize] using h

theorem after_small (hg : 2≤g) (x : Whole ℓ g) (i : Fin ℓ) :
    (after fit x i).length*g^2≤2*epochSize g i :=
  (Nat.mul_le_mul_right _ (after_length fit x i)).trans (Parameters.earlier_size hg i)

variable (D : Machine n w C) (R : RandomTape Ω C) (a : Ω)
def epochLog (F : Fin n → Whole ℓ g) (x : Whole ℓ g) (i : Fin ℓ) : Log w :=
  let pre := before fit x i
  segmentLog D R a pre.length (afterPrefix D R a (rows fit F) pre) (epochElements fit x i)

def recentLog (F : Fin n → Whole ℓ g) (x : Whole ℓ g) (i : Fin ℓ) : Log w :=
  let pre := before fit x i++epochElements fit x i
  segmentLog D R a pre.length (afterPrefix D R a (rows fit F) pre) (after fit x i)

def oldMemory (F : Fin n → Whole ℓ g) (x : Whole ℓ g) (i : Fin ℓ) :=
  afterPrefix D R a (rows fit F) (before fit x i)

theorem old_independent (F : Fin n → Whole ℓ g) (i : Fin ℓ) (u v : Block ℓ g i) (o : Outside g i) :
    oldMemory fit D R a F (join i u o) i=oldMemory fit D R a F (join i v o) i := by
  unfold oldMemory; rw [before_independent fit i u v o]

variable {tu : ℕ} (hu : WorstUpdate D R (tu:ℝ≥0∞))
include hu in
theorem physical_final (F : Fin n → Whole ℓ g) (x : Whole ℓ g) (i : Fin ℓ) :
    applyWrites (applyWrites (oldMemory fit D R a F x i) (epochLog fit D R a F x i))
      (recentLog fit D R a F x i)=afterPrefix D R a (rows fit F) (updates fit x) := by
  obtain ⟨c,hc⟩ := suffix_ok D R hu a (rows fit F) (before fit x i) (epochElements fit x i)
  obtain ⟨d,hd⟩ := suffix_ok D R hu a (rows fit F) (before fit x i++epochElements fit x i) (after fit x i)
  rw [oldMemory,epochLog,recentLog,(segmentLog_valid D R a _ _ _ _ c hc).1,(segmentLog_valid D R a _ _ _ _ d hd).1,history_split]

include hu in
theorem log_lengths (F : Fin n → Whole ℓ g) (x : Whole ℓ g) (i : Fin ℓ) :
    (epochLog fit D R a F x i).length≤epochSize g i*tu ∧
    (recentLog fit D R a F x i).length≤(after fit x i).length*tu := by
  have h := epoch_log_budget D R hu a (rows fit F) (before fit x i) (epochElements fit x i)
  have r := epoch_log_budget D R hu a (rows fit F) (before fit x i++epochElements fit x i) (after fit x i)
  rw [epoch_length] at h
  exact ⟨by exact_mod_cast h,by exact_mod_cast r⟩

end
end DisjointnessDraft.Native
