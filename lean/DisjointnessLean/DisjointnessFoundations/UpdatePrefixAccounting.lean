import DisjointnessFoundations.EpochWriteLedger

namespace DisjointnessFoundations.ProtocolRun

open CellProbe Simulation Execution Chronogram
open scoped ENNReal
noncomputable section

variable {w : ℕ} {F E Q Coin Ω : Type}

def afterPrefix (D : DataStructure w F E Q Coin) (R : RandomTape Ω Coin)
    (seed : Ω) (S : F) (xs : List E) : Memory w :=
  ((prefixRun D R seed S xs).map Prod.fst).getD (D.preprocess (R.preprocess seed) S)

theorem prefix_ok (D : DataStructure w F E Q Coin) (R : RandomTape Ω Coin) {tu : ℝ≥0∞}
    (h : WorstUpdate D R tu) (seed : Ω) (S : F) (xs : List E) :
    ∃ c, prefixRun D R seed S xs = some (afterPrefix D R seed S xs,c) := by
  obtain ⟨m,c,run,_⟩ := h seed S xs
  exact ⟨c,by simp [afterPrefix,run]⟩

theorem suffix_ok (D : DataStructure w F E Q Coin) (R : RandomTape Ω Coin) {tu : ℝ≥0∞}
    (h : WorstUpdate D R tu) (seed : Ω) (S : F) (pre xs : List E) :
    ∃ c, insertAll D R seed pre.length (afterPrefix D R seed S pre) xs =
      some (afterPrefix D R seed S (pre++xs),c) := by
  obtain ⟨b,hb⟩ := prefix_ok D R h seed S pre
  obtain ⟨d,hd⟩ := prefix_ok D R h seed S (pre++xs)
  have preappend :
      prefixRun D R seed S (pre++xs) = (do
        let (m,c) ← prefixRun D R seed S pre
        let (last,e) ← insertAll D R seed pre.length m xs
        pure (last,c+e)) := by simpa [prefixRun] using run_append D R seed 0 _ pre xs
  rw [preappend,hb] at hd
  simp only [Option.bind_eq_bind,Option.some_bind] at hd
  cases he : insertAll D R seed pre.length (afterPrefix D R seed S pre) xs with
  | none => simp [he] at hd
  | some p =>
    rcases p with ⟨last,c⟩
    simp [he] at hd
    exact ⟨c,by rw [hd.1]⟩

private theorem insert_next (D : DataStructure w F E Q Coin) (R : RandomTape Ω Coin)
    {tu : ℝ≥0∞} (h : WorstUpdate D R tu) (seed : Ω) (S : F) (pre : List E) (x : E) :
    ∃ c, insertOne D (R.insertion pre.length seed) x (afterPrefix D R seed S pre) =
        some (afterPrefix D R seed S (pre++[x]),c) ∧ (c : ℝ≥0∞) ≤ tu := by
  obtain ⟨b,hb⟩ := prefix_ok D R h seed S pre
  obtain ⟨m,k,hk,pay⟩ := h seed S pre
  have eq := congrArg Prod.fst (Option.some.inj (hk.symm.trans hb))
  change m = afterPrefix D R seed S pre at eq
  subst m
  obtain ⟨d,hd⟩ := suffix_ok D R h seed S pre [x]
  have paid := pay x
  cases e : insertOne D (R.insertion pre.length seed) x (afterPrefix D R seed S pre) with
  | none => simp [insertAll,e] at hd
  | some p =>
    rcases p with ⟨next,c⟩
    simp [insertAll,e] at hd
    exact ⟨c,by rw [hd.1],by simpa [e,cost] using paid⟩

theorem segment_budget (D : DataStructure w F E Q Coin) (R : RandomTape Ω Coin)
    {tu : ℝ≥0∞} (h : WorstUpdate D R tu) (seed : Ω) (S : F) (pre xs : List E) :
    ∃ c, insertAll D R seed pre.length (afterPrefix D R seed S pre) xs =
        some (afterPrefix D R seed S (pre ++ xs),c) ∧ (c : ℝ≥0∞) ≤ xs.length * tu := by
  induction xs generalizing pre with
  | nil => exact ⟨0,by simp [insertAll],by simp⟩
  | cons x xs ih =>
    obtain ⟨c,hc,hpay⟩ := insert_next D R h seed S pre x
    obtain ⟨d,hd,dpay⟩ := ih (pre++[x])
    have eq : (pre++[x]).length = pre.length+1 := by simp
    refine ⟨c+d,?_,?_⟩
    · rw [insertAll,hc]
      simp only [Option.bind_eq_bind,Option.some_bind]
      rw [←eq,hd]
      simp [List.append_assoc]
    · simp only [Nat.cast_add,List.length_cons,Nat.cast_one,add_mul,one_mul]
      rw [add_comm (c : ℝ≥0∞)]
      exact add_le_add dpay hpay

theorem epoch_log_budget (D : DataStructure w F E Q Coin) (R : RandomTape Ω Coin)
    {tu : ℝ≥0∞} (h : WorstUpdate D R tu) (seed : Ω) (S : F)
    (pre epoch : List E) :
    ((segmentLog D R seed pre.length (afterPrefix D R seed S pre) epoch).length : ℝ≥0∞) ≤
    (epoch.length : ℝ≥0∞)*tu := by
  obtain ⟨c,hc,pay⟩ := segment_budget D R h seed S pre epoch
  have len := (segmentLog_valid D R seed _ _ _ _ _ hc).2
  exact (by exact_mod_cast len : ((segmentLog D R seed pre.length
    (afterPrefix D R seed S pre) epoch).length : ℝ≥0∞) ≤ c).trans pay

end
end DisjointnessFoundations.ProtocolRun
