import DisjointnessFoundations.DescendingEpochOrder

namespace DisjointnessFoundations.HardWrites

open CellProbe Execution Chronogram
open scoped ENNReal
noncomputable section

variable {w : ℕ} {F E Q Coin Ω : Type}

theorem segmentLog_append (D : DataStructure w F E Q Coin) (R : RandomTape Ω Coin)
    (seed : Ω) (t : ℕ) (m mid : Memory w) (xs ys : List E) (c : ℕ)
    (ok : insertAll D R seed t m xs = some (mid,c)) :
    segmentLog D R seed t m (xs++ys) = segmentLog D R seed t m xs ++
      segmentLog D R seed (t+xs.length) mid ys := by
  induction xs generalizing t m c with
  | nil =>
    cases ok
    simp [segmentLog]
  | cons x xs ih =>
    cases hx : insertOne D (R.insertion t seed) x m with
    | none => simp [insertAll,hx] at ok
    | some p =>
      rcases p with ⟨next,b⟩
      cases ht : insertAll D R seed (t+1) next xs with
      | none => simp [insertAll,hx,ht] at ok
      | some q =>
        rcases q with ⟨last,d⟩
        simp [insertAll,hx,ht] at ok
        obtain ⟨rfl,rfl⟩ := ok
        have idx : t+1+xs.length = t+(x::xs).length := by simp; omega
        simp only [List.cons_append,segmentLog,hx,ih _ _ _ ht,idx,List.append_assoc]

abbrev Group (ℓ w : ℕ) := Fin ℓ × Log w

end
end DisjointnessFoundations.HardWrites
