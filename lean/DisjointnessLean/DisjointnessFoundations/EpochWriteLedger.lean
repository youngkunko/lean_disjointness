import DisjointnessFoundations.RecordingInterpreter
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

namespace DisjointnessFoundations.Chronogram

open CellProbe Simulation Execution
open scoped BigOperators

noncomputable section
open Classical

variable {w : ℕ} {Family Element Index Coin Ω : Type}

theorem run_append (D : DataStructure w Family Element Index Coin) (R : RandomTape Ω Coin)
    (seed : Ω) (t : ℕ) (mem : Memory w) (xs ys : List Element) :
    insertAll D R seed t mem (xs++ys) = (do
      let (mid,c) ← insertAll D R seed t mem xs
      let (last,d) ← insertAll D R seed (t+xs.length) mid ys
      return (last,c+d)) := by
  induction xs generalizing t mem with
  | nil =>
    simp only [List.nil_append,insertAll,List.length_nil,Nat.add_zero,Option.bind_eq_bind,Option.some_bind]
    cases insertAll D R seed t mem ys with
    | none => rfl
    | some p => obtain ⟨l,d⟩ := p; simp
  | cons x xs ih =>
    cases hx : insertOne D (R.insertion t seed) x mem with
    | none => simp [insertAll,hx]
    | some p =>
      obtain ⟨m,b⟩ := p
      simp only [List.cons_append,insertAll,hx,Option.bind_eq_bind,Option.some_bind]
      rw [ih]
      cases h : insertAll D R seed (t+1) m xs with
      | none => simp [h]
      | some q =>
        obtain ⟨mid,c⟩ := q
        have idx : t+1+xs.length = t+(x::xs).length := by simp; omega
        simp only [h,idx,Option.pure_def,Option.bind_eq_bind,Option.some_bind]
        cases insertAll D R seed (t+(x::xs).length) mid ys with
        | none => rfl
        | some z => obtain ⟨last,d⟩ := z; simp [Nat.add_assoc]

/-- Replay the same shortest terminating run used to execute an update. -/
def singleLog (D : DataStructure w Family Element Index Coin) (coin : Coin) (x : Element)
    (m : Memory w) : Log w :=
  if h : ∃ n, (updateRun D.updateStep n (D.startUpdate coin x) m).isSome then
    ((record D.updateStep (Nat.find h) (D.startUpdate coin x) m).map Prod.fst).getD []
  else []

theorem singleLog_valid (D : DataStructure w Family Element Index Coin) (coin : Coin)
    (x : Element) (m m' : Memory w) (c : ℕ) (h : insertOne D coin x m = some (m',c)) :
    applyWrites m (singleLog D coin x m) = m' ∧ (singleLog D coin x m).length ≤ c := by
  obtain ⟨n,hn⟩ := finish_witness _ h
  have yes : ∃ k, (updateRun D.updateStep k (D.startUpdate coin x) m).isSome := ⟨n,by simp [hn]⟩
  unfold insertOne finish at h
  rw [dif_pos yes] at h
  dsimp only at h
  rw [updateRun_records] at h
  obtain ⟨⟨l,d⟩,hl,hp⟩ := Option.map_eq_some_iff.mp h
  obtain ⟨eq,rfl⟩ := Prod.mk.inj hp
  simpa [singleLog,yes,hl] using And.intro eq (record_short _ _ _ _ hl)

def segmentLog (D : DataStructure w Family Element Index Coin) (R : RandomTape Ω Coin)
    (seed : Ω) : ℕ → Memory w → List Element → Log w
  | _,_,[] => []
  | t,m,x::xs => match insertOne D (R.insertion t seed) x m with
    | none => []
    | some (next,_) => singleLog D (R.insertion t seed) x m ++ segmentLog D R seed (t+1) next xs

theorem segmentLog_valid (D : DataStructure w Family Element Index Coin) (R : RandomTape Ω Coin)
    (seed : Ω) (t : ℕ) (m m' : Memory w) (xs : List Element) (c : ℕ)
    (h : insertAll D R seed t m xs = some (m',c)) :
    applyWrites m (segmentLog D R seed t m xs) = m' ∧ (segmentLog D R seed t m xs).length ≤ c := by
  induction xs generalizing t m c with
  | nil =>
    cases h
    exact ⟨rfl,Nat.le_refl _⟩
  | cons x xs ih =>
    cases hx : insertOne D (R.insertion t seed) x m with
    | none => simp [insertAll,hx] at h
    | some p =>
      obtain ⟨mid,b⟩ := p
      cases ht : insertAll D R seed (t+1) mid xs with
      | none => simp [insertAll,hx,ht] at h
      | some q =>
        obtain ⟨last,d⟩ := q
        simp [insertAll,hx,ht] at h
        obtain ⟨rfl,rfl⟩ := h
        have u := singleLog_valid D _ _ _ _ _ hx
        have v := ih _ _ _ ht
        simp only [segmentLog,hx,applyWrites_append,u.1,List.length_append]
        exact ⟨v.1,Nat.add_le_add u.2 v.2⟩

def lastEpoch {ℓ : ℕ} (writes : Fin ℓ → Log w) (i : Fin ℓ) (a : Word w) : Prop :=
  Written (writes i) a ∧ ∀ j, j < i → ¬ Written (writes j) a

theorem unique_last {ℓ : ℕ} {writes : Fin ℓ → Log w} {i j : Fin ℓ} {a}
    (hi : lastEpoch writes i a) (hj : lastEpoch writes j a) : i = j := by
  rcases lt_trichotomy i j with h|h|h
  · exact (hj.2 i h hi.1).elim
  · exact h
  · exact (hi.2 j h hj.1).elim

def charged {ℓ : ℕ} (writes : Fin ℓ → Log w) (i : Fin ℓ) (tr : Log w) : ℕ :=
  (tr.filter (fun p => decide (lastEpoch writes i p.1))).length

theorem total_charged {ℓ : ℕ} (writes : Fin ℓ → Log w) (tr : Log w) :
    ∑ i, charged writes i tr ≤ tr.length := by
  induction tr with
  | nil => simp [charged]
  | cons p ps ih =>
    have one : (∑ i : Fin ℓ, if lastEpoch writes i p.1 then (1 : ℕ) else 0) ≤ 1 := by
      by_cases ex : ∃ i, lastEpoch writes i p.1
      · obtain ⟨i,hi⟩ := ex
        rw [Finset.sum_eq_single i]
        · simp [hi]
        · intro j _ ne
          refine if_neg (fun hj => ne (unique_last hj hi))
        · simp
      · simp [not_exists.mp ex]
    have split (i : Fin ℓ) :
        charged writes i (p::ps) =
          (if lastEpoch writes i p.1 then 1 else 0) + charged writes i ps := by
      by_cases h : lastEpoch writes i p.1 <;> simp [charged,h,Nat.add_comm]
    rw [List.length_cons,Finset.sum_congr rfl (fun i _ => split i),Finset.sum_add_distrib,Nat.add_comm]
    exact Nat.add_le_add ih one

end
end DisjointnessFoundations.Chronogram
