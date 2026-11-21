import DisjointnessFoundations.ProbeMachineInterface

namespace DisjointnessFoundations.Execution

open Simulation CellProbe
open scoped ENNReal

variable {w : ℕ} {Family Element Index Coin Ω : Type}

abbrev Log (w : ℕ) := List (Word w × Word w)

theorem applyWrites_append (mem : Memory w) (x y : Log w) :
    applyWrites mem (x ++ y) = applyWrites (applyWrites mem x) y := by
  induction x generalizing mem with
  | nil => rfl
  | cons p xs ih =>
    rcases p with ⟨a,v⟩
    exact ih _

def record {S : Type} (step : S → UpdateStep (Word w) S) :
    ℕ → S → Memory w → Option (Log w × ℕ)
  | fuel,s,mem => match step s with
    | .done => some ([],0)
    | .read a k => match fuel with
      | 0 => none
      | n+1 => (record step n (k (mem a)) mem).map (fun (l,c) => (l,c+1))
    | .write a v k => match fuel with
      | 0 => none
      | n+1 => (record step n k (Function.update mem a v)).map (fun (l,c) => ((a,v)::l,c+1))

theorem updateRun_records {S : Type} (step : S → UpdateStep (Word w) S)
    (fuel : ℕ) (s : S) (mem : Memory w) :
    updateRun step fuel s mem =
      (record step fuel s mem).map (fun (log,c) => (applyWrites mem log,c)) := by
  induction fuel generalizing s mem with
  | zero =>
    cases eq : step s <;> rw [updateRun,record,eq] <;> rfl
  | succ n ih =>
    cases eq : step s with
    | done => rw [updateRun,record,eq]; rfl
    | read a k =>
      rw [updateRun,record,eq]
      change (updateRun step n (k (mem a)) mem).map _ = ((record step n (k (mem a)) mem).map (fun (l,c) => (l,c+1))).map _
      rw [ih]
      cases record step n (k (mem a)) mem with
      | none => rfl
      | some p => rcases p with ⟨l,c⟩; rfl
    | write a v k =>
      rw [updateRun,record,eq]
      change (updateRun step n k (Function.update mem a v)).map _ =
        ((record step n k (Function.update mem a v)).map (fun (l,c) => ((a,v)::l,c+1))).map _
      rw [ih]
      cases record step n k (Function.update mem a v) with
      | none => rfl
      | some p =>
        rcases p with ⟨l,c⟩
        have e : Function.update mem a v = (fun x => if x=a then v else mem x) := by
          funext x
          split
          · rename_i h; subst x; simp
          · rename_i h; exact Function.update_of_ne h v mem
        change some (applyWrites (Function.update mem a v) l,c+1) =
          some (applyWrites (fun x => if x=a then v else mem x) l,c+1)
        rw [e]

theorem record_short {S : Type} (step : S → UpdateStep (Word w) S) (fuel : ℕ)
    (s : S) (m : Memory w) {log : Log w} {c : ℕ} (hr : record step fuel s m = some (log,c)) :
    log.length ≤ c := by
  induction fuel generalizing s m log c with
  | zero =>
    cases eq : step s <;> simp [record,eq] at hr
    obtain ⟨rfl,rfl⟩ := hr
    exact Nat.le_refl _
  | succ n ih =>
    cases eq : step s with
    | done =>
      rw [record,eq] at hr
      cases hr
      exact Nat.le_refl _
    | read a k =>
      rw [record,eq] at hr
      obtain ⟨⟨l,d⟩,ok,h⟩ := Option.map_eq_some_iff.mp hr
      cases h
      exact (ih _ _ ok).trans (Nat.le_succ _)
    | write a v k =>
      rw [record,eq] at hr
      obtain ⟨⟨l,d⟩,ok,h⟩ := Option.map_eq_some_iff.mp hr
      cases h
      exact Nat.succ_le_succ (ih _ _ ok)

theorem finish_witness {α : Type*} (f : ℕ → Option α) {v : α}
    (h : finish f = some v) : ∃ n, f n = some v := by
  unfold finish at h
  split at h
  · rename_i e; exact ⟨Nat.find e,h⟩
  · contradiction

theorem insertOne_writes (D : DataStructure w Family Element Index Coin) (coin : Coin)
    (x : Element) (mem finalMem : Memory w) (c : ℕ) (h : insertOne D coin x mem = some (finalMem,c)) :
    ∃ log : Log w, applyWrites mem log = finalMem ∧ log.length ≤ c := by
  obtain ⟨n,hn⟩ := finish_witness _ h
  rw [updateRun_records] at hn
  obtain ⟨⟨l,d⟩,hl,hp⟩ := Option.map_eq_some_iff.mp hn
  obtain ⟨eq,rfl⟩ := Prod.mk.inj hp
  exact ⟨l,eq,record_short _ _ _ _ hl⟩

theorem insertAll_writes (D : DataStructure w Family Element Index Coin) (R : RandomTape Ω Coin)
    (seed : Ω) (xs : List Element) (t : ℕ) (mem finalMem : Memory w) (c : ℕ)
    (h : insertAll D R seed t mem xs = some (finalMem,c)) :
    ∃ log : Log w, applyWrites mem log = finalMem ∧ log.length ≤ c := by
  induction xs generalizing t mem c with
  | nil => cases h; exact ⟨[],rfl,Nat.le_refl _⟩
  | cons x xs ih =>
    cases h₁ : insertOne D (R.insertion t seed) x mem with
    | none => simp [insertAll,h₁] at h
    | some p =>
      obtain ⟨mid,b⟩ := p
      cases h₂ : insertAll D R seed (t+1) mid xs with
      | none => simp [insertAll,h₁,h₂] at h
      | some p =>
        obtain ⟨last,d⟩ := p
        simp [insertAll,h₁,h₂] at h
        obtain ⟨rfl,rfl⟩ := h
        obtain ⟨u,hu,lu⟩ := insertOne_writes D _ _ _ _ _ h₁
        obtain ⟨v,hv,lv⟩ := ih _ _ _ h₂
        exact ⟨u++v,by rwa [applyWrites_append,hu],by simpa using Nat.add_le_add lu lv⟩

theorem epoch_and_suffix (D : DataStructure w Family Element Index Coin) (R : RandomTape Ω Coin)
    (seed : Ω) (t : ℕ) (xs ys : List Element) (base mid finalMem : Memory w) (c d : ℕ)
    (epochRun : insertAll D R seed t base xs = some (mid,c))
    (suffixRun : insertAll D R seed (t+xs.length) mid ys = some (finalMem,d)) :
    ∃ epoch later : Log w, epoch.length ≤ c ∧ later.length ≤ d ∧
      applyWrites (applyWrites base epoch) later = finalMem := by
  obtain ⟨u,hu,lu⟩ := insertAll_writes _ _ _ _ _ _ _ _ epochRun
  obtain ⟨v,hv,lv⟩ := insertAll_writes _ _ _ _ _ _ _ _ suffixRun
  exact ⟨u,v,lu,lv,by rwa [hu]⟩

end DisjointnessFoundations.Execution
