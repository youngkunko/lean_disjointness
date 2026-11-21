import DisjointnessFoundations.EpochWriteLedger

namespace DisjointnessFoundations.UpdateCutoff

open CellProbe Execution
open scoped ENNReal
noncomputable section

variable {w : ℕ} {S F E J C Ω : Type}

def step (op : S → UpdateStep (Word w) S) : ℕ × S → UpdateStep (Word w) (ℕ × S)
  | (0,_) => .done
  | (b+1,s) => match op s with
    | .done => .done
    | .read a k => .read a (fun v => (b,k v))
    | .write a v k => .write a v (b,k)

theorem bounded (op : S → UpdateStep (Word w) S) (B : ℕ) (s : S) (m : Memory w) :
    ∃ v t, updateRun (step op) B (B,s) m = some (v,t) ∧ t ≤ B := by
  induction B generalizing s m with
  | zero => exact ⟨m,0,rfl,Nat.le_refl _⟩
  | succ b ih =>
    cases hs : op s with
    | done => exact ⟨m,0,by simp [updateRun,step,hs],Nat.zero_le _⟩
    | read a k =>
      obtain ⟨v,t,h,le⟩ := ih (k (m a)) m
      exact ⟨v,t+1,by simp [updateRun,step,hs,h],Nat.succ_le_succ le⟩
    | write a v k =>
      obtain ⟨u,t,h,le⟩ := ih k (Function.update m a v)
      exact ⟨u,t+1,by simp [updateRun,step,hs,h],Nat.succ_le_succ le⟩

theorem preserves (op : S → UpdateStep (Word w) S) (fuel B : ℕ) (s : S) (m v : Memory w) (t : ℕ)
    (h : updateRun op fuel s m = some (v,t)) (ht : t ≤ B) :
    updateRun (step op) B (B,s) m = some (v,t) := by
  induction fuel generalizing B s m v t with
  | zero =>
    cases hs : op s <;> simp [updateRun,hs] at h
    case done =>
      rcases h with ⟨rfl,rfl⟩
      cases B <;> simp [updateRun,step,hs]
  | succ n ih =>
    cases hs : op s with
    | done =>
      have he : m=v ∧ 0=t := by simpa [updateRun,hs] using h
      rcases he with ⟨rfl,rfl⟩
      cases B <;> simp [updateRun,step,hs]
    | read a k =>
      rw [updateRun,hs] at h
      obtain ⟨⟨u,d⟩,hd,he⟩ := Option.map_eq_some_iff.mp h
      simp only [Prod.mk.injEq] at he
      obtain ⟨rfl,rfl⟩ := he
      obtain ⟨b,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (show B ≠ 0 by omega)
      have h' := ih b _ _ _ _ hd (by omega)
      simp [updateRun,step,hs,h']
    | write a x k =>
      rw [updateRun,hs] at h
      obtain ⟨⟨u,d⟩,hd,he⟩ := Option.map_eq_some_iff.mp h
      simp only [Prod.mk.injEq] at he
      obtain ⟨rfl,rfl⟩ := he
      obtain ⟨b,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (show B ≠ 0 by omega)
      have h' := ih b _ _ _ _ hd (by omega)
      simp [updateRun,step,hs,h']

def machine (D : DataStructure w F E J C) (B : ℕ) : DataStructure w F E J C where
  UState := ℕ × D.UState
  QState := D.QState
  preprocess := D.preprocess
  startUpdate c e := (B,D.startUpdate c e)
  updateStep := step D.updateStep
  startQuery := D.startQuery
  queryStep := D.queryStep

variable (D : DataStructure w F E J C) (R : RandomTape Ω C) (B : ℕ)

theorem one (coin : C) (e : E) (m : Memory w) :
    ∃ v t, insertOne (machine D B) coin e m = some (v,t) ∧ t≤B := by
  obtain ⟨v,t,hr,ht⟩ := bounded D.updateStep B (D.startUpdate coin e) m
  refine ⟨v,t,?_,ht⟩
  unfold insertOne
  exact finish_eq_some _ (fun le ok => updateRun_mono _ le _ _ ok) hr

theorem same (coin : C) (e : E) (m v : Memory w) (t : ℕ)
    (h : insertOne D coin e m = some (v,t)) (lt : t≤B) :
    insertOne (machine D B) coin e m = some (v,t) := by
  obtain ⟨n,hr⟩ := finish_witness _ h
  unfold insertOne
  exact finish_eq_some _ (fun le ok => updateRun_mono _ le _ _ ok)
    (preserves D.updateStep n B (D.startUpdate coin e) m v t hr lt)

theorem all (a : Ω) (j : ℕ) (m : Memory w) (xs : List E) :
    ∃ v t, insertAll (machine D B) R a j m xs = some (v,t) := by
  induction xs generalizing j m with
  | nil => exact ⟨m,0,rfl⟩
  | cons x xs ih =>
    obtain ⟨mid,c,hmid,_⟩ := one D B (R.insertion j a) x m
    obtain ⟨v,t,hr⟩ := ih (j+1) mid
    exact ⟨v,c+t,by simp [insertAll,hmid,hr]⟩

theorem worst : WorstUpdate (machine D B) R B := by
  intro a f xs
  obtain ⟨m,c,h⟩ := all D R B a 0 (D.preprocess (R.preprocess a) f) xs
  refine ⟨m,c,h,fun x => ?_⟩
  obtain ⟨v,t,hr,le⟩ := one D B (R.insertion xs.length a) x m
  rw [hr]
  change (t : ℝ≥0∞) ≤ B
  exact_mod_cast le

end
end DisjointnessFoundations.UpdateCutoff
