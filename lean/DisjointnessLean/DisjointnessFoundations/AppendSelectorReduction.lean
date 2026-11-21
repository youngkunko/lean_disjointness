import DisjointnessFoundations.BoundedUpdateFuel
import DisjointnessFoundations.RecodeProbeInputs

namespace DisjointnessFoundations.SingleSelector

open CellProbe MeasureTheory
open scoped ENNReal
noncomputable section
open Classical

variable {w : ℕ} {F' E J C Ω : Type}
variable (D : DataStructure w F' E J C) (R : RandomTape Ω C) (B : ℕ)

def Pays (a : Ω) (f : F') (xs : List E) : Prop :=
  ∀ (p : List E) (e : E) (s : List E), xs = p ++ e :: s →
    ∃ (m : Memory w) (c : ℕ) (v : Memory w) (t : ℕ),
      prefixRun D R a f p = some (m,c) ∧
      insertOne D (R.insertion p.length a) e m = some (v,t) ∧ t ≤ B

theorem pays_prefix (a : Ω) (f : F') (p s : List E)
    (h : Pays D R B a f (p++s)) : Pays D R B a f p := by
  intro pre e tail eq
  exact h pre e (tail++s) (by rw [eq,List.append_assoc]; rfl)

theorem snoc {F' E J C Ω : Type} (M : DataStructure w F' E J C) (T : RandomTape Ω C)
    (a : Ω) (f : F') (p : List E) (e : E) (m v : Memory w) (c t : ℕ)
    (pre : prefixRun M T a f p = some (m,c)) (next : insertOne M (T.insertion p.length a) e m=some (v,t)) :
    prefixRun M T a f (p++[e]) = some (v,c+t) := by
  unfold prefixRun at pre ⊢
  rw [Chronogram.run_append,pre]
  simp [insertAll,next]

theorem agrees (a : Ω) (f : F') (xs : List E) (paid : Pays D R B a f xs) :
    prefixRun (UpdateCutoff.machine D B) R a f xs = prefixRun D R a f xs := by
  induction xs using List.reverseRecOn with
  | nil => rfl
  | append_singleton p e ih =>
    have hp := pays_prefix D R B a f p [e] paid
    obtain ⟨m,c,v,t,pre,once,bound⟩ := paid p e [] rfl
    rw [snoc D R a f p e m v c t pre once]
    exact snoc _ R a f p e m v c t ((ih hp).trans pre)
      (UpdateCutoff.same D B _ e m v t once bound)

end
end DisjointnessFoundations.SingleSelector
