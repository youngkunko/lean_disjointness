import DisjointnessFoundations.QueryTraceInterpreter
import Mathlib.Data.Fintype.Option
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.List.OfFn

namespace DisjointnessFoundations.Description

open Simulation
noncomputable section

abbrev Cell (w : ℕ) := Fin (2^w)
/-- A length field, padded address–word pairs, and an optional Boolean output. -/
abbrev TraceCode (w d : ℕ) := Fin (d+1) × (Fin d → Cell w × Cell w) × Option Bool

def encodeTrace (w d : ℕ) (t : Transcript (Cell w) (Cell w)) : TraceCode w d :=
  (⟨min t.probes.length d, by omega⟩, fun i => (t.probes[i.val]?).getD (0,0), t.answer)

def decodeTrace (w d : ℕ) (c : TraceCode w d) : Transcript (Cell w) (Cell w) :=
  ⟨List.ofFn (fun i : Fin c.1.val => c.2.1 ⟨i.val, by omega⟩), c.2.2⟩

theorem decode_encode (w d : ℕ) (t : Transcript (Cell w) (Cell w)) (ht : t.probes.length ≤ d) :
    decodeTrace w d (encodeTrace w d t) = t := by
  cases t with
  | mk ps ans =>
    unfold decodeTrace
    congr
    apply List.ext_getElem
    · simp [decodeTrace, encodeTrace, min_eq_left ht]
    · intro i h1 h2
      simp [decodeTrace, encodeTrace, List.getElem?_eq_getElem h2]

end
end DisjointnessFoundations.Description
