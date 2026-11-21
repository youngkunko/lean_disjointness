import DisjointnessDraft.Streaming.IndexedBits

/-! At least one bit must probe: with no probes, the final physical bit
operation at a fixed position has a report independent of preprocessing. -/
namespace DisjointnessDraft.Streaming.Binary.Indexed
open DisjointnessFoundations WordProgram RegularExpression Classical
noncomputable section

private theorem free {w} (p : Op w) (m m' : CellProbe.Memory w) (zero : (p.run m).2.2=0) :
    (p.run m).1=(p.run m').1 := by
  cases p with
  | pure => rfl
  | read a k => change 1+_ = 0 at zero; omega
  | write a x k => change 1+_ = 0 at zero; omega

theorem positive_budget {n b w} {Ω : Type} (D : Machine w Ω) (seed : Ω) (C : Code (Symbol n n) b)
    (np : 0<n) (bp : 0<b) (t : ℕ) (correct : Correct D seed C) (budget : Budget D seed C t) : 1≤t := by
  by_contra! nt
  let z : Fin n := ⟨0,np⟩
  let empty : Family n := fun _ => ∅
  let full : Family n := fun _ => Finset.univ
  let raw := (word [z] z).flatMap C.bits
  have reports (f : Family n) (ne : raw≠[]) : ((input D seed C f raw).1=true) ↔ ∀x∈[z],x∉f z := by
    rw [correct f raw ne,RegularExpression.rmatch_iff_matches']
    exact Code.reduction C bp f [z] z
  have ne : raw≠[] := by
    intro eq
    have sz := (List.flatMap_eq_nil_iff.mp eq) marker (by simp [word])
    have := congrArg List.length sz; simp at this; omega
  obtain ⟨pre,bit,eq⟩ := (List.eq_nil_or_concat' raw).resolve_left ne
  have last (f : Family n) : (input D seed C f raw).1=((D.bit seed pre.length bit).run (input D seed C f pre).2.1).1 := by
    rw [eq]; simpa [batch,Program.run_bind,Program.run] using (next D seed C f pre [bit] (by simp) false).1
  have same : (input D seed C empty raw).1=(input D seed C full raw).1 := by
    rw [last,last]; apply free
    have b := budget empty pre bit; omega
  have yes : (input D seed C empty raw).1=true := (reports empty ne).mpr (by simp [empty])
  have no : ¬((input D seed C full raw).1=true) := by rw [reports full ne]; simp [full]
  exact no (same ▸ yes)
end
end DisjointnessDraft.Streaming.Binary.Indexed
