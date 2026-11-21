import DisjointnessDraft.Applications.UnitGirth
import DisjointnessDraft.Applications.GirthCycles
import DisjointnessDraft.Transfer.Ordinal

/-! A native unit-edge update supplies just its two ordered endpoints. -/
namespace DisjointnessDraft.Applications.UnitGirthNative
open GirthTarget ShortTransfer Transfer.Compiler MeasureTheory Filter Classical
noncomputable section
variable {V : Type}
abbrev Pair (V : Type) := V×V
abbrev History (V : Type) := List (Instr (Pair V) Unit)
def includeUnit (h : History V) : Hist V := h.map (Sum.map (fun p => (p,(1:ℤ))) id)
def legal (f : Unit) (h : History V) := GirthTarget.legal 1 f (includeUnit h)
def exact (f : Unit) (h : History V) := exactSpec f (includeUnit h)
def threshold (D : ℤ) (f : Unit) (h : History V) := testSpec D f (includeUnit h)

private def strip (_ : ℕ) (e : Edit V) := e.1
private def ask (_ : ℕ) (q : Unit) := q
private theorem on_history (h : Hist V) (i : ℕ) :
    Ordinal.ops strip ask i h=h.map (Sum.map Prod.fst id) := by
  induction h generalizing i with
  | nil => rfl
  | cons op xs ih => simp only [Ordinal.ops,List.map_cons,ih]; cases op <;> rfl

private theorem tagged (f : Unit) (h : Hist V) (ok : GirthTarget.legal 1 f h) :
    includeUnit (Ordinal.ops strip ask 0 h)=h := by
  rw [on_history,includeUnit,List.map_map]
  conv_rhs => rw [←List.map_id (l:=h)]
  apply List.map_congr_left
  intro x m
  cases x with
  | inl k =>
    obtain ⟨⟨u,v⟩,d⟩ := k
    have md : graph h u d v := List.mem_filterMap.mpr ⟨_,m,rfl⟩
    obtain ⟨a,b⟩ := ok.2.1 u d v md
    have one : d=1 := by omega
    cases one; rfl
  | inr q => rfl

theorem transport [Fintype V] {lo hi c : ℝ} {N} {A : Type} (spec : Unit → Hist V → Unit → A)
    (H : Bound lo hi c N true (GirthTarget.legal 1) spec) :
    Bound lo hi c N true (legal (V:=V)) (fun f h => spec f (includeUnit h)) := by
  intro w tu tq tu1 tq1 wl wh Ω _ μ _ D G
  let T := Ordinal.target strip ask D
  have g := Ordinal.guarantees strip ask μ D legal (fun f h => spec f (includeUnit h)) tu tq G
  have compat {f} {h : Hist V} (ok : GirthTarget.legal 1 f h) : Ordinal.safe strip ask legal f h := by
    change GirthTarget.legal 1 f (includeUnit (Ordinal.ops strip ask 0 h)); rwa [tagged f h ok]
  apply H w tu tq tu1 tq1 wl wh Ω μ T
  constructor
  · intro a f h u ok; exact g.update a f h u (compat ok)
  · intro f h q ok; exact g.query f h q (compat ok)
  · intro a f h q ok
    have ans := g.correct a f h q (compat ok)
    have pre : GirthTarget.legal 1 f h := by cases f; exact prefix_legal (List.prefix_append ..) ok
    change _=spec f (includeUnit (Ordinal.ops strip ask 0 h)) q at ans
    rwa [tagged f h pre] at ans
  · intro f h op ok; exact g.measurable f h op (compat ok)

theorem lower (lo hi : ℝ) (lp : 0<lo) (lh : lo≤hi) :
    ∃c : ℝ,0<c ∧ ∀ᶠ N : ℕ in atTop,∃hz : 0<UnitEncoding.unitSize N,
      let T := UnitEncoding.U (UnitEncoding.unitSize N) hz ⊕ Fin (UnitGirth.padding N hz)
      Fintype.card T=N ∧ Bound lo hi c N true (legal (V:=T)) exact ∧
        Bound lo hi c N true (legal (V:=T)) (threshold (PlanarTarget.normal (UnitEncoding.unitSize N))) := by
  obtain ⟨c,cp,e⟩ := UnitGirth.lower lo hi lp lh
  refine ⟨c,cp,?_⟩
  filter_upwards [e] with N ⟨hz,count,ex,th⟩
  exact ⟨hz,count,transport _ ex,transport _ th⟩
end
end DisjointnessDraft.Applications.UnitGirthNative
