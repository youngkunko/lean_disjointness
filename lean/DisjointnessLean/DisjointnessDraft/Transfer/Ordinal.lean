import DisjointnessDraft.Transfer.Operational

/-! Relabel target operands by their public operation ordinal. The ordinal
is stored in the clock already charged by the physical compiler. -/
namespace DisjointnessDraft.Transfer.Compiler.Ordinal
open DisjointnessFoundations CellProbe MeasureTheory
open scoped ENNReal
noncomputable section
variable {F U Q V J A Ω : Type} {w : ℕ}
variable (up : ℕ → U → V) (ask : ℕ → Q → J)
def op (i : ℕ) : Instr U Q → Instr V J := Sum.map (up i) (ask i)
def ops : ℕ → List (Instr U Q) → List (Instr V J)
  | _,[] => []
  | i,x::xs => op up ask i x::ops (i+1) xs

@[simp] theorem length (i : ℕ) (xs : List (Instr U Q)) : (ops up ask i xs).length=xs.length := by
  induction xs generalizing i with
  | nil => rfl
  | cons x xs ih => simp [ops,ih]
theorem append (i : ℕ) (xs ys : List (Instr U Q)) :
    ops up ask i (xs++ys)=ops up ask i xs++ops up ask (i+xs.length) ys := by
  induction xs generalizing i with
  | nil => simp [ops]
  | cons x xs ih => simp [ops,ih,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm]
def target (D : Target F V J A w Ω) : Target F U Q A w Ω :=
  ⟨D.init,fun a i u => D.update a i (up i u),fun a i q => D.query a i (ask i q)⟩
theorem step (D : Target F V J A w Ω) (a : Ω) (i : ℕ) (x : Instr U Q) :
    targetStep (target up ask D) a i x=targetStep D a i (op up ask i x) := by cases x <;> rfl
theorem scripts (D : Target F V J A w Ω) (a : Ω) (i : ℕ) (xs : List (Instr U Q)) :
    script (target up ask D) a i xs=script D a i (ops up ask i xs) := by
  induction xs generalizing i with
  | nil => rfl
  | cons x xs ih => simp [ops,script,step,ih]
theorem costs (D : Target F V J A w Ω) (a : Ω) (f : F) (h : List (Instr U Q)) (x : Instr U Q) :
    expense (target up ask D) a f h x=expense D a f (ops up ask 0 h) (op up ask h.length x) := by
  simp only [expense,observed,scripts,step,length]; rfl

def safe (legal : F → List (Instr V J) → Prop) (f : F) (h : List (Instr U Q)) := legal f (ops up ask 0 h)
def report (spec : F → List (Instr V J) → J → A) (f : F) (h : List (Instr U Q)) (q : Q) :=
  spec f (ops up ask 0 h) (ask h.length q)

theorem guarantees [MeasurableSpace Ω] (μ : Measure Ω) (D : Target F V J A w Ω)
    (legal : F → List (Instr V J) → Prop) (spec : F → List (Instr V J) → J → A) (tu : ℕ) (tq : ℝ)
    (g : Guarantees μ D legal spec tu tq) :
    Guarantees μ (target up ask D) (safe up ask legal) (report up ask spec) tu tq := by
  have eq (h : List (Instr U Q)) (x : Instr U Q) :
      ops up ask 0 (h++[x])=ops up ask 0 h++[op up ask h.length x] := by simp [append,ops]
  constructor
  · intro a f h u ok; rw [costs]; apply g.update
    simpa only [safe,eq] using ok
  · intro f h q ok; simp_rw [costs]; apply g.query
    simpa only [safe,eq] using ok
  · intro a f h q ok
    have z := g.correct a f (ops up ask 0 h) (ask h.length q) (by simpa only [safe,eq] using ok)
    change ((D.query a h.length (ask h.length q)).run ((script (target up ask D) a 0 h).run (D.init a f)).2.1).1=_
    rw [scripts]; simpa only [observed,report,length] using z
  · intro f h x ok; simp_rw [costs]; apply g.measurable
    simpa only [safe,eq] using ok

end
end DisjointnessDraft.Transfer.Compiler.Ordinal
