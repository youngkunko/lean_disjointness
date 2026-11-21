import DisjointnessDraft.Corruption.Theorem
import DisjointnessFoundations.UniformProductLaws
import DisjointnessFoundations.InformationConditioning
import DisjointnessFoundations.EntropyOfConditionedLaws

namespace DisjointnessDraft.Information
open MeasureTheory ProbabilityTheory
open scoped ProbabilityTheory BigOperators
noncomputable section
open Classical

abbrev Layer (N s : ℕ) := ↥(Corruption.layer N s)
abbrev Family (m : ℕ) (W : Type*) := Fin m → W
abbrev World (m N s : ℕ) (W O R : Type*) := Family m W × (Layer N s × (O × R))

/-- Deterministic components of the draft's protocol. Only Bob uses the
independent private coin, in the packet sent before the query is known. -/
structure Game (m N s : ℕ) (W O R U P A : Type*) where
  block : W → Layer N s
  merlin : Family m W → Layer N s → O → U
  packet : U → R → P
  reply : Family m W → O → P → Fin m → A
  verify : P → A → U → Bool

variable {m N s : ℕ} {W O R U P A : Type*}
abbrev View (m : ℕ) (W O P A : Type*) := ((O × P) × (Fin m → A)) × (Fin m → Option W)

def rowPrefix (j : ℕ) (F : Family m W) : Fin m → Option W :=
  fun i => if i.val<j then some (F i) else none

namespace Game
variable (G : Game m N s W O R U P A)
def advice (v : World m N s W O R) := G.merlin v.1 v.2.1 v.2.2.1
def psi (v : World m N s W O R) := G.packet (G.advice v) v.2.2.2
def phi (v : World m N s W O R) := (v.2.2.1,G.psi v)
def answers (v : World m N s W O R) := G.reply v.1 v.2.2.1 (G.psi v)
def public (v : World m N s W O R) := (G.phi v,G.answers v)
def observed (q : Fin m) (v : World m N s W O R) : View m W O P A :=
  (G.public v,rowPrefix q.val v.1)
def accepted (q : Fin m) (v : World m N s W O R) := G.verify (G.psi v) (G.answers v q) (G.advice v)
def label (q : Fin m) (v : World m N s W O R) := (G.observed q v,G.accepted q v)
def row (q : Fin m) (v : World m N s W O R) := G.block (v.1 q)
def Sound := ∀q v,G.accepted q v=true → Disjoint (G.row q v).val v.2.1.val
end Game

scoped instance layerSpace : MeasurableSpace (Layer N s) := ⊤
scoped instance layerSingleton : MeasurableSingletonClass (Layer N s) := ⟨fun _ => trivial⟩

variable [Fintype W] [MeasurableSpace W] [MeasurableSingletonClass W]
  [MeasurableSpace O] [MeasurableSpace R]

/-- The whole family and the target update are independent uniforms.
The outside updates and coins can each have an arbitrary independent law. -/
def experiment (m N s : ℕ) (W : Type*) [Fintype W] [MeasurableSpace W]
    (o : Measure O) (r : Measure R) [SFinite o] [SFinite r] : Measure (World m N s W O R) :=
  (DisjointnessFoundations.HardIndependence.unif (Family m W)).prod
    ((DisjointnessFoundations.HardIndependence.unif (Layer N s)).prod (o.prod r))

def acceptance [Fintype O] [Fintype R] [MeasurableSingletonClass O] [MeasurableSingletonClass R]
    (G : Game m N s W O R U P A) (o : Measure O) (r : Measure R) [SFinite o] [SFinite r] :=
  (∑ q : Fin m, (experiment m N s W o r).real (G.accepted q ⁻¹' {true}))/m

end
end DisjointnessDraft.Information
