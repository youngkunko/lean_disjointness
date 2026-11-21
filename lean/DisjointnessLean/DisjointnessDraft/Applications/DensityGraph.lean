import DisjointnessDraft.Applications.DensityIncidence
import DisjointnessDraft.Applications.DensityLower
import Mathlib.Data.Sym.Sym2

/-! The final problem accepts any unordered non-loop vertex pair, starts
empty and maximizes the ordinary induced edge/vertex ratio. Host slots are
erased before every actual update. -/
namespace DisjointnessDraft.Applications.DensityGraph
open DensityHost DensityIncidence Transfer.Compiler ShortTransfer Finset Filter MeasureTheory Classical
noncomputable section
variable {n p w : ℕ} {Ω A : Type}

abbrev Hist (V : Type) := List (Instr (Sym2 V) Unit)
def inserted {V : Type} (h : Hist V) := h.filterMap Sum.getLeft?
def legal {V : Type} (_ : Unit) (h : Hist V) := (inserted h).Nodup ∧ ∀e∈inserted h,¬e.IsDiag
def induced {V : Type} (h : Hist V) (z : V→Bool) := (inserted h).toFinset.filter fun e => ∀x∈e,z x=true
def value {V : Type} [Fintype V] (_ : Unit) (h : Hist V) (_ : Unit) : ℚ :=
  univ.sup' univ_nonempty (fun z : V→Bool => ((induced h z).card:ℚ)/(univ.filter (fun v => z v=true)).card)
def decision {V : Type} [Fintype V] (theta : ℚ) (u : Unit) (h : Hist V) (q : Unit) := decide (theta≤value u h q)

def encode (e : Edge n) : Sym2 (Vertex n p) := Sym2.mk (pair e)
theorem injective : Function.Injective (@encode n p) := fun e u h => unique e u (Sym2.mk_eq_mk_iff.mp h)
theorem loopless (e : Edge n) : ¬(encode (p:=p) e).IsDiag := by
  rw [encode,Sym2.isDiag_iff_proj_eq]; exact simple e
def translate (h : DensitySchedule.History n) : Hist (Vertex n p) := h.map (Sum.map encode id)
@[simp] theorem translate_append (h s : DensitySchedule.History n) :
    translate (p:=p) (h++s)=translate h++translate s := List.map_append
theorem updates (h : DensitySchedule.History n) : inserted (translate (p:=p) h)=(DensitySchedule.edits h).map encode := by
  induction h with
  | nil => rfl
  | cons op h ih => cases op <;> simp [inserted,translate,DensitySchedule.edits] at ih ⊢ <;> exact ih

theorem valid_graph (u : Unit) (h : DensitySchedule.History n) (ok : DensitySchedule.legal u h) :
    legal u (translate (p:=p) h) := by
  unfold legal; rw [updates]; exact ⟨ok.map injective,by rintro e he; obtain ⟨g,_,rfl⟩ := List.mem_map.mp he; exact loopless g⟩

private theorem both (e : Edge n) (z : Choose n p) : (∀x∈encode e,z x=true) ↔ z (pair e).1=true ∧ z (pair e).2=true := by
  unfold encode
  generalize pair (p:=p) e = ab; rcases ab with ⟨a,b⟩
  simp [Sym2.mem_iff]

theorem induced_host (h : DensitySchedule.History n) (z : Choose n p) :
    induced (translate h) z=(univ.filter (fun e =>
      DensitySchedule.graph h e=true ∧ z (pair e).1=true ∧ z (pair e).2=true)).image encode := by
  ext a
  simp only [induced,mem_filter,List.mem_toFinset,updates,List.mem_map,mem_image,mem_univ,true_and,
    DensitySchedule.graph,decide_eq_true_eq]
  constructor
  · rintro ⟨⟨e,h,rfl⟩,selected⟩
    exact ⟨e,⟨h,(both e z).mp selected⟩,rfl⟩
  · rintro ⟨e,⟨h,ok⟩,rfl⟩
    exact ⟨⟨e,h,rfl⟩,(both e z).mpr ok⟩

theorem score_eq (hn : 0<n) (h : DensitySchedule.History n) (q : Unit) :
    value () (translate (p:=p) h) q=DensitySchedule.valueSpec hn p () h q := by
  unfold value DensitySchedule.valueSpec DensityHost.maximum
  congr 1
  · ext z; simp
  funext z
  rw [score,selected_vertices,selected_edges,induced_host,card_image_of_injective _ injective]
  push_cast; rfl

def restrict (D : Target Unit (Sym2 (Vertex n p)) Unit A w Ω) : Target Unit (Edge n) Unit A w Ω :=
  ⟨D.init,fun a t e => D.update a t (encode e),D.query⟩

private theorem evaluation (D : Target Unit (Sym2 (Vertex n p)) Unit A w Ω) (a : Ω) (t : ℕ) (h : DensitySchedule.History n) :
    script (restrict D) a t h=script D a t (translate h) := by
  induction h generalizing t with
  | nil => rfl
  | cons op h ih => cases op <;> simp only [script,translate,List.map_cons,Sum.map_inl,Sum.map_inr,id_eq,ih] <;> rfl

private theorem same_memory (D : Target Unit (Sym2 (Vertex n p)) Unit A w Ω) (a : Ω) (u : Unit) (h : DensitySchedule.History n) :
    observed (restrict D) a u h=observed D a u (translate h) := by unfold observed; rw [evaluation]; rfl
private theorem cost (D : Target Unit (Sym2 (Vertex n p)) Unit A w Ω) (a : Ω) (u : Unit) (h : DensitySchedule.History n) (op : Instr (Edge n) Unit) :
    expense (restrict D) a u h op=expense D a u (translate h) (Sum.map encode id op) := by
  unfold expense; rw [same_memory]
  simp only [translate,List.length_map]
  cases op <;> rfl
private theorem transport [MeasurableSpace Ω] (μ : Measure Ω) (D : Target Unit (Sym2 (Vertex n p)) Unit A w Ω)
    {oldSpec : Unit→DensitySchedule.History n→Unit→A} {newSpec : Unit→Hist (Vertex n p)→Unit→A}
    (eq : ∀u h q,newSpec u (translate h) q=oldSpec u h q) {tu : ℕ} {tq : ℝ}
    (gu : Guarantees μ D legal newSpec tu tq) : Guarantees μ (restrict D) DensitySchedule.legal oldSpec tu tq := by
  have val (u : Unit) (h : DensitySchedule.History n) (op : Instr (Edge n) Unit) (ok : DensitySchedule.legal u (h++[op])) :
      legal u (translate (p:=p) h ++ [Sum.map encode id op]) := by
    simpa only [translate,List.map_append,List.map_singleton] using (valid_graph (p:=p) u _ ok)
  constructor
  · intro a u h x ok; rw [cost]; exact gu.update a u _ _ (val u h (.inl x) ok)
  · intro u h q ok; simp only [cost]; exact gu.query u _ q (val u h (.inr q) ok)
  · intro a u h q ok
    have result := gu.correct a u _ q (val u h (.inr q) ok)
    rw [←eq]
    rw [same_memory]
    simpa only [translate,List.length_map,restrict] using result
  · intro u h op ok; simp only [cost]; exact gu.measurable u _ _ (val u h op ok)

/-- Worst-case update and expected zero-error query costs on unrestricted
simple graphs with precisely N vertices. The rational threshold is set before
the update stream begins. -/
theorem lower (lo hi : ℝ) (lp : 0<lo) (lh : lo≤hi) :
    ∃ c : ℝ,0<c ∧ ∀ᶠ N : ℕ in atTop,
      let n := DensitySchedule.sourceSize N
      let V := Vertex n (DensitySchedule.extra N)
      Fintype.card V=N ∧ Bound lo hi c N true (legal (V:=V)) value ∧
        Bound lo hi c N true (legal (V:=V)) (decision (threshold n)) := by
  obtain ⟨c,cp,L⟩ := DensitySchedule.lower lo hi lp lh
  refine ⟨c,cp,?_⟩
  filter_upwards [L,eventually_ge_atTop 12] with N h b
  let n := DensitySchedule.sourceSize N
  let p := DensitySchedule.extra N
  have pos := DensitySchedule.positive N b
  obtain ⟨card,raw,test⟩ := h pos
  refine ⟨card,?_,?_⟩
  · intro w tu tq u1 q1 wl wh Ω _ μ _ D gu
    exact raw w tu tq u1 q1 wl wh Ω μ (restrict D) (transport μ D (fun _ => score_eq pos) gu)
  · intro w tu tq u1 q1 wl wh Ω _ μ _ D gu
    exact test w tu tq u1 q1 wl wh Ω μ (restrict D) (transport μ D (fun _ h q => by
      simp [decision,DensitySchedule.decisionSpec,score_eq pos]) gu)

end
end DisjointnessDraft.Applications.DensityGraph
