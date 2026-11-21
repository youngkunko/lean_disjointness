import DisjointnessDraft.Transfer.AuxiliaryMachine
import DisjointnessDraft.Transfer.Relational

/-! Constant auxiliary probe budgets and bounded, legal target operation
lists suffice for the measured simulation in the polynomial transfer theorem.
The only cost assumptions on the simulated data structure are its ordinary
per-operation guarantees on fixed, legal histories. -/
namespace DisjointnessDraft.Transfer.Auxiliary
open DisjointnessFoundations CellProbe WordProgram Compiler Classical MeasureTheory
open scoped ENNReal
noncomputable section
variable (C : Controller n w F U Q A)
/-- A legal batch for a fresh insertion and its two probe budgets. -/
def InsertionValid (legal : F → List (Instr U Q) → Prop) (uAux uOps : ℕ) : Prop :=
  ∀ f xs x,(xs++[x]).Nodup →
    let s := stage C f xs
    let z := (C.insert x).run s.auxiliary
    z.1.1=s.history.length ∧ z.2.2≤uAux ∧ z.1.2.length≤uOps ∧
      OnPath legal (C.initial f) s.history (z.1.2.map Sum.inl)

structure Valid (legal : F → List (Instr U Q) → Prop) (spec : F → List (Instr U Q) → Q → A)
    (uAux uOps qAux qOps : ℕ) (sel : Bool) : Prop where
  update : InsertionValid C legal uAux uOps
  query : ∀ f xs q,xs.Nodup →
    let s := stage C f xs
    let z := (C.finish q).run s.auxiliary
    z.1.1=s.history.length ∧ z.2.2≤qAux ∧ z.1.2.1.length≤qOps ∧
      (∀u,.inl u∈z.1.2.1 → sel=true) ∧ OnPath legal (C.initial f) s.history z.1.2.1 ∧
      z.1.2.2 (answers spec (C.initial f) s.history z.1.2.1)=DisjointnessDraft.answer f xs q

variable (D : Compiler.Target F U Q A w Ω)
private theorem insertion_pays [MeasurableSpace Ω] (μ : Measure Ω)
    (g : Costs μ D legal tu tq) (valid : InsertionValid C legal uAux uOps) (tu1 : 1≤tu) :
    ∀ a f (xs : List (Fin n)), xs.Nodup →
      SingleSelector.Pays (machine C D) (tape Ω) ((uAux+uOps)*tu) a f xs := by
  have idx := fun f xs x nd => (valid f xs x nd).1
  intro a f xs nd p x tail eq
  have pre : (p++[x]).Nodup := by
    apply List.Nodup.of_append_left (l₂:=tail); simpa [List.append_assoc,←eq] using nd
  let s := stage C f p
  let z := (C.insert x).run s.auxiliary
  obtain ⟨t,hist⟩ := physical_history C D idx a f p (List.nodup_append.mp pre).1
  obtain ⟨start,aux,ops,on⟩ := valid f p x pre
  have last := physical_update C D a x (observed D a (C.initial f) s.history).2.1 s.auxiliary
  dsimp only at last; rw [start] at last
  have bill := insertion_cost μ D a g (C.initial f) s.history z.1.2 on
  rw [←actual_bill] at bill
  refine ⟨_,_,_,_,hist,last,?_⟩
  change z.2.2+_≤_
  change z.1.2.length≤uOps at ops
  change z.2.2≤uAux at aux
  exact (Nat.add_le_add (aux.trans (Nat.le_mul_of_pos_right _ tu1)) (bill.trans (Nat.mul_le_mul_right tu ops))).trans_eq
    (Nat.add_mul uAux uOps tu).symm

theorem on_fresh [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    {tu : ℕ} {tq : ℝ} (g : Guarantees μ D legal spec tu tq)
    (v : Valid C legal spec uAux uOps qAux qOps sel) (tu1 : 1≤tu) (tq1 : 1≤tq) :
    Fresh.OnFresh μ (machine C D) (tape Ω) ((uAux+uOps)*tu)
       ((qAux+qOps:ℕ)*Transfer.charge sel tu tq) := by
  have idx := fun f xs x nd => (v.update f xs x nd).1
  have complete (a : Ω) (f : Family n) (xs : List (Fin n)) (q : Fin n) (nd : xs.Nodup) :
      let s := stage C f xs
      let z := (C.finish q).run s.auxiliary
      finalRun (machine C D) (tape Ω) a f xs q =
        some (DisjointnessDraft.answer f xs q,z.2.2+total D a (C.initial f) s.history z.1.2.1) := by
    obtain ⟨t,hist⟩ := physical_history C D idx a f xs nd
    let s := stage C f xs
    let z := (C.finish q).run s.auxiliary
    obtain ⟨start,_,_,_,on,sem⟩ := v.query f xs q nd
    have last := physical_query C D a q (observed D a (C.initial f) s.history).2.1 s.auxiliary
    dsimp only at last
    change z.1.1=s.history.length at start
    change _=some (z.1.2.2 _,z.2.2+_) at last
    change _=some (z.1.2.2 ((script D a z.1.1 z.1.2.1).run _).1,
      z.2.2+((script D a z.1.1 z.1.2.1).run _).2.2) at last
    rw [start,actual_answers μ D a spec g _ _ _ on,actual_bill,sem] at last
    unfold finalRun; rw [hist]; exact last
  refine ⟨?_,?_,?_,?_⟩
  · exact insertion_pays C D μ g.costs v.update tu1
  · intro a f xs q nd; simp [complete a f xs q nd]
  · intro f xs q nd
    let s := stage C f xs; let z := (C.finish q).run s.auxiliary
    have meas := (final_cost μ D g.costs (C.initial f) s.history z.1.2.1 (v.query f xs q nd).2.2.2.2.1).1
    simp_rw [complete _ f xs q nd]
    exact (measurable_of_countable (fun t : ℕ => (t:ℝ≥0∞))).comp (measurable_const.add meas)
  · intro f xs q nd
    let s := stage C f xs; let z := (C.finish q).run s.auxiliary
    obtain ⟨_,ax,op,gate,path,_⟩ := v.query f xs q nd
    obtain ⟨_,paid⟩ := final_cost μ D g.costs (C.initial f) s.history z.1.2.1 path
    have bill := paid.trans (count_charge (by linarith : 0≤tq) sel _ gate)
    have one : 1≤Transfer.charge sel tu tq := by
      cases sel <;> simp [Transfer.charge] <;> linarith [Nat.cast_nonneg (α:=ℝ) tu]
    have one' : 1≤ENNReal.ofReal (Transfer.charge sel tu tq) := by simpa using ENNReal.ofReal_le_ofReal one
    have aux : (z.2.2:ℝ≥0∞)≤qAux := by exact_mod_cast ax
    have len : (z.1.2.1.length:ℝ≥0∞)≤qOps := by exact_mod_cast op
    simp_rw [complete _ f xs q nd]
    change (∫⁻ a,(↑(z.2.2+total D a (C.initial f) s.history z.1.2.1):ℝ≥0∞) ∂μ)≤_
    simp only [Nat.cast_add,lintegral_add_left measurable_const,lintegral_const,measure_univ,mul_one]
    calc _ ≤ (qAux:ℝ≥0∞)*ENNReal.ofReal (Transfer.charge sel tu tq)+qOps*ENNReal.ofReal (Transfer.charge sel tu tq) :=
           add_le_add (aux.trans (le_mul_of_one_le_right' one')) (bill.trans (mul_le_mul_right' len _))
         _ = _ := by rw [←add_mul,ENNReal.ofReal_mul (by positivity)]; norm_cast
/-- The transfer lemma for deterministic, memory-dependent target batches.
The resource bounds cover the controller and target calls separately. -/
theorem polynomial (lo hi : ℝ) (lp : 0<lo) (lh : lo≤hi)
    (uAux uOps qAux qOps : ℕ) (haveU : 1≤uAux+uOps) (haveQ : 1≤qAux+qOps)
    (d e : ℝ) (d1 : 1≤d) (e1 : 1≤e) :
    ∃ c : ℝ,0<c ∧ ∀ᶠ n : ℕ in Filter.atTop, ∀ N w tu : ℕ,
      Real.logb 2 n≤e*Real.logb 2 N → Real.logb 2 N≤d*Real.logb 2 n →
      1≤tu → lo*Real.logb 2 N≤w → (w:ℝ)≤hi*Real.logb 2 N →
      ∀ (F U Q A Ω : Type) [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
        (C : Controller n w F U Q A) (D : Compiler.Target F U Q A w Ω)
        (legal : F → List (Instr U Q) → Prop) (spec : F → List (Instr U Q) → Q → A)
        (sel : Bool) (tq : ℝ),1≤tq → Guarantees μ D legal spec tu tq →
        Valid C legal spec uAux uOps qAux qOps sel →
          c*(Tradeoff.ratio N w tu)^2≤Transfer.charge sel tu tq ∧
          c*(FixedFamilySizes.logRatio N)^2≤max (tu:ℝ) tq := by
  obtain ⟨c,cp,H⟩ := Transfer.polynomial lo hi lp lh (uAux+uOps) (qAux+qOps) 2 haveU haveQ (by decide) d e d1 e1
  refine ⟨c,cp,?_⟩
  filter_upwards [H,Tradeoff.log_tends.eventually_ge_atTop 1] with n low npos
  intro N w tu nl ln t1 wl wh F U Q A Ω _ μ _ C D legal spec sel tq q1 gu ok
  have logpos : 0<Real.logb 2 (N:ℝ) := by
    by_contra! bad
    have := mul_nonpos_of_nonneg_of_nonpos (by linarith : 0≤e) bad
    linarith
  have wd : 0<w := by exact_mod_cast (mul_pos lp logpos).trans_le wl
  exact low N w (w+1) tu nl ln t1 wl wh (by omega) (by omega) Ω Ω μ (machine C D) (tape Ω)
    sel tq q1 (on_fresh C D μ gu ok t1 q1)


/-- Only the target operation sequence must be fixed by the source input.
Any legitimate replies may affect the controller's auxiliary addresses. -/
structure InterleavedValid (code : Fin n → QueryProgram w U Q A)
    (legal : F → List (Instr U Q) → Prop) (rel : F → List (Instr U Q) → Q → A → Prop)
    (uAux uOps qAux qOps : ℕ) (sel : Bool) : Prop where
  update : InsertionValid C legal uAux uOps
  query : ∀ f xs q, xs.Nodup →
    let s := stage C f xs
    ∃ ops : List (Instr U Q), ops.length≤qOps ∧ (∀u,.inl u∈ops → sel=true) ∧
      OnPath legal (C.initial f) s.history ops ∧
      ∀ (reply : F → List (Instr U Q) → Q → A),
        (∀ f' h j,legal f' (h++[.inr j]) → rel f' h j (reply f' h j)) →
        let v := QueryProgram.inspect reply (C.initial f) (code q) s.history s.auxiliary
        v.ordinalsCorrect ∧ v.probes≤qAux ∧ v.operations=ops ∧ v.answer=DisjointnessDraft.answer f xs q

theorem interleaved_on_fresh [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (code : Fin n → QueryProgram w U Q A)
    {tu : ℕ} {tq : ℝ} (g : RelGuarantees μ D legal rel tu tq)
    (v : InterleavedValid C code legal rel uAux uOps qAux qOps sel) (tu1 : 1≤tu) (tq1 : 1≤tq) :
    Fresh.OnFresh μ (interleavedMachine C D code qAux) (tape Ω) ((uAux+uOps)*tu)
       ((qAux+qOps:ℕ)*Transfer.charge sel tu tq) := by
  have idx := fun f xs x nd => (v.update f xs x nd).1
  have complete (f : Family n) (xs : List (Fin n)) (q : Fin n) (nd : xs.Nodup) :
      ∃ ops : List (Instr U Q), ops.length≤qOps ∧ (∀u,.inl u∈ops → sel=true) ∧
        OnPath legal (C.initial f) (stage C f xs).history ops ∧
        ∀ a : Ω, finalRun (interleavedMachine C D code qAux) (tape Ω) a f xs q =
          some (DisjointnessDraft.answer f xs q,qAux+total D a (C.initial f) (stage C f xs).history ops) := by
    obtain ⟨ops,len,gate,path,all⟩ := v.query f xs q nd
    refine ⟨ops,len,gate,path,fun a => ?_⟩
    obtain ⟨indices,bound,seq,ans⟩ := all (QueryProgram.observedAnswer D a) (g.correct a)
    have run := interleavedQuery C D code qAux idx a f xs q nd indices bound
    dsimp only at run
    rw [ans,seq] at run
    exact run
  refine ⟨?_,?_,?_,?_⟩
  · intro a f xs nd pre x tail eq
    obtain ⟨m,c,z,t,hist,next,bill⟩ := insertion_pays C D μ g.toCosts v.update tu1 a f xs nd pre x tail eq
    exact ⟨m,c,z,t,(interleavedPrefix C D code qAux a f pre).trans hist,next,bill⟩
  · intro a f xs q nd
    obtain ⟨_,_,_,_,run⟩ := complete f xs q nd
    simp [run a]
  · intro f xs q nd
    obtain ⟨ops,_,_,path,run⟩ := complete f xs q nd
    have meas := (final_cost μ D g.toCosts (C.initial f) (stage C f xs).history ops path).1
    simp_rw [run]
    exact (measurable_of_countable (fun t : ℕ => (t:ℝ≥0∞))).comp (measurable_const.add meas)
  · intro f xs q nd
    obtain ⟨ops,len,gate,path,run⟩ := complete f xs q nd
    obtain ⟨_,paid⟩ := final_cost μ D g.toCosts (C.initial f) (stage C f xs).history ops path
    have bill := paid.trans (count_charge (by linarith : 0≤tq) sel _ gate)
    have one : 1≤Transfer.charge sel tu tq := by
      cases sel <;> simp [Transfer.charge] <;> linarith [Nat.cast_nonneg (α:=ℝ) tu]
    have one' : 1≤ENNReal.ofReal (Transfer.charge sel tu tq) := by simpa using ENNReal.ofReal_le_ofReal one
    have len' : (ops.length:ℝ≥0∞)≤qOps := by exact_mod_cast len
    simp_rw [run]
    change (∫⁻ a,(↑(qAux+total D a (C.initial f) (stage C f xs).history ops):ℝ≥0∞) ∂μ)≤_
    simp only [Nat.cast_add,lintegral_add_left measurable_const,lintegral_const,measure_univ,mul_one]
    calc _ ≤ (qAux:ℝ≥0∞)*ENNReal.ofReal (Transfer.charge sel tu tq)+qOps*ENNReal.ofReal (Transfer.charge sel tu tq) :=
           add_le_add (le_mul_of_one_le_right' one') (bill.trans (mul_le_mul_right' len' _))
         _ = _ := by rw [←add_mul,ENNReal.ofReal_mul (by positivity)]; norm_cast

/-- The appendix transfer bounds for interleaved auxiliary probes and arbitrary
valid target reports, under the stated tape-independent schedule hypothesis. -/
theorem interleaved_polynomial (lo hi : ℝ) (lp : 0<lo) (lh : lo≤hi)
    (uAux uOps qAux qOps : ℕ) (haveU : 1≤uAux+uOps) (haveQ : 1≤qAux+qOps)
    (d e : ℝ) (d1 : 1≤d) (e1 : 1≤e) :
    ∃ c : ℝ,0<c ∧ ∀ᶠ n : ℕ in Filter.atTop, ∀ N w tu : ℕ,
      Real.logb 2 n≤e*Real.logb 2 N → Real.logb 2 N≤d*Real.logb 2 n →
      1≤tu → lo*Real.logb 2 N≤w → (w:ℝ)≤hi*Real.logb 2 N →
      ∀ (F U Q A Ω : Type) [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
        (C : Controller n w F U Q A) (code : Fin n → QueryProgram w U Q A) (D : Compiler.Target F U Q A w Ω)
        (legal : F → List (Instr U Q) → Prop) (rel : F → List (Instr U Q) → Q → A → Prop)
        (sel : Bool) (tq : ℝ),1≤tq → RelGuarantees μ D legal rel tu tq →
        InterleavedValid C code legal rel uAux uOps qAux qOps sel →
          c*(Tradeoff.ratio N w tu)^2≤Transfer.charge sel tu tq ∧
          c*(FixedFamilySizes.logRatio N)^2≤max (tu:ℝ) tq := by
  obtain ⟨c,cp,H⟩ := Transfer.polynomial lo hi lp lh (uAux+uOps) (qAux+qOps) 2 haveU haveQ (by decide) d e d1 e1
  refine ⟨c,cp,?_⟩
  filter_upwards [H,Tradeoff.log_tends.eventually_ge_atTop 1] with n low npos
  intro N w tu nl ln t1 wl wh F U Q A Ω _ μ _ C code D legal rel sel tq q1 gu ok
  have logpos : 0<Real.logb 2 (N:ℝ) := by
    by_contra! bad
    have := mul_nonpos_of_nonneg_of_nonpos (by linarith : 0≤e) bad
    linarith
  have wd : 0<w := by exact_mod_cast (mul_pos lp logpos).trans_le wl
  exact low N w (w+1) tu nl ln t1 wl wh (by omega) (by omega) Ω Ω μ (interleavedMachine C D code qAux) (tape Ω)
    sel tq q1 (interleaved_on_fresh C D μ code gu ok t1 q1)


end
end DisjointnessDraft.Transfer.Auxiliary
