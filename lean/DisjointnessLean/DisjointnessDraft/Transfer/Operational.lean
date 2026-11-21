import DisjointnessDraft.Transfer.Memory
import DisjointnessDraft.Transfer.Bounds

/-! Physical assembly of the per-history compiler and expected query bounds.
The word containing the clock is charged once for a final query and twice for an insertion. -/
namespace DisjointnessDraft.Transfer.Compiler
open DisjointnessFoundations CellProbe WordProgram MeasureTheory
open scoped ENNReal
noncomputable section
open Classical
variable {F U Q A Ω : Type} {n w v us fs : ℕ}
variable (S : Schedule n F U Q A) (L : Layout w v) (D : Target F U Q A w Ω)

@[simp] theorem before_append (x y : List (Fin n)) :
    before S (x++y)=before S x++before S y := by simp [before,List.flatMap_append]
@[simp] theorem before_cons (x : Fin n) (xs : List (Fin n)) :
    before S (x::xs)=(S.insert x).map Sum.inl ++ before S xs := by simp [before]
@[simp] theorem before_singleton (x : Fin n) : before S [x]=(S.insert x).map Sum.inl := by simp [before]

theorem history_room (sizeU : ∀ x,(S.insert x).length≤us) (room : n*us<2^v)
    (xs : List (Fin n)) (hx : xs.Nodup) : (before S xs).length<2^v := by
  have maxlen (ys : List (Fin n)) : (before S ys).length≤ys.length*us := by
    induction ys with
    | nil => simp [before]
    | cons y ys ih =>
      simp only [before_cons,List.length_append,List.length_map,List.length_cons,Nat.add_mul,Nat.one_mul]
      have u := sizeU y; omega
  have len : xs.length≤n := by rw [←List.toFinset_card_of_nodup hx]; simpa using Finset.card_le_univ xs.toFinset
  exact (maxlen xs).trans_lt ((Nat.mul_le_mul_right _ len).trans_lt room)

theorem data_history (sizeU : ∀ x,(S.insert x).length≤us) (room : n*us<2^v) (a : Ω)
    (f : Family n) (xs : List (Fin n)) (fresh : xs.Nodup) :
    let h := before S xs
    let z := observed D a (S.initial f) h
    prefixRun (machine L S D) (tape Ω) a f xs = some (image L h.length z.2.1,z.2.2+2*xs.length) := by
  induction xs using List.reverseRecOn with
  | nil => simp [prefixRun,before,observed,script,machine,tape,insertAll]
  | append_singleton xs x ih =>
    have pre := ih ((List.nodup_append.mp fresh).1)
    have fits := history_room S sizeU room xs (List.nodup_append.mp fresh).1
    unfold prefixRun at pre ⊢
    rw [Chronogram.run_append,pre]
    simp only [Option.bind_eq_bind,Option.some_bind,insertAll]
    simp only [tape,id_eq]
    rw [update_eq L S D a x _ _ fits]
    simp [before_append,before_singleton,before,observed,script_append,List.flatMap_append]
    omega

theorem final_history (sizeU : ∀ x,(S.insert x).length≤us) (room : n*us<2^v)
    (a : Ω) (f : Family n) (xs : List (Fin n)) (fresh : xs.Nodup) (q : Fin n) :
    let h := before S xs
    let z := (script D a h.length (S.finish q)).run (observed D a (S.initial f) h).2.1
    finalRun (machine L S D) (tape Ω) a f xs q=some (S.decode q z.1,z.2.2+1) := by
  rw [finalRun,data_history S L D sizeU room a f xs fresh]
  exact final_eq L S D a q _ _ (history_room S sizeU room xs fresh)

private theorem insertion_path (valid : ∀ f xs q, xs.Nodup → ∀ h, h <+: before S xs ++ S.finish q → legal (S.initial f) h)
    (q : Fin n) (f : Family n) (xs : List (Fin n)) (x : Fin n) (fresh : (xs++[x]).Nodup) :
    OnPath legal (S.initial f) (before S xs) ((S.insert x).map Sum.inl) := by
  rintro h ⟨suffix,e⟩
  apply valid f (xs++[x]) q fresh
  exact ⟨suffix++S.finish q,by simp only [before_append,before_singleton,←e,List.append_assoc]⟩

theorem finish_path (valid : ∀ f xs q, xs.Nodup → ∀ h, h <+: before S xs ++ S.finish q → legal (S.initial f) h)
    (f : Family n) (xs : List (Fin n)) (q : Fin n) (fresh : xs.Nodup) :
    OnPath legal (S.initial f) (before S xs) (S.finish q) := by
  rintro h ⟨rest,e⟩
  apply valid f xs q fresh
  exact ⟨rest,by simp [e]⟩

theorem count_charge {tu : ℕ} {tq : ℝ} (qp : 0≤tq) (sel : Bool) (ops : List (Instr U Q))
    (h : ∀ u,Sum.inl u∈ops → sel=true) :
    (ops.map (chargeOp tu tq)).sum ≤ ops.length*ENNReal.ofReal (Transfer.charge sel tu tq) := by
  induction ops with
  | nil => simp
  | cons a ops ih =>
    have rest := ih (fun u hu => h u (by simp [hu]))
    have single : chargeOp tu tq a ≤ ENNReal.ofReal (Transfer.charge sel tu tq) := by
      cases a with
      | inl u => simp [chargeOp,Transfer.charge,h u (by simp),ENNReal.ofReal_add qp (Nat.cast_nonneg _)]
      | inr q => cases sel <;> simp [chargeOp,Transfer.charge,ENNReal.ofReal_add qp (Nat.cast_nonneg _)]
    simp only [List.length_cons,Nat.cast_add,Nat.cast_one,add_mul,one_mul,List.map_cons,List.sum_cons]
    simpa only [add_comm] using add_le_add single rest

/-- Per-target-operation guarantees, the fixed schedule's semantic validation,
and its finite size bounds give the exact fresh-sequence interface consumed
by the ordinary Disjointness theorem. -/
theorem on_fresh_actual [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ] (hn : 0<n)
    (g : Costs μ D legal tu tq)
    (paths : ∀ f xs q, xs.Nodup → ∀ h, h <+: before S xs ++ S.finish q → legal (S.initial f) h)
    (correct : ∀ a f xs q, xs.Nodup →
       S.decode q ((script D a (before S xs).length (S.finish q)).run (observed D a (S.initial f) (before S xs)).2.1).1 =
         DisjointnessDraft.answer f xs q) (tu1 : 1≤tu) (tq1 : 1≤tq)
    (sizeU : ∀ x,(S.insert x).length≤us) (sizeF : ∀ q,(S.finish q).length≤fs)
    (sel : Bool) (hasUpdate : ∀ q u,.inl u∈S.finish q → sel=true) (room : n*us<2^v) :
    Fresh.OnFresh μ (machine L S D) (tape Ω) ((us+2)*tu) ((fs+1)*Transfer.charge sel tu tq) := by
  have qp : 0≤tq := by linarith
  refine ⟨?_,?_,?_,?_⟩
  · intro a f xs fresh p x tail eq
    have nodup : (p++[x]).Nodup := by
      apply List.Nodup.of_append_left (l₂:=tail)
      simpa only [List.append_assoc,List.singleton_append,←eq] using fresh
    have pre := (List.nodup_append.mp nodup).1
    have exec := data_history S L D sizeU room a f p pre
    have upd := update_eq L S D a x (observed D a (S.initial f) (before S p)).2.1
      (before S p).length (history_room S sizeU room p pre)
    have bill := insertion_cost μ D a g (S.initial f) (before S p) (S.insert x)
      (insertion_path S paths ⟨0,hn⟩ f p x nodup)
    rw [←actual_bill] at bill
    refine ⟨_,_,_,_,exec,upd,?_⟩
    have size := Nat.mul_le_mul_right tu (sizeU x)
    rw [Nat.add_mul]; omega
  · intro a f xs q fresh
    rw [final_history S L D sizeU room a f xs fresh q]
    simp [correct a f xs q fresh]
  · intro f xs q fresh
    have meas := (final_cost μ D g (S.initial f) (before S xs) (S.finish q) (finish_path S paths f xs q fresh)).1
    simp_rw [final_history S L D sizeU room _ f xs fresh q,actual_bill]
    change Measurable (fun a => ((total D a (S.initial f) (before S xs) (S.finish q)+1:ℕ):ℝ≥0∞))
    exact (measurable_of_countable (fun x : ℕ => (x:ℝ≥0∞))).comp (meas.add measurable_const)
  · intro f xs q fresh
    obtain ⟨meas,paid⟩ := final_cost μ D g (S.initial f) (before S xs) (S.finish q) (finish_path S paths f xs q fresh)
    simp_rw [final_history S L D sizeU room _ f xs fresh q,actual_bill]
    simp only [cost,Nat.cast_add,Nat.cast_one]
    have meas' : Measurable (fun a => (total D a (S.initial f) (before S xs) (S.finish q):ℝ≥0∞)) :=
       (measurable_of_countable (fun x : ℕ => (x:ℝ≥0∞))).comp meas
    rw [lintegral_add_left meas']
    simp only [lintegral_const,measure_univ,mul_one]
    have one : 1≤Transfer.charge sel tu tq := by
      have htu : (0:ℝ)≤tu := Nat.cast_nonneg _
      cases sel <;> simp [Transfer.charge] <;> linarith
    have unit : (1:ℝ≥0∞)≤ENNReal.ofReal (Transfer.charge sel tu tq) := by exact_mod_cast (ENNReal.ofReal_le_ofReal one)
    have sizes : ((S.finish q).length:ℝ≥0∞) ≤ fs := by exact_mod_cast sizeF q
    calc _ ≤ (S.finish q).length * ENNReal.ofReal (Transfer.charge sel tu tq) + ENNReal.ofReal (Transfer.charge sel tu tq) :=
               add_le_add (paid.trans (count_charge qp sel _ (hasUpdate q))) unit
         _ ≤ fs * ENNReal.ofReal (Transfer.charge sel tu tq) + ENNReal.ofReal (Transfer.charge sel tu tq) :=
               add_le_add_right (mul_le_mul_right' sizes _) _
         _ = _ := by rw [ENNReal.ofReal_mul (by positivity),ENNReal.ofReal_add (Nat.cast_nonneg _) (by norm_num)]
                     simp [add_mul]

theorem on_fresh [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ] (hn : 0<n)
    (spec : F → List (Instr U Q) → Q → A) (g : Guarantees μ D legal spec tu tq)
    (ok : Valid S legal spec) (tu1 : 1≤tu) (tq1 : 1≤tq)
    (sizeU : ∀ x,(S.insert x).length≤us) (sizeF : ∀ q,(S.finish q).length≤fs)
    (sel : Bool) (hasUpdate : ∀ q u,.inl u∈S.finish q → sel=true) (room : n*us<2^v) :
    Fresh.OnFresh μ (machine L S D) (tape Ω) ((us+2)*tu) ((fs+1)*Transfer.charge sel tu tq) := by
  apply on_fresh_actual S L D μ hn g.costs ok.1 _ tu1 tq1 sizeU sizeF sel hasUpdate room
  intro a f xs q fresh
  rw [actual_answers μ D a spec g (S.initial f) (before S xs) (S.finish q) (finish_path S ok.1 f xs q fresh)]
  exact ok.2 f xs q fresh

end
end DisjointnessDraft.Transfer.Compiler
