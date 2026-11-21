import DisjointnessDraft.Applications.Arrays
import DisjointnessDraft.Applications.ShortTransfer

/-! The target performs genuine row/column increments on an integer matrix
and returns the integer value of a maximum entry. -/
namespace DisjointnessDraft.Applications.Erickson
open Transfer.Compiler MeasureTheory Filter Real
open Classical
noncomputable section

abbrev Matrix (n : ℕ) := Fin n → Fin n → ℤ
abbrev Edit (n : ℕ) := Fin n ⊕ Fin n
def inc (M : Matrix n) : Edit n → Matrix n
  | .inl u => fun i j => M i j + if i=u then 1 else 0
  | .inr v => fun i j => M i j + if j=v then 1 else 0

def entries (M : Matrix n) : Finset ℤ := Finset.univ.image (fun p : Fin n × Fin n => M p.1 p.2)
def maximum (M : Matrix n) : ℤ := if h : (entries M).Nonempty then (entries M).max' h else 0
def state (M : Matrix n) (ops : List (Instr (Edit n) Unit)) :=
  ops.foldl (fun m op => op.elim (inc m) (fun _ => m)) M
def spec (M : Matrix n) (ops : List (Instr (Edit n) Unit)) (_ : Unit) := maximum (state M ops)
def marked (f : Family n) (X : Finset (Fin n)) : Matrix n :=
  fun i j => (Arrays.bit (j∈f i):ℤ) + Arrays.bit (j∈X)
def schedule (n : ℕ) : Schedule n (Matrix n) (Edit n) Unit ℤ :=
  ⟨fun f => marked f ∅,fun j => [.inr j],fun q => [.inl (.inl q),.inr ()],fun _ vs => decide (vs.headD 0≠3)⟩

theorem next (f : Family n) (X : Finset (Fin n)) (j : Fin n) (fresh : j∉X) :
    inc (marked f X) (.inr j)=marked f (insert j X) := by
  funext i k
  by_cases eq : k=j
  · subst k; simp [inc,marked,Arrays.bit,fresh]
  · simp [inc,marked,Arrays.bit,eq]

theorem after_columns (f : Family n) (xs : List (Fin n)) (fresh : xs.Nodup) :
    state (marked f ∅) (before (schedule n) xs)=marked f xs.toFinset := by
  induction xs using List.reverseRecOn with
  | nil => rfl
  | append_singleton xs j ih =>
    have old := (List.nodup_append.mp fresh).1
    have newj : j∉xs.toFinset := by
      intro h; exact (List.nodup_append.mp fresh).2.2 (List.mem_toFinset.mp h) (by simp)
    simp only [before_append,before_singleton,schedule,List.map_cons,List.map_nil,state,List.foldl_append,
      List.foldl_cons,List.foldl_nil,Sum.elim_inl] at *
    rw [ih old,next f _ j newj]
    simp [Finset.insert_eq,Finset.union_comm]

theorem largest (f : Family n) (X : Finset (Fin n)) (q : Fin n) :
    maximum (inc (marked f X) (.inl q))=3 ↔ ∃ j,j∈f q ∧ j∈X := by
  let M := inc (marked f X) (.inl q)
  have val i j : M i j = (Arrays.matrix f X q i j:ℤ) := by
    dsimp [M,inc,marked,Arrays.matrix,Arrays.bit]; split_ifs <;> norm_num
  have mem (v : ℤ) : v∈entries M ↔ ∃ i j,M i j=v := by simp [entries,Prod.exists]
  have non : (entries M).Nonempty := ⟨M q q,(mem _).mpr ⟨q,q,rfl⟩⟩
  change maximum M=3 ↔ _
  rw [maximum,dif_pos non,←(Arrays.erickson f X q).2]
  constructor
  · intro h
    obtain ⟨i,j,eq⟩ := (mem _).mp (Finset.max'_mem _ non)
    exact ⟨i,j,by exact_mod_cast ((val i j).symm.trans (eq.trans h))⟩
  · rintro ⟨i,j,eq⟩
    apply le_antisymm
    · obtain ⟨u,v,e⟩ := (mem _).mp (Finset.max'_mem _ non)
      rw [←e,val]
      exact_mod_cast (Arrays.erickson f X q).1 u v
    · exact Finset.le_max' _ _ ((mem _).mpr ⟨i,j,by simp [val,eq]⟩)

theorem valid (n : ℕ) : Valid (schedule n) (fun _ _ => True) spec := by
  refine ⟨by simp,?_⟩
  intro f xs q nd
  change decide (maximum (state (marked f ∅) (before (schedule n) xs++[.inl (.inl q)]))≠3)=_
  have eq : state (marked f ∅) (before (schedule n) xs++[.inl (.inl q)])=
      inc (marked f xs.toFinset) (.inl q) := by
    simpa [state,List.foldl_append] using congrArg (fun M => inc M (.inl q)) (after_columns f xs nd)
  rw [eq]
  apply decide_eq_decide.mpr
  simp only [ne_eq,largest,List.mem_toFinset,not_exists]
  tauto

/-- The hard histories start with a Boolean matrix and have at most n+2
operations. In particular all integer entries remain at most n+3. -/
def legal (M : Matrix n) (h : List (Instr (Edit n) Unit)) :=
  (∀ i j, M i j = 0 ∨ M i j = 1) ∧ h.length ≤ n+2

theorem bounded_valid (n : ℕ) : Valid (schedule n) legal spec := by
  refine ⟨?_,(valid n).2⟩
  intro f xs q nd h pre
  constructor
  · intro i j
    change marked f ∅ i j = 0 ∨ marked f ∅ i j = 1
    by_cases m : j∈f i <;> simp [marked,Arrays.bit,m]
  · have size : (before (schedule n) xs).length = xs.length := by
      simp [before,schedule,←List.map_eq_flatMap]
    have count : xs.length ≤ n := by simpa using nd.length_le_card
    have bound := pre.length_le
    simp only [List.length_append,size] at bound
    change h.length ≤ xs.length + 2 at bound
    omega

theorem lower (lo hi : ℝ) (lp : 0<lo) (lh : lo≤hi) :
    ∃ c : ℝ,0<c ∧ ∀ᶠ N : ℕ in atTop,
      let n := ShortTransfer.stringSize N
      n*n≤N ∧ ShortTransfer.Bound lo hi c N true (@legal n) spec := by
  obtain ⟨c,cp,event⟩ := ShortTransfer.eventual lo hi lp lh
  obtain ⟨k,b⟩ := eventually_atTop.mp event
  refine ⟨c,cp,?_⟩
  filter_upwards [ShortTransfer.string_geometry k] with N g
  obtain ⟨kn,_,fit,low,high⟩ := g
  refine ⟨by omega,?_⟩
  exact b _ kn N low high (schedule _) true (bounded_valid _) (by simp [schedule]) (by simp [schedule]) (by simp)

end
end DisjointnessDraft.Applications.Erickson
