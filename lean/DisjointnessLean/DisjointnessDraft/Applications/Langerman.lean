import DisjointnessDraft.Applications.Arrays
import DisjointnessDraft.Applications.ShortTransfer

/-! Integer assignments on a fixed linear order, followed by the ordinary
nonempty-zero-prefix query. Each block contributes exactly 2n+2 entries. -/
namespace DisjointnessDraft.Applications.Langerman
open Transfer.Compiler Filter Real
open Classical
noncomputable section

inductive Pos (n : ℕ) where
  | first
  | head (j : Fin n)
  | entry (j i : Fin n) (second : Bool)
  | tail (j : Fin n)
  deriving DecidableEq, Fintype
abbrev Store (n : ℕ) := Pos n → ℤ
abbrev Edit (n : ℕ) := Pos n × ℤ
def write (a : Store n) (e : Edit n) : Store n := fun p => if p=e.1 then e.2 else a p
def state (a : Store n) (ops : List (Instr (Edit n) Unit)) :=
  ops.foldl (fun v op => op.elim (write v) (fun _ => v)) a

def cells (j : Fin n) : (m : ℕ) → m≤n → List (Pos n)
  | 0,_ => []
  | m+1,h => cells j m (by omega) ++ [.entry j ⟨m,by omega⟩ false,.entry j ⟨m,by omega⟩ true]
def order (n : ℕ) : List (Pos n) :=
  .first :: (List.finRange n).flatMap (fun j => [.head j] ++ cells j n le_rfl ++ [.tail j])
theorem cells_length (j : Fin n) (m : ℕ) (h : m≤n) : (cells j m h).length=2*m := by
  induction m with
  | zero => rfl
  | succ m ih => simp [cells,ih,Nat.mul_add]
theorem order_length (n : ℕ) : (order n).length=1+n*(2*n+2) := by
  have e (l : List (Fin n)) : (l.flatMap (fun j => [Pos.head j] ++ cells j n le_rfl ++ [.tail j])).length=l.length*(2*n+2) := by
    induction l with
    | nil => simp
    | cons j l ih => simp only [List.flatMap_cons,List.length_append,List.length_singleton,cells_length,ih,List.length_cons,List.length_nil,Nat.add_mul,one_mul]; ring
  simp only [order,List.length_cons,e,List.length_finRange]; omega

/-- Every physical coordinate occurs once in the listed prefix order. -/
theorem order_nodup (n : ℕ) : (order n).Nodup := by
  let names : Pos n ≃ Unit ⊕ Fin n ⊕ (Fin n × Fin n × Bool) ⊕ Fin n :=
    { toFun := fun p => match p with
        | .first => .inl () | .head j => .inr (.inl j)
        | .entry j i b => .inr (.inr (.inl (j,i,b))) | .tail j => .inr (.inr (.inr j))
      invFun := fun p => match p with
        | .inl _ => .first | .inr (.inl j) => .head j
        | .inr (.inr (.inl (j,i,b))) => .entry j i b | .inr (.inr (.inr j)) => .tail j
      left_inv := by intro p; cases p <;> rfl
      right_inv := by rintro (⟨⟩|j|⟨j,i,b⟩|j) <;> rfl }
  have inc (j i : Fin n) (b : Bool) (m : ℕ) (h : m≤n) (hi : i.val<m) :
      Pos.entry j i b∈cells j m h := by
    induction m with
    | zero => omega
    | succ m ih =>
      rcases Nat.lt_or_eq_of_le (Nat.le_of_lt_succ hi) with old|last
      · exact List.mem_append_left _ (ih (by omega) old)
      · have eq : i=⟨m,by omega⟩ := Fin.ext last
        cases b <;> simp [cells,eq]
  have all : (order n).toFinset=Finset.univ := by
    ext p
    cases p with
    | first => simp [order]
    | head j => simp [order]
    | tail j => simp [order]
    | entry j i b => simp [order]; exact ⟨j,inc j i b n le_rfl i.isLt⟩
  apply (Multiset.toFinset_card_eq_card_iff_nodup (m:=(order n : Multiset (Pos n)))).mp
  change (order n).toFinset.card=(order n).length
  rw [all,order_length,Finset.card_univ,Fintype.card_congr names]
  simp; ring

def marked (f : Family n) (X : Finset (Fin n)) (a : ℤ) : Store n
  | .first => a
  | .head j => if j∈X then -2*(n:ℤ) else 0
  | .tail j => if j∈X then 0 else -2*(n:ℤ)
  | .entry j i second => if j∈f i then 1 else if second then 0 else 2
def pred (f : Family n) (i : ℕ) (j : Fin n) := ∃ h : i<n,j∈f ⟨i,h⟩
@[simp] theorem pred_val (f : Family n) (i j : Fin n) : pred f i.val j ↔ j∈f i := by simp [pred]
theorem cell_values (f : Family n) (X : Finset (Fin n)) (a : ℤ) (j : Fin n) (m : ℕ) (h : m≤n) :
    (cells j m h).map (marked f X a)=Arrays.pairs (pred f) j m := by
  induction m with
  | zero => rfl
  | succ m ih =>
    have hm : m<n := by omega
    by_cases b : j∈f ⟨m,hm⟩ <;> simp [cells,Arrays.pairs,ih,marked,pred,hm,b]

theorem values (f : Family n) (X : Finset (Fin n)) (a : ℤ) :
    (order n).map (marked f X a) = a::(List.finRange n).flatMap (fun j => Arrays.block (pred f) (↑X) j n) := by
  simp [order,List.map_flatMap,Arrays.block,cell_values,marked]

def offset {n} (q : Fin n) : ℤ := 2*((n:ℤ)-(q.val:ℤ)-1)+1
def edits (n : ℕ) (j : Fin n) : List (Edit n) := [(.head j,-2*(n:ℤ)),(.tail j,0)]
def spec (a : Store n) (ops : List (Instr (Edit n) Unit)) (_ : Unit) :=
  decide (0∈Arrays.prefixes 0 ((order n).map (state a ops)))
def schedule (n : ℕ) : Schedule n (Store n) (Edit n) Unit Bool :=
  ⟨fun f => marked f ∅ 1,edits n,fun q => [.inl (.first,offset q),.inr ()],fun _ vs => !vs.headD false⟩

theorem next (f : Family n) (X : Finset (Fin n)) (a : ℤ) (j : Fin n) :
    (edits n j).foldl write (marked f X a)=marked f (insert j X) a := by
  funext p; cases p with
  | first => rfl
  | entry => rfl
  | head k => by_cases e : k=j <;> simp [edits,write,marked,e]
  | tail k => by_cases e : k=j <;> simp [edits,write,marked,e]
theorem select (f : Family n) (X : Finset (Fin n)) (a v : ℤ) :
    write (marked f X a) (.first,v)=marked f X v := by funext p; cases p <;> rfl

theorem data (f : Family n) (xs : List (Fin n)) :
    state (marked f ∅ 1) (before (schedule n) xs)=marked f xs.toFinset 1 := by
  induction xs using List.reverseRecOn with
  | nil => rfl
  | append_singleton xs j ih =>
    rw [before_append,before_singleton]
    change state _ (before _ xs ++ ((edits n j).map Sum.inl))=_
    have step (a : Store n) (h : List (Instr (Edit n) Unit)) :
        state a (h++((edits n j).map Sum.inl))=(edits n j).foldl write (state a h) := by simp [edits,state,List.foldl_append]
    rw [step,ih,next]
    simp [Finset.insert_eq,Finset.union_comm]

theorem valid (n : ℕ) : Valid (schedule n) (fun _ _ => True) spec := by
  refine ⟨by simp,?_⟩
  intro f xs q _
  have h : state (marked f ∅ 1) (before (schedule n) xs++[.inl (.first,offset q)])=marked f xs.toFinset (offset q) := by
    simpa [state,List.foldl_append,select] using congrArg (fun a => write a (.first,offset q)) (data f xs)
  change (!decide (0∈Arrays.prefixes 0 ((order n).map (state (marked f ∅ 1) (before (schedule n) xs++[.inl (.first,offset q)])))))=_
  rw [h,values]
  apply Bool.eq_iff_iff.mpr
  simp only [Bool.not_eq_true',decide_eq_false_iff_not,DisjointnessDraft.answer,decide_eq_true_eq,offset,
    Arrays.langerman,List.mem_finRange,true_and,Finset.mem_coe,List.mem_toFinset,pred_val,not_exists]
  tauto

def fits (n : ℕ) (v : ℤ) := -(2*(n:ℤ)+2) ≤ v ∧ v ≤ 2*(n:ℤ)+2

/-- Both the preprocessed array and every subsequent assignment use signed
integers of logarithmic bit length. -/
def legal (a : Store n) (h : List (Instr (Edit n) Unit)) :=
  (∀ p, fits n (a p)) ∧ ∀ e : Edit n, Sum.inl e∈h → fits n e.2

theorem bounded_valid (n : ℕ) : Valid (schedule n) legal spec := by
  refine ⟨?_,(valid n).2⟩
  intro f xs q _ h pre
  constructor
  · intro p
    change fits n (marked f ∅ 1 p)
    cases p with
    | first => simp [marked,fits]; omega
    | head j => simp [marked,fits]; omega
    | tail j => simp [marked,fits]; omega
    | entry j i b => cases b <;> by_cases m : j∈f i <;> simp [marked,fits,m] <;> omega
  · intro e mem
    rcases List.mem_append.mp (pre.subset mem) with past | final
    · change Sum.inl e ∈ (xs.flatMap (edits n)).map (Sum.inl : Edit n → Instr (Edit n) Unit) at past
      obtain ⟨e',inside,eq⟩ := List.mem_map.mp past
      cases eq
      obtain ⟨j,_,hit⟩ := List.mem_flatMap.mp inside
      simp [edits] at hit
      rcases hit with rfl | rfl <;> simp [fits] <;> omega
    · have eq : e=(.first,offset q) := by simpa [schedule] using final
      rw [eq]
      have qn := q.isLt
      dsimp [fits,offset]
      omega

theorem lower (lo hi : ℝ) (lp : 0<lo) (lh : lo≤hi) :
    ∃ c : ℝ,0<c ∧ ∀ᶠ N : ℕ in atTop,
      let n := ShortTransfer.stringSize N
      (order n).length≤N ∧ ShortTransfer.Bound lo hi c N true (@legal n) spec := by
  obtain ⟨c,cp,event⟩ := ShortTransfer.eventual lo hi lp lh
  obtain ⟨k,b⟩ := eventually_atTop.mp event
  refine ⟨c,cp,?_⟩
  filter_upwards [ShortTransfer.string_geometry k] with N g
  obtain ⟨kn,hn,fit,low,high⟩ := g
  refine ⟨?_,b _ kn N low high (schedule _) true (bounded_valid _) (by simp [schedule,edits]) (by simp [schedule]) (by simp)⟩
  rw [order_length]; nlinarith [Nat.mul_le_mul_left (ShortTransfer.stringSize N) hn]

end
end DisjointnessDraft.Applications.Langerman
