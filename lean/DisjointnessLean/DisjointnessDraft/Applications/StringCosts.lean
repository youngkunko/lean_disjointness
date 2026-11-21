import DisjointnessDraft.Applications.Strings
import DisjointnessDraft.Transfer.Compiler

/-! The actual contiguous intervals and one-symbol patterns of the internal
dictionary and active-document reductions. Indices for strings are zero based. -/
namespace DisjointnessDraft.Applications.StringCosts
open Transfer.Compiler Finset
open Classical
noncomputable section
variable {n N : ℕ}

structure Span where
  start : ℕ
  length : ℕ
  deriving DecidableEq

structure Text (A : Type) where
  length : ℕ
  read : ℕ → A

def Span.fits (p : Span) (n : ℕ) := p.start+p.length≤n

def occurs {A : Type} (T : Text A) (p r : Span) :=
  ∃ j : ℕ,j+p.length≤r.length ∧ ∀ k : Fin p.length,T.read (p.start+k.val)=T.read (r.start+j+k.val)

def symbolAt (F : Family n) (k : ℕ) : Option (Fin n) :=
  if h : k<n*n then
    let z := finProdFinEquiv.symm (⟨k,h⟩ : Fin (n*n))
    Strings.row F z.1 z.2
  else if h : k-n*n<n then some ⟨k-n*n,h⟩ else none

def dictionaryText (F : Family n) : Text (Option (Fin n)) := ⟨n*n+n,symbolAt F⟩
def singletonAt (x : Fin n) : Span := ⟨n*n+x.val,1⟩
def segment (q : Fin n) : Span := ⟨n*q.val,n⟩

theorem row_pos (F : Family n) (q j : Fin n) : symbolAt F (n*q.val+j.val)=Strings.row F q j := by
  have eq : n*q.val+j.val=(finProdFinEquiv (q,j)).val := by dsimp [finProdFinEquiv]; omega
  rw [eq]
  unfold symbolAt; rw [dif_pos (finProdFinEquiv (q,j)).isLt]; simp only [Fin.eta,Equiv.symm_apply_apply]

theorem suffix_pos (F : Family n) (j : Fin n) : symbolAt F (n*n+j.val)=some j := by simp [symbolAt,j.isLt]

theorem singleton_occurs (F : Family n) (x q : Fin n) :
    occurs (dictionaryText F) (singletonAt x) (segment q) ↔ x∈F q := by
  constructor
  · rintro ⟨v,h,read⟩
    have hv : v<n := by change v+1≤n at h; omega
    have hit := read (0 : Fin 1)
    change symbolAt F (n*n+x.val+0)=symbolAt F (n*q.val+v+0) at hit
    simp only [Nat.add_zero,suffix_pos] at hit
    rw [row_pos F q ⟨v,hv⟩] at hit
    by_cases mem : (⟨v,hv⟩ : Fin n)∈F q
    · have same : x=⟨v,hv⟩ := by simpa [Strings.row,mem] using hit
      exact same ▸ mem
    · simp [Strings.row,mem] at hit
  · intro hx
    refine ⟨x.val,x.isLt,?_⟩; intro k
    have kz : k.val=0 := by have := k.isLt; dsimp [singletonAt] at this; omega
    change symbolAt F (n*n+x.val+k.val)=symbolAt F (n*q.val+x.val+k.val)
    simp [kz,suffix_pos,row_pos,Strings.row,hx]

def docIds {U Q : Type} (h : List (Instr U Q)) := h.filterMap (fun op => op.elim some (fun _ => none))

def dictQuery (T : Text (Option (Fin n))) (h : List (Instr Span Span)) (r : Span) : Bool :=
  decide (∃ p∈docIds h, occurs T p r)

def dictLegal (N : ℕ) (T : Text (Option (Fin n))) (h : List (Instr Span Span)) :=
  T.length + ((docIds h).map Span.length).sum ≤ N ∧ ∀op∈h,(op.elim id id).fits T.length

def dictSchedule (n : ℕ) : Schedule n (Text (Option (Fin n))) Span Span Bool :=
  ⟨dictionaryText,fun j => [singletonAt j],fun q => [.inr (segment q)],fun _ a => !(a.headD false)⟩

private theorem updates_before {U Q A F : Type} {g : Fin n→U} {i : Family n→F} {q : Fin n→List (Instr U Q)}
    {d : Fin n→List A→Bool} (xs : List (Fin n)) :
    before (Schedule.mk i (fun j => [g j]) q d) xs=xs.map (Sum.inl ∘ g) := by
  simp [before,←List.map_eq_flatMap]

private theorem read_ids {U Q : Type} (xs : List (Fin n)) (g : Fin n→U) :
    docIds (Q:=Q) (xs.map (Sum.inl ∘ g))=xs.map g := by
  induction xs with
  | nil => rfl
  | cons a xs ih => simp_all [docIds]

private theorem length_le {T : Type} (f : T→ℕ) (l : List T) (each : ∀x∈l,f x≤1) : (l.map f).sum≤l.length := by
  induction l with
  | nil => simp
  | cons a xs ih =>
    have head := each a (by simp)
    have tail := ih (fun x h => each x (by simp [h]))
    simp; omega

private theorem complement (F : Family n) (xs : List (Fin n)) (q : Fin n) :
    (!(decide (∃x∈xs,x∈F q)))=answer F xs q := by
  apply Bool.eq_iff_iff.mpr
  simp [answer]

theorem dictionary_valid (room : n*n+2*n+1≤N) :
    Valid (dictSchedule n) (dictLegal N) dictQuery := by
  constructor
  · intro F xs q nd h part
    have hp : h <+: xs.map (Sum.inl ∘ singletonAt) ++ [.inr (segment q)] := by
      simpa only [dictSchedule,updates_before] using part
    have count : xs.length≤n := by
      rw [←List.toFinset_card_of_nodup nd]; simpa using card_le_univ xs.toFinset
    have hit (op) (mem : op∈h) : op∈xs.map (Sum.inl ∘ singletonAt) ++ [.inr (segment q)] := hp.subset mem
    refine ⟨?_,?_⟩
    · have nlen := hp.length_le
      have cost := length_le Span.length (docIds h) (by
        intro x hx
        obtain ⟨op,mem,eq⟩ := List.mem_filterMap.mp hx
        rcases List.mem_append.mp (hit op mem) with d|last
        · obtain ⟨i,_,rfl⟩ := List.mem_map.mp d
          have e : singletonAt i=x := Option.some.inj eq
          simp [←e,singletonAt]
        · obtain rfl := List.mem_singleton.mp last
          contradiction)
      have shorter : (docIds h).length≤h.length := List.length_filterMap_le ..
      change n*n+n+_≤N
      simp only [List.length_append,List.length_map,List.length_singleton] at nlen; omega
    · intro op hop
      rcases List.mem_append.mp (hit op hop) with d|last
      · obtain ⟨i,_,rfl⟩ := List.mem_map.mp d
        change n*n+i.val+1≤n*n+n; have := i.isLt; omega
      · obtain rfl := List.mem_singleton.mp last
        change n*q.val+n≤n*n+n
        exact Nat.add_le_add_right (Nat.mul_le_mul_left _ q.isLt.le) _
  · intro F xs q _
    change (!(dictQuery (dictionaryText F) (before (dictSchedule n) xs) (segment q)))=_
    rw [show before (dictSchedule n) xs=xs.map (Sum.inl ∘ singletonAt) from updates_before xs]
    unfold dictQuery; rw [read_ids]
    have eq : (∃p∈xs.map singletonAt,occurs (dictionaryText F) p (segment q)) ↔ ∃x∈xs,x∈F q := by
      constructor
      · rintro ⟨p,hp,d⟩; obtain ⟨x,h,rfl⟩ := List.mem_map.mp hp; exact ⟨x,h,(singleton_occurs F x q).mp d⟩
      · rintro ⟨x,h,d⟩; exact ⟨_,List.mem_map.mpr ⟨x,h,rfl⟩,(singleton_occurs F x q).mpr d⟩
    simpa only [eq] using complement F xs q

abbrev Symbol (n : ℕ) := Strings.Symbol (Fin n)
def docs (F : Family n) (j : Fin n) : List (Symbol n) :=
  .mark :: (List.finRange n).map (fun q => if j∈F q then .label q else .blank)
def docSize (ds : Fin n→List (Symbol n)) := ∑i,(ds i).length
def docQuery (ds : Fin n→List (Symbol n)) (h : List (Instr (Fin n) (List (Symbol n) × List (Symbol n)))) (pq : List (Symbol n) × List (Symbol n)) :=
  decide (∃ j∈docIds h,pq.1 <:+: ds j ∧ pq.2 <:+: ds j)
def docLegal (N : ℕ) (ds : Fin n→List (Symbol n)) (h : List (Instr (Fin n) (List (Symbol n) × List (Symbol n)))) :=
  docSize ds≤N ∧ ∀p,Sum.inr p∈h → docSize ds+p.1.length+p.2.length≤N

def docSchedule (n : ℕ) : Schedule n (Fin n→List (Symbol n)) (Fin n) (List (Symbol n)×List (Symbol n)) Bool :=
  ⟨docs,fun j => [j],fun q => [.inr ([.label q],[.mark])],fun _ a => !(a.headD false)⟩

theorem document_size (F : Family n) : docSize (docs F)=n*(n+1) := by simp [docSize,docs]

private theorem one_infix {α : Type} (x : α) (s : List α) : [x] <:+: s ↔ x∈s := by
  rw [List.mem_iff_append]; constructor <;> rintro ⟨u,v,h⟩ <;> exact ⟨u,v,by simpa [List.append_assoc] using h.symm⟩

theorem document_hits (F : Family n) (q j : Fin n) :
    ([Strings.Symbol.label q] <:+: docs F j ∧ [Strings.Symbol.mark] <:+: docs F j) ↔ j∈F q := by
  simp only [one_infix,docs,List.mem_cons,List.mem_map,List.mem_finRange,true_and]
  constructor
  · rintro ⟨h,_⟩
    rcases h with h|⟨i,eq⟩
    · contradiction
    · split_ifs at eq with mem
      · cases eq; exact mem
  · intro mem; exact ⟨Or.inr ⟨q,by simp [mem]⟩,Or.inl trivial⟩

theorem documents_valid (room : n*(n+1)+2≤N) : Valid (docSchedule n) (docLegal N) docQuery := by
  constructor
  · intro F xs q nd h pre
    refine ⟨by change docSize (docs F)≤N; rw [document_size]; omega,?_⟩
    intro p mem
    have seen := pre.subset mem
    change Sum.inr p∈before (docSchedule n) xs++[.inr ([.label q],[.mark])] at seen
    rw [show before (docSchedule n) xs=xs.map (Sum.inl ∘ id) from updates_before xs] at seen
    have eq : p=([.label q],[.mark]) := by simpa using seen
    simp [eq,docSchedule,document_size]; omega
  · intro F xs q _
    change (!(docQuery (docs F) (before (docSchedule n) xs) ([.label q],[.mark])))=_
    rw [show before (docSchedule n) xs=xs.map (Sum.inl ∘ id) from updates_before xs]
    unfold docQuery; rw [read_ids,List.map_id]
    simp only [document_hits]; exact complement F xs q


def docOneQuery (ds : Fin n→List (Symbol n)) (h : List (Instr (Fin n) (List (Symbol n)))) (p : List (Symbol n)) :=
  decide (∃j∈docIds h,p <:+: ds j)
def docOneLegal (N : ℕ) (ds : Fin n→List (Symbol n)) (h : List (Instr (Fin n) (List (Symbol n)))) :=
  docSize ds≤N ∧ ∀p,Sum.inr p∈h → docSize ds+p.length≤N
def docOneSchedule (n : ℕ) : Schedule n (Fin n→List (Symbol n)) (Fin n) (List (Symbol n)) Bool :=
  ⟨docs,fun j => [j],fun q => [.inr [.label q]],fun _ a => !(a.headD false)⟩

theorem document_label (F : Family n) (q j : Fin n) : [Strings.Symbol.label q] <:+: docs F j ↔ j∈F q := by
  have marker : [Strings.Symbol.mark] <:+: docs F j := (one_infix ..).mpr (by simp [docs])
  simpa only [marker,and_true] using document_hits F q j

theorem documents_one_valid (room : n*(n+1)+1≤N) : Valid (docOneSchedule n) (docOneLegal N) docOneQuery := by
  constructor
  · intro F xs q _ h pre
    refine ⟨by change docSize (docs F)≤N; rw [document_size]; omega,?_⟩
    intro p mem
    have seen := pre.subset mem
    change Sum.inr p∈before (docOneSchedule n) xs++[.inr [.label q]] at seen
    rw [show before (docOneSchedule n) xs=xs.map (Sum.inl ∘ id) from updates_before xs] at seen
    have eq : p=[.label q] := by simpa using seen
    simp [eq,docOneSchedule,document_size]; omega
  · intro F xs q _
    change (!(docOneQuery (docs F) (before (docOneSchedule n) xs) [.label q]))=_
    rw [show before (docOneSchedule n) xs=xs.map (Sum.inl ∘ id) from updates_before xs]
    unfold docOneQuery; rw [read_ids,List.map_id]
    simp only [document_label]; exact complement F xs q

end
end DisjointnessDraft.Applications.StringCosts
