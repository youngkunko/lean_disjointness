import DisjointnessDraft.Applications.Strings
import DisjointnessDraft.Transfer.Compiler

/-! The Hamming reduction with a genuine sliding substring, the two exact
pattern edits, a fixed threshold, and the total-length bound. -/
namespace DisjointnessDraft.Applications.StringAlignment
open Transfer.Compiler Finset Strings
open scoped BigOperators
open Classical
noncomputable section
variable {n N : ℕ}
structure Instance where
  textLength : ℕ
  patternLength : ℕ
  text : ℕ → Bool
  initial : ℕ → Bool
abbrev SetBit := ℕ×Bool
def setBit (p : ℕ→Bool) (e : SetBit) : ℕ→Bool := fun k => if k=e.1 then e.2 else p k
def present (X : Finset (Fin n)) (j : ℕ) := decide (∃x∈X,x.val=j)
def patt (X : Finset (Fin n)) (k : ℕ) : Bool :=
  codeP (present X (k/3)) ⟨k%3,Nat.mod_lt _ (by decide)⟩
def raw (F : Family n) (k : ℕ) : Bool :=
  if h : k<n*n then
    let z := finProdFinEquiv.symm (⟨k,h⟩ : Fin (n*n))
    decide (z.2∈F z.1)
  else false
def textBit (F : Family n) (k : ℕ) : Bool := codeT (raw F (k/3)) ⟨k%3,Nat.mod_lt _ (by decide)⟩

def ini (F : Family n) : Instance := ⟨6*(n*n),(n*n)*3,textBit F,patt (n:=n) ∅⟩
def edits (j : Fin n) : List SetBit := [(3*j.val,true),(3*j.val+2,true)]
def start (q : Fin n) := 3*(n*q.val)
def threshold (n : ℕ) := 2*(n*n)-1

def pattern (I : Instance) (h : List (Instr SetBit ℕ)) :=
  h.foldl (fun p op => op.elim (setBit p) (fun _ => p)) I.initial

def distance (I : Instance) (h : List (Instr SetBit ℕ)) (b : ℕ) :=
  ∑ k : Fin I.patternLength,if pattern I h k.val=I.text (b+k.val) then 0 else 1

def spec (k : ℕ) (I : Instance) (h : List (Instr SetBit ℕ)) (b : ℕ) : Bool := decide (distance I h b≤k)

def legal (N : ℕ) (I : Instance) (h : List (Instr SetBit ℕ)) :=
  I.textLength+I.patternLength≤N ∧ ∀op∈h,op.elim (fun e => e.1<I.patternLength) (fun b => b+I.patternLength≤I.textLength)

def schedule (n : ℕ) : Schedule n Instance SetBit ℕ Bool :=
  ⟨ini,edits,fun q => [.inr (start q)],fun _ l => !(l.headD false)⟩

private theorem present_insert (j : Fin n) (X : Finset (Fin n)) (k : ℕ) :
    present (insert j X) k=(decide (j.val=k) || present X k) := by
  by_cases h : j.val=k
  · simp [present,h]
  · simp [present,h]

theorem assign_pair (X : Finset (Fin n)) (j : Fin n) :
    ((edits j).foldl setBit (patt X))=patt (insert j X) := by
  funext k
  have mod := Nat.mod_lt k (by decide : 0<3)
  have reconstruct := Nat.mod_add_div k 3
  change (if k=3*j.val+2 then true else if k=3*j.val then true else patt X k)=_
  by_cases h : j.val=k/3
  · have k0 : k%3=0 ∨ k%3=1 ∨ k%3=2 := by omega
    rcases k0 with z|z|z <;> simp [patt,present_insert,h,z,codeP] <;> omega
  · have e : k≠3*j.val ∧ k≠3*j.val+2 := by omega
    simp [patt,setBit,present_insert,h,e.1,e.2]

theorem pattern_after (F : Family n) (xs : List (Fin n)) :
    pattern (ini F) (before (schedule n) xs)=patt xs.toFinset := by
  induction xs using List.reverseRecOn with
  | nil => rfl
  | append_singleton xs j ih =>
    have e : before (schedule n) (xs++[j])=before (schedule n) xs++(edits j).map Sum.inl := by simp [before,schedule]
    rw [e]
    unfold pattern; rw [List.foldl_append]
    change ((edits j).foldl setBit (pattern (ini F) (before (schedule n) xs)))=_
    rw [ih,assign_pair]
    simp [Finset.insert_eq,Finset.union_comm]

theorem raw_slot (F : Family n) (q j : Fin n) : raw F (n*q.val+j.val)=decide (j∈F q) := by
  have eq : n*q.val+j.val=(finProdFinEquiv (q,j)).val := by dsimp [finProdFinEquiv]; omega
  rw [eq]; unfold raw; rw [dif_pos (finProdFinEquiv (q,j)).isLt]; simp only [Fin.eta,Equiv.symm_apply_apply]

theorem aligned (F : Family n) (xs : List (Fin n)) (q : Fin n) :
    distance (ini F) (before (schedule n) xs) (start q) ≤ threshold n ↔ ∃j∈xs,j∈F q := by
  let G := fun z : Fin (n*n) => present xs.toFinset z.val
  let T := fun z : Fin (n*n) => raw F (n*q.val+z.val)
  have tally := hamming_count G T
  have eq : distance (ini F) (before (schedule n) xs) (start q) =
      hd (fun i : Fin (n*n) × Fin 3 => codeP (G i.1) i.2) (fun i => codeT (T i.1) i.2) := by
    unfold distance; rw [pattern_after]
    change (∑k : Fin ((n*n)*3), if patt xs.toFinset k.val=textBit F (start q+k.val) then 0 else 1)=_
    rw [←Equiv.sum_comp (finProdFinEquiv : Fin (n*n)×Fin 3≃Fin ((n*n)*3))]
    apply sum_congr rfl
    rintro ⟨z,t⟩ _
    have idx : (finProdFinEquiv (z,t)).val=3*z.val+t.val := by dsimp [finProdFinEquiv]; omega
    have idx' : start q+(3*z.val+t.val)=3*(n*q.val+z.val)+t.val := by dsimp [start]; ring
    simp [idx,idx',patt,textBit,G,T,Nat.mul_add_div (by decide : 0<3),Nat.div_eq_of_lt t.isLt,Nat.mod_eq_of_lt t.isLt]
  have hit : 0<overlap G T ↔ ∃j∈xs,j∈F q := by
    rw [overlap,card_pos]; constructor
    · rintro ⟨i,hi⟩
      have both : G i=true ∧ T i=true := by simpa using hi
      obtain ⟨j,hj,eq⟩ : ∃j∈xs,j.val=i.val := by simpa [G,present] using both.1
      have u := both.2
      dsimp [T] at u; rw [←eq,raw_slot] at u
      exact ⟨j,hj,of_decide_eq_true u⟩
    · rintro ⟨j,hj,mem⟩
      have pos : 0<n := Nat.zero_lt_of_lt q.isLt
      let z : Fin (n*n) := ⟨j.val,j.isLt.trans_le (Nat.le_mul_of_pos_right _ pos)⟩
      refine ⟨z,mem_filter.mpr ⟨mem_univ _,?_⟩⟩
      simp [G,T,z,present,raw_slot,mem,hj]; exact ⟨j,hj,rfl⟩
  rw [eq,←hit]
  simp only [Fintype.card_fin] at tally
  have pos : 0<n*n := Nat.mul_pos (Nat.zero_lt_of_lt q.isLt) (Nat.zero_lt_of_lt q.isLt)
  unfold threshold; omega

theorem valid (room : 9*(n*n)≤N) : Valid (schedule n) (legal N) (spec (threshold n)) := by
  constructor
  · intro F xs q _ h pre
    refine ⟨?_,?_⟩
    · change 6*(n*n)+(n*n)*3≤N; omega
    · intro op hop
      have mem := pre.subset hop
      rcases List.mem_append.mp mem with b|last
      · obtain ⟨u,hu,rfl⟩ := List.mem_map.mp b
        obtain ⟨j,_,hj⟩ := List.mem_flatMap.mp hu
        change u∈[(3*j.val,true),(3*j.val+2,true)] at hj
        have fit := j.isLt.trans_le (Nat.le_mul_of_pos_right n (Nat.zero_lt_of_lt q.isLt))
        rcases List.mem_cons.mp hj with rfl|t
        · change 3*j.val<(n*n)*3; omega
        · obtain rfl := List.mem_singleton.mp t; change 3*j.val+2<(n*n)*3; omega
      · obtain rfl := List.mem_singleton.mp last
        change 3*(n*q.val)+(n*n)*3≤6*(n*n)
        have u := Nat.mul_le_mul_left n q.isLt.le; omega
  · intro F xs q _
    change (!(decide (distance (ini F) (before (schedule n) xs) (start q)≤threshold n)))=_
    apply Bool.eq_iff_iff.mpr; simp [aligned F xs q,answer]


def distanceSchedule (n : ℕ) : Schedule n Instance SetBit ℕ ℕ :=
  ⟨ini,edits,(schedule n).finish,fun _ l => !(decide (l.headD 0≤threshold n))⟩

theorem distance_valid (room : 9*(n*n)≤N) : Valid (distanceSchedule n) (legal N) distance :=
  ⟨(valid room).1,(valid room).2⟩

end
end DisjointnessDraft.Applications.StringAlignment
