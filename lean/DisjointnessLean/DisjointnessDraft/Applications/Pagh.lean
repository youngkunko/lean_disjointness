import DisjointnessDraft.Applications.ShortTransfer
import DisjointnessDraft.Transfer.Ordinal

/-! Each target update appends the intersection of two named sets. The last
set's actual index follows from the compiler's physically maintained ordinal. -/
namespace DisjointnessDraft.Applications.Pagh
open Transfer.Compiler MeasureTheory Filter Real
open Classical
noncomputable section

structure Sets (n : ℕ) where
  count : ℕ
  atIndex : ℕ → Finset (Fin n)
abbrev Edit := ℕ × ℕ
abbrev Ask (n : ℕ) := ℕ × Fin n
abbrev History (n : ℕ) := List (Instr Edit (Ask n))
def intersect (s : Sets n) (xy : Edit) : Sets n :=
  ⟨s.count+1,fun k => if k=s.count then s.atIndex xy.1 ∩ s.atIndex xy.2 else s.atIndex k⟩
def state (s : Sets n) (h : History n) := h.foldl (fun a op => op.elim (intersect a) (fun _ => a)) s
def spec (s : Sets n) (h : History n) (p : Ask n) := decide (p.2∈(state s h).atIndex p.1)
def enabled (s : Sets n) : Instr Edit (Ask n) → Prop
  | .inl (i,j) => i<s.count ∧ j<s.count ∧ s.count<2*n+1
  | .inr (i,_) => i<s.count
def legal (s : Sets n) (h : History n) := s.count≤2*n+1 ∧
  ∀ l x,l++[x] <+: h → enabled (state s l) x

theorem prefix_legal (s : Sets n) {h H : History n} (p : h<+:H) (ok : legal s H) : legal s h :=
  ⟨ok.1,fun l x pre => ok.2 l x (pre.trans p)⟩
theorem extend (s : Sets n) (h : History n) (op : Instr Edit (Ask n)) (ok : legal s h)
    (valid : enabled (state s h) op) : legal s (h++[op]) := by
  refine ⟨ok.1,?_⟩
  intro l x pre
  by_cases len : (l++[x]).length≤h.length
  · exact ok.2 l x (List.prefix_of_prefix_length_le pre (List.prefix_append ..) len)
  · have eq := pre.eq_of_length_le (by simp_all; omega)
    have same := congrArg List.length eq
    simp only [List.length_append,List.length_singleton] at same
    obtain ⟨rfl,one⟩ := List.append_inj eq (by omega : l.length=h.length)
    have sameOp : x=op := by simpa using one
    simpa [sameOp] using valid

def initial (f : Family n) : Sets n :=
  ⟨n+1,fun k => if h : k<n then Finset.univ.filter (fun q => (⟨k,h⟩:Fin n)∉f q) else Finset.univ⟩
def up (n : ℕ) (t : ℕ) (x : Fin n) : Edit := (n+t,x)
def ask (n : ℕ) (t : ℕ) (q : Fin n) : Ask n := (n+t,q)
def plan (n : ℕ) : Schedule n (Sets n) (Fin n) (Fin n) Bool :=
  ⟨initial,fun x => [x],fun q => [.inr q],fun _ vs => vs.headD false⟩
def history (n : ℕ) (xs : List (Fin n)) : History n := Ordinal.ops (up n) (ask n) 0 (before (plan n) xs)
@[simp] theorem before_len (xs : List (Fin n)) : (before (plan n) xs).length=xs.length := by simp [before,plan,←List.map_eq_flatMap]
@[simp] theorem history_append (xs : List (Fin n)) (x : Fin n) :
    history n (xs++[x])=history n xs++[.inl (up n xs.length x)] := by
  simp [history,before_append,before_singleton,Ordinal.append,Ordinal.ops,Ordinal.op,plan,before,←List.map_eq_flatMap]

theorem invariant (f : Family n) (xs : List (Fin n)) :
    let s := state (initial f) (history n xs)
    s.count=n+xs.length+1 ∧ (∀ (j q : Fin n),q∈s.atIndex j.val ↔ j∉f q) ∧
      (∀q,q∈s.atIndex (n+xs.length) ↔ ∀x∈xs,x∉f q) := by
  induction xs using List.reverseRecOn with
  | nil => simp [state,history,before,Ordinal.ops,initial]
  | append_singleton xs x ih =>
    let s := state (initial f) (history n xs)
    obtain ⟨cnt,base,cur⟩ := ih
    change s.count=_ at cnt
    change (∀ (j q : Fin n),q∈s.atIndex j.val ↔ j∉f q) at base
    change (∀q,q∈s.atIndex (n+xs.length) ↔ ∀x∈xs,x∉f q) at cur
    rw [history_append]
    have st : state (initial f) (history n xs++[.inl (up n xs.length x)])=intersect s (up n xs.length x) := by simp [state,List.foldl_append,s]
    rw [st]
    dsimp only
    refine ⟨by simp [intersect,cnt]; omega,?_,?_⟩
    · intro j q
      have ne : j.val≠s.count := by have := j.isLt; omega
      simp [intersect,ne,base]
    · intro q
      have eq : n+(xs++[x]).length=s.count := by simp [cnt]; omega
      rw [show (intersect s (up n xs.length x)).atIndex (n+(xs++[x]).length)=s.atIndex (n+xs.length) ∩ s.atIndex x.val by simp only [intersect,eq,if_pos rfl]; rfl]
      simp only [Finset.mem_inter,cur,base,List.mem_append,List.mem_singleton]
      constructor
      · rintro ⟨old,newx⟩ j (hj|rfl); exact old j hj; exact newx
      · exact fun h => ⟨fun j hj => h j (Or.inl hj),h x (Or.inr rfl)⟩

theorem legal_data (f : Family n) (xs : List (Fin n)) (nd : xs.Nodup) : legal (initial f) (history n xs) := by
  induction xs using List.reverseRecOn with
  | nil => simp [legal,initial,history,before,Ordinal.ops]; omega
  | append_singleton xs x ih =>
    have lim := nd.length_le_card
    simp only [List.length_append,List.length_singleton,Fintype.card_fin] at lim
    have cnt := (invariant f xs).1
    rw [history_append]
    apply extend _ _ _ (ih (List.nodup_append.mp nd).1)
    simp only [up,enabled,cnt]; have := x.isLt; omega

theorem valid (n : ℕ) : Valid (plan n) (Ordinal.safe (up n) (ask n) legal)
    (Ordinal.report (up n) (ask n) spec) := by
  constructor
  · intro f xs q nd h pre
    obtain ⟨rest,eq⟩ := pre
    have mapped : Ordinal.ops (up n) (ask n) 0 h <+: Ordinal.ops (up n) (ask n) 0 (before (plan n) xs++(plan n).finish q) :=
      ⟨_,by rw [←eq,Ordinal.append]⟩
    apply prefix_legal _ mapped
    change legal _ (Ordinal.ops _ _ 0 (before _ xs++[.inr q]))
    rw [Ordinal.append]
    simp only [Nat.zero_add,before_len,Ordinal.ops,Ordinal.op,Sum.map_inr]
    apply extend _ _ _ (legal_data f xs nd)
    change n+xs.length<(state (initial f) (history n xs)).count
    rw [(invariant f xs).1]; omega
  · intro f xs q _
    change decide (q∈(state (initial f) (history n xs)).atIndex (n+(before (plan n) xs).length))=_
    rw [before_len]
    exact decide_eq_decide.mpr ((invariant f xs).2.2 q)

theorem lower (lo hi : ℝ) (lp : 0<lo) (lh : lo≤hi) :
    ∃ c : ℝ,0<c ∧ ∀ᶠ n : ℕ in atTop, ShortTransfer.Bound lo hi c n false
      (legal (n:=n)) spec := by
  obtain ⟨c,cp,event⟩ := ShortTransfer.eventual lo hi lp lh
  refine ⟨c,cp,?_⟩
  filter_upwards [event,eventually_ge_atTop 1] with n h hn
  have cube : n≤n^3 := by simpa [pow_succ,Nat.mul_assoc] using Nat.le_mul_of_pos_left n (Nat.mul_pos hn hn)
  have virt := h n le_rfl cube (plan n) false (valid n) (by simp [plan]) (by simp [plan]) (by simp [plan])
  intro w tu tq tu1 tq1 wl wh Ω _ μ _ D g
  exact virt w tu tq tu1 tq1 wl wh Ω μ (Ordinal.target (up n) (ask n) D)
    (Ordinal.guarantees (up n) (ask n) μ D legal spec tu tq g)

end
end DisjointnessDraft.Applications.Pagh
