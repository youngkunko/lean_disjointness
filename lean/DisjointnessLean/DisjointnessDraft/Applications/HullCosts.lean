import DisjointnessDraft.Applications.GeometricCosts
import DisjointnessDraft.Applications.HullConfig

/-! Operational convex-hull counting on integer input points. The premise
about extreme points refers to the actual rounded configuration. -/
namespace DisjointnessDraft.Applications.HullCosts
open Finset Transfer.Compiler GeoPair HullConfig ShortTransfer Filter
open Classical
noncomputable section
variable {n m N : ℕ}
abbrev Grid := Fin 3 → ℤ
def realPoint (x : Grid) : Point := fun i => x i
def limit (N : ℕ) : ℤ := 1000*((N:ℤ)+1)^12
def fit (N : ℕ) (x : Grid) := ∀i, |x i|≤limit N

def legal (N : ℕ) (P : Finset Grid) (h : List (Instr Grid Unit)) :=
  (state P h).card≤N ∧ ∀v∈state P h,fit N v
def vertices (P : Finset Grid) := ((convexHull ℝ (realPoint '' (↑P : Set Grid))).extremePoints ℝ).ncard
def spec (P : Finset Grid) (h : List (Instr Grid Unit)) (_ : Unit) := vertices (state P h)
def initial (f : Label m → Grid) (S : Family m) := (present S ∅ ∅).image f

theorem present_split (S : Family m) (X : Finset (Fin m)) (T : Finset (Fin (m+1))) :
    present S X T = present S ∅ ∅ ∪ X.image Label.block ∪ T.image Label.sel := by
  ext v; cases v <;> simp [present]

theorem count_state (f : Label m → Grid) (S : Family m) (X : Finset (Fin m)) (T : Finset (Fin (m+1))) :
    vertices (initial f S∪X.image (f ∘ Label.block)∪T.image (f ∘ Label.sel))=
      count (realPoint ∘ f) S X T := by
  have e : initial f S∪X.image (f ∘ Label.block)∪T.image (f ∘ Label.sel)=(present S X T).image f := by
    rw [present_split S X T,image_union,image_union]; simp [initial,image_image]
  simp [e,vertices,count,Set.image_image]

def shape (m : ℕ) : Label m ≃ ((Fin (m+1)×Fin m) ⊕ ((Fin m×Fin m)⊕(Fin m⊕Fin (m+1)))) where
  toFun
    | .guard i j => .inl (i,j)
    | .datum i j => .inr (.inl (i,j))
    | .block j => .inr (.inr (.inl j))
    | .sel a => .inr (.inr (.inr a))
  invFun
    | .inl (i,j) => .guard i j
    | .inr (.inl (i,j)) => .datum i j
    | .inr (.inr (.inl j)) => .block j
    | .inr (.inr (.inr a)) => .sel a
  left_inv a := by cases a <;> rfl
  right_inv a := by rcases a with ⟨i,j⟩ | (⟨i,j⟩ | (j|a)) <;> rfl

theorem population (m : ℕ) : Fintype.card (Label m)=2*(m*m)+3*m+1 := by
  rw [Fintype.card_congr (shape m)]; simp [Fintype.card_sum,Fintype.card_prod]; ring

def decode (_ : Fin n) (a : List ℕ) := decide
  (a[1]?.getD 0-a[2]?.getD 0 = a[0]?.getD 0-a[1]?.getD 0)

def schedule (f : Label (n+n) → Grid) : Schedule n (Finset Grid) Grid Unit ℕ :=
  ⟨fun F => initial f (paired F),fun j => [f (.block (original n j))],fun q =>
    [.inl (f (.sel (second q).succ)),.inr (),.inl (f (.sel (second q).castSucc)),.inr (),
      .inl (f (.sel (first q).castSucc)),.inr ()],decode⟩

@[simp] theorem data (f : Label (n+n) → Grid) (xs : List (Fin n)) :
    before (schedule f) xs=xs.map (Sum.inl ∘ f ∘ Label.block ∘ original n) := by simp [before,schedule,←List.map_eq_flatMap]

private theorem safe (f : Label (n+n) → Grid) (bounds : ∀v,fit N (f v))
    (room : Fintype.card (Label (n+n))+n+6≤N) :
    ∀F xs q,xs.Nodup → ∀h,h <+: before (schedule f) xs++(schedule f).finish q → legal N ((schedule f).initial F) h := by
  intro F xs q nd h pre
  have count : xs.length≤n := by rw [←List.toFinset_card_of_nodup nd]; simpa using card_le_univ xs.toFinset
  have z := pre.length_le
  rw [data] at z
  simp only [schedule,List.length_append,List.length_map,List.length_cons,List.length_nil] at z
  have c : (initial f (paired F)).card≤Fintype.card (Label (n+n)) := card_image_le.trans (card_le_univ _)
  refine ⟨(state_size _ _).trans (by change (initial f (paired F)).card+h.length≤N; omega),?_⟩
  intro v hv
  rcases (state_mem _ _ _).mp hv with hi|add
  · obtain ⟨u,_,rfl⟩ := mem_image.mp hi; exact bounds u
  · rcases List.mem_append.mp (pre.subset add) with u|q'
    · rw [data] at u
      have mem : ∃j∈xs,f (.block (original n j))=v := by simpa [Function.comp_def] using u
      obtain ⟨j,_,rfl⟩ := mem
      exact bounds _
    · simp [schedule] at q'
      rcases q' with rfl|rfl|rfl <;> apply bounds

set_option maxHeartbeats 800000 in
private theorem observed (f : Label (n+n)→Grid) (inj : Function.Injective (realPoint ∘ f))
    (classes : ∀ S X T, classification (realPoint ∘ f) S X T) (F : Family n) (xs : List (Fin n)) (q : Fin n) :
    (schedule f).decode q (answers spec ((schedule f).initial F) (before (schedule f) xs) ((schedule f).finish q))=answer F xs q := by
  let high := (second q).succ
  let mid := (second q).castSucc
  let low := (first q).castSucc
  let X := xs.toFinset.map (original n)
  let S := paired F
  let P := initial f S∪X.image (f ∘ Label.block)
  let r := realPoint ∘ f
  have a : low≤mid := by change 2*q.val≤2*q.val+1; omega
  have b : mid≤high := by change 2*q.val+1≤2*q.val+1+1; omega
  have link : (first q).succ=mid := Fin.ext (by simp [mid,first,second])
  have dh := count_difference r S X {high} {mid,high} (second q) inj (classes ..) (classes ..)
    (by simp [high]) (by simp [high]) (by simp [mid]) (by simp [mid,b])
  have dl := count_difference r S X {mid,high} {low,mid,high} (first q) inj (classes ..) (classes ..)
    (by simp [link]) (by simp [link,b]) (by simp [low]) (by simp [low,a,a.trans b])
  have s0 : state (initial f S) (before (schedule f) xs)=P := by
    rw [data,on_data]; dsimp only [P,X]; ext v
    simp [Finset.mem_image,Finset.mem_map,Function.comp_def]
  have s1 : vertices (insert (f (.sel high)) P)=count r S X {high} := by simpa only [P,r,image_insert,image_singleton,Function.comp_apply,union_insert,show ∀ (A : Finset Grid) (x : Grid), A∪{x}=insert x A from fun A x => by ext y; simp; tauto] using count_state f S X {high}
  have s2 : vertices (insert (f (.sel mid)) (insert (f (.sel high)) P))=count r S X {mid,high} := by
    simpa only [P,r,image_insert,image_singleton,Function.comp_apply,union_insert,show ∀ (A : Finset Grid) (x : Grid), A∪{x}=insert x A from fun A x => by ext y; simp; tauto] using count_state f S X {mid,high}
  have s3 : vertices (insert (f (.sel low)) (insert (f (.sel mid)) (insert (f (.sel high)) P)))=count r S X {low,mid,high} := by
    simpa only [P,r,image_insert,image_singleton,Function.comp_apply,union_insert,show ∀ (A : Finset Grid) (x : Grid), A∪{x}=insert x A from fun A x => by ext y; simp; tauto] using count_state f S X {low,mid,high}
  simp only [show (schedule f).decode q=decode q from rfl,
    show (schedule f).initial F=initial f S from rfl,
    show (schedule f).finish q=[.inl (f (.sel high)),.inr (),.inl (f (.sel mid)),.inr (),.inl (f (.sel low)),.inr ()] from rfl,
    answers,decode,List.getElem?_cons_zero,List.getElem?_cons_succ,Option.getD_some,spec,on_query,on_insert]
  rw [s0,s1,s2,s3]
  simp only [dl,dh,Nat.add_left_cancel_iff]
  exact difference_test F xs q

theorem valid (f : Label (n+n)→Grid) (inj : Function.Injective (realPoint ∘ f))
    (classes : ∀ S X T, classification (realPoint ∘ f) S X T) (bounds : ∀v,fit N (f v))
    (room : Fintype.card (Label (n+n))+n+6≤N) : Valid (schedule f) (legal N) spec :=
  ⟨safe f bounds room,fun F xs q _ => observed f inj classes F xs q⟩

/-- An integer realization of the manuscript's finite classification suffices
for the physical all-size bound. -/
theorem lower_of_realization (lo hi : ℝ) (lp : 0<lo) (lh : lo≤hi)
    (realizations : ∀ᶠ N : ℕ in atTop, ∃ f : Label (stringSize N+stringSize N)→Grid,
      Function.Injective (realPoint ∘ f) ∧ (∀ S X T,classification (realPoint ∘ f) S X T) ∧ ∀v,fit N (f v)) :
    ∃c : ℝ,0<c ∧ ∀ᶠ N : ℕ in atTop,Bound lo hi c N true (legal N) spec := by
  obtain ⟨c,cp,low⟩ := ShortTransfer.eventual lo hi lp lh
  obtain ⟨k,hk⟩ := eventually_atTop.mp low
  refine ⟨c,cp,?_⟩
  filter_upwards [string_geometry (max k 20),realizations] with N params h
  obtain ⟨big,_,cap,nN,pow⟩ := params
  obtain ⟨f,inj,cl,bounds⟩ := h
  have bn : 20≤stringSize N := (le_max_right ..).trans big
  have room : Fintype.card (Label (stringSize N+stringSize N))+stringSize N+6≤N := by
    rw [population]; nlinarith [Nat.mul_le_mul_right (stringSize N) bn]
  exact hk _ ((le_max_left ..).trans big) N nN pow (schedule f) true (valid f inj cl bounds room)
    (by simp [schedule]) (by simp [schedule]) (by simp)

end
end DisjointnessDraft.Applications.HullCosts
