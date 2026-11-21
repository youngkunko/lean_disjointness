import DisjointnessDraft.Applications.GeometricCosts

/-! Integer point insertions and maximal-point counts. Three successive
selectors compare adjacent genuine and reference rows on the same structure. -/
namespace DisjointnessDraft.Applications.MaximaCosts
open Finset Transfer.Compiler GeoPair Points ShortTransfer Filter
open GeometricCosts (bounded ceiling index_limit)
open Classical
noncomputable section
variable {n m N : ℕ}

def labels (S : Family m) (X : Finset (Fin m)) (T : Finset ℤ) : Finset (Label m) :=
  (GeometricCosts.pairs S).image pointTag ∪ X.image Label.block ∪ T.image Label.sel
def configuration (S : Family m) (X : Finset (Fin m)) (T : Finset ℤ) := (labels S X T).image coords

@[simp] theorem label_present (S : Family m) (X : Finset (Fin m)) (T : Finset ℤ) (v : Label m) :
    v∈labels S X T ↔ present S X T v := by
  cases v <;> simp [labels,GeometricCosts.pairs,pointTag,present,Prod.exists]

theorem coords_injective (m : ℕ) : Function.Injective (@coords m) := by
  intro x y eq
  have xy : dominates (coords x) (coords y) := eq ▸ ⟨le_rfl,le_rfl,le_rfl⟩
  have yx : dominates (coords y) (coords x) := eq ▸ ⟨le_rfl,le_rfl,le_rfl⟩
  cases x with
  | point a b =>
    cases y with
    | point i j => obtain ⟨rfl,rfl⟩ := (points_dom a b i j).mp xy; rfl
    | block j => exact False.elim (point_no_block a b j xy)
    | sel s => exact False.elim (point_no_sel a b s xy)
  | block a =>
    cases y with
    | point i j => exact False.elim (point_no_block i j a yx)
    | block j => rw [(blockers_dom a j).mp xy]
    | sel r => exact False.elim (block_no_sel a r xy)
  | sel r =>
    cases y with
    | point i j => exact False.elim (point_no_sel i j r yx)
    | block j => exact False.elim (block_no_sel j r yx)
    | sel s => exact congrArg Label.sel (congrArg (fun p : R3 => p.2.2) eq)

def maximalPoints (P : Finset R3) := P.filter fun v => ∀u∈P,dominates u v → u=v

theorem maximal_image (S : Family m) (X : Finset (Fin m)) (T : Finset ℤ) (r : ℤ)
    (top : r∈T) (largest : ∀s∈T,s≤r) (rn : r≤m) :
    (maximalPoints (configuration S X T)).card=(maximalSet S X r).card := by
  rw [←card_image_of_injective _ (coords_injective m)]
  congr 1
  ext v
  constructor
  · intro h; obtain ⟨mem,maxi⟩ := mem_filter.mp h
    obtain ⟨a,pa,rfl⟩ := mem_image.mp mem
    refine mem_image.mpr ⟨a,(maximalSet_correct S X T r top largest rn a).mpr ⟨(label_present ..).mp pa,?_⟩,rfl⟩
    intro b pb dom
    exact coords_injective m (maxi _ (mem_image_of_mem coords ((label_present ..).mpr pb)) dom)
  · intro h
    obtain ⟨a,pa,rfl⟩ := mem_image.mp h
    obtain ⟨pm,mx⟩ := (maximalSet_correct S X T r top largest rn a).mp pa
    refine mem_filter.mpr ⟨mem_image_of_mem coords ((label_present ..).mpr pm),?_⟩
    intro u hu dom
    obtain ⟨b,pb,rfl⟩ := mem_image.mp hu
    rw [mx b ((label_present ..).mp pb) dom]

def initial (S : Family m) : Finset R3 := (GeometricCosts.pairs S).image fun z => p z.1 z.2
theorem config (S : Family m) (X : Finset (Fin m)) (T : Finset ℤ) :
    configuration S X T = initial S ∪ X.image blocker ∪ T.image (selector m) := by
  simp [configuration,labels,image_union,image_image,initial,pointTag,coords,Function.comp_def]

def legal (N : ℕ) (P : Finset R3) (h : List (Instr R3 Unit)) :=
  (state P h).card≤N ∧ ∀v∈state P h,bounded N v.1 ∧ bounded N v.2.1 ∧ bounded N v.2.2
def spec (P : Finset R3) (h : List (Instr R3 Unit)) (_ : Unit) := (maximalPoints (state P h)).card

def decode (_ : Fin n) (a : List ℕ) := decide
  (a[0]?.getD 0-a[1]?.getD 0 = a[1]?.getD 0-a[2]?.getD 0)
def cut (q : Fin n) := idx (first q)
def schedule (n : ℕ) : Schedule n (Finset R3) R3 Unit ℕ :=
  ⟨fun F => initial (paired F),fun j => [blocker (original n j)],fun q =>
    [.inl (selector (n+n) (cut q-1)),.inr (),.inl (selector (n+n) (cut q)),.inr (),
      .inl (selector (n+n) (cut q+1)),.inr ()],decode⟩

@[simp] theorem data (xs : List (Fin n)) :
    before (schedule n) xs=xs.map (Sum.inl ∘ blocker ∘ original n) := by simp [before,schedule,←List.map_eq_flatMap]
theorem data_state (F : Family n) (xs : List (Fin n)) :
    state (initial (paired F)) (before (schedule n) xs)=initial (paired F)∪(xs.toFinset.map (original n)).image blocker := by
  rw [data,on_data]; ext v; simp [Finset.mem_image,Finset.mem_map,Function.comp_def]

private theorem coord_range (dim : m≤N) (i j : Fin m) :
    (bounded N (p i j).1 ∧ bounded N (p i j).2.1 ∧ bounded N (p i j).2.2) ∧
    (bounded N (blocker j).1 ∧ bounded N (blocker j).2.1 ∧ bounded N (blocker j).2.2) ∧
    ∀r : ℤ, 0≤r → r≤m → bounded N (selector m r).1 ∧ bounded N (selector m r).2.1 ∧ bounded N (selector m r).2.2 := by
  have I := index_limit i; have J := index_limit j
  have c : (m:ℤ)≤N := by exact_mod_cast dim
  have sq := mul_self_le_mul_self (show (0:ℤ)≤m by positivity) c
  have pos := mul_nonneg (show 0≤4*(m:ℤ) by positivity) (show 0≤ idx j by omega)
  have mul := mul_le_mul_of_nonneg_left J.2 (show 0≤4*(m:ℤ) by positivity)
  unfold bounded ceiling p blocker selector
  dsimp only [Prod.fst,Prod.snd]
  constructor
  · repeat' apply And.intro
    all_goals nlinarith [I.1,I.2,J.1,J.2]
  constructor
  · repeat' apply And.intro
    all_goals nlinarith [I.1,I.2,J.1,J.2]
  intro r lo hi
  repeat' apply And.intro
  all_goals nlinarith [I.1,I.2,J.1,J.2]

private theorem safe (dim : n+n≤N) (room : (n+n)*(n+n)+n+8≤N) :
    (∀F xs q, xs.Nodup → ∀h, h <+: before (schedule n) xs ++ (schedule n).finish q →
       legal N ((schedule n).initial F) h) := by
  intro F xs q nd h pre
  have count : xs.length≤n := by rw [←List.toFinset_card_of_nodup nd]; simpa using card_le_univ xs.toFinset
  have size := pre.length_le
  rw [data] at size
  simp only [schedule,List.length_append,List.length_map,List.length_cons,List.length_nil] at size
  have initialSize : (initial (paired F)).card≤(n+n)*(n+n) :=
    card_image_le.trans (by simpa using card_le_univ (GeometricCosts.pairs (paired F)))
  refine ⟨(state_size _ _).trans (by change (initial (paired F)).card+h.length≤N; omega),?_⟩
  intro v hv
  rcases (state_mem _ _ _).mp hv with hp|op
  · obtain ⟨⟨i,j⟩,_,rfl⟩ := mem_image.mp hp
    exact (coord_range dim i j).1
  · have full := pre.subset op
    rcases List.mem_append.mp full with left|right
    · rw [data] at left
      have mem : ∃j∈xs,blocker (original n j)=v := by simpa [Function.comp_def] using left
      obtain ⟨j,_,rfl⟩ := mem
      exact (coord_range dim (first q) (original n j)).2.1
    · simp [schedule] at right
      have a := index_limit (first q)
      have b := index_limit (second q)
      rw [first_val] at b
      dsimp [cut] at *
      rcases right with rfl|rfl|rfl <;> apply (coord_range dim (first q) (first q)).2.2 <;> omega

private theorem observed (F : Family n) (xs : List (Fin n)) (q : Fin n) :
    (schedule n).decode q (answers spec ((schedule n).initial F) (before (schedule n) xs) ((schedule n).finish q))=
    answer F xs q := by
  let S := paired F
  let X := xs.toFinset.map (original n)
  let r := cut q
  let H := before (schedule n) xs
  let m := n+n
  let P := initial S ∪ X.image blocker
  have idx := index_limit (second q)
  rw [first_val] at idx
  have rn : r+1≤(m:ℤ) := idx.2
  have h1 : (maximalPoints (insert (selector m (r-1)) P)).card = (maximalSet S X (r-1)).card := by
    convert maximal_image S X {r-1} (r-1) (by simp) (by simp) (by omega) using 2
    simp [config,P,m,Finset.image_union,Finset.insert_eq,Finset.union_assoc,Finset.union_left_comm,Finset.union_comm]
  have h2 : (maximalPoints (insert (selector m r) (insert (selector m (r-1)) P))).card=(maximalSet S X r).card := by
    convert maximal_image S X {r,r-1} r (by simp) (by simp) (by omega) using 2
    simp [config,P,m,Finset.image_union,Finset.insert_eq,Finset.union_assoc,Finset.union_left_comm,Finset.union_comm]
  have h3 : (maximalPoints (insert (selector m (r+1)) (insert (selector m r) (insert (selector m (r-1)) P)))).card=
      (maximalSet S X (r+1)).card := by
    convert maximal_image S X {r+1,r,r-1} (r+1) (by simp) (by (simp; omega)) rn using 2
    simp [config,P,m,Finset.image_union,Finset.insert_eq,Finset.union_assoc,Finset.union_left_comm,Finset.union_comm]
  have hist : state (initial S) (before (schedule n) xs)=P := data_state F xs
  have a := maxima_query S X (first q)
  have b := maxima_query S X (second q)
  change (maximalSet S X (r-1)).card-(maximalSet S X r).card=_ at a
  rw [first_val] at b
  simp only [add_sub_cancel_right] at b
  change (maximalSet S X r).card-(maximalSet S X (r+1)).card=_ at b
  simp only [show (schedule n).decode q=decode q from rfl,
    show (schedule n).initial F=initial S from rfl,
    show (schedule n).finish q=[.inl (selector m (r-1)),.inr (),.inl (selector m r),.inr (),
      .inl (selector m (r+1)),.inr ()] from rfl, answers,decode,
    List.getElem?_cons_zero,List.getElem?_cons_succ,Option.getD_some,spec,on_query,on_insert]
  rw [hist,h1,h2,h3]
  simp only [a,b]
  exact difference_test F xs q

theorem valid (dim : n+n≤N) (room : (n+n)*(n+n)+n+8≤N) : Valid (schedule n) (legal N) spec :=
  ⟨safe dim room,fun F xs q _ => observed F xs q⟩

theorem lower (lo hi : ℝ) (lp : 0<lo) (lh : lo≤hi) :
    ∃ c : ℝ,0<c ∧ ∀ᶠ N : ℕ in atTop, Bound lo hi c N true (legal N) spec := by
  obtain ⟨c,cp,low⟩ := ShortTransfer.eventual lo hi lp lh
  obtain ⟨k,hk⟩ := eventually_atTop.mp low
  refine ⟨c,cp,?_⟩
  filter_upwards [string_geometry (max k 4)] with N params
  obtain ⟨big,_,fit,nN,pow⟩ := params
  obtain ⟨room,dim⟩ := GeometricCosts.sizes ((le_max_right ..).trans big) fit
  exact hk _ ((le_max_left ..).trans big) N nN pow (schedule _) true (valid dim room)
    (by simp [schedule]) (by simp [schedule]) (by simp)

end
end DisjointnessDraft.Applications.MaximaCosts
