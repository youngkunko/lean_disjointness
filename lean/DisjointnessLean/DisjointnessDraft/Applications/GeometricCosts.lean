import DisjointnessDraft.Applications.GeoPair

/-! Physical distinct-color counting on integer points and axis-parallel
rectangles. Comparing two dominance ranges removes stored row-size metadata. -/
namespace DisjointnessDraft.Applications.GeometricCosts
open Finset Transfer.Compiler GeoPair Points ShortTransfer Filter
open Classical
noncomputable section

variable {n m N : ℕ}
abbrev Point := ℤ×ℤ
abbrev Colored (m : ℕ) := Point × Fin m
structure Rect where
  low : Point
  high : Point

def Rect.inside (r : Rect) (v : Point) := r.low.1≤v.1 ∧ v.1≤r.high.1 ∧ r.low.2≤v.2 ∧ v.2≤r.high.2
def rectangle (q : Fin m) : Rect := ⟨(0,0),(width m*idx q+m,width m*((m:ℤ)+1-idx q))⟩
def ceiling (N : ℕ) : ℤ := 100*((N:ℤ)+1)^2
def bounded (N : ℕ) (a : ℤ) := -ceiling N≤a ∧ a≤ceiling N
def goodPoint (N : ℕ) (v : Point) := bounded N v.1 ∧ bounded N v.2

def pairs (S : Family m) : Finset (Fin m×Fin m) := univ.filter (fun ij => ij.2∈S ij.1)
def initial (S : Family m) : Finset (Colored m) := (pairs S).image fun ij => (rowPoint ij.1 ij.2,ij.2)
def new (j : Fin m) : Colored m := (insertPoint j,j)
def colors (P : Finset (Colored m)) (r : Rect) := (P.filter (fun v => r.inside v.1)).image Prod.snd
def spec (P : Finset (Colored m)) (h : List (Instr (Colored m) Rect)) (r : Rect) := (colors (state P h) r).card

def legal (N : ℕ) (P : Finset (Colored m)) (h : List (Instr (Colored m) Rect)) :=
  (state P h).card≤N ∧ (∀v∈state P h, goodPoint N v.1) ∧
    ∀r, Sum.inr r∈h → goodPoint N r.low ∧ goodPoint N r.high

theorem color_law (S : Family m) (X : Finset (Fin m)) (q : Fin m) :
    colors (initial S ∪ X.image new) (rectangle q) = S q ∪ X := by
  ext j
  constructor
  · rintro h
    obtain ⟨z,hz,e⟩ := mem_image.mp h
    obtain ⟨mem,inside⟩ := mem_filter.mp hz
    rcases mem_union.mp mem with row|added
    · obtain ⟨⟨i,k⟩,hk,rfl⟩ := mem_image.mp row
      change k=j at e; subst k
      have hi : i=q := (row_rect q i j).mp inside
      subst i; exact mem_union_left _ (mem_filter.mp hk).2
    · obtain ⟨k,hk,rfl⟩ := mem_image.mp added
      change k=j at e; subst k; exact mem_union_right _ hk
  · intro h
    rcases mem_union.mp h with row|add
    · refine mem_image.mpr ⟨(rowPoint q j,j),mem_filter.mpr ⟨mem_union_left _ ?_,(row_rect q q j).mpr rfl⟩,rfl⟩
      exact mem_image.mpr ⟨(q,j),mem_filter.mpr ⟨mem_univ _,row⟩,rfl⟩
    · exact mem_image.mpr ⟨new j,mem_filter.mpr ⟨mem_union_right _ (mem_image_of_mem new add),insert_rect q j⟩,rfl⟩

theorem sizes (nn : 4≤n) (room : 9*(n*n)≤N) : (n+n)*(n+n)+n+8≤N ∧ n+n≤N := by
  have h := Nat.mul_le_mul_right n nn
  constructor <;> nlinarith

theorem index_limit (i : Fin m) : 1≤ idx i ∧ idx i≤(m:ℤ) := by
  have := i.isLt; dsimp [idx]; omega

private theorem coord_range (hm : m≤N) (i j : Fin m) :
    goodPoint N (rowPoint i j) ∧ goodPoint N (insertPoint j) ∧
    goodPoint N (rectangle i).low ∧ goodPoint N (rectangle i).high := by
  have I := index_limit i
  have J := index_limit j
  have c : (m:ℤ)≤N := by exact_mod_cast hm
  have W : 0≤width m := by unfold width; positivity
  have a := mul_le_mul_of_nonneg_left I.2 W
  have b := mul_le_mul_of_nonneg_left (show (m:ℤ)+1-idx i≤m by omega) W
  have z := mul_nonneg W (show 0≤ idx i by omega)
  have y := mul_nonneg W (show 0≤(m:ℤ)+1-idx i by omega)
  have sq := mul_self_le_mul_self (show (0:ℤ)≤m by positivity) c
  unfold goodPoint bounded ceiling rowPoint insertPoint rectangle
  dsimp only [Prod.fst,Prod.snd,Rect.low,Rect.high]
  unfold width at *
  constructor
  all_goals repeat' constructor
  all_goals nlinarith

def decode (_ : Fin n) (ans : List ℕ) := decide (ans[0]?.getD 0 = ans[1]?.getD 0)
def schedule (n : ℕ) : Schedule n (Finset (Colored (n+n))) (Colored (n+n)) Rect ℕ :=
  ⟨fun F => initial (paired F),fun j => [new (original n j)],
    fun q => [.inr (rectangle (first q)),.inr (rectangle (second q))],decode⟩

@[simp] theorem data (xs : List (Fin n)) :
    before (schedule n) xs=xs.map (Sum.inl ∘ new ∘ original n) := by simp [before,schedule,←List.map_eq_flatMap]
theorem data_state (F : Family n) (xs : List (Fin n)) :
    state (initial (paired F)) (before (schedule n) xs)=initial (paired F)∪(xs.toFinset.map (original n)).image new := by
  rw [data,on_data]
  ext v; simp [Finset.mem_image,Finset.mem_map,Function.comp_def]

theorem valid (dim : n+n≤N) (room : (n+n)*(n+n)+n+8≤N) :
    Valid (schedule n) (legal N) spec := by
  constructor
  · intro F xs q nd h pr
    have pre : h <+: xs.map (Sum.inl ∘ new ∘ original n)++[.inr (rectangle (first q)),.inr (rectangle (second q))] := by simpa [schedule,before,←List.map_eq_flatMap] using pr
    have count : xs.length≤n := by rw [←List.toFinset_card_of_nodup nd]; simpa using card_le_univ xs.toFinset
    have maxInit : (initial (paired F)).card≤(n+n)*(n+n) :=
      (card_image_le).trans (by simpa using card_le_univ (pairs (paired F)))
    refine ⟨?_,?_,?_⟩
    · have p := pre.length_le
      simp only [List.length_append,List.length_map,List.length_cons,List.length_nil] at p
      exact (state_size _ _).trans (by change (initial (paired F)).card+h.length≤N; omega)
    · intro v hv
      rcases (state_mem _ _ _).mp hv with hm|added
      · obtain ⟨⟨i,j⟩,_,rfl⟩ := mem_image.mp hm
        exact (coord_range dim i j).1
      · have mem := pre.subset added
        simp [Function.comp_def] at mem
        obtain ⟨j,_,rfl⟩ := mem
        exact (coord_range dim (first q) (original n j)).2.1
    · intro r hr
      have seen := pre.subset hr
      simp at seen
      rcases seen with rfl|rfl
      · exact (coord_range dim (first q) (first q)).2.2
      · exact (coord_range dim (second q) (first q)).2.2
  · intro F xs q _
    simp only [show (schedule n).decode q=decode q from rfl,
      show (schedule n).initial F=initial (paired F) from rfl,
      show (schedule n).finish q=[.inr (rectangle (first q)),.inr (rectangle (second q))] from rfl,
      answers,decode,List.getElem?_cons_zero,List.getElem?_cons_succ,Option.getD_some,spec,on_query,data_state,color_law]
    exact union_test F xs q

theorem lower (lo hi : ℝ) (lp : 0<lo) (lh : lo≤hi) :
    ∃ c : ℝ,0<c ∧ ∀ᶠ N : ℕ in atTop,
      Bound lo hi c N false (legal (m:=stringSize N+stringSize N) N) spec := by
  obtain ⟨c,cp,low⟩ := ShortTransfer.eventual lo hi lp lh
  obtain ⟨k,hk⟩ := eventually_atTop.mp low
  refine ⟨c,cp,?_⟩
  filter_upwards [string_geometry (max k 4)] with N params
  obtain ⟨big,_,fit,nN,pow⟩ := params
  obtain ⟨room,dim⟩ := sizes ((le_max_right ..).trans big) fit
  exact hk _ ((le_max_left ..).trans big) N nN pow (schedule _) false (valid dim room)
    (by simp [schedule]) (by simp [schedule]) (by simp [schedule])

end
end DisjointnessDraft.Applications.GeometricCosts
