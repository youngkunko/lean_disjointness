import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Finset.Card
import Mathlib.Data.Fintype.Fin
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-! Integer coordinates for the maxima and distinct-color reductions. Indices
are converted to the manuscript's one-based coordinates before evaluation. -/
namespace DisjointnessDraft.Applications.Points
open Classical Finset
noncomputable section
def idx {n} (i : Fin n) : ℤ := i.val+1
private theorem bounds {n} (i : Fin n) : 1≤idx i ∧ idx i≤(n:ℤ) := by
  have := i.isLt
  dsimp [idx]
  omega
private theorem idx_eq {n} {i j : Fin n} (e : idx i=idx j) : i=j := by
  apply Fin.ext; dsimp [idx] at e; omega
abbrev R3 := ℤ × ℤ × ℤ
def dominates (a b : R3) := b.1≤a.1 ∧ b.2.1≤a.2.1 ∧ b.2.2≤a.2.2
def p {n} (i j : Fin n) : R3 := (4*n*idx j-idx i,(n:ℤ)-idx j,idx i)
def blocker {n} (j : Fin n) : R3 := (4*n*idx j,(n:ℤ)-idx j,(n:ℤ)+1)
def selector (n : ℕ) (r : ℤ) : R3 := (4*n*((n:ℤ)+1),(n:ℤ)+1,r)

private theorem gap {n} (x y : Fin n) (lt : idx x<idx y) :
    4*(n:ℤ)*idx x+4*n ≤ 4*n*idx y := by
  have h : idx x+1≤idx y := by omega
  have g := mul_le_mul_of_nonneg_left h (show 0≤4*(n:ℤ) by positivity)
  linarith

theorem points_dom {n} (a b i j : Fin n) : dominates (p a b) (p i j) ↔ a=i ∧ b=j := by
  constructor
  · rintro ⟨hx,hy,hz⟩
    change 4*(n:ℤ)*idx j-idx i ≤ 4*n*idx b-idx a at hx
    change (n:ℤ)-idx j ≤ n-idx b at hy
    change idx i≤idx a at hz
    have A := bounds a
    have I := bounds i
    have eq : idx b=idx j := by
      by_contra ne
      have s : idx b<idx j := by omega
      linarith only [gap b j s,A.1,I.2,hx]
    rw [eq] at hx
    exact ⟨idx_eq (by omega),idx_eq eq⟩
  · rintro ⟨rfl,rfl⟩; exact ⟨le_rfl,le_rfl,le_rfl⟩

theorem blocker_dom {n} (b i j : Fin n) : dominates (blocker b) (p i j) ↔ b=j := by
  constructor
  · rintro ⟨hx,hy,hz⟩
    change 4*(n:ℤ)*idx j-idx i ≤ 4*n*idx b at hx
    change (n:ℤ)-idx j ≤ n-idx b at hy
    apply idx_eq
    by_contra ne
    have lt : idx b<idx j := by omega
    have := bounds i
    linarith only [gap b j lt,hx,this.1,this.2]
  · rintro rfl
    have := bounds i
    dsimp [dominates,p,blocker]; omega

theorem selector_dom {n} (i j : Fin n) (r : ℤ) :
    dominates (selector n r) (p i j) ↔ idx i≤r := by
  have I := bounds i
  have J := bounds j
  have w := mul_le_mul_of_nonneg_left J.2 (show 0≤4*(n:ℤ) by positivity)
  dsimp [dominates,p,selector]
  constructor
  · exact fun h => h.2.2
  · intro h; refine ⟨?_,by omega,h⟩; linarith only [w,I.1,J.1,J.2]

theorem blockers_dom {n} (j k : Fin n) : dominates (blocker j) (blocker k) ↔ j=k := by
  dsimp [dominates,blocker]
  constructor
  · rintro ⟨a,b,_⟩
    apply idx_eq
    by_contra ne
    have := gap j k (by omega)
    have h := bounds j
    omega
  · rintro rfl; exact ⟨le_rfl,le_rfl,le_rfl⟩

theorem point_no_block {n} (i j k : Fin n) : ¬dominates (p i j) (blocker k) := by
  have := bounds i; dsimp [dominates,p,blocker]; omega
theorem point_no_sel {n} (i j : Fin n) (r : ℤ) : ¬dominates (p i j) (selector n r) := by
  have := bounds j; dsimp [dominates,p,selector]; omega
theorem block_no_sel {n} (j : Fin n) (r : ℤ) : ¬dominates (blocker j) (selector n r) := by
  have := bounds j; dsimp [dominates,blocker,selector]; omega
theorem sel_no_block {n} (j : Fin n) {r : ℤ} (h : r≤n) : ¬dominates (selector n r) (blocker j) := by
  dsimp [dominates,selector,blocker]; omega

inductive Label (n : ℕ) where
  | point (i j : Fin n) | block (j : Fin n) | sel (r : ℤ)
  deriving DecidableEq
def coords {n} : Label n → R3
  | .point i j => p i j | .block j => blocker j | .sel r => selector n r

def present {n} (S : Fin n → Finset (Fin n)) (X : Finset (Fin n)) (selectors : Finset ℤ) : Label n → Prop
  | .point i j => j∈S i | .block j => j∈X | .sel r => r∈selectors

def maximal {n} (A : Label n → Prop) (v : Label n) :=
  A v ∧ ∀ u,A u → dominates (coords u) (coords v) → u=v

theorem maxima {n} (S : Fin n → Finset (Fin n)) (X : Finset (Fin n)) (selectors : Finset ℤ)
    (r : ℤ) (top : r∈selectors) (largest : ∀ s∈selectors,s≤r) (rn : r≤n) (v : Label n) :
    maximal (present S X selectors) v ↔ match v with
    | .point i j => j∈S i ∧ j∉X ∧ r<idx i
    | .block j => j∈X
    | .sel s => s=r := by
  cases v with
  | point i j =>
    constructor
    · rintro ⟨m,h⟩; refine ⟨m,?_,?_⟩
      · intro hx; have := h (.block j) hx ((blocker_dom j i j).2 rfl); contradiction
      · by_contra! bad
        have := h (.sel r) top ((selector_dom i j r).2 bad); contradiction
    · rintro ⟨hs,hx,hi⟩; refine ⟨hs,?_⟩
      intro u hu h
      cases u with
      | point a b => obtain ⟨rfl,rfl⟩ := (points_dom a b i j).1 h; rfl
      | block k => cases (blocker_dom k i j).1 h; exact False.elim (hx hu)
      | sel s => have := largest s hu; have := (selector_dom i j s).1 h; omega
  | block j =>
    constructor
    · exact fun h => h.1
    · intro m; refine ⟨m,?_⟩
      intro u hu h
      cases u with
      | point a b => exact False.elim (point_no_block a b j h)
      | block k => rw [(blockers_dom k j).1 h]
      | sel s => exact False.elim (sel_no_block j ((largest s hu).trans rn) h)
  | sel s =>
    constructor
    · rintro ⟨hs,h⟩
      have sr := largest s hs
      have e := h (.sel r) top (show dominates (selector n r) (selector n s) from ⟨le_rfl,le_rfl,sr⟩)
      cases e; rfl
    · intro sr; subst s; refine ⟨top,?_⟩
      intro u hu h
      cases u with
      | point a b => exact False.elim (point_no_sel a b r h)
      | block j => exact False.elim (block_no_sel j r h)
      | sel s => have rs : r≤s := h.2.2; rw [le_antisymm (largest s hu) rs]

def surviving {n} (S : Fin n → Finset (Fin n)) (X : Finset (Fin n)) (r : ℤ) :
    Finset (Fin n × Fin n) := univ.filter fun ij => ij.2∈S ij.1 ∧ ij.2∉X ∧ r<idx ij.1
def pointTag {n} (ij : Fin n × Fin n) := Label.point ij.1 ij.2
def maximalSet {n} (S : Fin n → Finset (Fin n)) (X : Finset (Fin n)) (r : ℤ) :=
  (surviving S X r).image pointTag ∪ X.image Label.block ∪ {Label.sel r}

theorem maximalSet_correct {n} (S : Fin n → Finset (Fin n)) (X : Finset (Fin n)) (selectors : Finset ℤ)
    (r : ℤ) (top : r∈selectors) (largest : ∀ s∈selectors,s≤r) (rn : r≤n) :
    ∀ v,v∈maximalSet S X r ↔ maximal (present S X selectors) v := by
  intro v
  rw [maxima S X selectors r top largest rn]
  cases v <;> simp [maximalSet,surviving,pointTag,Prod.exists]

theorem maximalSet_card {n} (S : Fin n → Finset (Fin n)) (X : Finset (Fin n)) (r : ℤ) :
    (maximalSet S X r).card=(surviving S X r).card+X.card+1 := by
  have dj : Disjoint ((surviving S X r).image pointTag) (X.image Label.block) := by
    apply disjoint_left.2; intro v a b
    obtain ⟨ij,_,rfl⟩ := mem_image.1 a
    obtain ⟨j,_,e⟩ := mem_image.1 b; contradiction
  have ds : Disjoint ((surviving S X r).image pointTag ∪ X.image Label.block) {Label.sel r} := by
    simp [Finset.disjoint_singleton_right,pointTag,Prod.exists]
  have ti : Function.Injective (@pointTag n) := by
    rintro ⟨a,b⟩ ⟨c,d⟩ h; simpa [pointTag] using h
  unfold maximalSet
  rw [card_union_of_disjoint ds,card_union_of_disjoint dj,card_image_of_injective _ ti,
    card_image_of_injective _ (fun _ _ e => Label.block.inj e),card_singleton]

theorem maxima_query {n} (S : Fin n → Finset (Fin n)) (X : Finset (Fin n)) (q : Fin n) :
    (maximalSet S X (idx q-1)).card-(maximalSet S X (idx q)).card=((S q)\X).card := by
  let layer := ((S q)\X).image (fun j => (q,j))
  have eq : surviving S X (idx q-1)=surviving S X (idx q) ∪ layer := by
    ext ij
    obtain ⟨i,j⟩ := ij
    by_cases e : i=q
    · subst i; simp [surviving,layer]
    · have other : idx i≠idx q := fun h => e (idx_eq h)
      simp [surviving,layer,Ne.symm e]
      omega
  have dis : Disjoint (surviving S X (idx q)) layer := by
    apply disjoint_left.2; intro ij a b
    obtain ⟨j,_,rfl⟩ := mem_image.1 b
    simp [surviving] at a
  have card : layer.card=((S q)\X).card := card_image_of_injective _ (fun _ _ e => (Prod.mk.inj e).2)
  rw [maximalSet_card,maximalSet_card,eq,card_union_of_disjoint dis,card]
  omega

def width (n : ℕ) : ℤ := 4*n+4
def rowPoint {n} (i j : Fin n) : ℤ × ℤ := (width n*idx i+idx j,width n*((n:ℤ)+1-idx i))
def insertPoint {n} (j : Fin n) : ℤ × ℤ := (idx j,0)
def inRect {n} (q : Fin n) (v : ℤ × ℤ) :=
  0≤v.1 ∧ v.1≤width n*idx q+n ∧ 0≤v.2 ∧ v.2≤width n*((n:ℤ)+1-idx q)

theorem row_rect {n} (q i j : Fin n) : inRect q (rowPoint i j) ↔ i=q := by
  have Q := bounds q
  have I := bounds i
  have J := bounds j
  have w : 0<width n := by dsimp [width]; omega
  have big : (n:ℤ)<width n := by dsimp [width]; omega
  dsimp only [rowPoint,inRect,Prod.fst,Prod.snd]
  constructor
  · rintro ⟨_,a,_,b⟩
    have qi := (mul_le_mul_left w).mp b
    apply idx_eq
    by_contra ne
    have d : idx q+1≤idx i := by omega
    have e := mul_le_mul_of_nonneg_left d w.le
    linarith only [a,J.1,big,e]
  · rintro rfl
    have Z := mul_nonneg w.le (show 0≤idx i by omega)
    refine ⟨by linarith,by linarith,mul_nonneg w.le (by omega),le_rfl⟩

theorem insert_rect {n} (q j : Fin n) : inRect q (insertPoint j) := by
  have Q := bounds q
  have J := bounds j
  have w : 0≤width n := by dsimp [width]; omega
  have z := mul_nonneg w (show 0≤idx q by omega)
  have y := mul_nonneg w (show 0≤(n:ℤ)+1-idx q by omega)
  dsimp [inRect,insertPoint]; omega

theorem color_set {n} (S : Fin n → Finset (Fin n)) (X : Finset (Fin n)) (q j : Fin n) :
    ((∃ i,j∈S i ∧ inRect q (rowPoint i j)) ∨ (j∈X ∧ inRect q (insertPoint j))) ↔ j∈S q ∪ X := by
  simp [row_rect,insert_rect]
theorem color_count {n} (S : Fin n → Finset (Fin n)) (X : Finset (Fin n)) (q : Fin n) :
    ((S q)∪X).card+((S q)∩X).card=(S q).card+X.card := card_union_add_card_inter _ _

end
end DisjointnessDraft.Applications.Points
