import DisjointnessDraft.Model
import DisjointnessDraft.Applications.HullStability
import Mathlib.Data.Matrix.Notation
import Mathlib.Tactic.DeriveFintype

/-! The finite configuration, its real coordinates, and the exact change in
vertex count read by successive selectors. The geometric classification is
stated explicitly so that its combinatorial and geometric parts can be used
independently. -/
namespace DisjointnessDraft.Applications.HullConfig
open Classical Finset Real
noncomputable section
inductive Label (n : ℕ) where
  | guard (i : Fin (n+1)) (j : Fin n) | datum (i j : Fin n) | block (j : Fin n) | sel (a : Fin (n+1))
  deriving DecidableEq,Fintype
abbrev Point := Fin 3 → ℝ

def angle {n} (j : Fin n) := 2*π*((j.val:ℝ)+1)/n
def column {n} (j : Fin n) (rad h : ℝ) : Point := ![rad*cos (angle j),rad*sin (angle j),h]
def coords (n : ℕ) : Label n → Point
  | .guard i j => let h : ℝ := 2*i.val+1; column j (Hull.radius n-h^2) h
  | .datum i j => let h : ℝ := 2*(i.val+1); column j (Hull.radius n-h^2) h
  | .block j => column j (Hull.radius n-1) (Hull.height n+1)
  | .sel a => ![0,0,Hull.selector (Hull.radius n) (2*a.val+1)]

def present {n} (S : Family n) (X : Finset (Fin n)) (T : Finset (Fin (n+1))) :=
  univ.filter fun v : Label n => match v with
    | .guard _ _ => True | .datum i j => j∈S i | .block j => j∈X | .sel a => a∈T
def visible {n} (S : Family n) (X : Finset (Fin n)) (T : Finset (Fin (n+1))) :=
  univ.filter fun v : Label n => match v with
    | .guard i j => i.val=0 ∨ (j∉X ∧ ∀ a∈T,i.val≤a.val)
    | .datum i j => j∈S i ∧ j∉X ∧ ∀ a∈T,i.val<a.val
    | .block j => j∈X
    | .sel a => a∈T ∧ ∀ b∈T,a≤b
def classification {n} (f : Label n → Point) (S : Family n) (X : Finset (Fin n)) (T : Finset (Fin (n+1))) :=
  (convexHull ℝ (f '' (↑(present S X T) : Set (Label n)))).extremePoints ℝ =
    f '' (↑(visible S X T) : Set (Label n))
def count {n} (f : Label n → Point) (S : Family n) (X : Finset (Fin n)) (T : Finset (Fin (n+1))) :=
  ((convexHull ℝ (f '' (↑(present S X T) : Set (Label n)))).extremePoints ℝ).ncard

theorem count_eq {n} (f : Label n → Point) (S : Family n) (X : Finset (Fin n)) (T : Finset (Fin (n+1)))
    (inj : Function.Injective f) (cl : classification f S X T) : count f S X T=(visible S X T).card := by
  unfold count; rw [cl,Set.ncard_image_of_injective _ inj,Set.ncard_coe_Finset]

private def body {n} (S : Family n) (X : Finset (Fin n)) (c : Fin (n+1)) :=
  univ.filter fun v : Label n => match v with
    | .guard i j => i.val=0 ∨ (j∉X ∧ i≤c)
    | .datum i j => j∈S i ∧ j∉X ∧ i.val<c.val
    | .block j => j∈X | .sel _ => False

private theorem at_cut {n} (S : Family n) (X : Finset (Fin n)) (T : Finset (Fin (n+1)))
    (a : Fin (n+1)) (mem : a∈T) (least : ∀ b∈T,a≤b) :
    visible S X T=insert (Label.sel a) (body S X a) := by
  ext v; cases v with
  | guard i j =>
    have iff : (∀ b∈T,i≤b) ↔ i≤a := ⟨fun h => h a mem,fun h b hb => le_trans h (least b hb)⟩
    simp [visible,body,iff]
  | datum i j =>
    have iff : (∀ b∈T,i.val<b.val) ↔ i.val<a.val := ⟨fun h => h a mem,fun h b hb => lt_of_lt_of_le h (least b hb)⟩
    simp [visible,body,iff]
  | block j => simp [visible,body]
  | sel b =>
    simp only [visible,body,mem_filter,mem_univ,true_and,mem_insert,Label.sel.injEq,or_false]
    constructor
    · rintro ⟨hb,h⟩; exact le_antisymm (h a mem) (least b hb)
    · rintro rfl; exact ⟨mem,least⟩

theorem visible_difference {n} (S : Family n) (X : Finset (Fin n)) (hi lo : Finset (Fin (n+1))) (q : Fin n)
    (hiMem : q.succ∈hi) (hiMin : ∀ b∈hi,q.succ≤b)
    (loMem : q.castSucc∈lo) (loMin : ∀ b∈lo,q.castSucc≤b) :
    (visible S X hi).card-(visible S X lo).card=(univ \ X).card+((S q) \ X).card := by
  let G := (univ \ X).image (Label.guard q.succ)
  let D := ((S q) \ X).image (Label.datum q)
  have eq : body S X q.succ=(body S X q.castSucc ∪ G) ∪ D := by
    ext v
    cases v with
    | block j => simp [body,G,D]
    | sel a => simp [body,G,D]
    | guard i j =>
      by_cases e : i=q.succ
      · subst i; simp [body,G,D,Fin.le_def]
      · have ne : i.val≠q.val+1 := fun h => e (Fin.ext h)
        have diff : i≤q.succ ↔ i≤q.castSucc := by change (i.val≤q.val+1) ↔ i.val≤q.val; omega
        simp [body,G,D,Ne.symm e,diff]
    | datum i j =>
      by_cases e : i=q
      · subst i; simp [body,G,D]
      · have ne : i.val≠q.val := fun h => e (Fin.ext h)
        simp [body,G,D,Ne.symm e]
        omega
  have gh : Disjoint (body S X q.castSucc) G := by
    apply Finset.disjoint_left.2; intro v vb vg
    obtain ⟨j,jx,rfl⟩ := mem_image.1 vg
    simp [body,Fin.le_def] at vb
  have dh : Disjoint (body S X q.castSucc ∪ G) D := by
    apply Finset.disjoint_left.2; intro v vb vd
    obtain ⟨j,jx,rfl⟩ := mem_image.1 vd
    simp [body,G] at vb
  have gc : G.card=(univ \ X).card := card_image_of_injective _ (fun _ _ e => (Label.guard.inj e).2)
  have dc : D.card=((S q) \ X).card := card_image_of_injective _ (fun _ _ e => (Label.datum.inj e).2)
  rw [at_cut S X hi q.succ hiMem hiMin,at_cut S X lo q.castSucc loMem loMin,
    card_insert_of_not_mem (by simp [body]),card_insert_of_not_mem (by simp [body]),eq,
    card_union_of_disjoint dh,card_union_of_disjoint gh,gc,dc]
  omega

theorem count_difference {n} (f : Label n → Point) (S : Family n) (X : Finset (Fin n))
    (hi lo : Finset (Fin (n+1))) (q : Fin n) (inj : Function.Injective f)
    (cHi : classification f S X hi) (cLo : classification f S X lo)
    (hiMem : q.succ∈hi) (hiMin : ∀ b∈hi,q.succ≤b)
    (loMem : q.castSucc∈lo) (loMin : ∀ b∈lo,q.castSucc≤b) :
    count f S X hi-count f S X lo=(univ \ X).card+((S q) \ X).card := by
  rw [count_eq f S X hi inj cHi,count_eq f S X lo inj cLo]
  exact visible_difference S X hi lo q hiMem hiMin loMem loMin
end
end DisjointnessDraft.Applications.HullConfig
