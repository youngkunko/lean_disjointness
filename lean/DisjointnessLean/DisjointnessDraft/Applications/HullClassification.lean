import DisjointnessDraft.Applications.HullApex
import DisjointnessDraft.Applications.HullBlocker
import DisjointnessDraft.Applications.HullInteger

/-! The complete finite hull-selector classification, stable under independent
perturbations of all three coordinates. The rounded integer-coordinate
dynamic lower bound follows using the three-selector physical reduction. -/
namespace DisjointnessDraft.Applications.HullClassification
open Hull HullConfig HullAngles HullHidden HullNeighbors HullExposure Real Finset Classical
noncomputable section
private theorem not_extreme {n I} (f : Label n → Point) (inj : Function.Injective f)
    (P : Finset (Label n)) (v : Label n) (W : I → Label n) (ok : ∀ i,W i∈P ∧ W i≠v)
    (contains : f v∈convexHull ℝ (Set.range (f ∘ W))) :
    f v∉(convexHull ℝ (f '' (↑P : Set (Label n)))).extremePoints ℝ := by
  let A := f '' (↑(P.erase v) : Set (Label n))
  have inside : Set.range (f ∘ W) ⊆ A := by
    rintro _ ⟨i,rfl⟩; exact ⟨_,Finset.mem_erase.mpr ⟨(ok i).2,(ok i).1⟩,rfl⟩
  have same : convexHull ℝ (f '' (↑P : Set (Label n)))=convexHull ℝ A := by
    apply Set.Subset.antisymm
    · apply convexHull_min _ (convex_convexHull _ _)
      rintro _ ⟨i,mi,rfl⟩
      by_cases eq : i=v
      · subst i; exact convexHull_mono inside contains
      · exact subset_convexHull ℝ A ⟨i,Finset.mem_erase.mpr ⟨eq,mi⟩,rfl⟩
    · exact convexHull_mono (Set.image_mono (by exact_mod_cast (Finset.erase_subset v P)))
  rw [same]
  intro m
  obtain ⟨i,mi,eq⟩ := extremePoints_convexHull_subset m
  exact (mem_erase.mp mi).1 (inj eq)

private theorem different {n} (n5 : 5≤n) (j : Fin n) : next j≠j ∧ prev j≠j := by
  have jn := j.isLt
  constructor <;> intro e <;> have z := congrArg Fin.val e <;> simp only [next,prev] at z <;> split_ifs at z <;> simp_all <;> omega

private theorem hidden {n} (n5 : 5≤n) (f : Label n → Point) (motion : ∀ v i,|f v i-coords n v i|≤eps n)
    (S : Family n) (X : Finset (Fin n)) (T : Finset (Fin (n+1))) (v : Label n)
    (presentV : v∈present S X T) (hid : v∉visible S X T) :
    f v∉(convexHull ℝ (f '' (↑(present S X T) : Set (Label n)))).extremePoints ℝ := by
  classical
  have inj := HullInteger.perturbed_injective f n5 motion
  have casesBlock (j : Fin n) (h : ℝ) (h2 : 2≤h) (hH : h≤height n)
      (loc : coords n v=column j (radius n-h^2) h) (mem : j∈X)
      (diff : ∀ k,HullBlocker.witnesses j k≠v) :
      f v∉(convexHull ℝ (f '' (↑(present S X T) : Set (Label n)))).extremePoints ℝ := by
    apply not_extreme f inj _ v (HullBlocker.witnesses j)
    · intro k; refine ⟨?_,diff k⟩; fin_cases k <;> simp [HullBlocker.witnesses,present,mem]
    · apply HullBlocker.enclosed n5 j h h2 hH (f v) (f ∘ HullBlocker.witnesses j)
      · intro i; simpa only [←loc] using motion v i
      · exact fun k i => motion _ i
  have casesCut (j : Fin n) (a : Fin (n+1)) (h : ℝ) (h2 : 2*(a.val:ℝ)+2≤h) (hH : h≤height n)
      (loc : coords n v=column j (radius n-h^2) h) (mem : a∈T)
      (diff : ∀ k,HullCone.witnesses j a k≠v) :
      f v∉(convexHull ℝ (f '' (↑(present S X T) : Set (Label n)))).extremePoints ℝ := by
    apply not_extreme f inj _ v (HullCone.witnesses j a)
    · intro k; refine ⟨?_,diff k⟩; fin_cases k <;> simp [HullCone.witnesses,present,mem]
    · apply HullCone.enclosed n5 j a h h2 hH (f v) (f ∘ HullCone.witnesses j a)
      · intro i; simpa only [←loc] using motion v i
      · exact fun k i => motion _ i
  cases v with
  | guard i j =>
    have ne : i.val≠0 := by intro z; exact hid (by simp [visible,show i=0 from Fin.ext z])
    have hH : 2*(i.val:ℝ)+1≤height n := by
      have h : (i.val:ℝ)≤n := by exact_mod_cast (show i.val≤n by have := i.isLt; omega)
      dsimp [height]; linarith
    by_cases block : j∈X
    · apply casesBlock j (2*(i.val:ℝ)+1) (by exact_mod_cast (show 2≤2*i.val+1 by omega)) hH rfl block
      intro k; have e : i≠0 := fun eq => ne (by rw [eq]; rfl)
      fin_cases k <;> simp [HullBlocker.witnesses,different n5 j,Ne.symm e]
    · obtain ⟨a,atop,low⟩ : ∃ a∈T,a.val < i.val := by
        apply Classical.byContradiction; intro none; apply hid; simp only [visible,mem_filter,mem_univ,true_and]; exact Or.inr ⟨block,fun a ha => le_of_not_gt (fun lt => none ⟨a,ha,lt⟩)⟩
      apply casesCut j a (2*(i.val:ℝ)+1) (by exact_mod_cast (show 2*a.val+2≤2*i.val+1 by omega)) hH rfl atop
      have neq : a≠i := by intro eq; subst a; omega
      intro k; fin_cases k <;> simp [HullCone.witnesses,neq]
  | datum i j =>
    have sm : j∈S i := by simpa [present] using presentV
    have hH : 2*((i.val:ℝ)+1)≤height n := by
      have h : (i.val:ℝ)+1≤n := by exact_mod_cast i.isLt
      dsimp [height]; linarith
    by_cases block : j∈X
    · apply casesBlock j (2*((i.val:ℝ)+1)) (by linarith [show (0:ℝ) ≤ i.val by positivity]) hH rfl block
      intro k; fin_cases k <;> simp [HullBlocker.witnesses]
    · obtain ⟨a,atop,low⟩ : ∃ a∈T,a.val ≤ i.val := by
        apply Classical.byContradiction; intro none; apply hid; simp only [visible,mem_filter,mem_univ,true_and]; exact ⟨sm,block,fun a ha => lt_of_not_ge (fun le => none ⟨a,ha,le⟩)⟩
      apply casesCut j a (2*((i.val:ℝ)+1)) (by exact_mod_cast (show 2*a.val+2≤2*(i.val+1) by omega)) hH rfl atop
      intro k; fin_cases k <;> simp [HullCone.witnesses]
  | block j => simp_all [present,visible]
  | sel t =>
    have mt : t∈T := by simpa [present] using presentV
    obtain ⟨s,sm,lt⟩ : ∃ s∈T,s < t := by
      apply Classical.byContradiction; intro none; apply hid; simp only [visible,mem_filter,mem_univ,true_and]; exact ⟨mt,fun s hs => le_of_not_gt (fun lt => none ⟨s,hs,lt⟩)⟩
    apply not_extreme f inj _ _ (HullApex.witnesses s)
    · intro k; cases k <;> simp [HullApex.witnesses,present,sm,ne_of_lt lt]
    · exact HullApex.enclosed n5 s t lt (f (.sel t)) (f ∘ HullApex.witnesses s) (motion _) (fun _ => motion _)

theorem robust {n} (n5 : 5≤n) (f : Label n → Point) (motion : ∀ v i,|f v i-coords n v i|≤eps n)
    (S : Family n) (X : Finset (Fin n)) (T : Finset (Fin (n+1))) :
    classification f S X T := by
  apply Set.Subset.antisymm
  · intro x ex
    obtain ⟨v,vp,rfl⟩ := extremePoints_convexHull_subset ex
    by_cases on : v∈visible S X T
    · exact ⟨v,on,rfl⟩
    · exact False.elim ((hidden n5 f motion S X T v vp on) ex)
  · rintro _ ⟨v,h,rfl⟩
    exact robust_vertex n5 f motion S X T v h

theorem exact {n} (n5 : 5≤n) (S : Family n) (X : Finset (Fin n)) (T : Finset (Fin (n+1))) :
    classification (coords n) S X T := robust n5 _ (by intro v i; simp [eps]; positivity) S X T

theorem snapped {n} (n5 : 5≤n) (S : Family n) (X : Finset (Fin n)) (T : Finset (Fin (n+1))) :
    classification (HullRounding.snapped n) S X T :=
  robust n5 _ (HullRounding.small_error n5) S X T

theorem integer_lower (lo hi : ℝ) (lp : 0<lo) (lh : lo≤hi) :
    ∃c : ℝ,0<c ∧ ∀ᶠ N : ℕ in Filter.atTop,ShortTransfer.Bound lo hi c N true (HullCosts.legal N) HullCosts.spec :=
  HullInteger.lower_of_snapped lo hi lp lh (fun _ h S X T => snapped h S X T)
end
end DisjointnessDraft.Applications.HullClassification
