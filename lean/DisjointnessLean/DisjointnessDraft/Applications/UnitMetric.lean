import DisjointnessDraft.Applications.UnitEncoding

namespace DisjointnessDraft.Applications.UnitEncoding
open FiniteSubdivision FinitePlanarDistance PlanarEncoding WeightedWalk PlanarPadding Subdivision Classical
noncomputable section
variable {n : ℕ} (hn : 0<n)
local notation "G" => mesh (dim n) (sourceDim hn)

include hn in
private theorem one {f : Family n} {xs : List (Fin n)} {a d b}
    (ed : wire (table f) (enabled xs) a d b) :
    ∃ e : Id (dim n),e.val=(a,b) ∧ (length e:ℤ)=d ∧ on f xs e := by
  let e : Id (dim n) := ⟨(a,b),⟨d,potential_of ed⟩⟩
  have eq := weight_eq ed
  have nn := weight_bounds (sourceDim hn) (rows xs) ed
  refine ⟨e,rfl,?_,?_⟩
  · dsimp [length,e]; rw [←eq,Int.toNat_of_nonneg nn.1.le]
  · change wire _ _ a (wireWeight (dim n) (PlanarMatching.place a) (PlanarMatching.place b)) b; rwa [←eq]

theorem forward {f : Family n} {xs : List (Fin n)} {a d b} (path : Path (edge (table f) (enabled xs)) a d b) :
    ∃ k : ℕ,(k:ℤ)=d ∧ Walk (withLive G (on f xs)) a k b := by
  induction path with
  | nil => exact ⟨0,rfl,.nil _⟩
  | @snoc u v k t _ ed ih =>
    obtain ⟨l,rfl,walk⟩ := ih
    rcases ed with e|e
    · obtain ⟨z,ab,len,live⟩ := one hn e
      have a : (withLive G (on f xs)).src z=u := congrArg Prod.fst ab
      have b : (withLive G (on f xs)).dst z=v := congrArg Prod.snd ab
      rw [←a] at walk; obtain rfl := b
      exact ⟨l+length z,by simp [len],walk.forward z live⟩
    · obtain ⟨z,ab,len,live⟩ := one hn e
      have a : (withLive G (on f xs)).src z=v := congrArg Prod.fst ab
      have b : (withLive G (on f xs)).dst z=u := congrArg Prod.snd ab
      rw [←b] at walk; obtain rfl := a
      exact ⟨l+length z,by simp [len],walk.backward z live⟩

theorem backward {f : Family n} {xs : List (Fin n)} {a d b} (path : Walk (withLive G (on f xs)) a d b) :
    Path (edge (table f) (enabled xs)) a d b := by
  have actual (e : Id (dim n)) (onE : on f xs e) :
      wire (table f) (enabled xs) e.val.1 (length e:ℤ) e.val.2 := by
    have e' := weight_eq (has_weight e (sourceDim hn)).1
    simpa only [e'] using onE
  induction path with
  | nil => exact .nil _
  | forward e w onE ih => rw [Nat.cast_add]; exact ih.snoc (Or.inl (actual e onE))
  | backward e w onE ih => rw [Nat.cast_add]; exact ih.snoc (Or.inr (actual e onE))

theorem distance (f : Family n) (xs : List (Fin n)) (q : Fin n) :
    let d : ℤ := 2*PlanarCore.H (dim n) - (if ∃x∈xs,x∈f q then 1 else 0)
    let term := UnitEncoding.query hn q
    Path (sym (unit G (on f xs))) term.1 d term.2 ∧
    ∀ t,Path (sym (unit G (on f xs))) term.1 t term.2 → d≤t := by
  intro d term
  have orig := PlanarEncoding.encoded_distance (pad:=0) f xs q
  obtain ⟨c,le,core⟩ := lower_path orig.1
  have cap : d≤c := orig.2 c (upper_path (root n) core)
  obtain rfl := le_antisymm le cap
  obtain ⟨k,eq,weighted⟩ := forward hn core
  let G' := withLive G (on f xs)
  let uv := start q.castSucc
  let vv := finishLine q.castSucc
  have all (l : ℕ) (w : Walk G' uv l vv) : k≤l := by
    have bound := orig.2 l (upper_path (root n) (backward hn w))
    omega
  obtain ⟨uw,m⟩ := Subdivision.distance G' weighted all
  refine ⟨?_,?_⟩
  · have exactK : (k:ℤ)=d := eq
    rw [←exactK]; exact unit_paths G (on f xs) _ _ k uw
  · intro t p
    obtain ⟨j,rfl,h⟩ := from_paths G (on f xs) p
    have le := m j h; omega

end
end DisjointnessDraft.Applications.UnitEncoding
