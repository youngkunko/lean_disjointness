import Mathlib.Tactic.Linarith

/-! Integer-weighted directed walks, and the one-edge reduction from
distance in a directed acyclic graph to directed girth. -/
namespace DisjointnessDraft.Applications.WeightedWalk
variable {V : Type}
inductive Path (E : V → ℤ → V → Prop) : V → ℤ → V → Prop
  | nil (v) : Path E v 0 v
  | snoc {s a b d t} : Path E s d a → E a t b → Path E s (d+t) b

theorem Path.append {E : V → ℤ → V → Prop} {a b c d t} (f : Path E a d b) (g : Path E b t c) : Path E a (d+t) c := by
  induction g with
  | nil => simpa using f
  | snoc _ e ih => simpa only [add_assoc] using ih.snoc e

theorem Path.mono {E F : V → ℤ → V → Prop} {a b d} (h : ∀ u t v,E u t v → F u t v) (f : Path E a d b) :
    Path F a d b := by
  induction f with | nil => exact .nil _ | snoc _ e ih => exact ih.snoc (h _ _ _ e)

theorem Path.nonneg {E : V → ℤ → V → Prop} {a b d} (pos : ∀ u t v,E u t v → 0≤t) (f : Path E a d b) : 0≤d := by
  induction f with | nil => rfl | snoc _ e ih => exact add_nonneg ih (pos _ _ _ e)

def addBack (E : V → ℤ → V → Prop) (src dst : V) (a : V) (k : ℤ) (b : V) :=
  E a k b ∨ (a=dst ∧ k=1 ∧ b=src)

private theorem split {E : V → ℤ → V → Prop} {a b src dst d} (p : Path (addBack E src dst) a d b) :
    Path E a d b ∨ ∃ k l,Path E a k dst ∧ Path (addBack E src dst) src l b ∧ d=k+1+l := by
  induction p with
  | nil => exact Or.inl (.nil _)
  | snoc _ edge ih =>
    rcases ih with r|⟨k,l,r,s,eq⟩
    · rcases edge with f|⟨rfl,rfl,rfl⟩
      · exact Or.inl (r.snoc f)
      · exact Or.inr ⟨_,0,r,.nil _,by omega⟩
    · exact Or.inr ⟨k,_,r,s.snoc edge,by omega⟩

theorem girth {E : V → ℤ → V → Prop} (rank : V → ℤ)
    (increases : ∀ u t v,E u t v → rank u<rank v) (pos : ∀ u t v,E u t v → 0≤t)
    {src dst d} (attain : Path E src d dst) (minimize : ∀ k,Path E src k dst → d≤k) :
    Path (addBack E src dst) src (d+1) src ∧ 0<d+1 ∧
      ∀ a k,0<k → Path (addBack E src dst) a k a → d+1≤k := by
  have pos' u t v (e : addBack E src dst u t v) : 0≤t := by rcases e with e|⟨_,rfl,_⟩; exact pos _ _ _ e; decide
  have ranks {u k v} (f : Path E u k v) : (u=v ∧ k=0) ∨ rank u<rank v := by
    induction f with
    | nil => exact Or.inl ⟨rfl,rfl⟩
    | snoc _ e ih =>
      have nxt := increases _ _ _ e
      rcases ih with ⟨rfl,_⟩|h <;> exact Or.inr (by omega)
  refine ⟨(attain.mono (fun _ _ _ e => Or.inl e)).snoc (Or.inr ⟨rfl,rfl,rfl⟩),by have := attain.nonneg pos; omega,?_⟩
  intro a k kpos w
  rcases split w with path|⟨c,l,first,tail,eq⟩
  · have := ranks path; omega
  · rcases split tail with rest|⟨c',l',first',end',eq'⟩
    · have := minimize _ (rest.append first); omega
    · have := minimize _ first'
      have := first.nonneg pos; have := end'.nonneg pos'; omega

end DisjointnessDraft.Applications.WeightedWalk
