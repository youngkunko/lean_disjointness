import DisjointnessDraft.Applications.Matching
import Mathlib.Data.Nat.Find
import Mathlib.Data.Fintype.Sum

/-! Maximum matching size as the greatest size of two injective endpoint
lists whose pairs are literal edges. The padding adds independent matched
pairs and, on odd sizes, one isolated right vertex. -/
namespace DisjointnessDraft.Applications.MatchingSize
open Classical
noncomputable section
variable {L R : Type} [Fintype L] [Fintype R]
def Admits (E : L → R → Prop) (k : ℕ) := ∃ l : Fin k ↪ L, ∃ r : Fin k ↪ R,∀ i,E (l i) (r i)
def maximum (E : L → R → Prop) := Nat.findGreatest (Admits E) (Fintype.card L)
def Full (E : L → R → Prop) := ∃ g : L ↪ R,∀ x,E x (g x)
def Perfect (E : L → R → Prop) := ∃ g : L ≃ R,∀ x,E x (g x)

omit [Fintype R] in
theorem largest [Fintype R] (E : L → R → Prop) : maximum E=Fintype.card L ↔ Full E := by
  have empty : Admits E 0 := ⟨⟨Fin.elim0,fun i => i.elim0⟩,⟨Fin.elim0,fun i => i.elim0⟩,fun i => i.elim0⟩
  constructor
  · intro eq
    have z := Nat.findGreatest_spec (n:=Fintype.card L) (Nat.zero_le _) empty
    change Admits E (maximum E) at z; rw [eq] at z
    obtain ⟨l,r,edges⟩ := z
    let e := Equiv.ofBijective l ((Fintype.bijective_iff_injective_and_card l).mpr ⟨l.injective,by simp⟩)
    refine ⟨e.symm.toEmbedding.trans r,fun x => ?_⟩
    have h : E (e (e.symm x)) (r (e.symm x)) := edges (e.symm x)
    simpa using h
  · rintro ⟨g,edges⟩
    let e := (Fintype.equivFin L).symm.toEmbedding
    exact Nat.findGreatest_eq (P:=Admits E) ⟨e,e.trans g,fun i => edges (e i)⟩

theorem perfect (E : L → R → Prop) (bal : Fintype.card L=Fintype.card R) : Perfect E ↔ Full E := by
  constructor
  · rintro ⟨e,h⟩; exact ⟨e.toEmbedding,h⟩
  · rintro ⟨e,h⟩
    exact ⟨Equiv.ofBijective e ((Fintype.bijective_iff_injective_and_card e).mpr ⟨e.injective,bal⟩),h⟩

abbrev Core (n : ℕ) := Matching.V (Fin n) (Fin n)
abbrev Left (n pad : ℕ) := Core n ⊕ Fin pad
abbrev Right (n pad extra : ℕ) := Left n pad ⊕ Fin extra

def padded (E : Core n → Core n → Prop) : Left n p → Right n p r → Prop
  | .inl a,.inl (.inl b) => E a b
  | .inr a,.inl (.inr b) => a=b
  | _,_ => False

theorem padded_full (E : Core n → Core n → Prop) :
    Full (padded (p:=p) (r:=r) E) ↔ Matching.Perfect E := by
  constructor
  · rintro ⟨g,h⟩
    have witness (a : Core n) : ∃ b : Core n,g (.inl a)=.inl (.inl b) ∧ E a b := by
      have v := h (.inl a)
      rcases eq : g (.inl a) with (b|b)|b
      · exact ⟨b,rfl,by simpa [eq,padded] using v⟩
      · simp [eq,padded] at v
      · simp [eq,padded] at v
    choose f eq ok using witness
    have inj : Function.Injective f := by
      intro a b e
      have t := g.injective ((eq a).trans (by rw [e,←eq b]))
      simpa using t
    exact ⟨Equiv.ofBijective f ⟨inj,Finite.surjective_of_injective inj⟩,ok⟩
  · rintro ⟨f,ok⟩
    let g := (Equiv.sumCongr f (Equiv.refl (Fin p))).toEmbedding.trans (Function.Embedding.inl : Left n p ↪ Right n p r)
    refine ⟨g,?_⟩; rintro (a|b)
    · exact ok a
    · exact rfl

def coreEquiv (n : ℕ) : Core n ≃ Unit ⊕ (Fin n ⊕ Fin n) where
  toFun | .endpt => .inl () | .row q => .inr (.inl q) | .col x => .inr (.inr x)
  invFun | .inl _ => .endpt | .inr (.inl q) => .row q | .inr (.inr x) => .col x
  left_inv a := by cases a <;> rfl
  right_inv a := by rcases a with ⟨⟩|(q|x) <;> rfl

@[simp] theorem core_card (n : ℕ) : Fintype.card (Core n)=1+n+n := by
  simpa [Nat.add_assoc] using Fintype.card_congr (coreEquiv n)
def leftCount (n p : ℕ) := 1+n+n+p
@[simp] theorem left_card : Fintype.card (Left n p)=leftCount n p := by simp [Left,leftCount]
@[simp] theorem right_card : Fintype.card (Right n p r)=leftCount n p+r := by simp [Right,leftCount]

end
end DisjointnessDraft.Applications.MatchingSize
