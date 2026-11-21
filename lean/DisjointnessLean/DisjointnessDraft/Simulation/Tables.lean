import DisjointnessFoundations.FiniteTraceEncoding
import Mathlib.Data.Fintype.Option
import Mathlib.Data.Finset.Sort
import Mathlib.Tactic

/-! Bounded partial tables represent lists of distinct address/content pairs,
independently of order. A length field and a padded ordered list encode them. -/
namespace DisjointnessDraft.PhysicalProtocol
open DisjointnessFoundations
open Classical
noncomputable section
abbrev Cell (w : ℕ) := Fin (2^w)
def domain (v : Cell w → Option (Cell w)) : Finset (Cell w) :=
  Finset.univ.filter (fun a => (v a).isSome)

@[simp] theorem in_domain (v : Cell w → Option (Cell w)) (a : Cell w) :
    a∈domain v ↔ (v a).isSome := by simp [domain]

abbrev Table (w cap : ℕ) := {v : Cell w → Option (Cell w) // (domain v).card ≤ cap}

def table (S : Finset (Cell w)) (f : Cell w → Cell w) (h : S.card≤cap) : Table w cap :=
  ⟨fun a => if a∈S then some (f a) else none,by
    have e : domain (fun a => if a∈S then some (f a) else none)=S := by
      ext a; by_cases a∈S <;> simp_all
    rwa [e]⟩

@[simp] theorem table_val (S : Finset (Cell w)) (f : Cell w → Cell w) (h : S.card≤cap) (a : Cell w) :
    (table S f h).val a = if a∈S then some (f a) else none := rfl

@[simp] theorem table_domain (S : Finset (Cell w)) (f : Cell w → Cell w) (h : S.card≤cap) :
    domain (table S f h).val=S := by ext a; by_cases a∈S <;> simp_all

abbrev ListCode (w k : ℕ) := Fin (k+1) × (Fin k → Cell w × Cell w)
private def entries (t : Table w k) := (domain t.1).toList.map (fun a => (a,(t.1 a).getD 0))
private theorem entries_mem (t : Table w k) (a v : Cell w) :
    (a,v)∈entries t ↔ t.val a=some v := by
  simp only [entries,List.mem_map,Finset.mem_toList,in_domain,Prod.mk.injEq]
  constructor
  · rintro ⟨y,hy,rfl,eq⟩; cases h : t.val y <;> simp_all
  · intro eq; exact ⟨_,by simp [eq],rfl,by simp [eq]⟩

private def pack (t : Table w k) : ListCode w k :=
  let code := Description.encodeTrace w k ⟨entries t,none⟩
  (code.1,code.2.1)

private theorem pack_injective : Function.Injective (@pack w k) := by
  intro t u h
  have eq : entries t=entries u := by
    let read := fun c : ListCode w k => (Description.decodeTrace w k (c.1,c.2,none)).probes
    have recover (z : Table w k) : read (pack z) = entries z := by
      change (Description.decodeTrace w k (Description.encodeTrace w k ⟨entries z,none⟩)).probes=_
      rw [Description.decode_encode]
      simpa [entries] using z.2
    rw [←recover t,←recover u,h]
  apply Subtype.ext
  funext a
  have atWord (v : Cell w) : t.val a=some v ↔ u.val a=some v := by rw [←entries_mem,←entries_mem,eq]
  cases e : t.val a with
  | some v => exact ((atWord v).mp e).symm
  | none =>
    cases f : u.val a with
    | none => rfl
    | some v => have := (atWord v).mpr f; simp_all

theorem table_card (w k : ℕ) : Fintype.card (Table w k) ≤ (k+1)*2^(2*w*k) := by
  have e := Fintype.card_le_of_injective _ (@pack_injective w k)
  simpa [ListCode,Cell,←pow_add,←pow_mul,two_mul] using e

def sampled (t : Table w k) (bits : Cell w → Bool) :=
  (domain t.1).filter (fun a => bits a)

abbrev Advice (w ek lk : ℕ) := Table w ek × Table w lk
abbrev Packet (w lk sampleCap : ℕ) := Option (Table w (lk+sampleCap))

def listed (u : Advice w ek lk) (a : Cell w) : Option (Cell w) := (u.2.val a).or (u.1.val a)

def send (u : Advice w ek lk) (bits : Cell w → Bool) (limit : ℕ) : Packet w lk limit :=
  let E := sampled u.1 bits
  if good : E.card≤limit then
    some (table (domain u.2.val ∪ E) (fun a => (listed u a).getD 0)
      (le_trans (Finset.card_union_le _ _) (Nat.add_le_add u.2.2 good)))
  else none

end
end DisjointnessDraft.PhysicalProtocol
