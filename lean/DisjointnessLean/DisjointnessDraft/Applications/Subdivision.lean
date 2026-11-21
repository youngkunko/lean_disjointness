import Mathlib.Data.Nat.Find
import Mathlib.Tactic.Linarith

/-! Subdivision of positive integral edges, including a link whose first unit
edge is missing until it is enabled. All its other vertices and unit edges
remain present. The exact distances between original vertices are preserved. -/
namespace DisjointnessDraft.Applications.Subdivision
open Classical
noncomputable section
structure Graph (V E : Type) where
  src : E → V
  dst : E → V
  len : E → ℕ
  positive : ∀ e,0<len e
  enabled : E → Prop
variable {V E : Type} (G : Graph V E)
inductive Walk : V → ℕ → V → Prop
  | nil (s) : Walk s 0 s
  | forward {s d} (e) : Walk s d (G.src e) → G.enabled e → Walk s (d+G.len e) (G.dst e)
  | backward {s d} (e) : Walk s d (G.dst e) → G.enabled e → Walk s (d+G.len e) (G.src e)

inductive Node where | core (v : V) | inner (e : E) (k : Fin (G.len e-1))
def atPos (e : E) (k : ℕ) : Node G :=
  if z : k=0 then .core (G.src e) else if h : k<G.len e then .inner e ⟨k-1,by omega⟩ else .core (G.dst e)

inductive UnitStep : Node G → Node G → Prop
  | along (e : E) (k : ℕ) (within : k<G.len e) (first : G.enabled e ∨ 0<k) : UnitStep (atPos G e k) (atPos G e (k+1))

inductive UnitWalk : Node G → ℕ → Node G → Prop
  | nil (u) : UnitWalk u 0 u
  | snoc {a b c d} : UnitWalk a d b → (UnitStep G b c ∨ UnitStep G c b) → UnitWalk a (d+1) c

private theorem append {a b c d t} (p : UnitWalk G a d b) (q : UnitWalk G b t c) : UnitWalk G a (d+t) c := by
  induction q with
  | nil => simpa using p
  | snoc _ e ih => exact ih.snoc e

private theorem reverse {a b d} (p : UnitWalk G a d b) : UnitWalk G b d a := by
  induction p with
  | nil => exact .nil _
  | snoc _ e ih =>
    have s := (UnitWalk.nil _).snoc e.symm
    simpa [Nat.add_comm] using append G s ih

private theorem strand (e : E) (on : G.enabled e) : UnitWalk G (.core (G.src e)) (G.len e) (.core (G.dst e)) := by
  have part (k : ℕ) (within : k≤G.len e) : UnitWalk G (.core (G.src e)) k (atPos G e k) := by
    induction k with
    | zero => exact .nil _
    | succ k ih => exact (ih (by omega)).snoc (Or.inl (.along e k (by omega) (Or.inl on)))
  simpa [atPos,Nat.ne_zero_of_lt (G.positive e)] using part (G.len e) le_rfl

theorem expand {s t d} (p : Walk G s d t) : UnitWalk G (.core s) d (.core t) := by
  induction p with
  | nil => exact .nil _
  | forward e _ on ih => exact append G ih (strand G e on)
  | backward e _ on ih => exact append G ih (reverse G (strand G e on))

private def Reached (s v : V) := ∃ d,Walk G s d v
private def dist (s v : V) := if h : Reached G s v then Nat.find h else 0
private theorem reached_dist {s v} (p : Reached G s v) : Walk G s (dist G s v) v := by
  rw [dist,dif_pos p]; exact Nat.find_spec p
private theorem shortest {s v d} (p : Walk G s d v) : dist G s v≤d := by
  rw [dist,dif_pos (show Reached G s v from ⟨d,p⟩)]
  exact Nat.find_min' _ p

private theorem near (s : V) (e : E) (on : G.enabled e) :
    dist G s (G.src e)≤dist G s (G.dst e)+G.len e ∧ dist G s (G.dst e)≤dist G s (G.src e)+G.len e := by
  by_cases h : Reached G s (G.src e)
  · have r := (reached_dist G h).forward e on
    exact ⟨shortest G ((reached_dist G ⟨_,r⟩).backward e on),shortest G r⟩
  · have n : ¬Reached G s (G.dst e) := fun ⟨d,r⟩ => h ⟨_,r.backward e on⟩
    simp [dist,h,n]

private def onStrand (s : V) (e : E) (k : ℕ) :=
  if G.enabled e then min (dist G s (G.src e)+k) (dist G s (G.dst e)+(G.len e-k)) else dist G s (G.dst e)
private def potential (s : V) : Node G → ℕ
  | .core v => dist G s v | .inner e k => onStrand G s e (k.val+1)

private theorem agrees (s : V) (e : E) (k : ℕ) (kl : k≤G.len e) (legal : G.enabled e∨0<k) :
    potential G s (atPos G e k)=onStrand G s e k := by
  by_cases z : k=0
  · subst k
    have yes := legal.resolve_right (by omega)
    simp [atPos,potential,onStrand,yes,min_eq_left (near G s e yes).1]
  · by_cases fit : k<G.len e
    · simp [atPos,z,fit,potential,show k-1+1=k by omega]
    · have eq : k=G.len e := by omega
      subst k
      by_cases on : G.enabled e
      · simp [atPos,z,potential,onStrand,on,min_eq_right (near G s e on).2]
      · simp [atPos,z,potential,onStrand,on]

private theorem lipschitz (s : V) {u v} (st : UnitStep G u v) :
    potential G s u≤potential G s v+1 ∧ potential G s v≤potential G s u+1 := by
  cases st with
  | along e k valid first =>
    rw [agrees G s e k valid.le first,agrees G s e (k+1) (by omega) (Or.inr (by omega))]
    by_cases on : G.enabled e <;> simp only [onStrand,on,if_true,if_false,min_def] <;> (try split_ifs) <;> omega

theorem cannot_shorten {s v d} (p : UnitWalk G (.core s) d (.core v)) : dist G s v ≤ d := by
  have aux {a b t} (w : UnitWalk G a t b) : potential G s b≤potential G s a+t := by
    induction w with
    | nil => omega
    | snoc _ e ih => rcases e with e|e <;> have h := lipschitz G s e <;> omega
  have zero := shortest G (Walk.nil s)
  have H := aux p
  dsimp [potential] at H
  omega

theorem distance {s v d} (path : Walk G s d v) (lower : ∀ t,Walk G s t v → d≤t) :
    UnitWalk G (.core s) d (.core v) ∧ ∀ t,UnitWalk G (.core s) t (.core v) → d≤t := by
  have ok : Reached G s v := ⟨_,path⟩
  exact ⟨expand G path,fun _ w => (lower _ (reached_dist G ok)).trans (cannot_shorten G w)⟩

end
end DisjointnessDraft.Applications.Subdivision
