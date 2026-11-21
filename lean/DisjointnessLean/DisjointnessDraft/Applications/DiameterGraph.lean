import DisjointnessDraft.Applications.PaddedDiameter
import DisjointnessDraft.Applications.PlanarEncoding
import DisjointnessDraft.Applications.GraphHistories

namespace DisjointnessDraft.Applications.DiameterGraph
open PlanarEncoding CoreSize FinitePlanarDistance WeightedWalk PlanarPadding Transfer.Compiler
open Classical
noncomputable section
variable {n pad : ℕ}
abbrev Base (n : ℕ) := FinitePlanarDistance.V (dim n)
abbrev W (n pad : ℕ) := Diameter.Node (Base n) ⊕ Fin pad
abbrev WeightEdge (V : Type) := (V×V)×ℤ
abbrev Net (V : Type) := V→ℤ→V→Prop

def center (s : Bool) : Diameter.Node (Base n) := .inr s
def visitor (s : Bool) (q : Fin (dim n)) : Base n := if s then finishLine q else start q
def anchor (s : Bool) : Base n := visitor s (Fin.last n)
def bulk (s : Bool) (v : Base n) := v=anchor s
def span (n : ℕ) := FiniteDiameter.L (dim n)

inductive Act (n : ℕ) where | attach (x : Fin n) | select (s : Bool) (q : Fin n)
  deriving DecidableEq
def inserted (a : Act n) : WeightEdge (W n pad) := match a with
  | .attach x => ((.inl (.inl (false,.right x.castSucc)),.inl (.inl (true,.right x.castSucc))),PlanarCore.link (dim n) (pos x))
  | .select s q => ((.inl (center s),.inl (.inl (visitor s q.castSucc))),span n)

def fan (acts : List (Act n)) (s : Bool) (v : Base n) (k : ℤ) :=
  (bulk s v ∧ k=3*span n) ∨ ∃q,Act.select s q∈acts ∧ v=visitor s q.castSucc ∧ k=span n
def links (acts : List (Act n)) : List (Fin n) := acts.filterMap (fun | .attach x => some x | .select _ _ => none)

def core (F : Family n) (xs : List (Fin n)) := FinitePlanarDistance.wire (p:=dim n) (table F) (enabled xs)
def middle (F : Family n) (a : List (Act n)) := FanDrawing.wire (core F (links a)) (fan a)
def graph (F : Family n) (a : List (Act n)) : Net (W n pad) := extend (middle F a) (center false)

def Merged {V : Type} (F : Net V) (us : List (WeightEdge V)) : Net V :=
  fun a k b => F a k b ∨ ((a,b),k)∈us

theorem visitor_inj (s : Bool) : Function.Injective (@visitor n s) := by
  cases s <;> intro a b eq <;> simpa [visitor,finishLine,start] using eq

theorem injective : Function.Injective (@inserted n pad) := by
  intro a b e
  cases a <;> cases b
  case attach.attach x y =>
    have h := congrArg (fun e : WeightEdge (W n pad) => e.1.1) e; simpa [inserted] using h
  · have h := congrArg (fun e : WeightEdge (W n pad) => e.1.1) e; cases h
  · have h := congrArg (fun e : WeightEdge (W n pad) => e.1.1) e; cases h
  case select.select s q t r =>
    have h := congrArg (fun e : WeightEdge (W n pad) => e.1.1) e
    have s' : s=t := by simpa [inserted,center] using h
    subst t
    have h := congrArg (fun e : WeightEdge (W n pad) => e.1.2) e
    have qr := visitor_inj s (show visitor s q.castSucc=visitor s r.castSucc by simpa [inserted] using h)
    obtain rfl := Fin.castSucc_injective _ qr; rfl

theorem mem_links {a : List (Act n)} {x : Fin n} : x∈links a ↔ Act.attach x∈a := by
  simp only [links,List.mem_filterMap]
  constructor
  · rintro ⟨y,hy,t⟩; cases y with
    | attach v => obtain rfl := Option.some.inj t; exact hy
    | select s q => contradiction
  · intro m; exact ⟨_,m,rfl⟩

theorem core_eq (F : Family n) (xs : List (Fin n)) (u v : Base n) (k : ℤ) :
    core F xs u k v ↔ core F [] u k v ∨ ∃ x∈xs,u=(false,Menu.right x.castSucc) ∧ v=(true,Menu.right x.castSucc) ∧ k=PlanarCore.link (dim n) (pos x) := by
  have h := PlanarEncoding.connector (pad:=0) F xs (.inl u) (.inl v) k
  constructor
  · intro e; rcases h.mp e with z|⟨x,hx,eq,wt⟩
    · exact Or.inl z
    · have z : u=(false,Menu.right x.castSucc) ∧ v=(true,Menu.right x.castSucc) := by simpa [ends] using eq
      obtain ⟨rfl,rfl⟩ := z; exact Or.inr ⟨x,hx,rfl,rfl,wt⟩
  · rintro (z|⟨x,hx,rfl,rfl,rfl⟩)
    · exact h.mpr (Or.inl z)
    · exact (PlanarEncoding.connector (pad:=0) F xs _ _ _).mpr (Or.inr ⟨x,hx,rfl,rfl⟩)

theorem acts (F : Family n) (a : List (Act n)) :
    graph (pad:=pad) F a = Merged (graph F []) (a.map inserted) := by
  funext u k v; apply propext
  have what : ((u,v),k)∈a.map inserted ↔ ∃ z∈a,inserted z=((u,v),k) := List.mem_map
  change _ ↔ _ ∨ _; rw [what]
  rcases u with (u|s)|i <;> rcases v with (v|t)|j
  all_goals try (constructor
                 · exact Or.inl
                 · rintro (e|⟨z,h,e⟩)
                   · exact e
                   · cases z <;> cases e)
  · change core F (links a) u k v ↔ core F [] u k v ∨ _
    rw [core_eq]; apply or_congr_right
    constructor
    · rintro ⟨x,m,rfl,rfl,rfl⟩; exact ⟨.attach x,mem_links.mp m,rfl⟩
    · rintro ⟨z,m,e⟩; cases z with
      | select => cases e
      | attach x =>
        obtain ⟨rfl,rfl,rfl⟩ : (false,Menu.right x.castSucc)=u ∧ (true,Menu.right x.castSucc)=v ∧ PlanarCore.link (dim n) (pos x)=k := by simpa [inserted,and_assoc] using e
        exact ⟨x,mem_links.mpr m,rfl,rfl,rfl⟩
  · change fan a s v k ↔ fan [] s v k ∨ _
    simp [fan]
    apply or_congr_right; constructor
    · rintro ⟨q,h,rfl,rfl⟩; exact ⟨.select s q,h,rfl⟩
    · rintro ⟨z,m,e⟩; cases z with
      | attach => cases e
      | select b q =>
        obtain ⟨rfl,rfl,rfl⟩ : b=s ∧ visitor b q.castSucc=v ∧ span n=k := by simpa [inserted,center,and_assoc] using e
        exact ⟨q,m,rfl,rfl⟩

theorem fresh (F : Family n) (z : Act n) : ¬plain (graph (pad:=pad) F []) (inserted z).1.1 (inserted z).1.2 := by
  cases z with
  | attach x => exact PlanarEncoding.missing (pad:=0) F x
  | select s q =>
    rintro ⟨k,h⟩
    change fan [] s (visitor s q.castSucc) k at h
    simp [fan,bulk,anchor] at h
    have eq := visitor_inj _ h.1
    have z := congrArg Fin.val eq; simp at z; omega

end
end DisjointnessDraft.Applications.DiameterGraph
