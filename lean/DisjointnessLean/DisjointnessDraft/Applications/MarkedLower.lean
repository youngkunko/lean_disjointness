import DisjointnessDraft.Transfer.Direct
import DisjointnessDraft.Applications.GraphVariants
import DisjointnessFoundations.PolynomialScaleComparison

/-! Operational lower bound for nearest marked vertex. The graph is connected
and bipartite, has a single mark initially, and supports strict insertions of
new marks. The Boolean query distinguishes distance below three. -/
namespace DisjointnessDraft.Applications.MarkedLower
open Graphs GraphVariants DisjointnessFoundations CellProbe MeasureTheory Filter Real Classical
open scoped ENNReal
noncomputable section
structure Input (V : Type) where
  edges : V → V → Prop
  initial : V

def good {V} (F : Input V) :=
  (∀ u v,F.edges u v → F.edges v u) ∧ (∀ u v,reach F.edges u v) ∧
  ∃ sides : V → Bool,∀ u v,F.edges u v → sides u ≠ sides v

def problem (V : Type) : Transfer.Problem (Input V) V V where
  legal F xs := good F ∧ xs.Nodup ∧ F.initial∉xs
  answer F xs q := decide (∃ v,(v=F.initial ∨ v∈xs) ∧ ∃ d<3,Walk F.edges q d v)

abbrev Vertex (n pad : ℕ) := MarkV (Fin n) (Fin n) ⊕ Fin pad
def strip {n pad} : Vertex n pad → MarkV (Fin n) (Fin n) | .inl v => v | .inr _ => .sentinel
def edge {n pad} (S : Family n) : Vertex n pad → Vertex n pad → Prop
  | .inl u,.inl v => markEdge (fun q j => j∈S q) u v
  | .inl .hubB,.inr _ | .inr _,.inl .hubB => True
  | _,_ => False

def inp {n pad} (S : Family n) : Input (Vertex n pad) := ⟨edge S,.inl .sentinel⟩
def put {n pad : ℕ} (j : Fin n) : Vertex n pad := .inl (.col j)
def ask {n pad : ℕ} (q : Fin n) : Vertex n pad := .inl (.row q)
def translation (n pad : ℕ) : Preload.Map n (Input (Vertex n pad)) (Vertex n pad) (Vertex n pad) :=
  ⟨inp,fun _ => [],0,fun _ => rfl,put,ask,true⟩

private theorem append {V} {G : V → V → Prop} {a b c d e} (p : Walk G a d b) (q : Walk G b e c) :
    Walk G a (d+e) c := by
  induction p with
  | nil => simpa using q
  | cons st _ ih => simpa only [Nat.succ_add] using Walk.cons st (ih q)

private theorem reversed {V} {G : V → V → Prop} (sym : ∀ a b,G a b→G b a) {a b d} (p : Walk G a d b) :
    Walk G b d a := by
  induction p with
  | nil => exact .nil _
  | cons e _ ih => exact append ih (.cons (sym _ _ e) (.nil _))

private theorem imageWalk {V U} {E : V → V → Prop} {G : U → U → Prop} (f : V → U)
    (ok : ∀ a b,E a b → G (f a) (f b)) {u d v} (w : Walk E u d v) : Walk G (f u) d (f v) := by
  induction w with | nil => exact .nil _ | cons e _ ih => exact .cons (ok _ _ e) ih

private theorem proj {n pad} (S : Family n) (u v : Vertex n pad) (h : edge S u v) :
    markEdge (fun q j => j∈S q) (strip u) (strip v) := by
  cases u with
  | inl a => cases v with
             | inl b => cases a <;> cases b <;> exact h
             | inr b => cases a <;> simp_all [edge,strip,markEdge]
  | inr a => cases v with
             | inl b => cases b <;> simp_all [edge,strip,markEdge]
             | inr b => contradiction

theorem valid_graph {n pad} (S : Family n) : good (inp (pad:=pad) S) := by
  have s (u v : Vertex n pad) (e : edge S u v) : edge S v u := by
    cases u with
    | inl a => cases v with
               | inl b => cases a <;> cases b <;> simp_all [edge,markEdge]
               | inr b => cases a <;> simp_all [edge]
    | inr a => cases v with
               | inl b => cases b <;> simp_all [edge]
               | inr b => contradiction
  have toHub (u : Vertex n pad) : reach (edge S) u (.inl .hubB) := by
    cases u with
    | inr a => exact ⟨1,.cons (b:=Sum.inl MarkV.hubB) trivial (.nil _)⟩
    | inl a => cases a with
               | row i => exact ⟨2,.cons (show edge S (.inl (.row i)) (.inl .hubA) from trivial) (.cons (b:=Sum.inl MarkV.hubB) trivial (.nil _))⟩
               | hubB => exact ⟨0,.nil _⟩
               | _ => exact ⟨1,.cons (b:=Sum.inl MarkV.hubB) trivial (.nil _)⟩
  refine ⟨s,?_,fun v => markSide (strip v),?_⟩
  · intro u v
    obtain ⟨d,pu⟩ := toHub u
    obtain ⟨e,pv⟩ := toHub v
    exact ⟨d+e,append pu (reversed s pv)⟩
  · intro u v e
    have flip (a b : MarkV (Fin n) (Fin n)) (h : markEdge (fun i j => j∈S i) a b) : markSide a ≠ markSide b := by
      cases a <;> cases b <;> simp_all [markSide,markEdge]
    exact flip _ _ (proj S u v e)

theorem hard_distance {n pad} (S : Family n) (xs : List (Fin n)) (q : Fin n) :
    let d := if Hit (fun i j => j∈S i) (·∈xs) q then 1 else 3
    (∃ v : Vertex n pad,(v=(inp S).initial ∨ v∈xs.map put) ∧ Walk (edge S) (ask q) d v) ∧
      ∀ v : Vertex n pad, (v=(inp S).initial ∨ v∈xs.map put) → ∀ e,Walk (edge S) (ask q) e v → d≤e := by
  intro d
  have near := marked_distance (fun i j => j∈S i) (·∈xs) q
  refine ⟨?_,?_⟩
  · obtain ⟨v,m,w⟩ := near.1
    refine ⟨.inl v,?_,?_⟩
    · cases v <;> simp_all [inp,marked,put]
    · exact imageWalk Sum.inl (fun a b (h : markEdge (fun i j => j∈S i) a b) =>
        (show edge S (.inl a) (.inl b) by cases a <;> cases b <;> exact h)) w
  · intro v m e w
    apply near.2 (strip v) e _ (imageWalk strip (proj S) w)
    rcases m with rfl|h
    · trivial
    · obtain ⟨j,mj,rfl⟩ := List.mem_map.1 h; exact mj

theorem proof (n pad : ℕ) : Transfer.Direct (problem (Vertex n pad)) (translation n pad) := by
  constructor
  · intro S xs nd
    change good (inp S) ∧ (xs.map put).Nodup ∧ Sum.inl MarkV.sentinel∉xs.map put
    exact ⟨valid_graph S, nd.map (fun a b e => MarkV.col.inj (Sum.inl.inj e)),by simp [put]⟩
  · intro S xs q nd
    have near := marked_distance (fun i j => j∈S i) (·∈xs) q
    have act (v : MarkV (Fin n) (Fin n)) : marked (·∈xs) v →
        (Sum.inl v : Vertex n pad)=(inp S).initial ∨ (Sum.inl v : Vertex n pad)∈xs.map put := by
      cases v <;> simp [marked,put,inp]
    have eq : (∃ v : Vertex n pad,(v=(inp S).initial ∨ v∈xs.map put) ∧ ∃ d<3,Walk (edge S) (ask q) d v)
        ↔ Hit (fun i j => j∈S i) (·∈xs) q := by
      constructor
      · rintro ⟨v,m,d,hd,w⟩
        have m' : marked (·∈xs) (strip v) := by
          rcases m with rfl|h
          · trivial
          · obtain ⟨j,mj,rfl⟩ := List.mem_map.1 h; exact mj
        have bd := near.2 _ _ m' (imageWalk strip (proj S) w)
        by_cases yes : Hit (fun i j => j∈S i) (·∈xs) q
        · exact yes
        · simp only [if_neg yes] at bd; omega
      · intro meet
        obtain ⟨v,m,w⟩ := near.1
        refine ⟨.inl v,act v m,1,by decide,?_⟩
        simp only [if_pos meet] at w
        exact imageWalk Sum.inl (fun a b (h : markEdge (fun i j => j∈S i) a b) => (show edge S (.inl a) (.inl b) by cases a <;> cases b <;> exact h)) w
    simp only [problem,translation,List.nil_append]
    simp only [inp] at eq ⊢
    simp only [eq]
    by_cases yes : Hit (fun i j => j∈S i) (·∈xs) q
    · have no : ¬∀ x∈xs,x∉S q := by obtain ⟨j,a,b⟩ := yes; exact fun h => h j b a
      simp [translation,InputReduction.out,DisjointnessDraft.answer,yes,no]
    · have no : ∀ x∈xs,x∉S q := fun x a b => yes ⟨x,b,a⟩
      (simp [translation,InputReduction.out,DisjointnessDraft.answer,yes,no]; exact no)

def coreEquiv (n : ℕ) : MarkV (Fin n) (Fin n) ≃ (Fin n ⊕ Fin n) ⊕ (Bool ⊕ Unit) where
  toFun | .row q => .inl (.inl q) | .col j => .inl (.inr j) | .hubA => .inr (.inl false)
        | .hubB => .inr (.inl true) | .sentinel => .inr (.inr ())
  invFun | .inl (.inl q) => .row q | .inl (.inr j) => .col j | .inr (.inl false) => .hubA
         | .inr (.inl true) => .hubB | .inr (.inr _) => .sentinel
  left_inv x := by cases x <;> rfl
  right_inv x := by rcases x with (i|j)|((a|b)|⟨⟩) <;> rfl

def pad (N : ℕ) := N-(2*(N/4)+3)
theorem cardinality (N : ℕ) (large : 8≤N) : Fintype.card (Vertex (N/4) (pad N))=N := by
  simp only [Vertex,Fintype.card_sum,Fintype.card_congr (coreEquiv (N/4)),Fintype.card_fin,
    Fintype.card_bool,Fintype.card_unit,pad]
  omega

theorem lower (lo hi : ℝ) (lp : 0<lo) (lu : lo≤hi) :
    ∃ c : ℝ, 0<c ∧ ∀ᶠ N : ℕ in atTop,
    let V := Vertex (N/4) (pad N)
    Fintype.card V=N ∧ ∀ w tu : ℕ, 1≤tu → lo*logb 2 N≤w → (w:ℝ)≤hi*logb 2 N →
    ∀ (Ω C : Type) [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
      (D : DataStructure w (Input V) V V C) (R : RandomTape Ω C) (tq : ℝ),
      1≤tq → Transfer.Target μ (problem V) D R tu tq →
      c*(Tradeoff.ratio N w tu)^2≤tq ∧ c*(FixedFamilySizes.logRatio N)^2≤max (tu:ℝ) tq := by
  obtain ⟨c,hc,ev⟩ := Transfer.direct_bounds lo hi lp lu 3 (by norm_num)
  obtain ⟨L,hL⟩ := eventually_atTop.mp ev
  refine ⟨c,hc,?_⟩
  filter_upwards [eventually_ge_atTop (4*L+16)] with N big
  let n := N/4
  have large : L≤n := by dsimp [n]; omega
  have n4 : 4≤n := by dsimp [n]; omega
  have cube : N≤n^3 := by
    have nf : N≤4*n+3 := by dsimp [n]; omega
    have z := Nat.mul_le_mul_right n n4
    have y := Nat.mul_le_mul_right (n^2) n4
    nlinarith only [nf,z,y,n4]
  have nN : n≤N := Nat.div_le_self _ _
  have logs := ApplicationSizes.log_range (by omega : 2≤n) nN cube
  intro V; refine ⟨cardinality _ (by omega),?_⟩
  intro w tu t1 wl wh Ω C _ μ _ D R tq q1 ok
  exact hL n large N w tu nN logs.2 t1 wl wh (Input V) V V Ω C μ (problem V)
    (translation n (pad N)) D R tq q1 (proof n _) ok

end
end DisjointnessDraft.Applications.MarkedLower
