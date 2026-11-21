import DisjointnessDraft.Applications.GraphSelectors
import DisjointnessDraft.Transfer.RelInitialization

namespace DisjointnessDraft.Applications.Distances
open DisjointnessFoundations Graphs GraphVariants GraphHistories GraphCosts Reachability Transfer.Compiler MeasureTheory Filter Real
open scoped ENNReal
noncomputable section
open Classical

def distance (E : W→W→Prop) (x y : W) : ℝ≥0∞ :=
  if can : ∃ k,Walk E x k y then (Nat.find can:ℕ) else ⊤

theorem at_most {E : W→W→Prop} {x y : W} {k : ℕ} (path : Walk E x k y) : distance E x y≤k := by
  have h : ∃ d, Walk E x d y := ⟨k,path⟩
  simp only [distance,dif_pos h,Nat.cast_le]; exact Nat.find_min' h path

theorem at_least {E : W→W→Prop} {x y : W} {k : ℕ} (no : ¬∃ d<k,Walk E x d y) : (k:ℝ≥0∞)≤distance E x y := by
  unfold distance; split
  · rename_i h; apply Nat.cast_le.mpr; by_contra! lt; exact no ⟨_,lt,Nat.find_spec h⟩
  · exact le_top

theorem symmetric_distance (E : W → W → Prop) (u v : W) :
    distance (sym E) u v=distance (sym E) v u := by
  have flip {x y : W} {k} (w : Walk (sym E) x k y) : Walk (sym E) y k x :=
    walk_map id (fun _ _ e => e.symm) (walk_rev w)
  have forward (x y : W) : distance (sym E) x y≤distance (sym E) y x := by
    unfold distance; split
    · rename_i h; split
      · rename_i other
        exact Nat.cast_le.mpr (Nat.find_min' h (flip (Nat.find_spec other)))
      · exact le_top
    · rename_i no; split
      · rename_i some; exact (no ⟨_,flip (Nat.find_spec some)⟩).elim
      · exact le_rfl
  exact le_antisymm (forward _ _) (forward _ _)

def within (α t report : ℝ≥0∞) := t≤report ∧ report≤α*t

theorem gap {W : Type} (G : W→W→Prop) (x y : W) (P : Prop) {near far : ℕ} {α report : ℝ≥0∞}
    (separate : α*near < (far:ℝ≥0∞)) (ok : within α (distance G x y) report)
    (yes : P → Walk G x near y) (no : (∃ d<far,Walk G x d y) → P) : report<far ↔ P := by
  constructor
  · intro lt; by_contra h; exact (not_lt_of_ge ((at_least (fun t => h (no t))).trans ok.1)) lt
  · intro h; exact lt_of_le_of_lt (ok.2.trans (mul_le_mul_left' (at_most (yes h)) α)) separate

variable {n p : ℕ}
theorem immediate (F : Family n) (xs : List (Fin n)) (q : Fin n) {α v : ℝ≥0∞} (lt : α*2<4)
    (ok : within α (distance (sym (Raw (edges F xs))) (row q) (target n p)) v) :
    v<4 ↔ explicit_hit F xs q := by
  apply gap (near:=2) (far:=4) _ _ _ _ (by simpa using lt) ok
  · rintro ⟨j,h,x⟩
    have first := (edge_exact F xs (row q) (.inl (.col j) : Vertex n p)).mpr h
    have second := (edge_exact F xs (.inl (.col j)) (target n p)).mpr x
    exact .cons (Or.inl first) (.cons (Or.inl second) (.nil _))
  · rintro ⟨d,sz,path⟩
    have send (a b : Vertex n p) (h : sym (Raw (edges F xs)) a b) :
        sym (base (extRows F) (·∈xs)) (strip a) (strip b) := h.imp (projects F xs) (projects F xs)
    exact (short_iff (extRows F) (·∈xs) (.inl q)).mp ⟨d,sz,walk_map strip send path⟩

theorem selected (F : Family n) (xs : List (Fin n)) (q : Fin n) {α v : ℝ≥0∞} (lt : α*3<5)
    (ok : within α (distance (sym (G F xs q .source)) (.inl .source) (target n p)) v) :
    v<5 ↔ explicit_hit F xs q := by
  apply gap (near:=3) (far:=5) _ _ _ _ (by simpa using lt) ok
  · rintro ⟨j,h,x⟩
    have s : G F xs q .source (.inl .source : Vertex n p) (row q) := up F xs q .source (Or.inr ⟨rfl,rfl⟩)
    have first : G F xs q .source (row q : Vertex n p) (.inl (.col j)) := up F xs q .source (Or.inl h)
    have second : G F xs q .source (.inl (.col j)) (target n p) := up F xs q .source (Or.inl x)
    exact .cons (Or.inl s) (.cons (Or.inl first) (.cons (Or.inl second) (.nil _)))
  · rintro ⟨d,sz,path⟩
    have send (a b : Vertex n p) (h : sym (G F xs q .source) a b) : fixedEdge (extRows F) (·∈xs) (.inl q) (strip a) (strip b) := by
      rcases h with e|e
      · rcases down F xs q .source e with v|s; exact Or.inl (Or.inl v); exact Or.inr (Or.inl s)
      · rcases down F xs q .source e with v|s; exact Or.inl (Or.inr v); exact Or.inr (Or.inr s)
    exact (fixed_short (extRows F) (·∈xs) (.inl q)).mp ⟨d,sz,walk_map strip send path⟩

end
end DisjointnessDraft.Applications.Distances
