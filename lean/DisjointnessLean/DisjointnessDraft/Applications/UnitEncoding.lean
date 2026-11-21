import DisjointnessDraft.Applications.SubdivisionPaths
import DisjointnessDraft.Applications.PlanarEncoding

/-! Fix one finite menu of potential strands before reading the source
family. Every point interior to a strand is allocated from the start. An
insertion flips the first unit edge of precisely one connector. -/
namespace DisjointnessDraft.Applications.UnitEncoding
open Subdivision FiniteSubdivision PlanarEncoding FinitePlanarDistance PlanarPadding OriginalGrid CoreSize WeightedWalk Classical
noncomputable section

def allRows (p : ℕ) (j : ℤ) := 1≤j ∧ j≤(p:ℤ)
def potential (p : ℕ) := wire (p:=p) (fun _ _ => true) (allRows p)
abbrev Id (p : ℕ) := {ab : V p × V p // plain (potential p) ab.1 ab.2}
noncomputable instance idFintype (p : ℕ) : Fintype (Id p) := Fintype.ofFinite _
def length (e : Id p) := (wireWeight p (PlanarMatching.place e.val.1) (PlanarMatching.place e.val.2)).toNat
theorem has_weight (e : Id p) (hp : 2≤p) :
    potential p e.val.1 (length e:ℤ) e.val.2 ∧ 0<length e ∧ length e≤8*p*(p+1) := by
  obtain ⟨k,h⟩ := e.property
  obtain ⟨lo,hi⟩ : 0<k ∧ k≤8*(p:ℤ)*(p+1) := weight_bounds hp (fun _ m => m) h
  have eq := weight_eq h
  have w : (length e:ℤ)=k := by dsimp [length]; rw [←eq,Int.toNat_of_nonneg lo.le]
  refine ⟨w.symm▸h,by omega,?_⟩
  have b : (length e:ℤ)≤8*(p:ℤ)*(p+1) := by omega
  exact_mod_cast b

def mesh (p : ℕ) (hp : 2≤p) : Graph (V p) (Id p) :=
  ⟨fun e => e.val.1,fun e => e.val.2,length,fun e => (has_weight e hp).2.1,fun _ => True⟩
theorem id_unique (hp : 2≤p) : Function.Injective (fun e => ((mesh p hp).src e,(mesh p hp).dst e)) :=
  fun _ _ e => Subtype.ext e

theorem potential_of {f : Family n} {xs : List (Fin n)} {a k b} (e : wire (table f) (enabled xs) a k b) :
    potential (dim n) a k b := by
  have mono {M : ℤ → ℤ → Bool} {p : ℤ} {u v k} (s : Step p M u k v) : Step p (fun _ _ => true) u k v := by
    cases s with
    | cell r c r1 rp c1 cp ed =>
      exact .cell r c r1 rp c1 cp (by
        cases ed <;> constructor
        all_goals rfl)
  have incl {x y k} (w : Wire (dim n) (table f) (enabled xs) x k y) : Wire (dim n) (fun _ _ => true) (allRows (dim n)) x k y := by
    cases w with
    | l s => exact .l (mono s)
    | r s => exact .r s
    | link j on => exact .link j (rows xs j on)
  exact incl e

def on (f : Family n) (xs : List (Fin n)) (e : Id (dim n)) := wire (table f) (enabled xs) e.val.1
    (wireWeight (dim n) (PlanarMatching.place e.val.1) (PlanarMatching.place e.val.2)) e.val.2

def coreDrawing (p : ℕ) (hp : 2≤p) : Drawing (underlying (mesh p hp)) where
  point u := Planarity.draw p (PlanarMatching.place u)
  injective := fun u v eq => PlanarMatching.inj (Planarity.core_vertices (displayed u) (displayed v) eq)
  miss := by
    rintro _ _ ⟨e,rfl,rfl⟩ z t lo hi
    exact Planarity.core_misses_vertices (drawn (has_weight e hp).1) (displayed z) t lo hi
  apart := by
    rintro _ _ _ _ ⟨e,rfl,rfl⟩ ⟨f,rfl,rfl⟩ t s t0 t1 s0 s1 eq
    obtain ⟨l,r⟩ := Planarity.core_segments (drawn (has_weight e hp).1) (drawn (has_weight f hp).1) t s t0 t1 s0 s1 eq
    exact ⟨PlanarMatching.inj l,PlanarMatching.inj r⟩

def sourceDim {n} (hn : 0<n) : 2≤dim n := by dsimp [dim]; omega
abbrev U (n : ℕ) (hn : 0<n) := Nodes (mesh (dim n) (sourceDim hn))
def bridge (x : Fin n) : Id (dim n) :=
  ⟨((false,.right x.castSucc),(true,.right x.castSucc)),⟨_,Wire.link (CoreSize.pos x) (by
    dsimp [allRows,CoreSize.pos,dim]; have := x.isLt; omega)⟩⟩
def added (hn : 0<n) (x : Fin n) : U n hn × U n hn :=
  (atNode (mesh (dim n) (sourceDim hn)) (bridge x) 0,atNode (mesh (dim n) (sourceDim hn)) (bridge x) 1)
def linkOn (f : Family n) (xs : List (Fin n)) (e : Id (dim n)) :
    on f xs e ↔ on f [] e ∨ ∃ x∈xs,e=bridge x := by
  obtain ⟨⟨a,b⟩,h⟩ := e
  have v := connector f xs (Sum.inl a : W n 0) (.inl b) (wireWeight (dim n) (PlanarMatching.place a) (PlanarMatching.place b))
  simpa [on,input,ends,weight,PlanarPadding.extend,bridge,Subtype.ext_iff,Prod.mk.injEq] using v

theorem bridge_new (f : Family n) (x : Fin n) : ¬on f [] (bridge x) :=
  fun h => missing (pad:=0) f x ⟨_,h⟩
theorem bridge_injective : Function.Injective (@bridge n) := by
  intro a b h; have eq := congrArg Subtype.val h; simpa [bridge] using eq

variable {n : ℕ} (hn : 0<n)
local notation "G" => mesh (dim n) (sourceDim hn)
def enabledEdge (f : Family n) (xs : List (Fin n)) (u v : U n hn) := Dart G (on f xs) u v

theorem first_edge (f : Family n) (xs : List (Fin n)) (u v : U n hn) :
    enabledEdge hn f xs u v ↔ enabledEdge hn f [] u v ∨ ∃ x∈xs,(u,v)=added hn x := by
  constructor
  · rintro ⟨e,k,h,on|pos,rfl,rfl⟩
    · cases linkOn f xs e |>.mp on with
      | inl h0 => exact Or.inl ⟨e,k,h,Or.inl h0,rfl,rfl⟩
      | inr r =>
        obtain ⟨x,hx,rfl⟩ := r
        by_cases zero : k=0
        · subst k; exact Or.inr ⟨x,hx,rfl⟩
        · exact Or.inl ⟨bridge x,k,h,Or.inr (by omega),rfl,rfl⟩
    · exact Or.inl ⟨e,k,h,Or.inr pos,rfl,rfl⟩
  · rintro (⟨e,k,h,op,rfl,rfl⟩|⟨x,h,pair⟩)
    · exact ⟨e,k,h,op.imp (fun a => (linkOn ..).mpr (Or.inl a)) id,rfl,rfl⟩
    · have a := congrArg Prod.fst pair; have b := congrArg Prod.snd pair
      exact ⟨bridge x,0,(G).positive _,Or.inl ((linkOn ..).mpr (Or.inr ⟨x,h,rfl⟩)),a,b⟩

theorem absent (f : Family n) (x : Fin n) : ¬enabledEdge hn f [] (added hn x).1 (added hn x).2 := by
  rintro ⟨e,k,fit,on,a,b⟩
  obtain ⟨rfl,rfl⟩ := same_segment G (coreDrawing ..) (id_unique _) ((G).positive (bridge x)) fit a b
  exact on.elim (bridge_new f x) (by omega)

theorem added_injective : Function.Injective (added hn) := by
  intro x y h
  have same := same_segment G (coreDrawing ..) (id_unique _) ((G).positive (bridge x)) ((G).positive (bridge y)) (congrArg Prod.fst h) (congrArg Prod.snd h)
  exact bridge_injective same.1

def query (q : Fin n) : U n hn × U n hn := (.inl (start q.castSucc),.inl (finishLine q.castSucc))
def drawing (f : Family n) (xs : List (Fin n)) : Drawing (enabledEdge hn f xs) :=
  FiniteSubdivision.drawing G (coreDrawing ..) (id_unique _) (on f xs)

theorem upper_plane (f : Family n) (xs : List (Fin n)) (u : U n hn) : 0≤((drawing hn f xs).point u).2 := by
  rcases u with u|⟨e,i⟩
  · exact upper_half u
  · have a := upper_half e.val.1; have b := upper_half e.val.2
    let t : ℝ := (i.val+1:ℝ)/length e
    have t0 : 0<t := by dsimp [t]; exact div_pos (by positivity) (by exact_mod_cast (has_weight e (sourceDim hn)).2.1)
    have t1 : t<1 := by
      have r := i.isLt
      dsimp [mesh] at r
      apply (div_lt_one (by exact_mod_cast (has_weight e (sourceDim hn)).2.1 : (0:ℝ)<length e)).mpr
      exact_mod_cast (by omega : i.val+1<length e)
    exact add_nonneg (mul_nonneg (by linarith : 0≤1-t) a) (mul_nonneg t0.le b)

end
end DisjointnessDraft.Applications.UnitEncoding
