import DisjointnessDraft.Applications.WeightedGirth
import DisjointnessDraft.Applications.DirectedSubdivision
import DisjointnessDraft.Applications.UnitMetric
import DisjointnessDraft.Applications.UnitSizes

/-! The physical unit-weight planar directed-girth lower bound. A connector
insertion enables one dart. All intermediate strand addresses are fixed in advance. -/
namespace DisjointnessDraft.Applications.UnitGirth
open PlanarEncoding FinitePlanarDistance UnitEncoding CoreSize Subdivision FiniteSubdivision
open GirthTarget GirthOrient GirthPadding PlanarPadding WeightedWalk ShortTransfer Filter Real Classical
noncomputable section
variable {n : ℕ} (hn : 0<n)
local notation "G" => mesh (dim n) (sourceDim hn)
def corner : U n hn := .inl (root n)

theorem forward (x : Fin n) : DirectedSubdivision.level G WeightedGirth.height (added hn x).1 <
    DirectedSubdivision.level G WeightedGirth.height (added hn x).2 := by
  have z := DirectedSubdivision.level_step G WeightedGirth.height (bridge x) 0 ((G).positive _)
  have w := WeightedGirth.crossing x
  change WeightedGirth.height ((G).src (bridge x)) < WeightedGirth.height ((G).dst (bridge x)) at w
  have pos : (0:ℚ)<(G).len (bridge x) := by exact_mod_cast (G).positive (bridge x)
  exact sub_pos.mp (z.symm ▸ div_pos (sub_pos.mpr w) pos)

def storage : Storage n (U n hn) where
  stored f xs := unit G (on f xs)
  potential := Dart G (fun _ => True)
  strength _ _ := 1
  rank := DirectedSubdivision.level G WeightedGirth.height
  put := added hn
  src q := (UnitEncoding.query hn q).1
  dst q := (UnitEncoding.query hn q).2
  inside := by rintro _ _ _ _ _ ⟨_,e,k,h,_,rfl,rfl⟩; exact ⟨e,k,h,Or.inl trivial,rfl,rfl⟩
  asymmetric := no_flip (FiniteSubdivision.drawing G (coreDrawing ..) (id_unique _) _)
  canonical := fun _ _ _ _ _ e => e.1
  activity := by
    intro f xs u k v
    change (k=1 ∧ enabledEdge hn f xs u v) ↔ (k=1 ∧ enabledEdge hn f [] u v) ∨ ∃x∈xs,(u,v)=added hn x ∧ k=1
    rw [first_edge]; aesop
  fresh := fun f x ⟨_,e⟩ => absent hn f x e.2
  injective := added_injective hn
  inserted := fun x => ⟨bridge x,0,(G).positive _,Or.inl trivial,rfl,rfl⟩
  forward := forward hn
  order q := (WeightedGirth.terminal_order q).le

theorem single_strand {f : Family n} {xs : List (Fin n)} {u k v}
    (e : wire (p:=dim n) (table f) (enabled xs) u k v) :
    ∃ z : Id (dim n),(G).src z=u ∧ (G).dst z=v ∧ ((G).len z:ℤ)=k ∧ on f xs z := by
  let z : Id (dim n) := ⟨(u,v),⟨k,potential_of e⟩⟩
  have eq := weight_eq e; have positive := (weight_bounds (sourceDim hn) (rows xs) e).1
  refine ⟨z,rfl,rfl,?_,?_⟩
  · change ((wireWeight _ _ _).toNat:ℤ)=k; rw [←eq,Int.toNat_of_nonneg positive.le]
  · change wire _ _ u (wireWeight _ _ _) v; rwa [←eq]

theorem project {f : Family n} {xs : List (Fin n)} {u k v}
    (w : Path (oriented (WeightedGirth.storage hn) f xs) u k v) :
    Path (oriented (storage hn) f xs) (.inl u) k (.inl v) := by
  induction w with
  | nil => exact .nil _
  | @snoc a b k d _ ed ih =>
    rcases ed with ⟨uv|vu,dir⟩
    · obtain ⟨z,rfl,rfl,rfl,op⟩ := single_strand hn uv
      have strand := (DirectedSubdivision.strand G WeightedGirth.height (on f xs) z op).1 dir
      exact ih.append strand
    · obtain ⟨z,rfl,rfl,rfl,op⟩ := single_strand hn vu
      have strand := (DirectedSubdivision.strand G WeightedGirth.height (on f xs) z op).2 dir
      exact ih.append strand

def diagram (f : Family n) (xs : List (Fin n)) : Drawing (plain ((storage hn).stored f xs)) where
  point := (UnitEncoding.drawing hn f xs).point
  injective := (UnitEncoding.drawing hn f xs).injective
  miss := fun ⟨_,e⟩ => (UnitEncoding.drawing hn f xs).miss e.2
  apart := fun ⟨_,e⟩ ⟨_,h⟩ => (UnitEncoding.drawing hn f xs).apart e.2 h.2

theorem left_plane (f : Family n) (xs : List (Fin n)) (v : U n hn) : 4≤((diagram hn f xs).point v).1 := by
  rcases v with u|⟨e,i⟩
  · exact WeightedGirth.leftmost hn u
  · have a := WeightedGirth.leftmost hn e.val.1; have b := WeightedGirth.leftmost hn e.val.2
    let t : ℝ := (i.val+1:ℝ)/(G).len e
    have p : 0<((G).len e:ℝ) := by exact_mod_cast (G).positive e
    have lo : 0≤t := div_nonneg (by positivity) p.le
    have hi : t≤1 := by apply (div_le_one p).mpr; have := i.isLt; exact_mod_cast (show i.val+1≤(G).len e by omega)
    change 4≤(1-t)*(Planarity.draw (dim n) (PlanarMatching.place e.val.1)).1+t*(Planarity.draw (dim n) (PlanarMatching.place e.val.2)).1
    nlinarith only [mul_nonneg (sub_nonneg.mpr hi) (sub_nonneg.mpr a),mul_nonneg lo (sub_nonneg.mpr b)]

def geometry : Geometry (storage hn) (corner hn) 1 (PlanarTarget.normal n) where
  diagram := diagram hn
  leftmost f xs v := by change 4≤_; exact left_plane hn f xs v
  above := upper_plane hn
  top _ _ q := WeightedGirth.top_y q.castSucc
  distinct _ := by intro eq; have eq' := Sum.inl.inj eq; exact Bool.noConfusion (congrArg Prod.fst eq')
  weights _ _ _ k _ e := by obtain rfl := e.1; exact ⟨by decide,le_rfl⟩
  positive := le_rfl
  distance f xs q := ⟨project hn (WeightedGirth.distances hn f xs q).1,
    fun k p => (UnitEncoding.distance hn f xs q).2 k (p.mono (fun _ _ _ e => e.1))⟩

def padding (N : ℕ) (hz : 0<unitSize N) := N-Fintype.card (U (unitSize N) hz)

theorem lower (lo hi : ℝ) (lp : 0<lo) (lh : lo≤hi) :
    ∃c : ℝ,0<c ∧ ∀ᶠ N : ℕ in atTop,∃hz : 0<unitSize N,
      let T := U (unitSize N) hz ⊕ Fin (padding N hz)
      Fintype.card T=N ∧ Bound lo hi c N true (GirthTarget.legal (V:=T) 1) exactSpec ∧
        Bound lo hi c N true (GirthTarget.legal (V:=T) 1) (testSpec (PlanarTarget.normal (unitSize N))) := by
  obtain ⟨c,cp,ev⟩ := Transfer.Compiler.lower lo hi lp lh 8 8 24 (by norm_num)
  obtain ⟨k,start⟩ := eventually_atTop.mp ev
  refine ⟨c,cp,?_⟩
  filter_upwards [UnitEncoding.geometry k] with N g
  let n := unitSize N
  obtain ⟨kn,n16,fit,nN,dist⟩ := g
  have nz : 0<n := by change 16≤n at n16; omega
  let pad := padding N nz
  have full : Fintype.card (U n nz ⊕ Fin pad)=N := by
    rw [Fintype.card_sum,Fintype.card_fin]; exact Nat.add_sub_of_le ((mesh_size n16 nz).trans fit)
  apply Exists.intro nz; refine ⟨full,?_⟩
  apply GirthTarget.physical _ (certificate _ _ (geometry nz) pad)
  intro F U Q A S legal spec sel valid ups fins gates w tu tq tu1 tq1 wl wh Ω _ μ _ D H
  have nn : (0:ℝ)<N := by exact_mod_cast nz.trans_le nN
  have logs := logb_le_logb_of_le (b:=2) (by norm_num) nn (by exact_mod_cast dist : (N:ℝ)≤(n:ℝ)^24)
  rw [logb_pow] at logs
  exact start n kn N w tu nN (by simpa using logs) tu1 wl wh F U Q A Ω μ S D legal spec sel tq tq1 H valid ups fins gates

end
end DisjointnessDraft.Applications.UnitGirth
