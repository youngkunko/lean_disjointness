import DisjointnessDraft.Applications.MatchTarget

/-! Every sufficiently large integer vertex count admits the planar bipartite
matching lower bound, both for the optimal weight and for the fixed threshold.
The exact counts include both outside terminals and isolated padding. -/
namespace DisjointnessDraft.Applications.MatchingLower
open MatchGraph MatchTarget PlanarEncoding CoreSize ShortTransfer Transfer.Compiler Filter
noncomputable section
def size (n : ℕ) := 16*(n+1)^2+8*(n+1)+2
def sourceSize (N : ℕ) := (N/100).sqrt
def extra (N : ℕ) := N-size (sourceSize N)
theorem card (n pad : ℕ) : Fintype.card (L n ⊕ R n pad)=size n+pad := by
  simp only [Fintype.card_sum,Fintype.card_option,Fintype.card_fin]
  rw [show Fintype.card (Core n)=8*(dim n)^2+4*(dim n) from paired_size _]
  simp [size,dim]; ring
theorem geometry (k : ℕ) : ∀ᶠ N : ℕ in atTop, k≤sourceSize N ∧ size (sourceSize N)≤N ∧
    sourceSize N≤N ∧ N≤sourceSize N^3 := by
  let b := max k 500
  filter_upwards [eventually_ge_atTop (100*(b*b):ℕ)] with N hN
  let n := sourceSize N
  have bn : b≤n := Nat.le_sqrt.mpr (by omega)
  have big : 500≤n := (le_max_right ..).trans bn
  have fit := Nat.sqrt_le (N/100)
  have next := Nat.lt_succ_sqrt (N/100)
  change n*n≤N/100 at fit
  change N/100<(n+1)*(n+1) at next
  have sq : size n≤100*(n*n) := by
    dsimp [size]; nlinarith only [big,Nat.mul_le_mul_right n big]
  have above : 100*((n+1)*(n+1))≤n^3 := by
    nlinarith only [big,Nat.mul_le_mul_right n big,Nat.mul_le_mul_right (n*n) big]
  exact ⟨(le_max_left ..).trans bn,sq.trans (by omega),(Nat.sqrt_le_self (N/100)).trans (Nat.div_le_self ..),
    by change N≤n^3; omega⟩

theorem lower (lo hi : ℝ) (lp : 0<lo) (lh : lo≤hi) :
    ∃ c : ℝ,0<c ∧ ∀ᶠ N : ℕ in atTop,
      let n := sourceSize N
      let pad := extra N
      Fintype.card (L n ⊕ R n pad)=N ∧ limit n≤(N:ℤ) ∧
      Bound lo hi c N true (legal (A:=L n) (B:=R n pad) (limit n)) valueSpec ∧
      Bound lo hi c N true (legal (A:=L n) (B:=R n pad) (limit n)) (decisionSpec (value n+1)) := by
  obtain ⟨c,cp,large⟩ := eventual lo hi lp lh
  obtain ⟨k,all⟩ := eventually_atTop.mp large
  refine ⟨c,cp,?_⟩
  filter_upwards [geometry k] with N geom
  let n := sourceSize N; let pad := extra N
  obtain ⟨nk,fit,nN,pow⟩ := geom
  have base : Realizes lo hi c n N := @all n nk N nN pow
  have cnt : Fintype.card (L n ⊕ R n pad)=N := by rw [card]; exact Nat.add_sub_of_le fit
  have weight : limit n≤(size n:ℤ) := by
    dsimp [limit,PlanarCore.H,dim,size]; push_cast; nlinarith [sq_nonneg (n:ℤ)]
  refine ⟨cnt,weight.trans (by exact_mod_cast fit),?_,?_⟩
  · intro w tu tq tu1 tq1 wl wh Ω _ μ _ D gu
    have bound := base _ true (value_valid n pad) (by simp [plan]) (by simp [plan]) (by simp)
    exact bound w tu tq tu1 tq1 wl wh Ω μ (initialized D (init n pad)) (init_guarantees μ D _ gu)
  · intro w tu tq tu1 tq1 wl wh Ω _ μ _ D gu
    have bound := base _ true (decision_valid n pad) (by simp [plan]) (by simp [plan]) (by simp)
    exact bound w tu tq tu1 tq1 wl wh Ω μ (initialized D (init n pad)) (init_guarantees μ D _ gu)
/-- Positive integer weights can be chosen freely on every legal planar input. -/
def positivePlanar {A B : Type} (_ : Unit) (h : Hist A B) :=
  ((edits h).map Prod.fst).Nodup ∧ (∀u k v,edges h u k v → 0<k) ∧
    Nonempty (PlanarPadding.Drawing (MatchGraph.plain (edges h)))

private theorem positive_bound {A B C : Type} {spec : Unit → Hist A B → Unit → C}
    {lo hi c : ℝ} {N : ℕ} {b : ℤ} (low : Bound lo hi c N true (legal b) spec) :
    Bound lo hi c N true positivePlanar spec := by
  intro w tu tq tu1 tq1 wl wh Ω _ μ _ D gu
  apply low w tu tq tu1 tq1 wl wh Ω μ D
  have sub (f : Unit) (h : Hist A B) (x : legal b f h) : positivePlanar f h :=
    ⟨x.1,fun u k v e => (x.2.1 u k v e).1,x.2.2⟩
  exact ⟨fun a f h u e => gu.update a f h u (sub f _ e),
    fun f h q e => gu.query f h q (sub f _ e),
    fun a f h q e => gu.correct a f h q (sub f _ e),
    fun f h op e => gu.measurable f h op (sub f _ e)⟩

theorem planar_lower (lo hi : ℝ) (lp : 0<lo) (lh : lo≤hi) :
    ∃ c : ℝ,0<c ∧ ∀ᶠ N : ℕ in atTop,
      let n := sourceSize N
      let pad := extra N
      Fintype.card (L n ⊕ R n pad)=N ∧
      Bound lo hi c N true (positivePlanar (A:=L n) (B:=R n pad)) valueSpec ∧
      Bound lo hi c N true (positivePlanar (A:=L n) (B:=R n pad)) (decisionSpec (value n+1)) := by
  obtain ⟨c,cp,all⟩ := lower lo hi lp lh
  refine ⟨c,cp,?_⟩
  filter_upwards [all] with N h
  exact ⟨h.1,positive_bound h.2.2.1,positive_bound h.2.2.2⟩
end
end DisjointnessDraft.Applications.MatchingLower
