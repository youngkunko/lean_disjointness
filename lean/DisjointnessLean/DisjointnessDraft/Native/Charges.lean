import DisjointnessDraft.Native.Operational

namespace DisjointnessDraft.Native
open DisjointnessFoundations CellProbe Simulation Execution Chronogram ProtocolRun HardProtocol PhysicalProtocol HardDistribution
open VerifiedEpoch
open scoped ENNReal BigOperators
noncomputable section
open Classical
variable {n ℓ g w : ℕ} {Ω Coin : Type} (fit : occupied ℓ g≤n)
def parts (D : Machine n w Coin) (R : RandomTape Ω Coin) (seed : Ω) (F : Fin n → Whole ℓ g) (I : Whole ℓ g)
    (pre : List (Fin n)) : List (Fin ℓ) → List (HardWrites.Group ℓ w)
  | [] => []
  | i :: rest =>
    (i, segmentLog D R seed pre.length (afterPrefix D R seed (rows fit F) pre) (epochElements fit I i)) ::
      parts D R seed F I (pre++epochElements fit I i) rest

theorem parts_append (D : Machine n w Coin) (R : RandomTape Ω Coin) (seed : Ω)
    (F : Fin n → Whole ℓ g) (I : Whole ℓ g) (pre : List (Fin n)) (a b : List (Fin ℓ)) :
    parts fit D R seed F I pre (a++b) = parts fit D R seed F I pre a ++
      parts fit D R seed F I (pre++a.flatMap (epochElements fit I)) b := by
  induction a generalizing pre with
  | nil => simp [parts]
  | cons i a ih => simp [parts,ih,List.append_assoc]

theorem parts_flatten (D : Machine n w Coin) (R : RandomTape Ω Coin) {tu : ℝ≥0∞}
    (h : WorstUpdate D R tu) (seed : Ω) (F : Fin n → Whole ℓ g) (I : Whole ℓ g) (pre : List (Fin n)) (a : List (Fin ℓ)) :
    (parts fit D R seed F I pre a).flatMap Prod.snd = segmentLog D R seed pre.length
      (afterPrefix D R seed (rows fit F) pre) (a.flatMap (epochElements fit I)) := by
  induction a generalizing pre with
  | nil => rfl
  | cons i a ih =>
    obtain ⟨c,hc⟩ := suffix_ok D R h seed (rows fit F) pre (epochElements fit I i)
    simp only [parts,List.flatMap_cons,ih,List.length_append]
    rw [HardWrites.segmentLog_append _ _ _ _ _ _ _ _ _ hc]

def owner (a : Word w) : List (HardWrites.Group ℓ w) → Option (Fin ℓ)
  | [] => none
  | (i,l) :: rest => (owner a rest).orElse fun _ => if Written l a then some i else none

private theorem owner_none (a : Word w) (groups : List (HardWrites.Group ℓ w)) :
    owner a groups = none ↔ ¬ Written (groups.flatMap Prod.snd) a := by
  induction groups with
  | nil => simp [owner,Written]
  | cons p rest ih =>
    obtain ⟨i,log⟩ := p
    have append (l r : Execution.Log w) : Written (l++r) a ↔ Written l a ∨ Written r a := by
      simp only [Written,List.mem_append,exists_or]
    rw [List.flatMap_cons, append]
    change (owner a rest).orElse (fun _ => if Written log a then some i else none) = none ↔ _
    cases hr : owner a rest with
    | none =>
      have hrest := ih.mp hr
      by_cases hlog : Written log a <;> simp [hlog,hrest]
    | some j =>
      have hrest : Written (rest.flatMap Prod.snd) a := by
        apply Classical.byContradiction
        intro hn
        have impossible := ih.mpr hn
        rw [hr] at impossible
        contradiction
      simp [hrest]

private theorem owner_suffix (a : Word w) (pre post : List (HardWrites.Group ℓ w)) {i}
    (h : owner a post = some i) : owner a (pre++post) = some i := by
  induction pre with
  | nil => exact h
  | cons p pre ih => obtain ⟨j,l⟩ := p; simp [owner,ih]

theorem owner_of_epoch (D : Machine n w Coin) (R : RandomTape Ω Coin)
    {tu : ℝ≥0∞} (h : WorstUpdate D R tu) (seed : Ω) (F : Fin n → Whole ℓ g) (I : Whole ℓ g) (i : Fin ℓ)
    (a : Word w)
    (hit : EpochCells (epochLog fit D R seed F I i) (recentLog fit D R seed F I i) a) :
    owner a (parts fit D R seed F I [] (order ℓ)) = some i := by
  let early := (order ℓ).take ((order ℓ).idxOf i)
  let late := (order ℓ).drop ((order ℓ).idxOf i+1)
  have mem : i ∈ order ℓ := by simp [order,List.mem_finRange]
  have lt := List.idxOf_lt_length_iff.mpr mem
  have e := List.take_append_drop ((order ℓ).idxOf i) (order ℓ)
  rw [List.drop_eq_getElem_cons lt,List.getElem_idxOf lt] at e
  change early ++ i::late = order ℓ at e
  conv_lhs => rw [← e,parts_append]
  apply owner_suffix
  simp only [List.nil_append,parts,owner]
  have hnl : owner a (parts fit D R seed F I (before fit I i ++ epochElements fit I i) late) = none := by
    apply (owner_none _ _).mpr
    rw [parts_flatten fit D R h]
    exact hit.2
  change (owner a (parts fit D R seed F I (before fit I i ++ epochElements fit I i) late)).orElse _ = _
  rw [hnl]
  exact if_pos hit.1


variable (D : Machine n w Coin) (R : RandomTape Ω Coin) (a : Ω)
def lastCells (z : Draw n ℓ g) (i : Fin ℓ) :=
  touched (epochLog fit D R a z.2.1 z.2.2 i) \ touched (recentLog fit D R a z.2.1 z.2.2 i)

def hits (z : Draw n ℓ g) (i : Fin ℓ) (fuel : ℕ) :=
  ((lastCells fit D R a z i) ∩ touched (trace fit D R a z fuel).probes).card

theorem distinct_budget {tu : ℕ} (hu : WorstUpdate D R (tu:ℝ≥0∞)) (z : Draw n ℓ g) (fuel : ℕ) :
    ∑ i, hits fit D R a z i fuel ≤ (trace fit D R a z fuel).probes.length := by
  let tr := (trace fit D R a z fuel).probes
  let cells (i : Fin ℓ) := lastCells fit D R a z i ∩ touched tr
  have dis : (Finset.univ : Finset (Fin ℓ)).toSet.PairwiseDisjoint cells := by
    intro i _ j _ ne
    apply Finset.disjoint_left.mpr
    intro addr hi hj
    have eq (k : Fin ℓ) (h : addr∈cells k) := owner_of_epoch fit D R hu a z.2.1 z.2.2 k addr
      (show EpochCells _ _ addr by simpa only [lastCells,Finset.mem_sdiff,mem_touched] using (Finset.mem_inter.mp h).1)
    exact ne (Option.some.inj ((eq i hi).symm.trans (eq j hj)))
  change ∑ i,(cells i).card ≤ tr.length
  rw [←Finset.card_biUnion dis]
  have sub : Finset.univ.biUnion cells ⊆ touched tr := by
    intro x hx
    obtain ⟨i,_,hi⟩ := Finset.mem_biUnion.mp hx
    exact (Finset.mem_inter.mp hi).2
  exact (Finset.card_le_card sub).trans ((List.toFinset_card_le _).trans (List.length_map ..).le)

def tau (fuel : ℕ) (i : Fin ℓ) := mean (fun z : Draw n ℓ g => (hits fit D R a z i fuel:ℝ))

theorem select_epoch {tu : ℕ} {tq : ℝ} (hu : WorstUpdate D R (tu:ℝ≥0∞)) (hz : FreshCorrect D R)
    (hl : 20≤ℓ) (fuel : ℕ) (cheap : mean (fun z : Draw n ℓ g => (reads fit D R a z:ℝ))≤tq) :
    ∃ i∈chronogram ℓ,tau fit D R a fuel i≤tq/(chronogram ℓ).card := by
  classical
  have hn := chronogram_card ℓ
  have p : 0<(chronogram ℓ).card := by omega
  let τ := tau fit D R a fuel
  have sum : ∑ i,τ i ≤ tq := by
    dsimp [τ,tau]
    rw [←mean_sum]
    apply le_trans _ cheap
    apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
    apply Finset.sum_le_sum
    intro z _
    have bound := distinct_budget fit D R a hu z fuel
    have traceBound : (trace fit D R a z fuel).probes.length≤reads fit D R a z := by
      have h := exact_trace fit D R hu hz a z
      dsimp only at h
      by_cases k : reads fit D R a z≤fuel
      · have same : trace fit D R a z fuel=trace fit D R a z (reads fit D R a z) := run_stable _ _ _ _ _ h.1 fuel (h.2.le.trans k)
        rw [same,h.2]
      · exact (run_length_le ..).trans (by omega)
    exact_mod_cast bound.trans traceBound
  have cap := (Finset.sum_le_univ_sum_of_nonneg (s:=chronogram ℓ) (f:=τ) (fun i => by
    dsimp [τ,tau,mean]; positivity)).trans sum
  by_contra! bad
  have all := Finset.sum_lt_sum_of_nonempty (Finset.card_pos.mp p) bad
  have pc : (0:ℝ)<(chronogram ℓ).card := by exact_mod_cast p
  simp only [Finset.sum_const,nsmul_eq_mul] at all
  rw [show ((chronogram ℓ).card:ℝ)*(tq/(chronogram ℓ).card)=tq by field_simp] at all
  exact (not_lt_of_ge cap) all

end
end DisjointnessDraft.Native
