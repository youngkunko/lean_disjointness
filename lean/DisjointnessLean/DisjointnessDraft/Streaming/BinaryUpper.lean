import DisjointnessDraft.Streaming.BitStorage
import DisjointnessDraft.Streaming.BinaryLower

/-! The same deterministic binary matcher answers every prefix and makes at
most ten word probes per input bit in total, with logarithmic word width. -/
namespace DisjointnessDraft.Streaming.Binary.BitStorage
open DisjointnessFoundations CellProbe WordProgram WordImage Real Classical
noncomputable section

theorem history (L : Layout n b w) (C : Code (Symbol n n) b) (hb : 0<b) (f : Family n) (raw : List Bool) :
    ∃ (src : List (Symbol n n)) (u : Buffer b) (s : Storage.Store n) (c : ℕ),
      Storage.valid s ∧ Invariant C raw src u ∧ Storage.parser s=consume f .first src ∧
      c+Storage.potential s≤10*raw.length ∧
      (machine L C hb).input C f raw =
        (decide (aligned u) && accepted (Storage.parser s),image L (pack u (Storage.words f s.1 s.2)),c) := by
  induction raw using List.reverseRecOn with
  | nil =>
    refine ⟨[],empty hb,(.first,[]),0,by simp [Storage.valid],rfl,rfl,by simp [Storage.potential],?_⟩
    simp [BitMachine.input,batch,machine,recover_exact _ hb,Program.run,Storage.parser,accepted]
  | append_singleton raw x ih =>
    obtain ⟨src,u,s,c,ok,inv,interp,paid,exec⟩ := ih
    let out := advanceBit C hb u x
    let t := nextStore f s out.2
    have good : Storage.valid t ∧ Storage.parser t=consume f .first (src++out.2.toList) ∧
        (2+wordCost s out.2)+Storage.potential t≤10+Storage.potential s := by
      cases eq : out.2 with
      | none => simp [t,nextStore,eq,ok,interp,wordCost]
      | some a =>
        have v := Storage.valid_next f s a ok
        have charge := Storage.charge f s a ok
        simp only [t,eq,nextStore,wordCost,Option.toList_some,consume,List.foldl_append,List.foldl_cons,List.foldl_nil]
        change Storage.valid (Storage.nextState f s a) ∧ Storage.parser (Storage.nextState f s a)=
          advance f (consume f .first src) a ∧ _
        exact ⟨v.1,v.2.trans (congrArg (fun ps => advance f ps a) interp),by omega⟩
    refine ⟨src++out.2.toList,out.1,t,c+(2+wordCost s out.2),good.1,advance_invariant C hb raw src u x inv,good.2.1,?_,?_⟩
    · simp only [List.length_append,List.length_singleton,Nat.mul_add,Nat.mul_one]; omega
    · change (batch _ false (raw++[x])).run _=_
      rw [batch_append]
      change (batch _ false raw |>.run _) = _ at exec
      rw [exec]
      simp only [batch,Program.run_bind,machine,Program.run,bit_run _ _ _ _ _ _ _ ok,Nat.add_zero]
      rfl

theorem upper (L : Layout n b w) (C : Code (Symbol n n) b) (hb : 0<b) :
    BitCorrect (machine L C hb) C ∧ ∀ f raw,((machine L C hb).input C f raw).2.2≤10*raw.length := by
  constructor
  · intro f raw _
    obtain ⟨src,u,s,c,_,inv,interp,_,run⟩ := history L C hb f raw
    rw [run]; apply Bool.eq_iff_iff.mpr
    simp only [Bool.and_eq_true,decide_eq_true_eq,interp,parser_correct,RegularExpression.rmatch_iff_matches',substitution]
    constructor
    · rintro ⟨endblock,mem⟩
      exact ⟨src,mem,((complete C hb raw src u inv src).mpr ⟨endblock,rfl⟩).symm⟩
    · rintro ⟨ts,mem,eq⟩
      obtain ⟨fin,rfl⟩ := (complete C hb raw src u inv ts).mp eq.symm
      exact ⟨fin,mem⟩
  · intro f raw
    obtain ⟨_,_,_,_,_,_,_,paid,run⟩ := history L C hb f raw
    rw [run]; dsimp; omega

theorem canonical_room (n : ℕ) : Nonempty (Layout n (width n) (2*width n+4)) := by
  let b := width n
  let u := 2^b
  have h₁ : n≤u := by
    have bound := Nat.lt_log2_self (n:=n+n+1)
    change n≤2^(Nat.log2 (n+n+1)+1); omega
  have h₂ : b≤u := (show b<2^b from Nat.lt_two_pow_self).le
  have pos : 0<u := pow_pos (by decide) _
  have scale : 2^(2*b+4)=16*(u*u) := by simp [u,pow_add,pow_mul,two_mul,pow_two]; ring
  apply room
  · change n*n+2*n+3≤2^(2*b+4)
    rw [scale]; nlinarith [Nat.mul_le_mul h₁ h₁,Nat.mul_le_mul_left u pos]
  · change n+8+b*u≤2^(2*b+4)
    rw [scale]; nlinarith [Nat.mul_le_mul_right u h₂,Nat.mul_le_mul_left u pos]

/-- The physical word width used by the construction lies within constant
factors of the log of the actual maximum binary expression size. -/
theorem separation_upper {n : ℕ} (hn : 7≤n) (C : Code (Symbol n n) (width n)) :
    let w := 2*width n+4
    ((w:ℝ)≤8*logb 2 (maximum C)) ∧ logb 2 (maximum C)≤4*w ∧
      ∃ D : BitMachine w, BitCorrect D C ∧ ∀ f raw,(D.input C f raw).2.2≤10*raw.length := by
  let M := maxLength n
  have r := max_range hn C
  have hm : n^2≤M := (quadratic (by omega : 1≤n)).1
  have h2 : (2:ℝ)≤M := by exact_mod_cast (show 2≤M by nlinarith)
  have one : 1≤logb 2 M := by
    simpa using logb_le_logb_of_le (b:=2) (by norm_num) (by norm_num : (0:ℝ)<2) h2
  have comp := logb_le_logb_of_le (b:=2) (by norm_num) (by linarith : (0:ℝ)<M) (by exact_mod_cast r.1 : (M:ℝ)≤maximum C)
  have now : 0<(maximum C:ℝ) := by linarith [show (M:ℝ)≤maximum C by exact_mod_cast r.1]
  have top := logb_le_logb_of_le (b:=2) (by norm_num) now (by exact_mod_cast r.2.1 : (maximum C:ℝ)≤(M:ℝ)^2)
  rw [logb_pow] at top
  have ncode : n≤2^(width n) := by have := Nat.lt_log2_self (n:=n+n+1); unfold width; omega
  have Mcode : M≤2^(2*width n+3) := by
    have mx := (quadratic (by omega : 1≤n)).2
    have p2 := Nat.mul_le_mul ncode ncode
    change maxLength n≤_; rw [pow_add,show 2*width n=width n+width n by omega,pow_add]
    simp only [pow_two] at mx; nlinarith
  have lp := logb_le_logb_of_le (b:=2) (by norm_num) (by linarith : (0:ℝ)<M)
    (by exact_mod_cast Mcode : (M:ℝ)≤(2:ℝ)^(2*width n+3))
  simp only [logb_pow,logb_self_eq_one (by norm_num : (1:ℝ)<2),mul_one] at lp
  have hb : 0<width n := Nat.succ_pos _
  let L := (canonical_room n).some
  refine ⟨?_,?_,machine L C hb,upper L C hb⟩
  · have size := r.2.2; unfold width at size; push_cast at size ⊢; dsimp [M] at comp one; linarith
  · push_cast at lp top ⊢; linarith

end
end DisjointnessDraft.Streaming.Binary.BitStorage
