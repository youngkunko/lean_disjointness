import DisjointnessDraft.Simulation.Game
import DisjointnessFoundations.TracePacketCardinality

/-! Fixed bit lengths for the three alphabets of the physical game. The
quarter-epsilon cap includes the abort flag and the packet's length field. -/
namespace DisjointnessDraft.PhysicalProtocol
open DisjointnessFoundations Description
noncomputable section

def adviceBits (w e l : ℕ) := (2*w+1)*(e+l)
def packetBits (w l c : ℕ) := (2*w+1)*(l+c)+1
def replyBits (w fuel : ℕ) := (2*w+1)*fuel+2

theorem table_bits (w k : ℕ) : Fintype.card (Table w k) ≤ 2^((2*w+1)*k) := by
  apply (table_card w k).trans
  have h : k+1≤2^k := Nat.lt_two_pow_self
  calc _ ≤ 2^k*2^(2*w*k) := Nat.mul_le_mul_right _ h
       _ = _ := by rw [←pow_add]; congr 1; ring

theorem advice_bits (w e l : ℕ) : Fintype.card (Advice w e l) ≤ 2^(adviceBits w e l) := by
  rw [Fintype.card_prod]
  exact (Nat.mul_le_mul (table_bits w e) (table_bits w l)).trans_eq (by rw [←pow_add]; congr 1; unfold adviceBits; ring)

theorem packet_bits (w l c : ℕ) : Fintype.card (Packet w l c) ≤ 2^(packetBits w l c) := by
  rw [Fintype.card_option,packetBits,pow_succ]
  have le := table_bits w (l+c)
  have pp : 0<2^((2*w+1)*(l+c)) := by positivity
  omega

theorem reply_bits (w fuel : ℕ) : Fintype.card (TraceCode w fuel) ≤ 2^(replyBits w fuel) :=
  ShortMessage.message_bits w fuel

theorem advice_length (hw : 2≤w) (later : l≤e) : adviceBits w e l ≤ 5*w*e := by
  unfold adviceBits
  nlinarith only [Nat.mul_le_mul_left (2*w+1) later,Nat.mul_le_mul_right e hw]

theorem packet_length {ε : ℝ} {w l c s : ℕ} (hw : 4≤w) (large : 32≤ε*s)
    (later : (l:ℝ)*w≤ε*s/32) (sampling : (c:ℝ)*w≤ε*s/16) : (packetBits w l c:ℝ)≤ε*s/4 := by
  have bw : 2*(w:ℝ)+1 ≤ (9/4)*(w:ℝ) := by
    have realW : (4:ℝ)≤w := by exact_mod_cast hw
    linarith
  have H := mul_le_mul_of_nonneg_right bw (show 0≤(l:ℝ)+c by positivity)
  simp only [packetBits,Nat.cast_add,Nat.cast_mul,Nat.cast_one,Nat.cast_ofNat]
  nlinarith only [H,large,later,sampling]

theorem reply_length (hw : 10≤w) {tq : ℝ} (one : 1≤tq) :
    (replyBits w ⌊8*tq⌋₊ : ℝ) ≤ 17*tq*w := by
  have up := Nat.floor_le (show 0≤8*tq by linarith)
  have combine := mul_le_mul_of_nonneg_left up (show 0≤2*(w:ℝ)+1 by positivity)
  have lo : (10:ℝ)≤w := by exact_mod_cast hw
  have margin := mul_le_mul_of_nonneg_right lo (show 0≤tq by linarith)
  simp only [replyBits,Nat.cast_add,Nat.cast_mul,Nat.cast_one,Nat.cast_ofNat]
  nlinarith only [combine,margin,one]

end
end DisjointnessDraft.PhysicalProtocol
