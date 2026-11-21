import DisjointnessFoundations.QueryTraceInterpreter

namespace DisjointnessFoundations.VerifiedEpoch

open Simulation

theorem run_stable {Addr Word State : Type} (step : State → QueryStep Addr Word State)
    (mem : Addr → Word) (fuel : Nat) (s : State) (b : Bool)
    (done : (run step mem fuel s).answer = some b) (k : Nat)
    (enough : (run step mem fuel s).probes.length ≤ k) :
    run step mem k s = run step mem fuel s := by
  induction fuel generalizing s k with
  | zero =>
    cases h : step s <;> cases k <;> simp [run,h] at done ⊢
  | succ n ih =>
    cases h : step s with
    | done x => cases k <;> simp [run,h]
    | read a resume =>
      have done' : (run step mem n (resume (mem a))).answer = some b := by
        simpa [run,h,Transcript.prepend] using done
      cases k with
      | zero => simp [run,h,Transcript.prepend] at enough
      | succ j =>
        have enough' : (run step mem n (resume (mem a))).probes.length ≤ j := by
          simpa [run,h,Transcript.prepend] using enough
        simp [run,h,ih _ done' _ enough']

theorem run_length_le {Addr Word State : Type} (step : State → QueryStep Addr Word State)
    (mem : Addr → Word) (fuel : Nat) (s : State) :
    (run step mem fuel s).probes.length ≤ fuel := probe_budget step mem fuel s

end DisjointnessFoundations.VerifiedEpoch
