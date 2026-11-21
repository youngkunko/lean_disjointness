import DisjointnessFoundations.FiniteProbeProgramCompiler

namespace DisjointnessFoundations.WordImage

open WordProgram CellProbe Classical
noncomputable section
set_option linter.unusedSectionVars false

variable {A V X : Type} [eqA : DecidableEq A] [inhV : Nonempty V] {w : ℕ}

structure Layout (A V : Type) (w : ℕ) where
  addr : A ↪ Word w
  value : V ↪ Word w
  blank : V

def codec (L : Layout A V w) : Codec A V w where
  live := fun _ => True
  addr := L.addr
  inject := by intro a _ b _ h; exact L.addr.injective h
  encode := L.value
  decode := Function.invFun L.value

def image (L : Layout A V w) (mem : A→V) : Memory w :=
  fun p => if h : p ∈ Set.range L.addr then L.value (mem h.choose) else L.value L.blank

include eqA inhV in
theorem image_at (L : Layout A V w) (mem : A→V) (a : A) : image L mem (L.addr a)=L.value (mem a) := by
  unfold image
  rw [dif_pos (Set.mem_range_self a)]
  rw [L.addr.injective (Set.mem_range_self a).choose_spec]

theorem image_outside (L : Layout A V w) (mem : A→V) (p : Word w) (missing : p∉Set.range L.addr) :
    image L mem p=L.value L.blank := dif_neg missing

include inhV in
theorem image_update (L : Layout A V w) (mem : A→V) (a : A) (v : V) :
    Function.update (image L mem) (L.addr a) (L.value v)=image L (Function.update mem a v) := by
  funext p
  by_cases hp : p ∈ Set.range L.addr
  · obtain ⟨j,rfl⟩ := hp
    by_cases e : j=a
    · subst j; simp [image_at]
    · have h : L.addr j ≠ L.addr a := fun he => e (L.addr.injective he)
      simp [Function.update_of_ne h,Function.update_of_ne e,image_at]
  · have h : p ≠ L.addr a := fun e => hp ⟨a,e.symm⟩
    simp [Function.update_of_ne h,image_outside,hp]

theorem update_exact (L : Layout A V w) (p : Program A V X) (mem : A→V) :
    let o := p.run mem
    updateRun (codec L).updateStep o.2.2 p (image L mem)=some (image L o.2.1,o.2.2) := by
  induction p generalizing mem with
  | pure r => rfl
  | read a k ih =>
    simp only [Program.run]
    rw [Nat.add_comm 1,updateRun,Codec.updateStep]
    simp only [codec,Function.comp_apply,image_at,Function.leftInverse_invFun L.value.injective (mem a)]
    exact congrArg (Option.map (fun (u,t) => (u,t+1))) (ih (mem a) mem)
  | write a v k ih =>
    simp only [Program.run]
    rw [Nat.add_comm 1,updateRun,Codec.updateStep]
    simp only [codec,image_update]
    exact congrArg (Option.map (fun (u,t) => (u,t+1))) (ih (Function.update mem a v))

theorem represents (L : Layout A V w) (mem : A→V) : (codec L).represents mem (image L mem) := by
  intro a _
  exact (congrArg (Function.invFun L.value) (image_at L mem a)).trans
    (Function.leftInverse_invFun L.value.injective (mem a))

end
end DisjointnessFoundations.WordImage
