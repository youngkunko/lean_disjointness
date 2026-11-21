import DisjointnessDraft.Applications.DensityHost
import DisjointnessDraft.Transfer.Initialization

/-! The empty graph is preloaded by legal single-edge insertions. Subsequent
updates insert the three edges of a column triangle; the final script inserts
one row triangle and performs a single query. -/
namespace DisjointnessDraft.Applications.DensitySchedule
open DensityHost Transfer.Compiler Finset Classical
noncomputable section
variable {n p : ℕ}
abbrev History (n : ℕ) := List (Instr (Edge n) Unit)
def edits (h : History n) := h.filterMap Sum.getLeft?
def legal (_ : Unit) (h : History n) := (edits h).Nodup
def graph (h : History n) (e : Edge n) : Bool := decide (e∈edits h)
def valueSpec (hn : 0<n) (p : ℕ) (_ : Unit) (h : History n) (_ : Unit) := DensityHost.maximum hn (graph h) p
def decisionSpec (hn : 0<n) (p : ℕ) (u : Unit) (h : History n) (q : Unit) :=
  decide (threshold n≤valueSpec hn p u h q)
def base (F : Family n) : Edge n→Prop
  | .left _ _ | .right _ _ => True
  | .middle i j _ => j∈F i
  | _ => False
def original (F : Family n) : Finset (Edge n) := univ.filter (base F)
def initCode (F : Family n) : History n := (original F).toList.map Sum.inl ++
  List.replicate (Fintype.card (Edge n)-(original F).card) (.inr ())
def init (n : ℕ) : Initialization (Family n) Unit (Edge n) Unit :=
  ⟨fun _ => (),initCode,Fintype.card (Edge n),fun F => by
    have z := card_le_univ (original F)
    simp only [initCode,List.length_append,List.length_replicate,List.length_map,Finset.length_toList]; omega⟩
@[simp] theorem edit_append (h g : History n) : edits (h++g)=edits h++edits g := List.filterMap_append
@[simp] theorem one_insert (e : Edge n) : edits [Sum.inl e]=[e] := rfl
@[simp] theorem one_read : edits (n:=n) [.inr ()]=[] := rfl
private theorem padding (a : ℕ) : edits (n:=n) (List.replicate a (.inr ()))=[] := by
  induction a with
  | zero => rfl
  | succ a ih => simp [edits,List.replicate_succ]
theorem initial_edits (F : Family n) : edits (initCode F)=(original F).toList := by
  unfold initCode edits; rw [List.filterMap_append,List.filterMap_map]
  rw [show List.filterMap Sum.getLeft? (List.replicate _ (.inr ()))=([] : List (Edge n)) from padding _]
  simp [Function.comp_def]

def tri {V : Type} (f : Fin 3→V) := [f 0,f 1,f 2]
theorem mem_tri {V : Type} (f : Fin 3→V) (v : V) : v∈tri f ↔ ∃a,v=f a := by
  simp only [tri,List.mem_cons,List.not_mem_nil,or_false]; constructor
  · rintro (h|h|h)
    · exact ⟨0,h⟩
    · exact ⟨1,h⟩
    · exact ⟨2,h⟩
  · rintro ⟨a,rfl⟩; fin_cases a <;> simp
def cols (xs : List (Fin n)) := xs.flatMap (fun j => tri (Edge.col j))
def full (F : Family n) (xs : List (Fin n)) (q : Fin n) := (original F).toList++cols xs++tri (Edge.row q)

theorem fresh (F : Family n) (xs : List (Fin n)) (q : Fin n) (nd : xs.Nodup) : (full F xs q).Nodup := by
  have cnd : (cols xs).Nodup := by
    induction nd with
    | nil => simp [cols]
    | @cons j xs ne _ ih =>
      change (tri (Edge.col j)++cols xs).Nodup
      refine List.nodup_append.mpr ⟨by simp [tri],ih,?_⟩
      intro e le ri
      obtain ⟨a,rfl⟩ := (mem_tri _ _).mp le
      obtain ⟨k,hk,m⟩ := List.mem_flatMap.mp ri
      obtain ⟨b,eq⟩ := (mem_tri _ _).mp m
      exact ne k hk (Edge.col.inj eq).1
  have oc : List.Disjoint (original F).toList (cols xs) := by
    intro e left right
    obtain ⟨k,hk,m⟩ := List.mem_flatMap.mp right
    obtain ⟨b,rfl⟩ := (mem_tri _ _).mp m
    simp [original,base] at left
  apply List.nodup_append.mpr
  refine ⟨List.nodup_append.mpr ⟨Finset.nodup_toList _,cnd,oc⟩,by simp [tri],?_⟩
  intro e left right; obtain ⟨a,rfl⟩ := (mem_tri _ _).mp right
  rcases List.mem_append.mp left with h|h
  · simp [original,base] at h
  · obtain ⟨k,_,hm⟩ := List.mem_flatMap.mp h
    obtain ⟨b,eq⟩ := (mem_tri _ _).mp hm; contradiction

theorem realized (F : Family n) (xs : List (Fin n)) (q : Fin n) :
    (fun e => decide (e∈full F xs q))=hard (fun i j => decide (j∈F i)) (fun j => decide (j∈xs)) q := by
  funext e
  cases e <;> simp [full,original,base,cols,List.mem_flatMap,mem_tri,hard]

def plan (A : Type) (dec : A→Bool) (d : A) (n : ℕ) : Schedule n (Family n) (Edge n) Unit A :=
  ⟨id,fun j => tri (Edge.col j),fun q => (tri (Edge.row q)).map Sum.inl ++ [.inr ()],
    fun _ l => dec (l.headD d)⟩

private theorem predata (A : Type) (dec : A→Bool) (d : A) (xs : List (Fin n)) :
    edits (before (plan A dec d n) xs)=cols xs := by simp [edits,before,plan,cols,List.filterMap_map,Function.comp_def]

private theorem prefixLegal (A : Type) (dec : A→Bool) (d : A) (F : Family n) (xs : List (Fin n)) (q : Fin n) (nd : xs.Nodup)
    (h : History n) (pre : h <+: before (plan A dec d n) xs ++ (plan A dec d n).finish q) :
    initLegal (init n) legal F h := by
  have pr := pre.filterMap Sum.getLeft?
  have sub : edits h <+: cols xs++tri (Edge.row q) := by
    change edits h <+: edits (before (plan A dec d n) xs++_) at pr
    simpa only [edits,List.filterMap_append,List.filterMap_cons,List.filterMap_nil,Sum.getLeft?_inl,Sum.getLeft?_inr,
      show (plan A dec d n).finish q=[.inl (.row q 0),.inl (.row q 1),.inl (.row q 2),.inr ()] from rfl,
      ←predata A dec d xs,tri] using pr
  obtain ⟨suffix,hs⟩ := sub
  have pre2 : (original F).toList++edits h <+: full F xs q := ⟨suffix,by simp [full,List.append_assoc,hs]⟩
  have good := (fresh F xs q nd).sublist pre2.sublist
  change (edits (initCode F++h)).Nodup
  simpa only [edits,List.filterMap_append,←initial_edits] using good

private theorem blocks (A : Type) (dec : A→Bool) (d : A) (F : Family n) (xs : List (Fin n)) (q : Fin n) :
    graph (initCode F++(((before (plan A dec d n) xs++[.inl (.row q 0)])++[.inl (.row q 1)])++[.inl (.row q 2)]))=
      hard (fun i j => decide (j∈F i)) (fun j => decide (j∈xs)) q := by
  rw [←realized F xs q]
  funext e
  have eq : edits (initCode F++(((before (plan A dec d n) xs++[.inl (.row q 0)])++[.inl (.row q 1)])++[.inl (.row q 2)]))=full F xs q := by
    rw [edit_append,edit_append,edit_append,edit_append,initial_edits,predata]
    simp [full,tri,List.append_assoc]
  change decide (e∈edits _) = decide (e∈full F xs q)
  simp only [eq]

private theorem test (hn : 0<n) (p : ℕ) (F : Family n) (xs : List (Fin n)) (q : Fin n) :
    (!(decide (threshold n≤DensityHost.maximum hn (hard (fun i j => decide (j∈F i)) (fun j => decide (j∈xs)) q) p)))=answer F xs q := by
  apply Bool.eq_iff_iff.mpr
  simp [threshold_iff,answer]; tauto

theorem value_valid (hn : 0<n) (p : ℕ) : Valid (plan ℚ (fun a => !(decide (threshold n≤a))) 0 n)
    (initLegal (init n) legal) (initSpec (init n) (valueSpec hn p)) := by
  constructor
  · exact prefixLegal _ _ _
  · intro F xs q _
    change (!(decide (threshold n≤DensityHost.maximum hn (graph (initCode F++_)) p)))=_
    rw [blocks]; exact test hn p F xs q

theorem decision_valid (hn : 0<n) (p : ℕ) : Valid (plan Bool (!·) false n)
    (initLegal (init n) legal) (initSpec (init n) (decisionSpec hn p)) := by
  constructor
  · exact prefixLegal _ _ _
  · intro F xs q _
    change (!(decide (threshold n≤DensityHost.maximum hn (graph (initCode F++_)) p)))=_
    rw [blocks]; exact test hn p F xs q

end
end DisjointnessDraft.Applications.DensitySchedule
