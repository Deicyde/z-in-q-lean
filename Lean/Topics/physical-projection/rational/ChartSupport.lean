import RationalChart
import ClosedProof
namespace PhysicalProjection
open ZeroInput.Sparse ProjectionDescent Triangular Triangular.Data
set_option maxRecDepth 18000
set_option maxHeartbeats 2000000

def privateSlots := [137,138,139,149,150,151,161,162,163]
def padeSlots := [80,81,90,91,96,97,102,103]
def changed := [136,140,141,148,152,153,160,164,165]
def ports := [136,148,160]
def earlySlots := [2,3,6,7,8,9,12,13,32,130,131,132,133,134,145,157]
def visible := apart (privateSlots++padeSlots)

theorem parents_len : parentSlots.length=130 := rfl

def pack (z : Assignment) (i : Fin 130) : Rat := z ((parentSlots[i.val]?).getD 0)

private theorem index_mem (l : List Nat) (i : Nat) (h : i∈l) : l[l.idxOf i]?.getD 0=i := by
  induction l with
  | nil => simp at h
  | cons a t ih =>
    by_cases e : a=i
    · subst i; simp
    · have later : i∈t := (List.mem_cons.mp h).resolve_left (Ne.symm e)
      simpa [List.idxOf_cons,cond_eq_ite,e] using ih later

theorem seed_pack (z : Assignment) (i : Nat) (hi : i∈parentSlots) : seed130 (pack z) i=z i := by
  have b := List.idxOf_lt_length_of_mem hi
  rw [parents_len] at b
  unfold seed130 compactSlot
  rw [finiteLift,dif_pos b]
  change z ((parentSlots[parentSlots.idxOf i]?).getD 0)=z i
  rw [index_mem _ _ hi]

theorem seed_missing (y : Fin 130→Rat) (i : Nat) (bad : i∉parentSlots) : seed130 y i=0 := by
  unfold seed130 compactSlot
  rw [List.idxOf_eq_length bad,parents_len];rfl

theorem seed_at_input (y : Fin 130→Rat) : seed130 y 1=finiteLift y 1 := rfl

theorem row_congr {z w : Assignment} (p : Polynomial)
    (h : ∀ t∈p, ∀ i∈t.monomial, z i=w i) : value z p=value w p := by
  have m (l : List Nat) (ok : ∀ i∈l,z i=w i) : monomialValue z l=monomialValue w l := by
    induction l with
    | nil => rfl
    | cons i t ih => simp only [monomialValue,ok i (by simp),ih (fun j hj => ok j (List.mem_cons_of_mem _ hj))]
  induction p with
  | nil => rfl
  | cons a tail ih =>
    simp only [value,termValue,m a.monomial (h a (by simp)),ih (fun t ht => h t (List.mem_cons_of_mem _ ht))]

theorem reads_slot {f : Nat→Bool} {p : Polynomial} (s : reads f p=true)
    {t : Term} (ht : t∈p) {i : Nat} (hi : i∈t.monomial) : f i=true :=
  List.all_eq_true.mp (List.all_eq_true.mp s t ht) i hi

/-- The recovery on a closed subset of the coordinates depends only on its free entries. -/
theorem recov_on (ps : List Pivot) (live : Nat→Bool) (x y : Assignment) (validity : valid ps=true)
    (closed : ∀ p∈ps, live p.slot=true → reads live p.num=true)
    (base : ∀ i, live i=true → i∉slots ps → x i=y i) :
    ∀ i,live i=true → recov ps x i=recov ps y i := by
  induction ps generalizing x y with
  | nil => intro i l;exact base i l (by simp [slots])
  | cons p ps ih =>
    have parts : (p.lead≠0 ∧ p.slot∉slots ps) ∧ reads (apart (p.slot::slots ps)) p.num=true ∧ valid ps=true := by
      simpa [valid,and_assoc] using validity
    apply ih _ _ parts.2.2 (fun q h => closed q (List.mem_cons_of_mem _ h))
    intro i il fresh
    by_cases eq : i=p.slot
    · subst i
      simp [put]
      apply congrArg (fun t : Rat => t/(p.lead:Rat))
      apply row_congr; intro t ht j hj
      have v := reads_slot (closed p (by simp) il) ht hj
      have free := reads_slot parts.2.1 ht hj
      exact base j v (by simpa [apart,slots] using free)
    · simp only [put,if_neg eq]
      exact base i il (by simpa [slots,eq] using fresh)

theorem physical_visible (g : Bool) : ∀ p∈ps g, reads visible p.row=true ∧ reads visible p.num=true := by
  have h : (ps g).all (fun p => reads visible p.row && reads visible p.num)=true := by cases g <;> decide
  intro p hp; simpa using List.all_eq_true.mp h p hp

theorem physical_early (g : Bool) : ∀ p∈ps g, earlySlots.contains p.slot=true → reads earlySlots.contains p.num=true := by
  have h : (ps g).all (fun p => !earlySlots.contains p.slot || reads earlySlots.contains p.num)=true := by cases g <;> decide
  intro p hp l
  have alt := List.all_eq_true.mp h p hp
  rw [l] at alt; exact alt

theorem physical_active (g : Bool) : ∀ r∈activeRows g, reads (apart privateSlots) r.2=true := by
  have h : (activeRows g).all (fun r => reads (apart privateSlots) r.2)=true := by cases g <;> decide
  exact List.all_eq_true.mp h

theorem no_hidden_pivot (g : Bool) {i : Nat} (hi : i∈privateSlots++padeSlots++changed++[1,32,135,147,159]) : i∉slots (ps g) := by
  have h : (privateSlots++padeSlots++changed++[1,32,135,147,159]).all (fun i => !(slots (ps g)).contains i)=true := by unfold ps; rw [slots0]; decide
  simpa using List.all_eq_true.mp h i hi

theorem outside_pivots (g : Bool) {i : Nat} (hi : inside i=false) : i∉slots (ps g) := by
  have h : (slots (ps g)).all inside=true := by unfold ps; rw [slots0]; decide
  intro p; have := List.all_eq_true.mp h i p; rw [hi] at this; contradiction

theorem middle_free (g : Bool) (y : Fin 130→Rat) {i : Nat} (hi : i∉slots (ps g)) :
    middle g y i=detectorSeed (preliminary g y) (seed130 y) i := keeps _ _ i hi

theorem detectorSeed_keep (pre base : Assignment) {i : Nat} (hi : i∉changed) : detectorSeed pre base i=base i := by
  simp [changed] at hi
  simp [detectorSeed,hi]

theorem fillPairs_keep (x : Assignment) {i : Nat} (hi : i∉padeSlots) : fillPairs x i=x i := by
  simp [padeSlots] at hi
  simp [fillPairs,hi]

theorem matrix_blind (g : Bool) {x z : Assignment} (ok : ∀p∈ps g,p.ok x)
    (away : off padeSlots x z) : ∀p∈ps g,p.ok z := by
  intro p hp
  have eq : value z p.row=value x p.row := by
    apply row_congr;intro t ht j hj
    have inVis := reads_slot (physical_visible g p hp).1 ht hj
    have h : j∉privateSlots ∧ j∉padeSlots := by simpa [visible,apart] using inVis
    exact away j h.2
  have clause := pivot_cell p.pre p.post p.slot p.lead
  exact (clause z).mp (eq.trans ((clause x).mpr (ok p hp)))

theorem point_pivots (g : Bool) (y : Fin 130→Rat) : ∀p∈ps g,p.ok (chartPoint g y) :=
  matrix_blind g (all_solved (ps g) (good0 g) _) (fun _ h => fillPairs_keep _ h)

end PhysicalProjection
