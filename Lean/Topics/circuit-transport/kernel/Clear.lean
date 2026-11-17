import Words
import Triangular
namespace CircuitTransport
open ZeroInput.Sparse
open ProjectionDescent (Polynomial)

structure Cell where
  num : Word
  den : Nat

abbrev Coords := Nat→Cell

def Represents (b : Book) (x : Assignment) (c : Cell) (v : Rat) :=
  0<c.den ∧ c.num.value b x=(c.den:Rat)*v

def Along (b : Book) (x : Assignment) (env : Coords) (z : Assignment) :=
  ∀ i, Represents b x (env i) (z i)

def monDen (env : Coords) : List Nat→Nat
  | [] => 1
  | i::m => (env i).den*monDen env m

def common (env : Coords) : Polynomial→Nat
  | [] => 1
  | t::ts => Nat.lcm (monDen env t.monomial) (common env ts)

private theorem common_pos {b x env z} (exactAt : Along b x env z) (p : Polynomial) : 0<common env p := by
  have nz (m : List Nat) : 0<monDen env m := by
    induction m with
    | nil => exact Nat.zero_lt_one
    | cons i m ih => exact Nat.mul_pos (exactAt i).1 ih
  induction p with
  | nil => exact Nat.zero_lt_one
  | cons t ts ih => exact Nat.lcm_pos (nz _) ih

private theorem common_dvd (env : Coords) (p : Polynomial) : ∀ t∈p, monDen env t.monomial ∣ common env p := by
  induction p with
  | nil => simp
  | cons t ts ih =>
    intro u mem;rcases List.mem_cons.mp mem with eq|h
    · subst u;exact Nat.dvd_lcm_left _ _
    · exact Nat.dvd_trans (ih u h) (Nat.dvd_lcm_right _ _)

def monWord (b : Book) (env : Coords) (first : Word) : List Nat → Word
  | [] => first
  | i::m => monWord b env (times b first (env i).num) m

def clearTerm (b : Book) (env : Coords) (den : Nat) (t : Term) : Word :=
  monWord b env (integer b (t.coefficient * (den/monDen env t.monomial:Nat))) t.monomial

private theorem mon_value {b x env z} (h : Along b x env z) (w : Word) (m : List Nat) :
    (monWord b env w m).value b x=w.value b x*(monDen env m:Rat)*monomialValue z m := by
  induction m generalizing w with
  | nil => simp [monWord,monDen,monomialValue]
  | cons i m ih =>
    change (monWord b env (times b w (env i).num) m).value b x=_
    rw [ih,times_value,(h i).2]
    simp only [monDen,Rat.natCast_mul,monomialValue];grobner

theorem clear_term_value {b x env z} (h : Along b x env z) (den : Nat) (t : Term)
    (multiple : monDen env t.monomial ∣ den) :
    (clearTerm b env den t).value b x=(den:Rat)*termValue z t := by
  have rat := congrArg (fun n : Nat => (n:Rat)) (Nat.div_mul_cancel multiple)
  simp only [Rat.natCast_mul] at rat
  unfold clearTerm;rw [mon_value h,integer_value]
  simp only [Rat.intCast_mul,Rat.intCast_natCast,termValue];grobner

def accumulate (b : Book) (env : Coords) (den : Nat) (start : Word) : Polynomial→Word
  | [] => start
  | t::ts => accumulate b env den (plus b start (clearTerm b env den t)) ts

def clearRow (b : Book) (env : Coords) (p : Polynomial) : Cell :=
  let d := common env p
  ⟨accumulate b env d (integer b 0) p,d⟩

private theorem accumulate_value {b x env z} (h : Along b x env z) (den : Nat) (w : Word) (p : Polynomial)
    (mult : ∀ t∈p, monDen env t.monomial ∣ den) :
    (accumulate b env den w p).value b x=w.value b x+(den:Rat)*value z p := by
  induction p generalizing w with
  | nil => simp [accumulate,value,Rat.add_zero]
  | cons t ts ih =>
    change (accumulate b env den (plus b w (clearTerm b env den t)) ts).value b x=_
    rw [ih _ (fun u hu => mult u (List.mem_cons_of_mem _ hu)),plus_value,clear_term_value h _ _ (mult t (by simp))]
    simp only [value];grobner

theorem clear_row_value {b x env z} (h : Along b x env z) (p : Polynomial) :
    Represents b x (clearRow b env p) (value z p) := by
  refine ⟨common_pos h p,?_⟩
  change (accumulate b env (common env p) (integer b 0) p).value b x=(common env p:Rat)*value z p
  rw [accumulate_value h _ _ _ (common_dvd _ _),integer_value];simp [Rat.zero_add]

def pivotCell (b : Book) (env : Coords) (p : Triangular.Pivot) : Cell :=
  let row := clearRow b env (p.pre++p.post)
  ⟨if 0<p.lead then times b (integer b (-1)) row.num else row.num,row.den*p.lead.natAbs⟩

theorem pivot_cell_value {b x env z} (h : Along b x env z) (p : Triangular.Pivot) (nz : p.lead≠0) :
    Represents b x (pivotCell b env p) (p.sol z) := by
  let r := clearRow b env (p.pre++p.post)
  have cr : Represents b x r (value z (p.pre++p.post)) := clear_row_value h _
  have lead : (p.lead:Rat)≠0 := fun eq => nz (Rat.intCast_eq_zero_iff.mp eq)
  have sol : p.sol z*(p.lead:Rat) = -(value z (p.pre++p.post)) := by
    have v : p.sol z*(p.lead:Rat)=value z p.num := Rat.div_mul_cancel lead
    rw [v,Triangular.Pivot.num,ProjectionDescent.scale_value];grobner
  refine ⟨Nat.mul_pos cr.1 (Int.natAbs_pos.mpr nz),?_⟩
  change (if 0<p.lead then times b (integer b (-1)) r.num else r.num).value b x=((r.den*p.lead.natAbs:Nat):Rat)*p.sol z
  rw [Rat.natCast_mul]
  by_cases pos : 0<p.lead
  · have eq := congrArg (fun i : Int => (i:Rat)) (Int.eq_natAbs_of_nonneg (Int.le_of_lt pos))
    rw [if_pos pos,times_value,integer_value,cr.2];simp only [Rat.intCast_natCast] at eq;grobner
  · have npos : 0≤ -p.lead := by omega
    have t := Int.eq_natAbs_of_nonneg npos
    rw [Int.natAbs_neg] at t
    have eq := congrArg (fun i : Int => (i:Rat)) t
    simp only [Rat.intCast_neg,Rat.intCast_natCast] at eq
    rw [if_neg pos,cr.2];grobner

def update (env : Coords) (i : Nat) (v : Cell) : Coords := fun j => if j=i then v else env j

def restore (b : Book) : List Triangular.Pivot→Coords→Coords
  | [], env => env
  | p::ps, env =>
    let c := pivotCell b env p
    restore b ps (update env p.slot c)

theorem restore_value {b x env z} (h : Along b x env z) (ps : List Triangular.Pivot)
    (valid : Triangular.valid ps=true) : Along b x (restore b ps env) (Triangular.recov ps z) := by
  induction ps generalizing env z with
  | nil => exact h
  | cons p ps ih =>
    have ok := valid
    simp [Triangular.valid,and_assoc] at ok
    apply ih _ ok.2.2.2;intro j
    by_cases e : j=p.slot
    · subst j; simpa [update,ProjectionDescent.put] using pivot_cell_value h p ok.1
    · simpa [update,ProjectionDescent.put,e] using h j

def initial (b : Book) (code : Nat→Nat) (i : Nat) : Cell :=
  ⟨if Triangular.inside i then varWord b (code i) else integer b 0,1⟩

theorem initial_value (b : Book) (code : Nat→Nat) (y : Fin 153→Rat) :
    Along b (finiteLift y) (initial b code) (Triangular.seed code y) := by
  intro i;refine ⟨Nat.zero_lt_one,?_⟩
  by_cases h : Triangular.inside i=true
  · simp [initial,Triangular.seed,h,variable_value,Rat.one_mul]
  · simp [initial,Triangular.seed,h,integer_value]

end CircuitTransport
