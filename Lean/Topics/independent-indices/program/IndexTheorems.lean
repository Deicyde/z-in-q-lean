import PhysicalLayout
import PeakLayout
import IndexData

namespace IndependentIndices
open CircuitTransport Data

def parentProgram (g : Bool) : Program := build (oldSeed g) (families g) oldRoutes oldShape
def splitProgram (g : Bool) : Program := build (newSeed g) (families g) newRoutes newShape

def holds (g marked : Bool) (y : Fin 134→Rat) (f : Frame) :=
  frameConditions newShape (families g) newRoutes marked (vector y) f

/-- The signed common rows and the four private systems are equivalent to the
    actual rational zero condition, including the marked fibre at input zero. -/
theorem split_iff (g marked : Bool) (y : Fin 134→Rat) :
    (splitProgram g).eval marked (vector y)=0 ↔
    holds g marked y .common ∧ holds g marked y .first ∧ holds g marked y .second ∧
    holds g marked y .third ∧ holds g marked y .scalar :=
  (pointwise ..).trans (grouped ..)

theorem unpaired_iff (g marked : Bool) (x : Fin 74→Rat) :
    (parentProgram g).eval marked (vector x)=0 ↔
    conditions oldShape (families g) oldRoutes marked (vector x) := pointwise ..

/-- Restricting the split circuit to the diagonal gives the same zero set. -/
theorem diagonal_iff (g marked : Bool) (x : Fin 74→Rat) :
    (splitProgram g).eval marked (vector (diagonal x))=0 ↔
    (parentProgram g).eval marked (vector x)=0 :=
  (pointwise ..).trans ((diagonal_chart ..).trans (unpaired_iff g marked x).symm)

theorem diagonal_projection (g marked : Bool) (a : Rat) :
    (∃x : Fin 74→Rat, vector x 1=a ∧ (parentProgram g).eval marked (vector x)=0) →
    ∃y : Fin 134→Rat, vector y 1=a ∧ (splitProgram g).eval marked (vector y)=0 := by
  rintro ⟨x,hx,p⟩
  exact ⟨diagonal x,(first_input x).trans hx,(diagonal_iff g marked x).mpr p⟩

/-- Common slots occupy positions 1--17, followed by the three 35-slot
    comparisons and the last 12-slot scalar. A frame reads no other coordinates. -/
theorem frame_congr (g marked : Bool) (f : Frame) (x y : Fin 134→Rat)
    (same : ∀i,inFrame f i=true → vector x i=vector y i) :
    holds g marked x f ↔ holds g marked y f := by
  have input : vector x 1=vector y 1 := same 1 (by cases f <;> decide)
  have activeEq : active newShape marked (vector x)=active newShape marked (vector y) := by
    unfold active;rw [input]
  have subset : ∀r∈active newShape marked (vector y), r∈newShape.high.refs++newShape.low.refs := by
    unfold active
    split
    · exact fun _ h=>List.mem_append_left _ h
    · exact fun _ h=>h
  unfold holds frameConditions
  rw [activeEq]
  constructor
  · intro h r hr hf
    have eq:=row_local (families g) r (vector x) (vector y) (subset r hr) (by rw [hf];exact same)
    exact eq.symm.trans (h r hr hf)
  · intro h r hr hf
    have eq:=row_local (families g) r (vector x) (vector y) (subset r hr) (by rw [hf];exact same)
    exact eq.trans (h r hr hf)

def axis (a : Rat) (i : Nat) : Rat := if i=1 then a else 0

private theorem protected_row {rs : Routes} (fs : Families) (r : Ref)
    (a : Rat) (h : peakOK rs r=true) : rowValue fs rs (axis a) r=0 := by
  obtain ⟨mark,slots⟩:=Bool.and_eq_true_iff.mp h
  change valueAt _ (routed (rs[r.cell]!).slots (axis a)) (r.index _)=0
  rw [Ref.index,if_pos mark]
  apply origin_value
  intro i hi
  unfold routed
  cases found : (rs[r.cell]!).slots[i]? with
  | none => rfl
  | some j =>
    have ht : ((rs[r.cell]!).slots.toList.drop 1)[i-1]?=some j := by
      rw [List.getElem?_drop,show 1+(i-1)=i by omega]
      simpa only [Array.getElem?_toList] using found
    have ne : j≠1 := of_decide_eq_true (List.all_eq_true.mp slots j (List.mem_of_getElem? ht))
    simp [axis,ne]

theorem high_on_axis (g : Bool) (a : Rat) :
    oldShape.high.sos (rowValue (families g) oldRoutes (axis a))=0 ∧
    newShape.high.sos (rowValue (families g) newRoutes (axis a))=0 := by
  constructor
  · exact (Tree.sos_zero ..).mpr (fun r hr=>protected_row _ r a (List.all_eq_true.mp peak_routes.1 r hr))
  · exact (Tree.sos_zero ..).mpr (fun r hr=>protected_row _ r a (List.all_eq_true.mp peak_routes.2 r hr))

/-- The old input and the independent marking rational number may differ. -/
def separatelyMarked (g : Bool) (x : Assignment) (t : Rat) : Rat :=
  let v:=rowValue (families g) newRoutes x
  newShape.high.sos v+(t*t)*newShape.low.sos v

theorem independent_mark (g : Bool) (a : Rat) : separatelyMarked g (axis a) 0=0 := by
  dsimp only [separatelyMarked]
  rw [(high_on_axis g a).2,Rat.zero_mul,Rat.zero_mul,Rat.zero_add]

theorem separate_iff (g : Bool) (x : Assignment) (t : Rat) :
    separatelyMarked g x t=0 ↔
      (∀r∈newShape.high.refs,rowValue (families g) newRoutes x r=0) ∧
      (t=0 ∨ ∀r∈newShape.low.refs,rowValue (families g) newRoutes x r=0) := by
  let f:=rowValue (families g) newRoutes x
  change newShape.high.sos f+(t*t)*newShape.low.sos f=0 ↔ _
  rw [←Tree.sos_zero newShape.high f,←Tree.sos_zero newShape.low f]
  have h:=newShape.high.nonnegative f;have l:=newShape.low.nonnegative f
  have sq : 0≤t*t := by
    rcases Rat.nonneg_total t with p|p
    · exact Rat.mul_nonneg p p
    · have pos:=Rat.mul_nonneg p p;grobner
  have xl:=Rat.mul_nonneg sq l
  constructor
  · intro eq
    have hh : newShape.high.sos f=0 := by grind
    have zz : (t*t)*newShape.low.sos f=0 := by grind
    rcases Rat.mul_eq_zero.mp zz with a|b
    · exact ⟨hh,Or.inl ((Rat.mul_eq_zero.mp a).elim id id)⟩
    · exact ⟨hh,Or.inr b⟩
  · rintro ⟨hh,hz|hl⟩ <;> grobner

theorem actual_mark (g : Bool) (x : Assignment) :
    (splitProgram g).eval true x=separatelyMarked g x (x 1) := (outputs ..).2

theorem zero_witness (g : Bool) :
    (splitProgram g).eval true (vector (fun _ : Fin 134=>0))=0 ∧
    (parentProgram g).eval true (vector (fun _ : Fin 74=>0))=0 := by
  have z (n : Nat) : vector (fun _ : Fin n=>0)=axis 0 := by
    funext i;unfold vector axis;split <;> simp
  constructor
  · rw [z,actual_mark];exact independent_mark g 0
  · rw [z]
    unfold parentProgram
    rw [(outputs ..).2]
    rw [(high_on_axis g 0).1]
    change (0:Rat)+(0*0)*_=0
    grobner
end IndependentIndices
