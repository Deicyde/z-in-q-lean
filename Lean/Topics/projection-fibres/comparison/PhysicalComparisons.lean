import Scalar84
import GeneralOrdinate
import BoundedTest

namespace ProjectionFibres.Comparison
open CircuitTransport StructuralReduction StructuralReduction.Transfer84 PhysicalProjection.Comparison
open PhysicalProjection.RootOrdinate ProgressionWitnesses.GeneralOrdinate

abbrev atWire (x : Fin 84→Rat) (i : Nat) := valueAt literalTape (cell x) i
def domain (x : Fin 84→Rat) := atWire x 9915≠0

theorem signed_zero (x : Fin 84→Rat) (marked : Bool) (active : marked=true → cell x 1≠0)
    (zero : output marked x=0) (i : Nat) (mem : i∈StructuralReduction.Output.wireList) : atWire x i=0 := by
  have bits:=signed84 archiveAt x
  cases marked with
  | false => exact bits.1.mp zero i mem
  | true => exact ((bits.2.mp zero).resolve_left (active rfl)) i mem

abbrev wireStep (x : Fin 84→Rat) {i : Nat} {o : Op} (bound : i<9918)
    (op : patch archiveAt i=o) (safe : o.safe i) : atWire x i=o.value (cell x) (atWire x) :=
  instruction (entry archiveAt bound op) safe _

theorem mul_left_nonzero {a b c : Rat} (hc : c≠0) (eq : c=a*b) : a≠0 :=
  fun h=>hc (by rw [eq,h,Rat.zero_mul])
theorem mul_right_nonzero {a b c : Rat} (hc : c≠0) (eq : c=a*b) : b≠0 :=
  fun h=>hc (by rw [eq,h,Rat.mul_zero])
theorem mul_nonzero {a b c : Rat} (ha : a≠0) (hb : b≠0) (eq : c=a*b) : c≠0 :=
  fun h=>(Rat.mul_eq_zero.mp (eq.symm.trans h)).elim ha hb

theorem bindPair (z : Rat×Rat) (a b : Rat) (ea : a=z.1) (eb : b=z.2) : z=(a,b) :=
  Prod.ext ea.symm eb.symm

def cubic (a b : Rat) : Q2 :=
  sub (times (sq (a,b)) (a,b)) (times (11,-6) (a,b))

def homogeneousPole (N D t s w : Rat) :=
  D^2*(D*w^2*(t^2*D-17*N)*(t^2*D+51*N)-
       (289*D-17*N)*(17*N-s^2*D)*(17*N+3*s^2*D))

theorem rational_pole {N D t s w : Rat} (hd : D≠0) (zero : homogeneousPole N D t s w=0) :
    ThreeCoordinates.Sextic (17*(N/D)) (289-17*(N/D)) := by
  have rep : (N/D)*D=N := Rat.div_mul_cancel hd
  have eq : D^5*Wires.residual (N/D) t s w=0 := by
    rw [←zero,←rep]
    rw [show N/D*D/D=N/D from Rat.mul_div_cancel hd]
    unfold homogeneousPole Wires.residual
    grobner
  have c := (Rat.mul_eq_zero.mp eq).resolve_left (by grind)
  exact ⟨t,s,w,by unfold Wires.residual at c;grobner⟩

/-- Equality of every patched instruction in the prefix gives equality of the entire programs. -/
theorem representation_ext (a b : Nat→Op) (same : ∀ i<9918, patch a i=patch b i) :
    program84 a=program84 b := by
  have values : (fun i : Fin 9918=>patch a i.val)=(fun i : Fin 9918=>patch b i.val) :=
    funext (fun i=>same i.val i.isLt)
  exact congrArg (fun vals : Fin 9918→Op=>List.ofFn vals++StructuralReduction.Output.suffix) values

end ProjectionFibres.Comparison
