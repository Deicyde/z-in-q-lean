import CubicGeometry
import Scalar84

namespace ProjectionFibres
open Lean.Grind StructuralReduction WitnessTransfer BinaryQuartic ProgressionWitnesses.SingleContact
open StructuralReduction.Transfer84
attribute [local instance] Semiring.natCast Ring.intCast

variable {K G G' : Type} [Field K] [IntModule G] [IntModule G'] {p : Nat} {w : ExtensionPlace p K}

/-- The ordinary or active marked physical output at 84 slots directly yields
the index divisor from the source H,R and the standard projective curve law.
All conditions on a doubled point, a local chart, or a multiplication remainder
have been eliminated from this statement. -/
theorem source_scalar_divisor84 (marked : Bool) (x : Fin 84→Rat)
    (active : marked=true → cell x 1≠0) (zero : output marked x=0) {m n : Int} {rho : K}
    (C : CubicGeometry ((3-rho)^2) G) (N : CubicGeometry ((3-(-rho))^2) G')
    (hp : Prime p) (large : 5≤p) (away : p≠17)
    (hr : Wires.contact (cell x 1)≠0) (positive : 0<order p (Wires.contact (cell x 1)))
    (odd : OddOrder (order p (Wires.contact (cell x 1))))
    (left : ScalarSource w C.model m n (cell x 25) (cell x 26))
    (right : ScalarSource w N.model m n (cell x 25) (cell x 26))
    (leftF : left.shared.f=w.incl.map (cell x 21)+w.incl.map (cell x 22)*rho)
    (rightF : right.shared.f=w.incl.map (cell x 21)+w.incl.map (cell x 22)*(-rho)) :
    ((p^17:Nat):Int)∣n-1 := by
  have two : w.incl.map 2=(2:K) := by
    calc _=w.incl.map ((2:Int):Rat) := congrArg w.incl.map (by decide)
         _=((2:Int):K) := w.incl.int 2
         _=2 := by grobner
  have norm : w.incl.map (Wires.normInput (pull x))=left.shared.f*right.shared.f := by
    rw [leftF,rightF,Wires.normInput,w.incl.sub,w.incl.pow,w.incl.mul,two,w.incl.pow]
    change (w.incl.map (cell x 21))^2-2*(w.incl.map (cell x 22))^2=_
    have r:=left.root
    have eq (a b : K) : a^2-2*b^2=(a+b*rho)*(a+b*(-rho)) := by
      calc _=a^2-b^2*rho^2 := by rw [r];grobner
           _=_ := by grobner
    exact eq _ _
  have nz : Wires.normInput (pull x)≠0 := fun z=>(w.product left.shared.live.1 right.shared.live.1).1
    (by rw [←norm,z,w.incl.zero])
  obtain ⟨num,recip,corr,pole⟩:=transported_rows marked x active zero
  exact source_scalar_divisor C.model N.model C.zeroAnchor N.zeroAnchor hp large away positive odd hr
    (Wires.scalar_wires parentFallback (pull x) hr nz num recip corr)
    (Wires.frame_sextic .scalar parentFallback (pull x) pole) left right norm

end ProjectionFibres
