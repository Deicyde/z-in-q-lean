import Child84Slice05
import Child84Source

namespace StructuralReduction.Transfer84
open CircuitTransport BinaryQuartic ProgressionWitnesses.SingleContact Lean.Grind
attribute [local instance] Semiring.natCast Ring.intCast

/-- Evaluate the published ordinary or marked final output on exactly 84 rationals. -/
def output (marked : Bool) (x : Fin 84→Rat) : Rat :=
  valueAt literalTape (cell x) (if marked then 9981 else 9980)

theorem scalar_rows (marked : Bool) (x : Fin 84→Rat) (active : marked=true → cell x 1≠0)
    (zero : output marked x=0) :
    valueAt literalTape (cell x) 1072=0 ∧ valueAt literalTape (cell x) 1038=0 ∧
    valueAt literalTape (cell x) 113=0 ∧ valueAt literalTape (cell x) 883=0 := by
  have bits := signed84 archiveAt x
  have allRows : ∀ j∈Output.wireList,childWire archiveAt x j=0 := by
    cases marked with
    | false => exact bits.1.mp zero
    | true => exact (bits.2.mp zero).resolve_left (active rfl)
  exact ⟨allRows _ (by decide),allRows _ (by decide),allRows _ (by decide),allRows _ (by decide)⟩

theorem transported_rows (marked : Bool) (x : Fin 84→Rat) (active : marked=true → cell x 1≠0)
    (zero : output marked x=0) :
    parentWire x 21956=0 ∧ parentWire x 21921=0 ∧ parentWire x 163=0 ∧ parentWire x 21764=0 := by
  obtain ⟨num,recip,corr,pole⟩:=scalar_rows marked x active zero
  exact ⟨(paired21956 archiveAt x).trans num,(paired21921 archiveAt x).trans recip,
         (paired163 archiveAt x).trans corr,(paired21764 archiveAt x).trans pole⟩

variable {p : Nat} {K : Type} [Field K] {w : ExtensionPlace p K}
variable {G G' : Type} [IntModule G] [IntModule G']
variable (chart : MultiplicationChart p w G) (other : MultiplicationChart p w G')

/-- The actual output zero supplies all four signed wire equations to the scalar argument. -/
theorem physical_scalar_divisor84 (marked : Bool) (x : Fin 84→Rat)
    (active : marked=true → cell x 1≠0) (zero : output marked x=0) {m n : Int} {rho : K}
    (hp : Prime p) (large : 5≤p) (away : p≠17)
    (hr : Wires.contact (cell x 1)≠0) (positive : 0<order p (Wires.contact (cell x 1)))
    (odd : OddOrder (order p (Wires.contact (cell x 1))))
    (left : ScalarBranch chart m n (cell x 25) (cell x 26) rho)
    (right : ScalarBranch other m n (cell x 25) (cell x 26) (-rho))
    (leftF : left.shared.f=w.incl.map (cell x 21)+w.incl.map (cell x 22)*rho)
    (rightF : right.shared.f=w.incl.map (cell x 21)+w.incl.map (cell x 22)*(-rho)) : ((p^17:Nat):Int)∣n-1 := by
  obtain ⟨num,recip,corr,pole⟩:=transported_rows marked x active zero
  exact Wires.physical_scalar_divisor chart other parentFallback (pull x) hp large away hr positive odd
    num recip corr pole left right leftF rightF

#print axioms scalar_rows
#print axioms transported_rows
#print axioms physical_scalar_divisor84
end StructuralReduction.Transfer84
