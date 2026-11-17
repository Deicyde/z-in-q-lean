import TwoRows
import Scalar84

namespace ProjectionFibres.Actual
open CircuitTransport StructuralReduction StructuralReduction.Transfer84
open BinaryQuartic ProgressionWitnesses.SingleContact
abbrev wire (x : Fin 84→Rat) (i : Nat) := childWire archiveAt x i
def r (x : Fin 84→Rat) := Wires.contact (cell x 1)
def A (x : Fin 84→Rat) := r x*(cell x 25)^2+(cell x 26)^2
def q (x : Fin 84→Rat) := qnorm (cell x 21) (cell x 22)

theorem r_positive (x : Fin 84→Rat) : 0<r x := by
  let t:=Wires.gateY (cell x 1)
  have sq : 0≤t^2 := by
    rcases Rat.nonneg_total t with h|h
    · exact Rat.pow_nonneg h
    · have g:=Rat.mul_nonneg h h
      rwa [show -t*(-t)=t^2 by grobner] at g
  change 0<(2401+t^2)*(2401+t^2-1)*(32*(2401+t^2)+343)
  apply Rat.mul_pos
  · exact Rat.mul_pos (by grind) (by grind)
  · grind

private theorem scale {t : Rat} : (67830:Rat)^48*t=0 ↔ t=0 := by
  rw [Rat.mul_eq_zero];simp [show (67830:Rat)^48≠0 by decide]

theorem equation_num (x : Fin 84→Rat) : wire x 1072=0 ↔ cell x 29*(r x)^16=A x := by
  rw [wire,←paired21956 archiveAt x,parentWire,Wires.numerator_row,Wires.gate_y2,scale]
  change A x-cell x 29*(r x)^16=0 ↔ _
  constructor <;> intro h <;> grobner

theorem equation_rec (x : Fin 84→Rat) : wire x 1038=0 ↔
    cell x 27*cell x 29*(r x)^16=(cell x 29)^2+(r x)^3*(q x)^2 := by
  rw [wire,←paired21921 archiveAt x,parentWire,Wires.reciprocal_row,Wires.gate_y2,scale]
  change cell x 27*cell x 29*(r x)^16-(cell x 29)^2-(r x)^3*(q x)^2=0 ↔ _
  constructor <;> intro h <;> grobner

theorem equation_corr (x : Fin 84→Rat) : wire x 113=0 ↔
    (cell x 27)^2=Wires.kappa*cell x 28*(r x)^3 := by
  rw [wire,←paired163 archiveAt x,parentWire,Wires.correction]
  change -(cell x 27)^2+Wires.kappa*cell x 28*(r x)^3=0 ↔ _
  constructor <;> intro h <;> grobner

theorem equation_pole (x : Fin 84→Rat) : wire x 883=
    pole (cell x 18) (cell x 19) (cell x 20) (Wires.kappa*cell x 28) := by
  rw [wire,←paired21764 archiveAt x,parentWire,Wires.sextic21764]
  change Wires.residual (Wires.kappa*cell x 28) (cell x 18) (cell x 19) (cell x 20)=_
  unfold Wires.residual pole
  grobner

theorem physical_norm (x : Fin 84→Rat) (h : wire x 513=0) : q x≠0 := by
  rw [wire,curve_row] at h
  exact norm_of_curve h

/-- Each depth follows from an active zero and an odd contact. -/
theorem physical_depths (mark : Bool) (x : Fin 84→Rat) (active : mark=true → cell x 1≠0)
    (zero : output mark x=0) {p : Nat} (hp : BinaryQuartic.Prime p) (large : 5≤p)
    (away : p≠17) (odd : OddOrder (order p (r x))) :
    0<order p (Wires.kappa*cell x 28) ∧
    strictDepth p (16*order p (r x)) 1 (q x) ∧
    strictDepth p (65*order p (r x)) 4 (cell x 25) ∧
    strictDepth p (67*order p (r x)) 4 (cell x 26) := by
  have rows : ∀i∈Output.wireList,wire x i=0 := by
    cases mark with
    | false => exact (signed84 archiveAt x).1.mp zero
    | true => exact ((signed84 archiveAt x).2.mp zero).resolve_left (active rfl)
  have nz:=physical_norm x (rows _ (by decide))
  have hr : r x≠0 := by have := r_positive x;grind
  obtain ⟨num,recip,corr,pole0⟩:=transported_rows mark x active zero
  have vals:=Wires.scalar_wires parentFallback (pull x) hr nz num recip corr
  have polePoint:=Wires.frame_sextic .scalar parentFallback (pull x) pole0
  have h:=scalar_depths hp large away hr odd vals polePoint
  exact ⟨h.2.1,h.2.2.2⟩

#print axioms physical_norm
#print axioms physical_depths
end ProjectionFibres.Actual
