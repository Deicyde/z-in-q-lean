import EllipticFrame
import IntegralCoordinates

namespace HeightSpecialization.Local
open Lean.Grind WitnessTransfer WitnessTransfer.Local WitnessTransfer.FiniteJet IndependentIndices.ChartJets
attribute [local instance] Semiring.natCast Ring.intCast

variable {O K : Type} [CommRing O] [Field K] [IsCharP K 0]

/-- An evaluated order-four remainder may occupy the highest coefficient of this
five-term jet. Multiplication by X discards it in the commutation test. -/
def rawTail {R : Type} [CommRing R] (b e : R) : J R 5 := (b,0,0,0,e,())

private theorem raw_chart {R : Type} [CommRing R] (v : J R 5) :
    val v Parameter.raw.q*X 5=X 5*val v Parameter.raw.a := CommSemiring.mul_comm .. 

omit [IsCharP K 0] in
private theorem linear (h : RingMap O K) (b : Int) (e : O) :
    X 5*h.jet 5 (rawTail (b:O) e)=scale 5 (b:K) (X 5) := by
  rw [X_mul]
  simp only [rawTail,RingMap.jet,cut,scale,X,con,h.zero,h.int,Semiring.mul_one,Semiring.mul_zero]

/-- The relation with duplication is verified on the jets of the specified curve. -/
theorem raw_interchanges (h : RingMap O K) (f : CurveData K 4) (b : Int) (e : O) :
    plug 5 f.dup (X 5*h.jet 5 (rawTail (b:O) e)) =
    plug 5 (h.jet 5 (rawTail (b:O) e)) (X 5*f.dup) := by
  have d:=physical_doubles Parameter.raw f (X 5) (raw_chart f.w)
  change plug 5 f.dup (X 5)=scale 5 2 (X 5) at d
  rw [plug_X] at d
  rw [linear,d,plug_scale,plug_scale,plug_X,plug_X,d,linear,scale_scale,scale_scale,CommSemiring.mul_comm (b:K) 2]

private theorem raw_evaluates {R : Type} [CommRing R] (t : R) : expands 5 t t (X 5) := by
  refine ⟨0,?_⟩
  change t=0+t*(1+t*(0+t*(0+t*(0+t*0))))+t^5*0
  grobner

/-- An actual integral fifth-order chord remainder constructs every component
of the old raw SourceValue, including its full coefficient-field commutation. -/
theorem raw_source (h : RingMap O K) (D : K) (b : Int) (z e v : O)
    (value : v=z*((b:O)+z^4*e)) :
    ∃ s : SourceValue O K h .raw b z z v, s.curve.D=D ∧ s.multiplierTail=(b:O)+z^4*e := by
  obtain ⟨f,hd⟩:=curve_exists 4 D
  refine ⟨{ curve := f
            m := rawTail (b:O) e
            chart := X 5
            tangent := h.int b
            interchanges := raw_interchanges h f b e
            physical := ?_
            multiplierTail := (b:O)+z^4*e
            evaluatesMultiplier := ?_
            atSource := raw_evaluates z
            atImage := ?_ },hd,rfl⟩
  · change val f.w Parameter.raw.q*h.jet 5 (X 5)=X 5*val f.w Parameter.raw.a
    rw [h.jet_X]
    exact raw_chart f.w
  · refine ⟨0,?_⟩
    change (b:O)+z^4*e=(b:O)+z*(0+z*(0+z*(0+z*(e+z*0))))+z^5*0
    grobner
  · rw [value]
    exact raw_evaluates _

end HeightSpecialization.Local
