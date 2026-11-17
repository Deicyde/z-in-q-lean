import RationalChart
namespace PhysicalProjection
open ZeroInput.Sparse ProjectionDescent Triangular Triangular.Data
set_option maxRecDepth 12000
set_option maxHeartbeats 500000

def pivotOK (g : Bool) (z : Assignment) := ∀ p∈ps g, p.ok z

private theorem row673 (g : Bool) (z : Assignment) (ok : pivotOK g z) :
    value z PPair.one.f = value (PPair.one.blank z) PPair.one.f + PPair.one.A z*z PPair.one.slot + 2*PPair.one.B z*z (PPair.one.slot+1) := by
  have h132 := ok p132 (List.mem_of_getElem? (show (ps g)[16]?=some p132 by cases g <;> rfl))
  have h133 := ok p133 (List.mem_of_getElem? (show (ps g)[17]?=some p133 by cases g <;> rfl))
  simp [Pivot.ok,Pivot.num,p132,p133,scale,value,termValue,monomialValue] at h132 h133
  simp [PPair.f,PPair.slot,PPair.xslot,PPair.blank,PPair.A,PPair.B,PPair.w0,PPair.w1,
    CircuitTransport.Quadratic.g0,CircuitTransport.Quadratic.g1,p673,put,value,termValue,monomialValue]
  grobner

private theorem row674 (g : Bool) (z : Assignment) (ok : pivotOK g z) :
    value z PPair.one.g = value (PPair.one.blank z) PPair.one.g + PPair.one.B z*z PPair.one.slot + PPair.one.A z*z (PPair.one.slot+1) := by
  have h132 := ok p132 (List.mem_of_getElem? (show (ps g)[16]?=some p132 by cases g <;> rfl))
  have h133 := ok p133 (List.mem_of_getElem? (show (ps g)[17]?=some p133 by cases g <;> rfl))
  simp [Pivot.ok,Pivot.num,p132,p133,scale,value,termValue,monomialValue] at h132 h133
  simp [PPair.g,PPair.slot,PPair.xslot,PPair.blank,PPair.A,PPair.B,PPair.w0,PPair.w1,
    CircuitTransport.Quadratic.g0,CircuitTransport.Quadratic.g1,p674,put,value,termValue,monomialValue]
  grobner

private theorem row677 (g : Bool) (z : Assignment) (ok : pivotOK g z) :
    value z PPair.two.f = value (PPair.two.blank z) PPair.two.f + PPair.two.A z*z PPair.two.slot + 2*PPair.two.B z*z (PPair.two.slot+1) := by
  have h150 := ok p150 (List.mem_of_getElem? (show (ps g)[22]?=some p150 by cases g <;> rfl))
  have h151 := ok p151 (List.mem_of_getElem? (show (ps g)[23]?=some p151 by cases g <;> rfl))
  simp [Pivot.ok,Pivot.num,p150,p151,scale,value,termValue,monomialValue] at h150 h151
  simp [PPair.f,PPair.slot,PPair.xslot,PPair.blank,PPair.A,PPair.B,PPair.w0,PPair.w1,
    CircuitTransport.Quadratic.g0,CircuitTransport.Quadratic.g1,p677,put,value,termValue,monomialValue]
  grobner

private theorem row678 (g : Bool) (z : Assignment) (ok : pivotOK g z) :
    value z PPair.two.g = value (PPair.two.blank z) PPair.two.g + PPair.two.B z*z PPair.two.slot + PPair.two.A z*z (PPair.two.slot+1) := by
  have h150 := ok p150 (List.mem_of_getElem? (show (ps g)[22]?=some p150 by cases g <;> rfl))
  have h151 := ok p151 (List.mem_of_getElem? (show (ps g)[23]?=some p151 by cases g <;> rfl))
  simp [Pivot.ok,Pivot.num,p150,p151,scale,value,termValue,monomialValue] at h150 h151
  simp [PPair.g,PPair.slot,PPair.xslot,PPair.blank,PPair.A,PPair.B,PPair.w0,PPair.w1,
    CircuitTransport.Quadratic.g0,CircuitTransport.Quadratic.g1,p678,put,value,termValue,monomialValue]
  grobner

private theorem row681 (g : Bool) (z : Assignment) (_ok : pivotOK g z) :
    value z PPair.three.f = value (PPair.three.blank z) PPair.three.f + PPair.three.A z*z PPair.three.slot + 2*PPair.three.B z*z (PPair.three.slot+1) := by
  simp [PPair.f,PPair.slot,PPair.xslot,PPair.blank,PPair.A,PPair.B,PPair.w0,PPair.w1,
    CircuitTransport.Quadratic.g0,CircuitTransport.Quadratic.g1,p681,put,value,termValue,monomialValue]
  grobner

private theorem row682 (g : Bool) (z : Assignment) (_ok : pivotOK g z) :
    value z PPair.three.g = value (PPair.three.blank z) PPair.three.g + PPair.three.B z*z PPair.three.slot + PPair.three.A z*z (PPair.three.slot+1) := by
  simp [PPair.g,PPair.slot,PPair.xslot,PPair.blank,PPair.A,PPair.B,PPair.w0,PPair.w1,
    CircuitTransport.Quadratic.g0,CircuitTransport.Quadratic.g1,p682,put,value,termValue,monomialValue]
  grobner

private theorem row685 (g : Bool) (z : Assignment) (_ok : pivotOK g z) :
    value z PPair.four.f = value (PPair.four.blank z) PPair.four.f + PPair.four.A z*z PPair.four.slot + 2*PPair.four.B z*z (PPair.four.slot+1) := by
  simp [PPair.f,PPair.slot,PPair.xslot,PPair.blank,PPair.A,PPair.B,PPair.w0,PPair.w1,
    CircuitTransport.Quadratic.g0,CircuitTransport.Quadratic.g1,p685,put,value,termValue,monomialValue]
  grobner

private theorem row686 (g : Bool) (z : Assignment) (_ok : pivotOK g z) :
    value z PPair.four.g = value (PPair.four.blank z) PPair.four.g + PPair.four.B z*z PPair.four.slot + PPair.four.A z*z (PPair.four.slot+1) := by
  simp [PPair.g,PPair.slot,PPair.xslot,PPair.blank,PPair.A,PPair.B,PPair.w0,PPair.w1,
    CircuitTransport.Quadratic.g0,CircuitTransport.Quadratic.g1,p686,put,value,termValue,monomialValue]
  grobner

theorem pade_f (g : Bool) (k : PPair) (z : Assignment) (ok : pivotOK g z) :
    value z k.f = value (k.blank z) k.f + k.A z*z k.slot + 2*k.B z*z (k.slot+1) := by
  cases k
  case one => exact row673 g z ok
  case two => exact row677 g z ok
  case three => exact row681 g z ok
  case four => exact row685 g z ok

theorem pade_g (g : Bool) (k : PPair) (z : Assignment) (ok : pivotOK g z) :
    value z k.g = value (k.blank z) k.g + k.B z*z k.slot + k.A z*z (k.slot+1) := by
  cases k
  case one => exact row674 g z ok
  case two => exact row678 g z ok
  case three => exact row682 g z ok
  case four => exact row686 g z ok

end PhysicalProjection
