import ProjectiveScalar

namespace HeightSpecialization.Local
open Lean.Grind ProjectionFibres StructuralReduction WitnessTransfer BinaryQuartic
attribute [local instance] Semiring.natCast Ring.intCast

variable {p : Nat} {K G O : Type} [Field K] [IntModule G] [CommRing O]
variable {D : K} (M : ProjectiveGroup D G) (w : ExtensionPlace p K)

private theorem fifthOrder {x : K} (nz : x≠0) : x^5≠0 ∧ w.val (x^5)=5*w.val x := by
  have p2:=w.product nz nz
  have p4:=w.product p2.1 p2.1
  have p5:=w.product nz p4.1
  have id : x*(x*x*(x*x))=x^5 := by grobner
  rw [id] at p5
  exact ⟨p5.1,by rw [p5.2,p4.2,p2.2];omega⟩

/-- In any ring containing the integral elements, the signed cubic group law
gives an actual fifth-power remainder. The parameter and the multiple may vanish. -/
theorem raw_signed (incl : RingMap O K) (lift : ∀a,w.deep 0 a → ∃e : O,a=incl.map e)
    (hD : w.deep 0 D) {P : G} (dom : M.formal w P) (b : Int) :
    ∃e : O,M.t (b • P)=M.t P*((b:K)+(M.t P)^4*incl.map e) := by
  by_cases tz : M.t P=0
  · have eq:=M.zero_parameter dom.1 tz
    subst P
    refine ⟨0,?_⟩
    rw [IntModule.zsmul_zero,M.origin.2.1,Semiring.zero_mul]
  let t:=M.t P
  let r:=M.t (b • P)-(b:K)*t
  have pos : 0<w.val t:=dom.2.1 tz
  have lay:=layer_of_reduction w (d:=w.val t) pos hD (M.equation P dom.1)
    (fun _=>Int.le_refl _) dom.2.2
  have estimate : w.deep (5*w.val t) r := (M.signed w hD pos dom.1 lay b).2.2
  have pow:=fifthOrder w tz
  let E:=r/t^5
  have clear : E*t^5=r := Field.div_mul_cancel pow.1
  have integral : w.deep 0 E := by
    intro ne
    have val:=w.product ne pow.1
    rw [clear] at val
    have bound:=estimate val.1
    have ve : w.val r=w.val E+w.val (t^5) := val.2
    have power : w.val (t^5)=5*w.val t := pow.2
    rw [power] at ve
    omega
  obtain ⟨e,ev⟩:=lift E integral
  refine ⟨e,?_⟩
  calc M.t (b • P)=(b:K)*t+r := by dsimp [r];grobner
       _=t*((b:K)+t^4*incl.map e) := by rw [←clear,ev];grobner

end HeightSpecialization.Local
