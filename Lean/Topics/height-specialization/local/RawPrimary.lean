import RawJets
import FifthOrder
import GroupPoints

namespace HeightSpecialization.Local
open Lean.Grind ProjectionFibres StructuralReduction WitnessTransfer WitnessTransfer.Local
attribute [local instance] Semiring.natCast Ring.intCast

variable {p : Nat} {K G O : Type} [Field K] [IsCharP K 0] [IntModule G] [CommRing O]
variable {D : K} (M : ProjectiveGroup D G) (w : ExtensionPlace p K)

structure RawComparison (h : RingMap O K) (m a : Int) (D x y : K) where
  side : Side O
  pair : JoinedPair h .raw side m a
  first : h.map side.x=x
  second : h.map side.y=y
  nx : side.nx=1
  ry : side.ry=1
  numCurve : pair.numerator.curve.D=D
  refCurve : pair.reference.curve.D=D
  common : side.x*pair.numerator.multiplierTail=side.y*pair.reference.multiplierTail

/-- A single equality of signed projective group multiples gives the complete
joined raw chart over the integral ring. The numerator and both indices may be zero. -/
theorem raw_joined (h : RingMap O K) (inj : Function.Injective h.map)
    (lift : ∀a,w.deep 0 a → ∃e : O,a=h.map e) (hD : w.deep 0 D)
    {P Q : G} (pf : M.formal w P) (qf : M.formal w Q) (ny : M.t Q≠0)
    (m a : Int) (same : m • P=a • Q) : Nonempty (RawComparison h m a D (M.t P) (M.t Q)) := by
  obtain ⟨x,hx⟩:=lift _ (deep_lower w (by decide) pf.2.1)
  obtain ⟨y,hy⟩:=lift _ (deep_lower w (by decide) qf.2.1)
  obtain ⟨ex,eqx⟩:=raw_signed M w h lift hD pf m
  obtain ⟨ey,eqy⟩:=raw_signed M w h lift hD qf a
  let v:=x*((m:O)+x^4*ex)
  have eval (z e : O) (i : Int) : h.map (z*((i:O)+z^4*e))=
      h.map z*((i:K)+(h.map z)^4*h.map e) := by rw [h.mul,h.add,h.int,h.mul,h.pow]
  have agree : v=y*((a:O)+y^4*ey) := by
    apply inj
    calc h.map v=M.t (m • P) := by rw [eqx,hx];exact eval x ex m
         _=M.t (a • Q) := congrArg M.t same
         _=h.map (y*((a:O)+y^4*ey)) := by rw [eqy,hy,eval]
  have nonzero : y≠0 := by intro yz;apply ny;rw [hy,yz,h.zero]
  let s : Side O:={x:=x,y:=y,nx:=1,ry:=1,nx_unit:=⟨1,Semiring.one_mul _⟩,
                    ry_unit:=⟨1,Semiring.one_mul _⟩,regular:=nonzero_reference h inj y nonzero}
  have nr : ∃ n : SourceValue O K h .raw m s.x (s.x*s.nx) v,
      n.curve.D=D ∧ n.multiplierTail=(m:O)+x^4*ex := by
    change ∃ n : SourceValue O K h .raw m x (x*1) v, _
    rw [Semiring.mul_one];exact raw_source h D m x ex v rfl
  obtain ⟨n,nd,nt⟩:=nr
  obtain ⟨r,rd,rt⟩:=raw_source h D a y ey v agree
  let j : JoinedPair h .raw s m a := {
    commonValue:=v,refValue:=y,numerator:=n,reference:=r
    refChart:=.same (Semiring.mul_one y).symm}
  refine ⟨⟨s,j,hx.symm,hy.symm,rfl,rfl,nd,rd,?_⟩⟩
  change x*n.multiplierTail=y*r.multiplierTail
  rw [nt,rt];exact agree

/-- The two affine points are ordinary multiples of a single source, with a
two-torsion translate on the reference. The remaining equalities identify actual wires. -/
structure PrimarySource (M : ProjectiveGroup D G) (m u : Int) (L fn fr : K) where
  base : G
  torsion : G
  killed : (2:Int) • torsion=0
  numerator : AffineAt M (u • ((2:Int) • base))
  reference : AffineAt M (m • base+torsion)
  numeratorWire : numerator.f=fn
  referenceWire : reference.f=fr
  ratioWire : M.t (u • ((2:Int) • base))=M.t (m • base+torsion)*L

end HeightSpecialization.Local
