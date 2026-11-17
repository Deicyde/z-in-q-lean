import RawPrimary
import LocalCharts

namespace HeightSpecialization.Local
open Lean.Grind ProjectionFibres ProjectionFibres.Comparison StructuralReduction WitnessTransfer WitnessTransfer.Local
open BinaryQuartic ProgressionWitnesses.SingleContact
attribute [local instance] Semiring.natCast Ring.intCast

variable {p : Nat} {K G : Type} [Field K] [IsCharP K 0] [IntModule G]
variable {w : ExtensionPlace p K} (o : LocalSetup p K w)

omit [IsCharP K 0] in
private theorem aligned {side : Side o.O} {D x y : K}
    (hx : o.incl.map side.x=x) (hy : o.incl.map side.y=y)
    (a : AffineValue D x) (b : AffineValue D y) : Nonempty (SourceParameters o side D a.f b.f) := by
  subst x;subst y
  exact ⟨⟨a,b,rfl,rfl⟩⟩

/-- Build the original RowGeometry directly. Its entire primary joined pair and
equality of the evaluated images follow from the cubic group, including negative indices. -/
theorem source_row {short : Bool} {m n u : Int} {rho L A fn fr an ar : K}
    (M : ProjectiveGroup ((3-rho)^2) G) (hp : Prime p) (large : 5≤p) (root : rho^2=2)
    (primary : PrimarySource M m u L fn fr) (numDepth : w.deep 1 fn) (refDepth : w.deep 1 fr)
    (alternate : Side o.O) (pair : JoinedPair o.incl (altChart short) alternate (m-2) (2*(u-n)))
    (same : alternate.x*pair.numerator.multiplierTail=alternate.y*pair.reference.multiplierTail)
    (chart : SourceParameters o alternate ((3-(-rho))^2) an ar)
    (ratio : o.incl.map (alternate.x*alternate.nx)=o.incl.map (alternate.y*alternate.ry)*A) :
    Nonempty (RowGeometry o short m n rho L A fn fr an ar) := by
  have lift (a : K) (d : w.deep 0 a) : ∃e : o.O,a=o.incl.map e := by
    obtain ⟨e,eq⟩:=o.lifts 0 a d
    exact ⟨e,by simpa only [Semiring.pow_zero,Semiring.one_mul] using eq⟩
  have hD:=(curve_coeffs w hp large root).2.2
  have pn : 0<w.val primary.numerator.f := (primary.numeratorWire ▸ numDepth) primary.numerator.live.1
  have qn : 0<w.val primary.reference.f := (primary.referenceWire ▸ refDepth) primary.reference.live.1
  obtain ⟨raw⟩:=raw_joined M w o.incl o.injective lift hD
    (primary.numerator.formal_of_reciprocal hp hD pn) (primary.reference.formal_of_reciprocal hp hD qn)
    primary.reference.live.2.2 m (2*u) (source_points m u n primary.base primary.torsion primary.killed).1
  obtain ⟨coords⟩:=aligned o raw.first raw.second primary.numerator.toAffineValue primary.reference.toAffineValue
  rw [primary.numeratorWire,primary.referenceWire] at coords
  refine ⟨⟨raw.side,alternate,u,raw.pair,pair,raw.common,same,coords,chart,?_,ratio⟩⟩
  rw [raw.nx,raw.ry,Semiring.mul_one,Semiring.mul_one,raw.first,raw.second,primary.ratioWire]

end HeightSpecialization.Local
