import ComparisonRow
import CubicGeometry
import Observation84

namespace HeightSpecialization.Local
open Lean.Grind ProjectionFibres ProjectionFibres.Comparison StructuralReduction StructuralReduction.Transfer84
open WitnessTransfer WitnessTransfer.Local IndependentIndices BinaryQuartic ProgressionWitnesses.SingleContact
attribute [local instance] Semiring.natCast Ring.intCast

variable {p : Nat} {K G : Type} [Field K] [IsCharP K 0] [IntModule G]
variable {w : ExtensionPlace p K} (o : LocalSetup p K w)

structure RowSource {rho : K} (M : ProjectiveGroup ((3-rho)^2) G)
    (short : Bool) (m n : Int) (L A fn fr an ar : K) where
  u : Int
  primary : PrimarySource M m u L fn fr
  alternate : Side o.O
  pair : JoinedPair o.incl (altChart short) alternate (m-2) (2*(u-n))
  common : alternate.x*pair.numerator.multiplierTail=alternate.y*pair.reference.multiplierTail
  chart : SourceParameters o alternate ((3-(-rho))^2) an ar
  ratio : o.incl.map (alternate.x*alternate.nx)=o.incl.map (alternate.y*alternate.ry)*A

abbrev NamedSource {r : K} (M : ProjectiveGroup ((3-r)^2) G) (f : Comparison.Frame) (x : Fin 84→Rat)
    (m n : Int) (i : Fin 4) (short : Bool) :=
  RowSource o M short m n (((f.primary x) i).eval w r) (((f.alt x) i).eval w r)
    (((f.refs x).nums i).eval w r) ((f.refs x).ref.eval w r)
    (((f.refs x).secondNums i).eval w r) ((f.refs x).secondRef.eval w r)

theorem named_row {r : K} (M : ProjectiveGroup ((3-r)^2) G) (x : Fin 84→Rat) (f : Comparison.Frame)
    {m n : Int} {i : Fin 4} {short : Bool} (s : NamedSource o M f x m n i short)
    (hp : Prime p) (large : 5≤p) (root : r^2=2) (recips : ReciprocalDepths w r (f.refs x)) :
    Nonempty (NamedRow o f x m n r i short) :=
  source_row o M hp large root s.primary (recips.nums i) (deep_lower w (by decide) recips.ref)
    s.alternate s.pair s.common s.chart s.ratio

/-- Four physical comparison rows on one primary cubic, with all eight
raw multiplier evaluations and all four of their common-point identities derived. -/
structure FourSourceRows (x : Fin 84→Rat) (f : Comparison.Frame) (m : Int) (ns : Labels) (r : K) where
  carrier : Type
  [groupCarrier : IntModule carrier]
  cubic : CubicGeometry ((3-r)^2) carrier
  a : NamedSource o cubic.model f x m ns.n₁ 0 true
  b : NamedSource o cubic.model f x m ns.n₂ 1 false
  c : NamedSource o cubic.model f x m ns.n₃ 2 false
  d : NamedSource o cubic.model f x m ns.n₄ 3 false

theorem FourSourceRows.toFour (x : Fin 84→Rat) (f : Comparison.Frame) {m : Int} {ns : Labels} {r : K}
    (s : FourSourceRows o x f m ns r) (hp : Prime p) (large : 5≤p) (root : r^2=2)
    (depths : ∀ step∈(f.data x).steps,w.deep (step.m:Int) (step.y.eval w r)) :
    Nonempty (FourRows o x f m ns r) := by
  letI:=s.groupCarrier
  have values:=curve_depths x f w r depths
  obtain ⟨a⟩:=named_row o s.cubic.model x f s.a hp large root values
  obtain ⟨b⟩:=named_row o s.cubic.model x f s.b hp large root values
  obtain ⟨c⟩:=named_row o s.cubic.model x f s.c hp large root values
  obtain ⟨d⟩:=named_row o s.cubic.model x f s.d hp large root values
  exact ⟨⟨a,b,c,d⟩⟩

#print axioms HeightSpecialization.Local.raw_signed
#print axioms HeightSpecialization.Local.raw_interchanges
#print axioms HeightSpecialization.Local.raw_source
#print axioms HeightSpecialization.Local.raw_joined
#print axioms HeightSpecialization.Local.source_row
#print axioms HeightSpecialization.Local.named_row
#print axioms HeightSpecialization.Local.FourSourceRows.toFour
end HeightSpecialization.Local
