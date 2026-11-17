import Observation84
namespace ProjectionFibres.Comparison
open StructuralReduction StructuralReduction.Transfer84 WitnessTransfer.Height WitnessTransfer.Local
open IndependentIndices IndependentIndices.Assembly BinaryQuartic ProgressionWitnesses.SingleContact Lean.Grind
attribute [local instance] Semiring.natCast Ring.intCast

/-- Each prime has its own completion, ring and group charts. The geometric
identifications are supplied at signs meeting all sixteen depths. -/
structure GeometryAt (x : Fin 84→Rat) (f : Frame) (p : Nat) (m : Int) (ns : Labels) where
  K : Type
  [fieldK : Field K]
  [charK : IsCharP K 0]
  w : ExtensionPlace p K
  rho : K
  root : rho^2=2
  prime : Prime p
  large : 5≤p
  away : p≠17
  oddOrder : OddOrder (order p (f.data x).R)
  regular : 0≤order p (f.data x).delta
  charts : ∀ r : K, (r=rho ∨ r= -rho) →
    (∀ s∈(f.data x).steps,w.deep (s.m:Int) (s.y.eval w r)) →
    ∃ o : LocalSetup p K w, Nonempty (FourRows o x f m ns r)

theorem GeometryAt.observation {x : Fin 84→Rat} {f : Frame} {p : Nat} {m : Int} {ns : Labels}
    (g : GeometryAt x f p m ns) (marked : Bool) (active : marked=true → cell x 1≠0) (zero : output marked x=0) :
    Nonempty (PrimeInputs p m ns (SquareGate.label (cell x 1))) := by
  letI:=g.fieldK
  letI:=g.charK
  obtain ⟨r,sign,depths,ratios⟩:=ratio_depths84 x marked active zero f g.prime g.large g.away
    g.w g.root g.oddOrder g.regular
  obtain ⟨o,⟨four⟩⟩:=g.charts r sign depths
  have rt : r^2=2 := by rcases sign with e|e <;> rw [e] <;> have := g.root <;> grobner
  exact fourObservations o x f four g.prime g.large rt ratios (curve_depths x f g.w r depths)

structure ComparisonGeometry (x : Fin 84→Rat) (f : Frame) (ns : Labels) where
  multiplier : Int
  primes : List Nat
  atPrime : ∀p∈primes, Nonempty (GeometryAt x f p multiplier ns)
  slopeCeiling : Nat
  fiveMark : slopeCeiling ≤ detectorConstant*(radical primes)^17+2

def ComparisonGeometry.observed {x : Fin 84→Rat} {f : Frame} {ns : Labels}
    (s : ComparisonGeometry x f ns) (marked : Bool) (active : marked=true → cell x 1≠0)
    (zero : output marked x=0) : Observed ns (SquareGate.label (cell x 1)) :=
  ⟨s.multiplier,s.primes,fun p member=>(s.atPrime p member).elim (fun d=>d.observation marked active zero),s.slopeCeiling,s.fiveMark⟩

/-- The three frames share their actual rational assignment and all four integral labels. -/
structure GeometricHeightData84 (x : Fin 84→Rat) where
  labels : Labels
  first : ComparisonGeometry x .first labels
  second : ComparisonGeometry x .second labels
  third : ComparisonGeometry x .third labels
  scalarMultiplier : Int
  primes : List Nat
  contacts : EvaluatedContacts x scalarMultiplier labels.n₂ primes
  scalarHeight : multiplicativeHeight (SquareGate.label (cell x 1)) ≤
    2^(2*scalarConstant*(radical primes)^17)
  oddFirst : labels.n₁%2=1
  lastNonzero : labels.n₄≠0
  anchorNonzero : labels.n₂-1≠0
  anchor : (anchorModulus:Int) ∣ labels.n₂-1
  abscissas : 2*(labelSize labels)^2 ≤ 15+3*largest first.slopeCeiling second.slopeCeiling third.slopeCeiling

theorem integer_of_comparison_charts84 (marked : Bool) (x : Fin 84→Rat) (zero : output marked x=0)
    (geometry : cell x 1≠0 → Nonempty (GeometricHeightData84 x)) : InputRestriction.IsInteger (cell x 1) := by
  apply integer_of_zero84 marked x zero
  intro ne
  obtain ⟨g⟩:=geometry ne
  exact ⟨⟨g.labels,g.first.observed marked (fun _=>ne) zero,g.second.observed marked (fun _=>ne) zero,
    g.third.observed marked (fun _=>ne) zero,g.scalarMultiplier,g.primes,g.contacts,g.scalarHeight,
    g.oddFirst,g.lastNonzero,g.anchorNonzero,g.anchor,g.abscissas⟩⟩

#print axioms LocalSetup.splitValue
#print axioms RowGeometry.recover
#print axioms RowGeometry.numeratorZeros
#print axioms LocalSetup.inputTest
#print axioms LocalSetup.lucasTest
#print axioms fourObservations
#print axioms GeometryAt.observation
#print axioms integer_of_comparison_charts84
end ProjectionFibres.Comparison
