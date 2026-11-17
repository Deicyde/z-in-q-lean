import SourceEndpoint
import PhysicalHeightBounds
import RootLogBound

namespace HeightSpecialization
open Lean.Grind Std StructuralReduction StructuralReduction.Transfer84 IndependentIndices IndependentIndices.Assembly
open ProjectionFibres ProjectionFibres.Actual ProjectionFibres.HeightSupport ProjectionFibres.Comparison
open WitnessTransfer.Height
attribute [local instance] Semiring.natCast Ring.intCast
set_option maxRecDepth 8192

abbrev J (x : Fin 84→Rat) := jointHeight (atWire x 1249) (atWire x 1252)

private theorem joint_positive (a b : Rat) : 0<jointHeight a b :=
  Nat.lt_of_lt_of_le (Nat.lcm_pos a.den_pos b.den_pos) (Nat.le_max_left ..)

variable {K : Type} [Field K] [LE K] [LT K] [LawfulOrderLT K] [IsLinearOrder K] [OrderedRing K]
variable {l : Analytic.LogLaw K}

/-- The labelled abscissas and the fibre at the one selected argument
supply the two geometric height inputs on the comparison side. -/
structure EllipticData (l : Analytic.LogLaw K) (x : Fin 84→Rat) where
  labels : Labels
  places : ∀ p∈fullPrimes (slope x (tallest x)), Nonempty (SourcePlace x (tallest x) p labels)
  abscissaHeight : K
  lower : (((labelSize labels)^2:Nat):K)≤6+abscissaHeight
  upper : abscissaHeight≤l.log ((J x:Nat):K)+(3/2:K)*l.log 2
  fibre : FibreBound l Analytic.detectorSet (fullPrimes (slope x (tallest x))) (2+1/slope x (tallest x))
  oddFirst : labels.n₁%2=1
  lastNonzero : labels.n₄≠0
  offsetNonzero : labels.n₂-1≠0
  anchor : (anchorModulus:Int)∣labels.n₂-1

def EllipticData.source {x : Fin 84→Rat} (g : EllipticData l x)
    (laws : Analytic.BinaryLogLaw l) (mult : Analytic.ProductLogLaw l) (zero : output false x=0) :
    SourceArithmetic x :=
  ⟨g.labels,g.places,Analytic.root_log_bound_half laws mult _ _ (joint_positive _ _) _ g.lower g.upper,
   analytic_slope (fromZero_domain x false (by simp) zero) laws g.fibre,
   g.oddFirst,g.lastNonzero,g.offsetNonzero,g.anchor⟩

def ScalarGeometry (l : Analytic.LogLaw K) (x : Fin 84→Rat) (n : Int) :=
  SmallInput (cell x 1) ∨ (ScalarCharts x n ∧
    Nonempty (FibreBound l Analytic.scalarSet (scalarFullPrimes (SquareGate.label (cell x 1)))
      (SquareGate.label (cell x 1))))

theorem circuit_defines_of_geometry (marked : Bool) (laws : Analytic.BinaryLogLaw l)
    (mult : Analytic.ProductLogLaw l) (integerFibres : ∀ n : Nat, circuitImage false (n:Rat))
    (selection : ∀ T : Rat, 0≤2*T+1 → T≠0 → circuitImage false T →
      ∃ y : Fin 80→Rat, y 0=T ∧ Binding.V y 9813=0 ∧
        ∃ g : EllipticData l (decoded y), ScalarGeometry l (decoded y) g.labels.n₂) :
    ∀ T, circuitImage marked T ↔ InputRestriction.IsInteger T := by
  apply circuit_defines_of_sources marked integerFibres
  intro T side nz represented
  obtain ⟨y,hy,eq,g,hg⟩:=selection T side nz represented
  have zero:=ordinary_decoded y ((Binding.ordinary_pointwise y).symm.trans eq)
  refine ⟨y,hy,eq,g.source laws mult zero,?_⟩
  rcases hg with small|⟨charts,⟨s⟩⟩
  · exact Or.inl small
  · exact Or.inr ⟨charts,analytic_scalar _ laws s⟩

#print axioms EllipticData.source
#print axioms circuit_defines_of_geometry
end HeightSpecialization
