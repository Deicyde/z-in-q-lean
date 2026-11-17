import Polynomial80
import ContactFrames

namespace ProjectionFibres.Actual
open StructuralReduction StructuralReduction.Transfer84 WitnessTransfer.Height
open IndependentIndices IndependentIndices.Assembly ProjectionFibres.Comparison ProjectionFibres.HeightSupport

/-- All eligible primitive contacts of this comparison slope are counted. -/
structure FullFrame (x : Fin 84→Rat) (f : Comparison.Frame) (ns : Labels) where
  multiplier : Int
  charts : ∀ p∈fullPrimes (HeightSupport.slope x f), Nonempty (AtContact x f p multiplier ns)

noncomputable def comparisonBound (x : Fin 84→Rat) (f : Comparison.Frame) :=
  detectorConstant*(radical (fullPrimes (HeightSupport.slope x f)))^17+2

/-- The three intermediate ceilings can always be replaced by their explicit upper bounds. -/
theorem ceilings_iff (N a b c : Nat) :
    (∃ i j k : Nat, i≤a ∧ j≤b ∧ k≤c ∧ 2*N^2≤15+3*largest i j k) ↔
      2*N^2≤15+3*largest a b c := by
  constructor
  · rintro ⟨i,j,k,hi,hj,hk,h⟩
    have bounds := largest_bounds a b c
    have le : largest i j k ≤ largest a b c := three_max (P:=fun t=>t≤largest a b c)
      (Nat.le_trans hi bounds.1) (Nat.le_trans hj bounds.2.1) (Nat.le_trans hk bounds.2.2)
    omega
  · intro h
    exact ⟨a,b,c,Nat.le_refl _,Nat.le_refl _,Nat.le_refl _,h⟩

noncomputable def FullFrame.geometry {x : Fin 84→Rat} {f : Comparison.Frame} {ns : Labels}
    (s : FullFrame x f ns) (dom : domain x) : ComparisonGeometry x f ns :=
  fullComparison x f ns dom s.multiplier s.charts (comparisonBound x f) (Nat.le_refl _)

/-- The four finite prime sets are determined by the rational witness. -/
structure FullArithmetic (x : Fin 84→Rat) where
  labels : Labels
  first : FullFrame x .first labels
  second : FullFrame x .second labels
  third : FullFrame x .third labels
  scalarMultiplier : Int
  scalarCharts : ∀ p∈scalarFullPrimes (SquareGate.label (cell x 1)),
    Nonempty (CubicAt p x scalarMultiplier labels.n₂)
  scalarHeight : multiplicativeHeight (SquareGate.label (cell x 1)) ≤
    2^(2*scalarConstant*(radical (scalarFullPrimes (SquareGate.label (cell x 1))))^17)
  oddFirst : labels.n₁%2=1
  lastNonzero : labels.n₄≠0
  anchorNonzero : labels.n₂-1≠0
  anchor : (anchorModulus:Int)∣labels.n₂-1
  abscissas : 2*(labelSize labels)^2 ≤
    15+3*largest (comparisonBound x .first) (comparisonBound x .second) (comparisonBound x .third)

noncomputable def FullArithmetic.realize {x : Fin 84→Rat} (g : FullArithmetic x) (zero : output false x=0) :
    ArithmeticData x := by
  have dom:=fromZero_domain x false (by simp) zero
  let B:=SquareGate.label (cell x 1)
  have contacts : ∀ p∈scalarFullPrimes B, StructuralHeights.Prime p ∧ ¬(p:Int)∣210 ∧
      StructuralHeights.Contact p (StructuralHeights.coordinates B) ∧
      Nonempty (CubicAt p x g.scalarMultiplier g.labels.n₂) := by
    intro p member
    obtain ⟨prime,good,_,hit⟩:=(mem_scalarFullPrimes B p).mp member
    exact ⟨prime,good,hit,g.scalarCharts p member⟩
  exact ⟨g.labels,g.first.geometry dom,g.second.geometry dom,g.third.geometry dom,
    ⟨g.scalarMultiplier,scalarFullPrimes B,contacts,g.scalarHeight⟩,
    g.oddFirst,g.lastNonzero,g.anchorNonzero,g.anchor,g.abscissas⟩

/-- Geometry is required on one witness per represented nonzero input on the half-line.
The primitive contacts determine the supports for the heights and divisibilities. -/
theorem circuit_defines_of_full_contacts (marked : Bool)
    (integerFibres : ∀ n : Nat, circuitImage false (n:Rat))
    (selection : ∀ T : Rat, 0≤2*T+1 → T≠0 → circuitImage false T →
      ∃ y : Fin 80→Rat, y 0=T ∧ Binding.V y 9813=0 ∧ Nonempty (FullArithmetic (decoded y))) :
    ∀ T, circuitImage marked T ↔ InputRestriction.IsInteger T := by
  apply circuit_defines_of_arithmetic marked integerFibres
  intro T side nz z
  obtain ⟨y,input,ordinary,⟨g⟩⟩:=selection T side nz z
  have zero:=ordinary_decoded y ((Binding.ordinary_pointwise y).symm.trans ordinary)
  exact ⟨y,input,ordinary,⟨g.realize zero⟩⟩

#print axioms FullArithmetic.realize
#print axioms circuit_defines_of_full_contacts
end ProjectionFibres.Actual
