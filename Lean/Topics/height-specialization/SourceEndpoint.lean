import JointRootBound
import GateHeight
import FourRawRows

namespace HeightSpecialization
open Lean.Grind StructuralReduction StructuralReduction.Transfer84 IndependentIndices IndependentIndices.Assembly
open ProjectionFibres ProjectionFibres.Actual ProjectionFibres.HeightSupport ProjectionFibres.Comparison
open WitnessTransfer WitnessTransfer.Local WitnessTransfer.Height
set_option maxRecDepth 8192

/-- The primary cubic and the alternate local data at a prime of one comparison. -/
structure SourcePlace (x : Fin 84→Rat) (f : Scale) (p : Nat) (ns : Labels) where
  K : Type
  [fieldK : Field K]
  [charK : IsCharP K 0]
  w : ExtensionPlace p K
  rho : K
  root : rho^2=2
  multiplier : Int
  charts : ∀ r : K, (r=rho ∨ r= -rho) →
    (∀ s∈(f.data x).steps,w.deep (s.m:Int) (s.y.eval w r)) →
    ∃ o : LocalSetup p K w, Nonempty (Local.FourSourceRows o x f multiplier ns r)

theorem SourcePlace.contact {x : Fin 84→Rat} {f : Scale} {p : Nat} {ns : Labels}
    (s : SourcePlace x f p ns) (mem : p∈fullPrimes (slope x f)) :
    Nonempty (AtContact x f p s.multiplier ns) := by
  letI:=s.fieldK
  letI:=s.charK
  obtain ⟨hp,away,_⟩:=(mem_fullPrimes _ _).mp mem
  obtain ⟨_,_,large,_⟩:=exceptional_units hp away
  refine ⟨⟨s.K,s.w,s.rho,s.root,?_⟩⟩
  intro r sign depths
  obtain ⟨o,⟨raw⟩⟩:=s.charts r sign depths
  have root : r^2=2 := by
    rcases sign with h|h
    · rw [h];exact s.root
    · rw [h];have :=s.root;grobner
  exact ⟨o,Local.FourSourceRows.toFour o x f raw hp large root depths⟩

/-- Sufficiency on the physical witness. The maximal rational height specifies the frame. -/
structure SourceArithmetic (x : Fin 84→Rat) where
  labels : Labels
  places : ∀ p∈fullPrimes (slope x (tallest x)), Nonempty (SourcePlace x (tallest x) p labels)
  product : JointProductHeight x labels
  height : SlopeHeight x (tallest x)
  oddFirst : labels.n₁%2=1
  lastNonzero : labels.n₄≠0
  offsetNonzero : labels.n₂-1≠0
  anchor : (anchorModulus:Int)∣labels.n₂-1

def SourceArithmetic.selected {x : Fin 84→Rat} (g : SourceArithmetic x)
    (zero : output false x=0) (scalar : ScalarCondition x g.labels.n₂) : SelectedArithmetic x := by
  have dom:=fromZero_domain x false (by simp) zero
  have tight:=joint_root_bound dom g.product g.height
  have roots : (labelSize g.labels)^2 < rootConstant*(M x (tallest x))^17 := by
    change _ < (2*detectorConstant)*(M x (tallest x))^17
    rw [Nat.mul_assoc];omega
  refine ⟨g.labels,tallest x,?_,roots,
    scalar,g.oddFirst,g.lastNonzero,g.offsetNonzero,g.anchor⟩
  intro p hp
  obtain ⟨s⟩:=g.places p hp
  exact ⟨s.multiplier,s.contact hp⟩

theorem small_circuit_integral (y : Fin 80→Rat) (vanish : Binding.V y 9813=0)
    (g : SourceArithmetic (decoded y)) (height : H (y 0)≤2^(10^701)) :
    InputRestriction.IsInteger (y 0) := by
  have z:=ordinary_decoded y ((Binding.ordinary_pointwise y).symm.trans vanish)
  have small : SmallInput (cell (decoded y) 1) := by
    rw [input_decoded];exact small_input_of_height _ height
  simpa only [input_decoded] using selected_integral z (g.selected z (Or.inl small))

theorem circuit_defines_of_sources (marked : Bool)
    (integerFibres : ∀ n : Nat, circuitImage false (n:Rat))
    (sources : ∀ T : Rat, 0≤2*T+1 → T≠0 → circuitImage false T →
      ∃ y : Fin 80→Rat, y 0=T ∧ Binding.V y 9813=0 ∧
        ∃ g : SourceArithmetic (decoded y), ScalarCondition (decoded y) g.labels.n₂) :
    ∀ T, circuitImage marked T ↔ InputRestriction.IsInteger T := by
  apply circuit_defines_of_one_comparison marked integerFibres
  intro T side nz represented
  obtain ⟨y,input,vanish,g,scalar⟩:=sources T side nz represented
  have z:=ordinary_decoded y ((Binding.ordinary_pointwise y).symm.trans vanish)
  exact ⟨y,input,vanish,⟨g.selected z scalar⟩⟩

#print axioms SourcePlace.contact
#print axioms SourceArithmetic.selected
#print axioms small_circuit_integral
#print axioms circuit_defines_of_sources
end HeightSpecialization
