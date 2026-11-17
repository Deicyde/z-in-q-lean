import GeometryEndpoint
import ProductPlaces

namespace HeightSpecialization
open ProjectionFibres ProjectionFibres.Comparison ProjectionFibres.HeightSupport ProjectionFibres.Actual
open IndependentIndices IndependentIndices.Assembly StructuralReduction StructuralReduction.Transfer84 WitnessTransfer.Height
set_option exponentiation.threshold 8192
set_option maxRecDepth 8192

/-- An exact integer inequality on four labels and two rational circuit coordinates. -/
def IndexHeight (x : Fin 84→Rat) (ns : Labels) := 2^((labelSize ns)^2) ≤ 64*J x

private theorem compare_heights {N U V j : Nat} (index : 2^(N^2)≤64*j)
    (pair : j^4≤U^5) (slope : U^2≤2^(4+3*V)) (margin : 68<V) : N^2<2*V := by
  have bound : 2^(8*N^2)≤2^(68+15*V) := by
    calc
      _=(2^(N^2))^8 := by rw [←Nat.pow_mul];congr 1;omega
      _≤(64*j)^8 := Nat.pow_le_pow_left index 8
      _=2^48*((j)^4)^2 := by rw [Nat.mul_pow,←Nat.pow_mul]
      _≤2^48*(U^5)^2 := Nat.mul_le_mul_left _ (Nat.pow_le_pow_left pair 2)
      _=2^48*(U^2)^5 := by simp only [←Nat.pow_mul]
      _≤2^48*(2^(4+3*V))^5 := Nat.mul_le_mul_left _ (Nat.pow_le_pow_left slope 5)
      _=_ := by rw [←Nat.pow_mul,←Nat.pow_add];congr 1;omega
  have e:=(Nat.pow_le_pow_iff_right (by decide : 1<2)).mp bound
  omega

theorem integer_root_bound {x : Fin 84→Rat} {ns : Labels} (dom : domain x)
    (index : IndexHeight x ns) (height : SlopeHeight x (tallest x)) :
    (labelSize ns)^2<rootConstant*(M x (tallest x))^17 := by
  let U:=H (slope x (tallest x))
  let V:=detectorConstant*(M x (tallest x))^17
  let N:=labelSize ns
  have pair : (J x)^4≤U^5 := physical_joint_height dom
  have slope : U^2≤2^(4+3*V) := height
  have pos:=Nat.pow_pos (scale_radical_pos x (tallest x)) (n:=17)
  have margin : 68<V := Nat.lt_of_lt_of_le (by decide +kernel : 68<detectorConstant)
    (by simpa only [Nat.mul_one] using Nat.mul_le_mul_left detectorConstant pos)
  change N^2<(2*detectorConstant)*(M x (tallest x))^17
  rw [Nat.mul_assoc];exact compare_heights index pair slope margin

structure IntegerData (x : Fin 84→Rat) where
  labels : Labels
  places : ∀ p∈fullPrimes (slope x (tallest x)), Nonempty (SourcePlace x (tallest x) p labels)
  index : IndexHeight x labels
  height : SlopeHeight x (tallest x)
  oddFirst : labels.n₁%2=1
  lastNonzero : labels.n₄≠0
  offsetNonzero : labels.n₂-1≠0
  anchor : (anchorModulus:Int)∣labels.n₂-1

def IntegerData.selected {x : Fin 84→Rat} (d : IntegerData x) (z : output false x=0)
    (cond : ScalarCondition x d.labels.n₂) : SelectedArithmetic x := by
  refine ⟨d.labels,tallest x,?_,integer_root_bound (fromZero_domain x false (by simp) z) d.index d.height,
    cond,d.oddFirst,d.lastNonzero,d.offsetNonzero,d.anchor⟩
  intro p hp
  obtain ⟨s⟩:=d.places p hp
  exact ⟨s.multiplier,s.contact hp⟩

theorem circuit_defines_of_index_height (marked : Bool)
    (integerFibres : ∀ n : Nat, circuitImage false (n:Rat))
    (selection : ∀ T : Rat, 0≤2*T+1 → T≠0 → circuitImage false T →
      ∃ y : Fin 80→Rat, y 0=T ∧ Binding.V y 9813=0 ∧
        ∃ g : IntegerData (decoded y), ScalarCondition (decoded y) g.labels.n₂) :
    ∀ T, circuitImage marked T ↔ InputRestriction.IsInteger T := by
  apply circuit_defines_of_one_comparison marked integerFibres
  intro T side nz represented
  obtain ⟨y,input,vanish,g,scalar⟩:=selection T side nz represented
  have z:=ordinary_decoded y ((Binding.ordinary_pointwise y).symm.trans vanish)
  exact ⟨y,input,vanish,⟨g.selected z scalar⟩⟩

#print axioms integer_root_bound
#print axioms IntegerData.selected
#print axioms circuit_defines_of_index_height
end HeightSpecialization
