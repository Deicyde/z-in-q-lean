import Arithmetic80
import Archive80

namespace ProjectionFibres.Actual
open ProjectionFibres.Binding InputRestriction

/-- Rational input projection of the released straight-line polynomial.
Instruction addresses count from zero. -/
def circuitImage (marked : Bool) (T : Rat) : Prop :=
  ∃ y : Fin 80→Rat, y 0=T ∧ V y (if marked then 9814 else 9813)=0

theorem circuit_image (marked : Bool) (T : Rat) : circuitImage marked T ↔ Image marked T := by
  simp only [circuitImage,Image,physical_pointwise]

/-- Necessary and sufficient half-line statements, directly on the two stored outputs. -/
theorem circuit_defines_iff (marked : Bool) :
    (∀ T, circuitImage marked T ↔ IsInteger T) ↔
      (∀ n : Nat, circuitImage false (n:Rat)) ∧
      (∀ T : Rat, 0≤2*T+1 → circuitImage false T → IsInteger T) := by
  simp only [circuit_image]
  exact defining_iff_half marked

/-- A sufficient pair of arithmetic theorems for the stored integer polynomial. -/
theorem circuit_defines_of_arithmetic (marked : Bool)
    (integerFibres : ∀ n : Nat, circuitImage false (n:Rat))
    (selection : ∀ T : Rat, 0≤2*T+1 → T≠0 → circuitImage false T →
      ∃ y : Fin 80→Rat, y 0=T ∧ V y 9813=0 ∧ Nonempty (ArithmeticData (decoded y))) :
    ∀ T, circuitImage marked T ↔ IsInteger T := by
  simp only [circuit_image] at *
  apply defining_of_selected_witnesses marked integerFibres
  intro T side nz z
  obtain ⟨y,input,ordinary,geom⟩:=selection T side nz z
  exact ⟨y,input,(ordinary_pointwise y).symm.trans ordinary,geom⟩

#print axioms circuit_defines_iff
#print axioms circuit_defines_of_arithmetic
end ProjectionFibres.Actual
