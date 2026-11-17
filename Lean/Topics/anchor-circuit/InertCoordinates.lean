import SexticOrder
import ScalarContacts

namespace AnchorCircuit.Inert
open StructuralReduction ProgressionWitnesses.SingleContact

private theorem coordinate_orders (v : RationalOrder) (two : v.ord 2=0) {a b : Rat} {k : Int}
    (realPart : a^2+2*b^2=0 ∨ 2*k≤v.ord (a^2+2*b^2))
    (mixed : 2*a*b≠0) (imagPart : v.ord (2*a*b)=2*k) :
    a≠0 ∧ b≠0 ∧ v.ord a=k ∧ v.ord b=k := by
  have an : a≠0 := fun h=>mixed (by rw [h]; grobner)
  have bn : b≠0 := fun h=>mixed (by rw [h]; grobner)
  have tn : (2:Rat)≠0 := by decide
  have ta : 2*a≠0 := fun h=>(Rat.mul_eq_zero.mp h).elim tn an
  rw [v.mul _ _ ta bn,v.mul _ _ tn an,two] at imagPart
  by_cases equal : v.ord a=v.ord b
  · exact ⟨an,bn,by omega,by omega⟩
  obtain ⟨asq,av⟩ := power_order v an 2
  obtain ⟨bsq,bv⟩ := power_order v bn 2
  have bs : 2*b^2≠0 := fun h=>(Rat.mul_eq_zero.mp h).elim tn bsq
  have ord : v.ord (2*b^2)=2*v.ord b := by rw [v.mul _ _ tn bsq,two,bv]; simp
  have av' : v.ord (a^2)=2*v.ord a := av
  have unequal := v.addUnequal _ _ asq bs (by rw [av',ord]; omega)
  have bound := realPart.resolve_left unequal.1
  rw [unequal.2,av',ord] at bound
  omega

/-- In (a+b√2)²=c+d√2 suppose ord₃(d)=2k and c is zero or ord₃(c)≥2k. -/
theorem three_adic_coordinates {a b : Rat} {k : Int}
    (realPart : a^2+2*b^2=0 ∨ 2*k≤order 3 (a^2+2*b^2))
    (mixed : 2*a*b≠0) (imagPart : order 3 (2*a*b)=2*k) :
    a≠0 ∧ b≠0 ∧ order 3 a=k ∧ order 3 b=k := by
  let hp : BinaryQuartic.Prime 3 := StructuralHeights.prime3
  exact coordinate_orders (primeOrder 3 hp) (order_nat_unit (n:=2) hp (by decide))
    realPart mixed imagPart

#print axioms three_adic_coordinates
end AnchorCircuit.Inert
