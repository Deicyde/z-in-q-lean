import ScalarTwists
import HeightClosure

namespace StructuralHeights
open IndependentIndices

/-- A square root of -d modulo p, in homogeneous coordinates with unit denominator. -/
def Represents (p : Nat) (d : Int) : Prop :=
  ∃ a b : Int, ¬(p:Int)∣b ∧ (p:Int)∣a^2+d*b^2

private theorem small_unit {p : Nat} (hp : Prime p) (good : ¬(p:Int)∣210)
    {c : Int} (small : c∣(210:Int)^5) : ¬(p:Int)∣c :=
  fun h=>good (prime_dvd_base hp 5 (Int.dvd_trans h small))

private theorem unit_denom {p : Nat} (hp : Prime p) (z : Rat) {a b : Int}
    (ua : ¬(p:Int)∣a) (div : (p:Int)∣a*z.num^2+b*(z.den:Int)^2) : ¬(p:Int)∣(z.den:Int) := by
  intro vd
  have db : (p:Int)∣b*(z.den:Int)^2 :=
    Int.dvd_mul_of_dvd_right (show (p:Int)∣(z.den:Int)^2 by
      rw [Int.pow_succ];exact Int.dvd_mul_of_dvd_right vd)
  have du : (p:Int)∣a*z.num^2 := by simpa using Int.dvd_sub div db
  have numerator := prime_dvd_base hp 2 (((prime_dvd_mul hp).mp du).resolve_left ua)
  have both:= (Int.gcd_eq_one_iff.mp (coordinates_primitive z)) _ numerator vd
  have bad := Nat.le_of_dvd (by decide : 0<1) (Int.ofNat_dvd_left.mp both)
  have := hp.1;omega

/-- Every scalar contact prime splits in at least one of three quadratic fields. -/
theorem splitting_restriction {p : Nat} (hp : Prime p) (good : ¬(p:Int)∣210)
    (x : Rat) (contact : Contact p (coordinates (SquareGate.label x))) :
    Represents p 1 ∨ Represents p 6 ∨ Represents p 14 := by
  let z:=SquareGate.value x
  have odd := (physical_contact hp good x).mp contact
  have divides:=odd_dvd odd
  change (p:Int)∣firstForm z.num z.den*secondForm z.num z.den*thirdForm z.num z.den at divides
  have denom {c : Int} (small : c∣(210:Int)^5) (unit : ¬(p:Int)∣(z.den:Int)) :
      ¬(p:Int)∣c*(z.den:Int) := fun d=>((prime_dvd_mul hp).mp d).elim (small_unit hp good small) unit
  rcases (prime_dvd_mul hp).mp divides with two|three
  · rcases (prime_dvd_mul hp).mp two with one|two
    · left
      have unit:=unit_denom hp z (small_unit hp good (by decide : (1:Int)∣210^5))
        (b:=2401) (by simpa [firstForm] using one)
      refine ⟨z.num,49*z.den,denom (by decide) unit,?_⟩
      have eq : z.num^2+1*(49*(z.den:Int))^2 = firstForm z.num z.den := by unfold firstForm;grobner
      exact eq ▸ one
    · right;left
      have unit:=unit_denom hp z (small_unit hp good (by decide : (1:Int)∣210^5))
        (b:=2400) (by simpa [secondForm] using two)
      refine ⟨z.num,20*z.den,denom (by decide) unit,?_⟩
      have eq : z.num^2+6*(20*(z.den:Int))^2 = secondForm z.num z.den := by unfold secondForm;grobner
      exact eq ▸ two
  · right;right
    have unit:=unit_denom hp z (small_unit hp good (by decide : (32:Int)∣210^5)) three
    refine ⟨32*z.num,420*z.den,denom (by decide) unit,?_⟩
    have eq : (32*z.num)^2+14*(420*(z.den:Int))^2=32*thirdForm z.num z.den := by unfold thirdForm;grobner
    exact eq ▸ Int.dvd_mul_of_dvd_right three

def fourPrimeConstant : Nat := 2^24*(2^16*(2*3)*(3*4)*(5*6)*(7*8))^6*4^5+128
def detectorConstant : Nat := HeightClosure.constant [2,3,5,7,11,13,17,29,37,41,2399]

set_option exponentiation.threshold 8192 in
set_option maxRecDepth 8192 in
theorem margins :
    2^231≤fourPrimeConstant ∧ fourPrimeConstant<2^232 ∧
    5^17*(2*detectorConstant)^40<(2*3^1436*11^17-1)^12 ∧
    (2*3^1435*11^17-1)^12≤5^17*(2*detectorConstant)^40 ∧
    80*fourPrimeConstant<2*3^1436 := by decide

#print axioms splitting_restriction
#print axioms margins
end StructuralHeights
