import ContactSieve
import Mathlib.NumberTheory.LegendreSymbol.Basic

namespace Sun28.NormSieve
open ManuscriptV15.Arithmetic
variable {p : ℕ} [Fact p.Prime]

def realResidue (p : ℕ) (z : Gaussian) : ZMod p := z.1
def imagResidue (p : ℕ) (z : Gaussian) : ZMod p := z.2

theorem gaussian_residue (z : Gaussian) : (gaussianNorm z : ZMod p) =
    (realResidue p z)^2+(imagResidue p z)^2 := by
  have e : (gaussianNorm z : ℤ)=z.1^2+z.2^2 :=
    Int.natAbs_of_nonneg (by positivity)
  simpa only [Int.cast_natCast,Int.cast_add,Int.cast_pow,realResidue,imagResidue] using
    congrArg (fun n : ℤ => (n : ZMod p)) e

/-- An odd prime dividing both adjacent norms must divide x and 1+y². -/
theorem diagonal_iff (odd : p≠2) (z : Gaussian) :
    (p∣adjacentNorm z true ∧ p∣adjacentNorm z false) ↔
      realResidue p z=0 ∧ (imagResidue p z)^2 = -1 := by
  have two : (2:ZMod p)≠0 := by
    rw [← Nat.cast_ofNat,Ne, ZMod.natCast_eq_zero_iff]
    exact fun h => odd ((Nat.prime_dvd_prime_iff_eq (Fact.out : p.Prime) Nat.prime_two).mp h)
  have four : (4:ZMod p)≠0 := by simpa [show (4:ZMod p) = 2*2 by norm_num] using mul_ne_zero two two
  have eqp : (adjacentNorm z true : ZMod p) = (realResidue p z + 1)^2+(imagResidue p z)^2 := by
    simpa [adjacentNorm,realResidue,imagResidue] using gaussian_residue (p:=p) (z.1+1,z.2)
  have eqm : (adjacentNorm z false : ZMod p) = (realResidue p z - 1)^2+(imagResidue p z)^2 := by
    simpa [adjacentNorm,realResidue,imagResidue,sub_eq_add_neg] using gaussian_residue (p:=p) (z.1-1,z.2)
  rw [←ZMod.natCast_eq_zero_iff,←ZMod.natCast_eq_zero_iff,eqp,eqm]
  constructor
  · rintro ⟨plus,minus⟩
    have kill : (4:ZMod p)*realResidue p z=0 := by linear_combination plus-minus
    have x := (mul_eq_zero.mp kill).resolve_left four
    exact ⟨x,by rw [x] at plus; linear_combination plus⟩
  · rintro ⟨x,y⟩
    rw [x,y]
    constructor <;> ring

/-- At an inert prime either adjacent norm vanishes exactly at one Gaussian residue. -/
theorem inert_iff (inert : p%4=3) (z : Gaussian) (sign : Bool) :
    p ∣ adjacentNorm z sign ↔
      realResidue p z = (if sign then -1 else 1) ∧ imagResidue p z=0 := by
  let x : ZMod p := realResidue p z + (if sign then 1 else -1)
  let y := imagResidue p z
  have eq : (adjacentNorm z sign : ZMod p)=x^2+y^2 := by
    cases sign <;> simp [x,y,adjacentNorm,realResidue,imagResidue,gaussian_residue]
  rw [←ZMod.natCast_eq_zero_iff,eq]
  constructor
  · intro zero
    have h : x^2= -y^2 := eq_neg_of_add_eq_zero_left zero
    have yn : y=0 := by
      by_contra nz
      exact ZMod.mod_four_ne_three_of_sq_eq_neg_sq' nz h inert
    have xn : x=0 := by simpa [yn] using h
    refine ⟨?_,yn⟩
    cases sign <;> simp [x] at xn ⊢ <;> linear_combination xn
  · rintro ⟨a,b⟩
    cases sign <;> simp_all [x,y]

/-- A diagonal obstruction occurs only at a split odd prime and on the norm fibre -1. -/
theorem self_obstruction (odd : p≠2) (z : Gaussian) (hp : p∣adjacentNorm z true)
    (hm : p∣adjacentNorm z false) : p%4=1 ∧ (gaussianNorm z : ZMod p) = -1 := by
  obtain ⟨x,y⟩ := (diagonal_iff odd z).mp ⟨hp,hm⟩
  have ns:=ZMod.mod_four_ne_three_of_sq_eq_neg_one y
  have parity := (Fact.out : p.Prime).eq_two_or_odd.resolve_left odd
  refine ⟨by omega,?_⟩
  rw [gaussian_residue,x,y]
  ring

end Sun28.NormSieve

#print axioms Sun28.NormSieve.gaussian_residue
#print axioms Sun28.NormSieve.diagonal_iff
#print axioms Sun28.NormSieve.inert_iff
#print axioms Sun28.NormSieve.self_obstruction
