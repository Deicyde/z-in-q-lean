import ThreeAdicRatio
import Mathlib.NumberTheory.Padics.Hensel
import Mathlib.NumberTheory.Padics.RingHoms

namespace Sun28.PointLifts
open Polynomial
noncomputable section

/-- Equal nonzero residues modulo three suffice to solve A h² = B over the
3-adic integers. Hensel's initial approximation is h = 1. -/
theorem three_square_lift {A B : ℤ_[3]} (same : PadicInt.toZMod A = PadicInt.toZMod B)
    (unit : PadicInt.toZMod A ≠ 0) : ∃ h : ℤ_[3], A*h^2=B := by
  let f : Polynomial ℤ_[3] := C A * X^2 - C B
  have small : ‖A-B‖ < 1 := by
    apply PadicInt.not_isUnit_iff.mp
    change A-B ∈ IsLocalRing.maximalIdeal ℤ_[3]
    rw [← PadicInt.ker_toZMod, RingHom.mem_ker]
    simp [same]
  have normA : ‖A‖=1 := by
    apply PadicInt.isUnit_iff.mp
    by_contra wrong
    change A ∈ IsLocalRing.maximalIdeal ℤ_[3] at wrong
    rw [← PadicInt.ker_toZMod, RingHom.mem_ker] at wrong
    exact unit wrong
  have norm2 : ‖(2:ℤ_[3])‖=1 := (PadicInt.norm_natCast_eq_one_iff (p:=3) (n:=2)).mpr (by decide)
  have ev (h : ℤ_[3]) : f.aeval h = A*h^2-B := by simp [f]
  have der : f.derivative.aeval (1:ℤ_[3]) = A*2 := by
    simp [f,Polynomial.derivative_mul,Polynomial.derivative_pow]
  have cond : ‖f.aeval (1:ℤ_[3])‖ < ‖f.derivative.aeval (1:ℤ_[3])‖^2 := by
    simpa only [ev,one_pow,mul_one,der,norm_mul,normA,norm2] using small
  obtain ⟨h,zero,_,_,_⟩ := hensels_lemma cond
  exact ⟨h,sub_eq_zero.mp ((ev h).symm.trans zero)⟩

/-- Both conics have integral ordinates at z=-1 for every unit ratio.
The identity for h₂ clears the unit denominator θ². -/
theorem three_unit_section (b θ s : ℤ_[3])
    (hb : PadicInt.toZMod b=2) (ht : PadicInt.toZMod θ=1)
    (hs : PadicInt.toZMod s≠0) :
    ∃ h j : ℤ_[3], b*h^2=(-1-1)*(-1+3) ∧
      (b*θ^2)*j^2=(-s^2-θ)*(-s^2+3*θ) := by
  have one : (PadicInt.toZMod s)^2=1 :=
    (show ∀ x : ZMod 3, x≠0 → x^2=1 by decide) _ hs
  have h2 : (2:ZMod 3)≠0 := by decide
  have m : PadicInt.toZMod ((-1-1)*(-1+3) : ℤ_[3])=2 := by
    calc
      _ = (PadicInt.toZMod : ℤ_[3] →+* ZMod 3) ((-4:ℤ):ℤ_[3]) := by congr 1; ring
      _ = ((-4:ℤ):ZMod 3) := map_intCast _ _
      _ = 2 := by decide
  obtain ⟨h,hh⟩ := three_square_lift (hb.trans m.symm) (hb ▸ h2)
  have t : PadicInt.toZMod (b*θ^2)=2 := by simp [hb,ht]
  have a : PadicInt.toZMod ((-s^2-θ)*(-s^2+3*θ)) = 2 := by
    simp only [map_mul,map_add,map_sub,map_neg,map_pow,map_ofNat,one,ht]
    decide
  obtain ⟨j,hj⟩ := three_square_lift (t.trans a.symm) (t ▸ h2)
  exact ⟨h,j,hh,hj⟩

end
end Sun28.PointLifts
#print axioms Sun28.PointLifts.three_square_lift
#print axioms Sun28.PointLifts.three_unit_section
