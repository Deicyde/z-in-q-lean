import Mathlib.Topology.Instances.AddCircle.Defs
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic

/-! Finite-order character square roots on cyclic local unit factors, in additive notation. -/
namespace ZInQBlueprint.WildLevel
noncomputable section
variable {A : Type*} [AddCommGroup A]

private def cycChar (n : ℕ) (z : A) (period : n • z=0) : ZMod n →+ A :=
  ZMod.lift n ⟨{toFun:= fun k:ℤ=>k • z, map_zero':=zero_zsmul _, map_add':=fun k l=>add_zsmul z k l},
    by simpa using period⟩

private theorem cycChar_nat (n : ℕ) (z : A) (period) (k : ℕ) : cycChar n z period (k:ZMod n)=k • z := by
  change ZMod.lift n _ (k:ZMod n)=_
  have h := ZMod.lift_coe (n:=n) (f:=⟨{toFun:=fun k:ℤ=>k • z, map_zero':=zero_zsmul _, map_add':=fun a b=>add_zsmul z a b},by simpa using period⟩) (k:ℤ)
  simpa using h

private theorem at_nat {n : ℕ} (χ : ZMod n →+ A) (k:ℕ) : χ (k:ZMod n)=k • χ 1 := by
  rw [← map_nsmul];simp

/-- On a cyclic group of order 2m, a character admits a square root
precisely when it is trivial on the involution. Doubling need only be
surjective in the coefficient group. -/
theorem halve_even (half : Function.Surjective (fun a:A=>a+a)) (m : ℕ) [NeZero m]
    (χ : ZMod (2*m) →+ A) : (∃ ψ : ZMod (2*m) →+ A, ∀ x, ψ x+ψ x=χ x) ↔ χ (m:ZMod (2*m))=0 := by
  constructor
  · rintro ⟨ψ,hψ⟩
    rw [←hψ,←map_add,←Nat.cast_add,←two_mul,ZMod.natCast_self,map_zero]
  · intro obstruction
    obtain ⟨y,hy⟩ := half (χ 1)
    change y+y=χ 1 at hy
    have m0 := (at_nat χ m).symm.trans obstruction
    have period : (2*m) • y=0 := by
      rw [mul_comm,mul_smul,two_smul,hy,m0]
    refine ⟨cycChar (2*m) y period,fun x=>?_⟩
    rw [←ZMod.natCast_zmod_val x,cycChar_nat,at_nat,←nsmul_add,hy]

/-- Passing from modulus n to 2n gives a half-character for any character.
This accounts for the extra power of two on the dyadic procyclic factor. -/
theorem halve_after_inflation (half : Function.Surjective (fun a:A=>a+a)) (n:ℕ) [NeZero n]
    (χ : ZMod n →+ A) : ∃ ψ : ZMod (2*n) →+ A, ∀ k : ℕ, ψ (k:ZMod (2*n))+ψ (k:ZMod (2*n))=χ (k:ZMod n) := by
  obtain ⟨y,hy⟩ := half (χ 1)
  change y+y=χ 1 at hy
  have pχ := (at_nat χ n).symm.trans (by rw [ZMod.natCast_self,map_zero])
  have period : (2*n) • y=0 := by rw [mul_comm,mul_smul,two_smul,hy,pχ]
  refine ⟨cycChar (2*n) y period,fun k=>?_⟩
  rw [cycChar_nat,at_nat,←nsmul_add,hy]

/-- Multiplicative characters can be written in the additive torsion group
of rational angles. Doubling is surjective there. -/
theorem angle_halves : Function.Surjective (fun a : AddCircle (1:ℚ)=>a+a) := by
  intro x
  obtain ⟨r,rfl⟩ := QuotientAddGroup.mk_surjective x
  refine ⟨(↑(r/2) : AddCircle (1:ℚ)),?_⟩
  change (↑(r/2) : AddCircle (1:ℚ)) + ↑(r/2)=↑r
  rw [←QuotientAddGroup.mk_add]
  congr 1
  ring

end
end ZInQBlueprint.WildLevel
#print axioms ZInQBlueprint.WildLevel.halve_even
#print axioms ZInQBlueprint.WildLevel.halve_after_inflation
#print axioms ZInQBlueprint.WildLevel.angle_halves
