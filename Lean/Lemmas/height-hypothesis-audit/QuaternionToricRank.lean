import IntegralQuaternionOrder
import RationalQuaternionAction
import Mathlib.RingTheory.Localization.Integer
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

/-! The discriminant-six order cannot act on a torus of rank one or two.
The rational norm argument proves the precise algebra obstruction in the
potential-good-reduction criterion. -/
namespace ZInQBlueprint.LevelThree.IntegralOrder
open QuaternionAlgebra
noncomputable section

private theorem even_norm_three (x y k : ℤ) (eqn : x^2 - 2*y^2 = 3*k) :
    (3:ℤ) ∣ x ∧ (3:ℤ) ∣ y := by
  have zero := congrArg (fun n : ℤ => (n : ZMod 3)) eqn
  have test : ∀ s t : ZMod 3, s^2-2*t^2=0 → s=0 ∧ t=0 := by decide
  have both := test (x:ZMod 3) (y:ZMod 3) (by
    simpa only [Int.cast_sub,Int.cast_mul,Int.cast_pow,Int.cast_ofNat,
      show (3:ZMod 3)=0 by decide,zero_mul] using zero)
  exact ⟨(ZMod.intCast_zmod_eq_zero_iff_dvd x 3).mp both.1,
    (ZMod.intCast_zmod_eq_zero_iff_dvd y 3).mp both.2⟩

private theorem integer_norm_anisotropic (a b c d : ℤ)
    (eqn : a^2-2*b^2+3*c^2-6*d^2 = 0) : a=0 ∧ b=0 ∧ c=0 ∧ d=0 := by
  generalize hsize : a.natAbs+b.natAbs+c.natAbs+d.natAbs = n
  induction n using Nat.strong_induction_on generalizing a b c d with
  | h n ih =>
    by_cases hn : n=0
    · exact ⟨Int.natAbs_eq_zero.mp (by omega),Int.natAbs_eq_zero.mp (by omega),
        Int.natAbs_eq_zero.mp (by omega),Int.natAbs_eq_zero.mp (by omega)⟩
    obtain ⟨⟨a',rfl⟩,⟨b',rfl⟩⟩ := even_norm_three a b (2*d^2-c^2) (by linarith only [eqn])
    obtain ⟨⟨c',rfl⟩,⟨d',rfl⟩⟩ := even_norm_three c d (2*b'^2-a'^2) (by nlinarith only [eqn])
    have small : a'.natAbs+b'.natAbs+c'.natAbs+d'.natAbs < n := by
      simp only [Int.natAbs_mul] at hsize
      norm_num at hsize
      omega
    have eqn' : a'^2-2*b'^2+3*c'^2-6*d'^2=0 := by nlinarith only [eqn]
    obtain ⟨rfl,rfl,rfl,rfl⟩ := ih _ small a' b' c' d' eqn' rfl
    simp

/-- Anisotropy over the rational field, proved by infinite descent at 3. -/
theorem reducedNorm_zero_iff (q : B) : reducedNorm q = 0 ↔ q=0 := by
  constructor
  · intro h
    let coords : Fin 4 → ℚ := ![q.re,q.imI,q.imJ,q.imK]
    obtain ⟨n,num⟩ := IsLocalization.exist_integer_multiples_of_finite (nonZeroDivisors ℤ) coords
    have hn : (n.val : ℚ) ≠ 0 := by exact_mod_cast nonZeroDivisors.coe_ne_zero n
    obtain ⟨a,ha⟩ := num 0
    obtain ⟨b,hb⟩ := num 1
    obtain ⟨c,hc⟩ := num 2
    obtain ⟨d,hd⟩ := num 3
    change (a:ℚ) = (n.val:ℤ) • q.re at ha
    change (b:ℚ) = (n.val:ℤ) • q.imI at hb
    change (c:ℚ) = (n.val:ℤ) • q.imJ at hc
    change (d:ℚ) = (n.val:ℤ) • q.imK at hd
    simp only [zsmul_eq_mul] at ha hb hc hd
    have form : q.re^2-2*q.imI^2+3*q.imJ^2-6*q.imK^2=0 := by
      simp [reducedNorm] at h
      nlinarith only [h]
    have eqn : (a:ℚ)^2-2*b^2+3*c^2-6*d^2=0 := by
      rw [ha,hb,hc,hd]
      linear_combination (n.val:ℚ)^2 * form
    have integral : a^2-2*b^2+3*c^2-6*d^2=0 := by exact_mod_cast eqn
    obtain ⟨rfl,rfl,rfl,rfl⟩ := integer_norm_anisotropic a b c d integral
    simp only [Int.cast_zero,zero_eq_mul,hn,false_or] at ha hb hc hd
    exact QuaternionAlgebra.ext ha hb hc hd
  · rintro rfl
    simp [reducedNorm]

/-- Every nonzero element of the actual rational quaternion algebra is a unit. -/
theorem isUnit_of_quaternion_ne_zero {q : B} (hq : q ≠ 0) : IsUnit q := by
  have hn : reducedNorm q ≠ 0 := fun h => hq ((reducedNorm_zero_iff q).mp h)
  let r := (reducedNorm q)⁻¹ • star q
  have qc : q*star q = algebraMap ℚ B (reducedNorm q) := by
    ext <;> simp [reducedNorm,QuaternionAlgebra.algebraMap_eq] <;> ring
  have cq : star q*q = algebraMap ℚ B (reducedNorm q) := by
    ext <;> simp [reducedNorm,QuaternionAlgebra.algebraMap_eq] <;> ring
  have scale : (reducedNorm q)⁻¹ • algebraMap ℚ B (reducedNorm q) = 1 := by
    rw [Algebra.smul_def,←map_mul,inv_mul_cancel₀ hn,map_one]
  exact ⟨⟨q,r,by simpa only [r,Algebra.mul_smul_comm,qc] using scale,
        by simpa only [r,Algebra.smul_mul_assoc,cq] using scale⟩,rfl⟩

/-- A nonzero rational representation of the printed integral order needs
at least four dimensions. In particular the character or cocharacter
space of a nonzero torus of rank at most two cannot carry its action. -/
theorem quaternion_order_representation_dimension (V : Type*) [AddCommGroup V]
    [Module ℚ V] [FiniteDimensional ℚ V] [Nontrivial V] (action : O →+* Module.End ℚ V) :
    4 ≤ Module.finrank ℚ V := by
  let f := extendRationalAction action
  obtain ⟨v,hv⟩ := exists_ne (0:V)
  let applyAt : B →ₗ[ℚ] V := (LinearMap.applyₗ (R:=ℚ) v).comp f.toLinearMap
  have inj : Function.Injective applyAt := by
    apply (LinearMap.ker_eq_bot).mp
    apply LinearMap.ker_eq_bot'.mpr
    intro q hq
    by_contra nonzero
    obtain ⟨u,hu⟩ := isUnit_of_quaternion_ne_zero nonzero
    have cancel := congrArg (fun z : V => f (↑u⁻¹:B) z) hq
    change f (↑u⁻¹:B) (f q v) = f (↑u⁻¹:B) 0 at cancel
    rw [←hu] at cancel
    have identity : f (↑u⁻¹:B) * f (u:B) = 1 := by rw [←map_mul,Units.inv_mul,map_one]
    apply hv
    simpa only [←Module.End.mul_apply,identity,Module.End.one_apply,map_zero] using cancel
  have bound := LinearMap.finrank_le_finrank_of_injective (f:=applyAt) inj
  simpa only [QuaternionAlgebra.finrank_eq_four] using bound

end
end ZInQBlueprint.LevelThree.IntegralOrder
#print axioms ZInQBlueprint.LevelThree.IntegralOrder.reducedNorm_zero_iff
#print axioms ZInQBlueprint.LevelThree.IntegralOrder.isUnit_of_quaternion_ne_zero
#print axioms ZInQBlueprint.LevelThree.IntegralOrder.quaternion_order_representation_dimension
