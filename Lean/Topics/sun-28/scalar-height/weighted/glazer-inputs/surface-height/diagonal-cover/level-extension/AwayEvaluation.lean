import AwayIntegers
import Mathlib.RingTheory.Localization.Integral
import Mathlib.RingTheory.IntegralClosure.IsIntegralClosure.Basic

open NumberField
open scoped NumberField
namespace ZInQBlueprint.LevelExtension
noncomputable section
variable {K L : Type*} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]

/-- Extension of scalars sends 210-integers to 210-integers. -/
def awayMap : away K →+* away L where
  toFun z := ⟨algebraMap K L z.1,by
    obtain ⟨a,k,H⟩ := (mem_away K z.1).mp z.2
    apply (mem_away L _).mpr
    refine ⟨algebraMap (𝓞 K) (𝓞 L) a,k,?_⟩
    rw [H,map_mul,map_pow,map_inv₀,map_ofNat]
    rfl⟩
  map_one' := Subtype.ext (map_one _)
  map_zero' := Subtype.ext (map_zero _)
  map_add' a b := Subtype.ext (map_add _ _ _)
  map_mul' a b := Subtype.ext (map_mul _ _ _)

instance : Algebra (away K) (away L) := (awayMap (K:=K) (L:=L)).toAlgebra
instance scalarToField : Algebra (away K) L := ((algebraMap K L).comp (away K).val.toRingHom).toAlgebra

instance (priority := 1200) : SMul (away K) L := (scalarToField (K:=K) (L:=L)).toSMul

instance : IsScalarTower (𝓞 K) (away K) L :=
  IsScalarTower.of_algebraMap_eq (R:=𝓞 K) (S:=away K) (A:=L) fun _ => rfl

/-- The extension of a number-field automorphism to the ring of 210-integers. -/
def actAway (σ : L ≃ₐ[K] L) : away L →ₐ[away K] away L where
  toRingHom := restrictAway σ
  commutes' a := Subtype.ext (σ.commutes (a:K))

/-- Integrality over the localized base clears all denominators except powers of 210. -/
theorem integral_mem_away {x : L} (hx : IsIntegral (away K) x) : x∈away L := by
  obtain ⟨⟨_,k,rfl⟩,hi⟩ := IsIntegral.exists_multiple_integral_of_isLocalization
    (Submonoid.powers (210:𝓞 K)) x hx
  have hi' : IsIntegral (𝓞 K) ((210:L)^k*x) := by
    simpa only [Submonoid.smul_def,Algebra.smul_def,map_pow,map_ofNat] using hi
  refine (mem_away L x).mpr ⟨⟨_,isIntegral_trans _ hi'⟩,k,?_⟩
  change x=(210:L)^k*x*(210:L)⁻¹^k
  rw [mul_comm ((210:L)^k) x,mul_assoc,←mul_pow,mul_inv_cancel₀ (by norm_num : (210:L)≠0),one_pow,mul_one]

/-- Every generic point of a finite coordinate algebra has 210-integral coordinates. -/
def integralPoint {S : Type*} [CommRing S] [Algebra (away K) S]
    [Algebra.IsIntegral (away K) S] (f : S →ₐ[away K] L) : S →ₐ[away K] away L where
  toFun z := ⟨f z,by
    apply integral_mem_away (K:=K)
    rw [IsIntegral,← f.comp_algebraMap]
    exact RingHom.IsIntegralElem.map (Algebra.IsIntegral.isIntegral (R:=away K) z) f.toRingHom⟩
  map_zero' := Subtype.ext (map_zero f)
  map_one' := Subtype.ext (map_one f)
  map_add' a b := Subtype.ext (map_add f _ _)
  map_mul' a b := Subtype.ext (map_mul f _ _)
  commutes' a := Subtype.ext (f.commutes a)

end
end ZInQBlueprint.LevelExtension
#print axioms ZInQBlueprint.LevelExtension.integral_mem_away
#print axioms ZInQBlueprint.LevelExtension.integralPoint
