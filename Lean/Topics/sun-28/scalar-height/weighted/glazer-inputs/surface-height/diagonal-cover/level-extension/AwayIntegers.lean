import EtalePointSeparation
import Mathlib.NumberTheory.NumberField.Basic
import Mathlib.RingTheory.Localization.AsSubring
import Mathlib.RingTheory.Localization.Ideal
import Mathlib.NumberTheory.RamificationInertia.Galois

open NumberField
open scoped NumberField nonZeroDivisors
namespace ZInQBlueprint.LevelExtension
noncomputable section
variable (L : Type*) [Field L] [NumberField L]

private theorem regular_powers : Submonoid.powers (210:𝓞 L) ≤ (𝓞 L)⁰ := by
  rintro a ⟨k,rfl⟩
  exact mem_nonZeroDivisors_of_ne_zero (pow_ne_zero _ (by norm_num))

/-- The actual ring of 210-integers inside the given number field. -/
def away : Subalgebra (𝓞 L) L :=
  Localization.subalgebra.ofField L (Submonoid.powers (210:𝓞 L)) (regular_powers L)

instance : IsLocalization.Away (210:𝓞 L) (away L) :=
  Localization.subalgebra.isLocalization_ofField L (Submonoid.powers _) (regular_powers L)

theorem mem_away (z : L) : z∈away L ↔ ∃ (a : 𝓞 L) (k : ℕ), z=(a:L)*(210:L)⁻¹^k := by
  constructor
  · rintro ⟨a,b,⟨k,rfl⟩,h⟩
    exact ⟨a,k,by simpa only [map_pow,map_ofNat,inv_pow] using h⟩
  · rintro ⟨a,k,h⟩
    exact ⟨a,(210:𝓞 L)^k,⟨k,rfl⟩,by simpa only [map_pow,map_ofNat,inv_pow] using h⟩

variable {L} {K : Type*} [Field K] [Algebra K L]

/-- A field automorphism over K preserves 210-integers. -/
def restrictAway (σ : L ≃ₐ[K] L) : away L →+* away L where
  toFun z := ⟨σ z.1,by
    obtain ⟨a,k,h⟩:=(mem_away L z.1).mp z.2
    apply (mem_away L _).mpr
    exact ⟨RingOfIntegers.mapAlgHom σ a,k,by rw [h,map_mul,map_pow,map_inv₀,map_ofNat]; rfl⟩⟩
  map_zero' := Subtype.ext (map_zero σ)
  map_one' := Subtype.ext (map_one σ)
  map_add' a b := Subtype.ext (map_add σ _ _)
  map_mul' a b := Subtype.ext (map_mul σ _ _)

theorem away_ideal_proper (P : Ideal (𝓞 L)) [hP : P.IsPrime] (unit : (210:𝓞 L)∉P) :
    (P.map (algebraMap (𝓞 L) (away L))) ≠ ⊤ := by
  have sep : Disjoint (Submonoid.powers (210:𝓞 L):Set (𝓞 L)) P := by
    rw [Set.disjoint_left]
    rintro a ⟨k,rfl⟩ mem
    exact unit (hP.mem_of_pow_mem _ mem)
  exact (IsLocalization.isPrime_of_isPrime_disjoint _ (away L) _ hP sep).ne_top

/-- Inertia acts trivially also on the residue classes of 210-integers.
The denominator is invertible at P. -/
theorem inertia_congr_away (P : Ideal (𝓞 L)) (σ : L ≃ₐ[K] L)
    (inertia : σ∈P.inertia (L ≃ₐ[K] L)) (z : away L) :
    restrictAway σ z - z ∈ P.map (algebraMap (𝓞 L) (away L)) := by
  obtain ⟨k,a,D⟩:=IsLocalization.Away.surj (210:𝓞 L) z
  let I := P.map (algebraMap (𝓞 L) (away L))
  let d : away L := algebraMap (𝓞 L) (away L) 210 ^ k
  have du : IsUnit d := IsLocalization.Away.algebraMap_pow_isUnit (210:𝓞 L) k
  have eq := congrArg (restrictAway σ) D
  have dd : restrictAway σ d = d := by apply Subtype.ext;change σ ((210:L)^k)=(210:L)^k;rw [map_pow,map_ofNat]
  change z*d=algebraMap (𝓞 L) (away L) a at D
  change restrictAway σ (z*d) = restrictAway σ (algebraMap (𝓞 L) (away L) a) at eq
  rw [map_mul,dd] at eq
  have E : restrictAway σ (algebraMap (𝓞 L) (away L) a) =
      algebraMap (𝓞 L) (away L) (σ • a) := by rfl
  apply (I.unit_mul_mem_iff_mem du).mp
  rw [mul_comm d,sub_mul,eq,D,E,←map_sub]
  exact Ideal.mem_map_of_mem _ (Ideal.mem_inertia.mp inertia a)

end
end ZInQBlueprint.LevelExtension
#print axioms ZInQBlueprint.LevelExtension.mem_away
#print axioms ZInQBlueprint.LevelExtension.away_ideal_proper
#print axioms ZInQBlueprint.LevelExtension.inertia_congr_away
