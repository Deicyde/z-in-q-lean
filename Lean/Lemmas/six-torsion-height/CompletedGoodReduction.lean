import LocalTorsionDescent
import AbelianModel
import Mathlib.NumberTheory.NumberField.Completion.FinitePlace

/-! Local abelian models at the finite places of an actual number field.
The two remaining external inputs are the quaternionic potential reduction
theorem and the finite-level Serre--Tate criterion. -/
open CategoryTheory AlgebraicGeometry NumberField ZInQBlueprint.AbelianModel
namespace ZInQBlueprint.TorsionHeight
noncomputable section
variable (A : GroupScheme ℚ)
def GoodOver (O : Type) [CommRing O] (L : Type) [Field L] [Algebra ℚ L] [Algebra O L] : Prop :=
  ∃ M : GroupScheme O, IsAbelianScheme M ∧ Nonempty
    ((baseChange (algebraMap O L)).obj M ≅ (baseChange (algebraMap ℚ L)).obj A)

variable {K : Type} [Field K] [NumberField K]
abbrev localField (v : FinitePlace K) := v.maximalIdeal.adicCompletion K
abbrev valuationIntegers (v : FinitePlace K) := v.maximalIdeal.adicCompletionIntegers K

def GoodAt (v : FinitePlace K) : Prop := GoodOver A (valuationIntegers v) (localField v)

/-- A finite extension of this completed local field, with an extension of its
valuation and a good abelian model. No global realization of the extension
is needed for the local potential-reduction theorem. -/
def PotentialAt (v : FinitePlace K) : Prop :=
  ∃ (E : Type) (_ : Field E) (_ : Algebra (localField v) E)
    (_ : FiniteDimensional (localField v) E) (_ : Algebra ℚ E)
    (_ : IsScalarTower ℚ (localField v) E) (O : ValuationSubring E),
    O.comap (algebraMap (localField v) E) = valuationIntegers v ∧ GoodOver A O E

/-- Number-field form of Serre--Tate, Theorem 2, Corollary 2(b): potential
good reduction and one full rational prime-to-residue level at least three.
Rationality here is tested on the actual local geometric torsion points. -/
def SerreTateCriterion : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (v : FinitePlace K),
    PotentialAt A v → ∀ n : ℕ, 3 ≤ n → IsUnit (n : valuationIntegers v) →
    FullLevel A n (localField v) → GoodAt A v

theorem good_everywhere_of_full_twelve (st : SerreTateCriterion A)
    (potential : ∀ v : FinitePlace K, PotentialAt A v) (level : FullLevel A 12 K) :
    ∀ v : FinitePlace K, GoodAt A v := by
  intro v
  obtain ⟨n,dvd,three,unit⟩ := local_level (valuationIntegers v)
  apply st K v (potential v) n three unit
  exact fullLevel_overfield A (fullLevel_of_dvd A dvd level) (IsScalarTower.toAlgHom ℚ K (localField v))

end
end ZInQBlueprint.TorsionHeight
#print axioms ZInQBlueprint.TorsionHeight.GoodAt
#print axioms ZInQBlueprint.TorsionHeight.PotentialAt
#print axioms ZInQBlueprint.TorsionHeight.good_everywhere_of_full_twelve
