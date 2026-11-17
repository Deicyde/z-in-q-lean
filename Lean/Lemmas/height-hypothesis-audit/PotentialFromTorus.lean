import QuaternionToricRank
import QuaternionGoodHeight

/-! Potential good reduction from the torus of a semistable special fibre.
Cocharacters are covariant, so the action uses the given endomorphism ring
with its usual multiplication. -/
open CategoryTheory AlgebraicGeometry NumberField
namespace ZInQBlueprint.TorsionHeight
open AbelianModel NormalDescent LevelThree.IntegralOrder

/-- Standard Néron-model input. After a finite extension realizing semistable
reduction and all geometric endomorphisms, failure of potential good reduction
gives a positive-dimensional torus. Its rational cocharacters carry a unital
action of the geometric endomorphism ring. -/
def SemistableTorusAction : Prop :=
  ∀ (A : GroupScheme ℚ), IsAbelianScheme A → SmoothOfRelativeDimension 2 A.X.hom →
    ∀ (K : Type) [Field K] [NumberField K] (v : FinitePlace K), ¬ PotentialAt A v →
      ∃ n : ℕ, 0 < n ∧ n ≤ 2 ∧ Nonempty
        (End ((baseChange (algebraMap ℚ Qbar)).obj A) →+* Module.End ℚ (Fin n → ℚ))

/-- The local theorem for the printed order uses no fullness, descent, or
restriction on the geometric endomorphisms of a special abelian surface. -/
theorem potential_of_semistable_torus_action (torus : SemistableTorusAction) :
    QuaternionPotentialReduction := by
  intro A ab dim ⟨rho,_⟩ K _ _ v
  by_contra bad
  obtain ⟨n,pos,bound,⟨act⟩⟩ := torus A ab dim K v bad
  let : Nonempty (Fin n) := ⟨⟨0,pos⟩⟩
  have lower := quaternion_order_representation_dimension (Fin n → ℚ) (act.comp rho)
  simp at lower
  omega

end ZInQBlueprint.TorsionHeight
#print axioms ZInQBlueprint.TorsionHeight.potential_of_semistable_torus_action
