import OrdinaryPolarizedEndpoint
import PotentialFromTorus
import PublishedGenusRows

/-! Glazer's bounded polynomial from the ordinary marked field, the
semistable torus action and Tian's genus criterion. -/

open AlgebraicGeometry
open scoped ZInQBlueprint.NormalDescent

namespace ZInQBlueprint.AbelComparison
open AbelianModel NormalDescent QuaternionMarking QuaternionLift ShimuraAtlas ThetaClass ZInQ
open LocalJacobians JacobianHeight JacobianConductor TorsionHeight MinimalDiscriminant
open WeierstrassCoordinates OriginalRank.PublishedGenusRows

/-- On the geometric side the semistable torus has rational cocharacter
space of dimension at most two. On the rank side the two factorization sums
are those in the statement of Tian's theorem. -/
theorem original_of_ordinary_geometry_and_tian (hF : GroupScheme ℚ → ℝ)
    (hp : GlobalHeightFormula hF) (effective : EffectiveSurfaceHeight hF)
    (torus : SemistableTorusAction)
    (st : ∀ A : GroupScheme ℚ, IsAbelianScheme A → SerreTateCriterion A)
    (ddmm : ∀ (p : ℕ) [Fact p.Prime], TwoTripleGoodReduction p)
    (factor : CartierPrimeFactorization) (read : IgusaCoordinates → ModuliClass)
    (classification : PolarizedIgusaClassification read) (fields : OrdinaryMarkedFields read)
    (torelli : PointedDeterminantTorelli) (coordinates : VoightCoordinateFormula)
    (tian : PublishedTian47) (rank : OriginalRank.ModularSimpleZero) : FrozenTarget :=
  original_of_ordinary_polarized_comparison hF hp effective (potential_of_semistable_torus_action torus)
    st ddmm factor read classification fields torelli coordinates (higher_order_of_tian47 tian) rank

end ZInQBlueprint.AbelComparison

#print axioms ZInQBlueprint.AbelComparison.original_of_ordinary_geometry_and_tian
