import AffineSurface
import ProductClasses
import PreparedProjection

namespace Sun28.TwistExtension
open ZInQ Ordinary Forward ScalarHeight WitnessIndices FixedPreparation Concrete
open PreparedPoles PairedClasses RealProjection RealCharts CyclicOrbit TwistRank
open scoped RealCharts
noncomputable section

/-- The project-specific obligation on one prescribed pair. -/
def Residual : Prop := ∀ β θ : ℕ, AdmissiblePair β θ → InputClass β → FixedSquares θ →
  NormConic β θ → θ≠1 → ¬Family β θ → ¬SquareSection β θ → ¬FactorPair β θ → AffineSurface β θ

theorem of_local_residual (old : LocalResidual) : Residual := by
  intro β θ adm input fp conic live f s _
  exact affine_iff_surface.mpr (surface_of_old adm.1 adm.2.1 ((realized_iff_common adm.1 adm.2.1).mpr
    (old β θ adm input fp conic live f s)))

theorem pole (rest : Residual) {B : ℚ} (ready : ClassPrepared B) : polePredicate smallMultipliers B := by
  obtain ⟨m,β,θ,mem,c⟩:=choose_classes ready.prepare
  obtain ⟨loc,conic⟩:=actual_pair ready.prepare mem c
  have adm : AdmissiblePair β θ:=⟨c.beta_positive,c.theta_positive,c.beta_sf,c.theta_sf,c.disjoint,
    c.beta_six,c.theta_six,c.beta_mod,c.theta_mod,c.beta_local,c.theta_local⟩
  obtain ⟨a,an,A⟩:=c.beta_scale
  obtain ⟨d,dn,H⟩:=c.theta_scale
  refine Or.inr ⟨m,mem,(branch_iff_surface (by exact_mod_cast adm.1) (by exact_mod_cast adm.2.1.ne')
    an dn A H).mpr ?_⟩
  by_cases eq : θ=1
  · subst θ; exact surface_of_old adm.1 adm.2.1 (diagonal c.beta_positive c.beta_sf c.beta_six)
  by_cases f : Family β θ
  · exact surface_of_old adm.1 adm.2.1 (realized_of_family adm.1 adm.2.1 c.beta_sf (c.beta_six.mul_right c.disjoint) f)
  by_cases s : SquareSection β θ
  · exact surface_of_old adm.1 adm.2.1 (realized_of_section adm.1 c.beta_sf (c.beta_six.mul_right c.disjoint) s)
  by_cases pair : FactorPair β θ
  · exact surface_of_factors adm.1 adm.2.1 pair
  exact affine_iff_surface.mp (rest β θ adm (ready.class_at m β θ mem c) loc conic eq f s pair)

theorem certificate (rest : Residual) {w x η} (h : SelectedAt w x η) :
    PointCertificate w fixedMultiplier anchor x η gamma denominator smallMultipliers smallMultipliers := by
  obtain ⟨q,hh,b,n,t,z⟩ := h.guards
  refine ⟨q,hh,b,(rational_chart_iff _).2 n,(rational_chart_iff _).2 t,(rational_chart_iff _).2 z,h.scales,?_,?_⟩
  · intro j
    obtain ⟨live,p⟩ := h.ordinary j
    exact ⟨live,pole rest p⟩
  · obtain ⟨δ,sgn,nz,p⟩ := h.scalar
    exact ⟨δ,sgn,nz,pole rest p⟩

local instance : CompactSpace RealPair := compact_pair
local instance : T2Space RealPair := hausdorff_pair
local instance : IsTopologicalAddGroup RealPair := topological_pair

theorem fixed_projection (classification : RealComponents.PublishedProposition72)
    (units : FiveMarkUnits.PublishedCorollary72) (height : FiveDescent.TwistHeight glazerConstant24)
    (sieve : WeightedSelection.PositiveSurplus) (rest : Residual) (x : ℚ) :
    (∃ w : Fin 28 → ℚ,eval28 Concrete.fixedPolynomial x w=0) ↔ ∃ k : ℤ,x=(k:ℚ) := by
  refine ⟨integral_of_root units ((SieveProjection.least_iff_sextic units).mpr height),?_⟩
  rintro ⟨k,rfl⟩
  let component := RealComponents.openComponent_of_published classification
  let orbit := of_open_component diagonalGenerator component
  let model := parameterModel_on_subgroup DiagonalClosure orbit (generator_value diagonalGenerator component)
  have prep := selected_preparation orbit model
    (ray_selection (NormSieve.pattern_iff.mpr (WeightedSelection.prime_values_iff_surplus.mpr sieve)))
  obtain ⟨a,η,data⟩ := prep k
  exact (polynomial_iff_certificate _).2 ⟨a,η,certificate rest data⟩

theorem integer_definition_28 (classification : RealComponents.PublishedProposition72)
    (units : FiveMarkUnits.PublishedCorollary72) (height : FiveDescent.TwistHeight glazerConstant24)
    (sieve : WeightedSelection.PositiveSurplus) (rest : Residual) : IntegerDefinition28 :=
  ⟨Concrete.fixedPolynomial,fixed_projection classification units height sieve rest⟩

end
end Sun28.TwistExtension
#print axioms Sun28.TwistExtension.of_local_residual
#print axioms Sun28.TwistExtension.pole
#print axioms Sun28.TwistExtension.certificate
#print axioms Sun28.TwistExtension.fixed_projection
#print axioms Sun28.TwistExtension.integer_definition_28
