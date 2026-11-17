import ChartOpen
import Mathlib.RingTheory.KrullDimension.Polynomial
import Mathlib.RingTheory.KrullDimension.Field
import Mathlib.RingTheory.Ideal.HasGoingUp
import Mathlib.RingTheory.Ideal.GoingUp
import Mathlib.Topology.KrullDimension

/-! Krull dimension of a finite double cover of the line and its two-chart completion. -/
open CategoryTheory AlgebraicGeometry Polynomial Order Topology TopologicalSpace
namespace ZInQBlueprint.BinaryCover
noncomputable section

/-- Contraction preserves strict inclusions. Conversely each finite chain lifts by going up. -/
theorem dimension_integral_extension (R A : Type*) [CommRing R] [CommRing A] [Algebra R A]
    [Algebra.IsIntegral R A] [FaithfulSMul R A] : ringKrullDim A = ringKrullDim R := by
  refine le_antisymm (Order.krullDim_le_of_strictMono (PrimeSpectrum.comap (algebraMap R A)) ?_) ?_
  · intro p q hp
    exact Ideal.IsIntegral.under_lt_under (R := R) (I := p.asIdeal) (J := q.asIdeal) hp
  · change Order.krullDim (PrimeSpectrum R) ≤ Order.krullDim (PrimeSpectrum A)
    unfold Order.krullDim
    refine iSup_le fun l => ?_
    obtain ⟨P⟩ := (inferInstance : Nonempty (l.head.asIdeal.primesOver A))
    obtain ⟨L,hlen,-,-⟩ := Ideal.exists_ltSeries_of_hasGoingUp l P.val
    exact le_iSup_of_le L (by rw [hlen])

theorem dimension_cover (K : Type) [Field K] (f : K[X]) :
    topologicalKrullDim (Spec (.of (Cover f))) = 1 := by
  change topologicalKrullDim (PrimeSpectrum (Cover f)) = 1
  rw [PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim]
  rw [dimension_integral_extension K[X] (Cover f)]
  simp

attribute [local instance] specializationOrder in
theorem dimension_le_of_cover {X : Scheme} (U : X.OpenCover)
    (h : ∀ i : U.I₀, topologicalKrullDim (U.X i) ≤ 1) : topologicalKrullDim X ≤ 1 := by
  change Order.krullDim (IrreducibleCloseds X) ≤ 1
  rw [Order.krullDim_eq_of_orderIso (irreducibleSetEquivPoints (α := X))]
  rw [Order.krullDim_eq_iSup_coheight, iSup_le_iff]
  intro x
  obtain ⟨i,y,rfl⟩ := U.exists_eq x
  rw [(U.f i).isOpenEmbedding.coheight_eq (U.f i)]
  refine (Order.coheight_le_krullDim y).trans ?_
  rw [← Order.krullDim_eq_of_orderIso (irreducibleSetEquivPoints (α := U.X i))]
  exact h i

theorem dimension_glued (K : Type) [Field K] (f g : K[X]) (h : SexticOverlap K f g) :
    topologicalKrullDim (glued K f g h) = 1 := by
  have dimf := dimension_cover K f
  refine le_antisymm (dimension_le_of_cover (openCover K f g h) ?_) ?_
  · intro i
    cases i with
    | none =>
      exact (puncture K f).isOpenEmbedding.isInducing.topologicalKrullDim_le.trans dimf.le
    | some j => exact (dimension_cover K (if j then g else f)).le
  · rw [← dimf]
    exact (chartInclusion K f g h false).left.isOpenEmbedding.isInducing.topologicalKrullDim_le

theorem paper_dimension (K : Type) [Field K] [CharZero K] (u : ℚ) :
    topologicalKrullDim (paperModel K u).left = 1 := dimension_glued K _ _ _

end
end ZInQBlueprint.BinaryCover
#print axioms ZInQBlueprint.BinaryCover.dimension_integral_extension
#print axioms ZInQBlueprint.BinaryCover.dimension_cover
#print axioms ZInQBlueprint.BinaryCover.dimension_le_of_cover
#print axioms ZInQBlueprint.BinaryCover.dimension_glued
#print axioms ZInQBlueprint.BinaryCover.paper_dimension
