import SixAffine
import Mathlib.RingTheory.PicardGroup

/-! The pullback on invertible modules of an actual affine scheme isomorphism. -/

open CategoryTheory AlgebraicGeometry Polynomial

namespace ZInQBlueprint.BinaryCover

noncomputable section

/-- The affine double cover is free of rank two over the affine line. -/
theorem rank_two {K : Type} [Field K] (f : K[X]) :
    Module.Finite K[X] (Cover f) ∧ Module.Free K[X] (Cover f) ∧
      Module.finrank K[X] (Cover f) = 2 :=
  ⟨inferInstance, inferInstance, QuadraticAlgebra.finrank_eq_two f 0⟩

/-- On an affine scheme, sections recover the coordinate ring. Its Picard
group is the group of isomorphism classes of invertible modules. -/
def affinePicardIso {R A B : Type} [CommRing R] [CommRing A] [CommRing B]
    [Algebra R A] [Algebra R B] (e : SpecOver (R := R) A ≅ SpecOver B) :
    CommGrpCat.of (CommRing.Pic B) ≅ CommGrpCat.of (CommRing.Pic A) := by
  let i : Opposite.op (CommRingCat.of A) ≅ Opposite.op (CommRingCat.of B) :=
    Spec.fullyFaithful.preimageIso ((Over.forget _).mapIso e)
  exact ((forget₂ CommRingCat CommSemiRingCat) ⋙ CommRing.Pic.functor).mapIso i.unop

/-- The isomorphism includes the groups of all invertible modules on the
two matching affine charts of the six-contact curve. -/
theorem local_affine_picard {p : ℕ} [Fact p.Prime] {u : ℚ} (hu : u ∉ ZInQ.contactSet)
    (v a : ℤ_[p]ˣ) (t : ℤ_[p]) (hc : PrimitiveParameters.Coordinates p u t (v : ℤ_[p]) (a : ℤ_[p])) :
    ∃ i : Bool, Nonempty (CommGrpCat.of (CommRing.Pic (Cover (paper ℚ_[p] u i))) ≅
      CommGrpCat.of (CommRing.Pic (Cover (GoodReductionCharts.polynomial p u v a t)))) := by
  obtain ⟨i, ⟨e⟩⟩ := local_paper_chart_iso p hu v a t hc
  exact ⟨i, ⟨affinePicardIso e⟩⟩

end
end ZInQBlueprint.BinaryCover

#print axioms ZInQBlueprint.BinaryCover.affinePicardIso
#print axioms ZInQBlueprint.BinaryCover.local_affine_picard

#print axioms ZInQBlueprint.BinaryCover.rank_two
