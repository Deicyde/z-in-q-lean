import PointedSextic
import Mathlib.AlgebraicGeometry.Sites.Fpqc
import Mathlib.CategoryTheory.Sites.LocallyBijective
import Mathlib.CategoryTheory.Sites.LeftExact
import Mathlib.Algebra.Category.Grp.Colimits
import Mathlib.Algebra.Category.Grp.FilteredColimits
import Mathlib.Algebra.Category.Grp.Limits

/-! A point after a quadratic extension suffices for the pointed test in
Milne's Jacobian theorem. All test schemes are schemes over the original base. -/
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
namespace ZInQBlueprint.PointedSextic
noncomputable section
local notation "S" => Spec (CommRingCat.of ℚ)
local notation "J" => Scheme.fppfTopology.over S

theorem field_cover (u : ℚ) :
    Flat (BinaryCover.SpecOver (R := ℚ) (SplittingField u)).hom ∧
    Surjective (BinaryCover.SpecOver (R := ℚ) (SplittingField u)).hom ∧
    LocallyOfFinitePresentation (BinaryCover.SpecOver (R := ℚ) (SplittingField u)).hom := by
  let e := CommRingCat.ofHom (algebraMap ℚ (SplittingField u))
  have H := (flat_and_surjective_SpecMap_iff e).2
    (RingHom.faithfullyFlat_algebraMap_iff.mpr inferInstance)
  exact ⟨H.1, H.2, (LocallyOfFinitePresentation.SpecMap_iff e).2
    (RingHom.finitePresentation_algebraMap.mpr (Algebra.FinitePresentation.of_finiteType.mp inferInstance))⟩

/-- Every test scheme has an fppf cover with a point on any curve containing
the infinity chart. Both maps out of the covering scheme are over the base. -/
theorem pointed_cover (u : ℚ) {C : Over S}
    (ι : BinaryCover.SpecOver (R := ℚ) (BinaryCover.Cover (BinaryCover.fixed ℚ u true)) ⟶ C)
    (T : Over S) : ∃ (V : Over S) (q : V ⟶ T), Nonempty (V ⟶ C) ∧
      Sieve.generate (Presieve.singleton q) ∈ J T := by
  let E := BinaryCover.SpecOver (R := ℚ) (SplittingField u)
  obtain ⟨flat, surj, fin⟩ := field_cover u
  let : Flat E.hom := flat
  let : Surjective E.hom := surj
  let : LocallyOfFinitePresentation E.hom := fin
  let V : Over S := Over.mk (pullback.fst T.hom E.hom ≫ T.hom)
  let q : V ⟶ T := Over.homMk (pullback.fst _ _)
  let e : V ⟶ E := Over.homMk (pullback.snd _ _) pullback.condition.symm
  refine ⟨V, q, ⟨e ≫ point u ≫ ι⟩, ?_⟩
  rw [GrothendieckTopology.mem_over_iff]
  apply Scheme.fppfTopology.superset_covering _ (Precoverage.generate_mem_toGrothendieck
    (pullback.fst T.hom E.hom).singleton_mem_fppfPrecoverage)
  rw [Sieve.generate_le_iff, Presieve.singleton_le_iff, Sieve.overEquiv_iff]
  exact Sieve.le_generate _ _ _ (Presieve.singleton_self q)

/-- A morphism of presheaves that is an isomorphism on pointed tests is
locally bijective on every test. This applies to Milne's canonical morphism. -/
theorem locally_bijective {C : Over S} {F G : (Over S)ᵒᵖ ⥤ GrpCat.{v}}
    (α : F ⟶ G) (u : ℚ)
    (ι : BinaryCover.SpecOver (R := ℚ) (BinaryCover.Cover (BinaryCover.fixed ℚ u true)) ⟶ C)
    (h : ∀ T : Over S, Nonempty (T ⟶ C) → Function.Bijective (α.app (op T))) :
    Presheaf.IsLocallyInjective J α ∧ Presheaf.IsLocallySurjective J α := by
  constructor
  · constructor
    intro T x y eq
    obtain ⟨V, q, p, cov⟩ := pointed_cover u ι T.unop
    apply (J).superset_covering _ cov
    rw [Sieve.generate_le_iff, Presieve.singleton_le_iff]
    apply (h V p).1
    change α.app (op V) (F.map q.op x) = α.app (op V) (F.map q.op y)
    rw [NatTrans.naturality_apply, NatTrans.naturality_apply, eq]
  · constructor
    intro T y
    obtain ⟨V, q, p, cov⟩ := pointed_cover u ι T
    apply (J).superset_covering _ cov
    rw [Sieve.generate_le_iff, Presieve.singleton_le_iff]
    exact (h V p).2 (G.map q.op y)

/-- The comparison becomes an isomorphism after fppf sheafification. -/
theorem sheafification_iso {C : Over S} {F G : (Over S)ᵒᵖ ⥤ GrpCat.{1}}
    (α : F ⟶ G) (u : ℚ)
    (ι : BinaryCover.SpecOver (R := ℚ) (BinaryCover.Cover (BinaryCover.fixed ℚ u true)) ⟶ C)
    (h : ∀ T : Over S, Nonempty (T ⟶ C) → Function.Bijective (α.app (op T))) :
    IsIso ((presheafToSheaf J (Type 1)).map (Functor.whiskerRight α (forget GrpCat))) := by
  obtain ⟨hI, hS⟩ := locally_bijective α u ι h
  apply ((J).W_iff _).mp
  apply ((J).W_iff_isLocallyBijective _).mpr
  exact ⟨(Presheaf.isLocallyInjective_forget_iff J α).mpr hI,
    (Presheaf.isLocallySurjective_iff_whisker_forget J α).mp hS⟩

end
end ZInQBlueprint.PointedSextic

#print axioms ZInQBlueprint.PointedSextic.field_cover
#print axioms ZInQBlueprint.PointedSextic.pointed_cover
#print axioms ZInQBlueprint.PointedSextic.locally_bijective
#print axioms ZInQBlueprint.PointedSextic.sheafification_iso
