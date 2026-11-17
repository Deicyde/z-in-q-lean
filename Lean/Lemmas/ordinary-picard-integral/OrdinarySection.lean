import IntegralInfinity
import HenselTriples
import RationalJacobian
import Nyll.SchemeTheory.RingTheory.Etale.AlgebraEtaleReducedReduced

/-! A finite étale *local* algebra over which the ordinary signed model has a section.
This works without a rational point on the original special fibre. -/
open CategoryTheory AlgebraicGeometry CategoryTheory.Limits IsLocalRing Polynomial
open ZInQBlueprint.BinaryCover ZInQBlueprint.OrdinaryModel
namespace ZInQBlueprint.IntegralPicard
noncomputable section

variable {R : Type} [CommRing R] [IsLocalRing R]

private theorem residue_anisotropic {s : R} (h : ¬ IsSquare (residue R s))
    (a b : ResidueField R) (e : a^2 - residue R s*b^2 = 0) : a=0 ∧ b=0 := by
  by_cases hb : b=0
  · subst b
    simp at e
    exact ⟨e,rfl⟩
  · exfalso
    apply h
    refine ⟨a/b,?_⟩
    field_simp
    linear_combination -e

/-- A nonsquare unit residue makes the quadratic algebra local. Its nonunits
are exactly those elements whose two coordinates vanish in the residue field. -/
theorem local_quadratic {s : R} (h : ¬IsSquare (residue R s)) : IsLocalRing (Cover s) := by
  classical
  apply IsLocalRing.of_isUnit_or_isUnit_one_sub_self
  intro z
  by_cases hz : IsUnit z
  · exact Or.inl hz
  · right
    have zn : residue R (z.norm)=0 := by
      by_contra hn
      exact hz (QuadraticAlgebra.isUnit_iff_norm_isUnit.mpr ((residue_ne_zero_iff_isUnit _).mp hn))
    have eqn : (residue R z.re)^2 - residue R s * (residue R z.im)^2 = 0 := by
      simpa [QuadraticAlgebra.norm_def,sq,mul_assoc] using zn
    obtain ⟨hr,hi⟩ := residue_anisotropic h _ _ eqn
    apply QuadraticAlgebra.isUnit_iff_norm_isUnit.mpr
    apply (residue_ne_zero_iff_isUnit _).mp
    simp [QuadraticAlgebra.norm_def,hr,hi]

theorem hensel_square [HenselianRing R (maximalIdeal R)] (s : Rˣ) (h2 : IsUnit (2:R))
    (hr : IsSquare (residue R (s:R))) : ∃ w : R, w^2=(s:R) := by
  obtain ⟨r, h⟩ := hr
  have hr' : r ≠ 0 := by
    intro hz
    exact (residue_ne_zero_iff_isUnit (s:R)).mpr s.isUnit (by simp [h,hz])
  let f : R[X] := X^2-C (s:R)
  obtain ⟨w,hw,-⟩ := HenselTriples.liftSimple f r
    (by simp [f,h,sq])
    (by
      have htwo : (2 : ResidueField R) ≠ 0 := by
        simpa only [map_ofNat] using (residue_ne_zero_iff_isUnit (2:R)).mpr h2
      simpa only [f,derivative_sub,derivative_X_pow,derivative_C,sub_zero,
        Nat.cast_ofNat, Nat.reduceSubDiff, pow_one, eval₂_mul,eval₂_ofNat,eval₂_C,eval₂_X,map_ofNat] using mul_ne_zero htwo hr')
  exact ⟨w,by simpa [f,sub_eq_zero,IsRoot.def] using hw⟩

private def sectionFromPoint (A : Type) [CommRing A] [Algebra R A] {M : Over (Spec (.of R))}
    (P : SpecOver (R:=R) A ⟶ M) :
    NeronModelInfra.SchemeHomOver (𝟙 (Spec (.of A)))
      (AlgebraicGeometry.SmoothProperCurve.baseChange R M.hom A) :=
  ⟨pullback.lift P.left (𝟙 _) (by simpa [SpecOver] using P.w),pullback.lift_snd _ _ _⟩

/-- The finite faithfully flat algebra can be taken local, reduced and étale.
In the split case it is the base itself and in the nonsplit case it is free of rank two. -/
theorem local_section_cover [IsNoetherianRing R] [_root_.IsReduced R]
    [HenselianRing R (maximalIdeal R)] (s : Rˣ) (t : R) (h2 : IsUnit (2:R)) :
    ∃ (A : Type) (_ : CommRing A) (_ : Algebra R A) (_ : IsLocalRing A)
      (_ : IsNoetherianRing A) (_ : _root_.IsReduced A) (_ : Module.Finite R A)
      (_ : Algebra.FinitePresentation R A) (_ : Module.FaithfullyFlat R A)
      (_ : Algebra.Etale R A), (Module.finrank R A = 1 ∨ Module.finrank R A = 2) ∧
      Nonempty (NeronModelInfra.SchemeHomOver (𝟙 (Spec (.of A)))
        (AlgebraicGeometry.SmoothProperCurve.baseChange R (model (s:R) t).hom A)) := by
  classical
  by_cases h : IsSquare (residue R (s:R))
  · obtain ⟨w,hw⟩ := hensel_square s h2 h
    have he : w*w = (s:R) • (1:R) + (0:R) • w := by simpa [sq] using hw
    let φ : Cover (s:R) →ₐ[R] R := QuadraticAlgebra.lift ⟨w,he⟩
    let j : SpecOver (R:=R) R ⟶ SpecOver (R:=R) (Cover (s:R)) :=
      Over.homMk (Spec.map (CommRingCat.ofHom φ.toRingHom)) (by
        change Spec.map _ ≫ Spec.map _ = Spec.map _
        rw [←Spec.map_comp]
        exact congrArg Spec.map (CommRingCat.hom_ext φ.comp_algebraMap))
    exact ⟨R,_,_,inferInstance,inferInstance,inferInstance,inferInstance,inferInstance,inferInstance,
      inferInstance,Or.inl (by simp),⟨sectionFromPoint R (j ≫ infinityPoint (s:R) t)⟩⟩
  · let A := Cover (s:R)
    have : IsLocalRing A := local_quadratic h
    have : Algebra.Etale R A := etale_quadratic s h2
    have : IsNoetherianRing A := IsNoetherianRing.of_finite R A
    have : _root_.IsReduced A := Algebra.Etale.isReduced_of_isReduced_of_isNoetherianRing R A
    exact ⟨A,_,_,‹IsLocalRing A›,‹IsNoetherianRing A›,‹_root_.IsReduced A›,inferInstance,
      inferInstance,inferInstance,‹Algebra.Etale R A›,Or.inr (by
        simpa [A] using Module.finrank_eq_card_basis (QuadraticAlgebra.basis (s:R) 0)),
      ⟨sectionFromPoint A (infinityPoint (s:R) t)⟩⟩

end
end ZInQBlueprint.IntegralPicard
#print axioms ZInQBlueprint.IntegralPicard.local_quadratic
#print axioms ZInQBlueprint.IntegralPicard.hensel_square
#print axioms ZInQBlueprint.IntegralPicard.local_section_cover
