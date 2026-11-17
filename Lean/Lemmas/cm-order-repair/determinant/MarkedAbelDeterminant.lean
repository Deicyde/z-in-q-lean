import CartierMultiplicity
import SixPolarizedTransport

/-! Galois transport of the determinant attached to a marked genus-two
Jacobian. An isomorphism of the underlying curves compatible with the
Abel morphism up to translation is enough, for any divisor multiplicity. -/
open CategoryTheory AlgebraicGeometry CategoryTheory.MonoidalCategory
open scoped CategoryTheory.MonObj ZInQBlueprint.NormalDescent
namespace ZInQBlueprint.CMRepair
open ThetaClass QuaternionMarking GeometricMarking AbelianModel NormalDescent CanonicalTheta
open SixAbelMap SixThetaRestriction
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

private theorem comap_eq_inverse_map {X Y : Scheme} (I : X.IdealSheafData) (f : Y ≅ X) :
    I.comap f.hom = I.map f.inv := by
  apply le_antisymm
  · apply Scheme.IdealSheafData.le_map_iff_comap_le.mpr
    rw [← Scheme.IdealSheafData.comap_comp, f.inv_hom_id, Scheme.IdealSheafData.comap_id]
  · have h := Scheme.IdealSheafData.map_mono f.inv (I.le_map_comap f.hom)
    simpa only [← Scheme.IdealSheafData.map_comp, f.hom_inv_id, Scheme.IdealSheafData.map_id] using h

/-- The scheme-theoretic image ideal is functorial under a commuting square
of isomorphisms.  The curve morphism can have arbitrary scheme-theoretic image. -/
theorem abel_image_pullbacks {C X Y : Scheme} (m : C ⟶ X) (a b : Y ≅ X) (c : C ≅ C)
    (diagram : m ≫ a.inv = c.hom ≫ m ≫ b.inv) : m.ker.comap a.hom = m.ker.comap b.hom := by
  rw [comap_eq_inverse_map, comap_eq_inverse_map, Scheme.IdealSheafData.map_ker,
    Scheme.IdealSheafData.map_ker, diagram, Scheme.Hom.ker_comp_of_isIso]

/-- An isomorphism to the conjugate abelian variety determines an automorphism
of its underlying scheme, semilinear above the chosen base automorphism. -/
def semilinearCorrection {A : GroupScheme Qbar} (σ : Qbar ≃ₐ[ℚ] Qbar)
    (φ : A ≅ (conjugation σ.toRingEquiv).mapCommGrp.obj A) : A.X.left ≅ A.X.left :=
  let specIso := Scheme.Spec.mapIso (RingEquiv.toCommRingCatIso σ.toRingEquiv).op
  let _ : IsIso (Spec.map (CommRingCat.ofHom σ.toRingHom)) := inferInstanceAs (IsIso specIso.hom)
  schemeIso (underlying φ) ≪≫ asIso (projection A σ)

/-- The field fixes the marked Abel pair up to a curve isomorphism and a
translation. The equality uses the actual Abel morphism on the underlying
schemes, so it remains meaningful for a semilinear isomorphism. -/
def AbelMarking {C : Scheme} {A : GroupScheme Qbar} (m : C ⟶ A.X.left) (z : Qbar) : Prop :=
  ∃ act : LevelThree.O →+* End A, Function.Injective act ∧
    ∀ σ : Qbar ≃ₐ[ℚ] Qbar, σ z = z →
      ∃ φ : A ≅ (conjugation σ.toRingEquiv).mapCommGrp.obj A,
        (act sqrtThree).asHom ≫ φ.hom =
          φ.hom ≫ (conjugation σ.toRingEquiv).mapCommGrp.map (act sqrtThree).asHom ∧
        ∃ (t : sections A) (c : C ≅ C),
          m ≫ (semilinearCorrection σ φ).inv = c.hom ≫ m ≫ (schemeIso (translation t)).inv

/-- The multiplicity may be unknown. The same integer occurs on both sides
because both pullbacks are taken from the original divisor. -/
theorem abel_marking_to_labelled {C : Scheme} {A : GroupScheme Qbar} (ab : IsAbelianScheme A)
    (m : C ⟶ A.X.left) (z : Qbar) (marked : AbelMarking m z) {L : A.X.left.Modules}
    (hL : L.IsInvertible) (s : 𝟙_ _ ⟶ L) (cartier : (Scheme.Modules.zeroSchemeIdeal s).IsInvertible)
    (n : ℕ) (power : Scheme.Modules.zeroSchemeIdeal s = m.ker^n) : LabelledModuli A L z := by
  obtain ⟨act, faithful, galois⟩ := marked
  refine ⟨act, faithful, ?_⟩
  intro σ fixed
  obtain ⟨φ, generator, t, c, diagram⟩ := galois σ fixed
  refine ⟨φ, generator, ?_⟩
  let a := schemeIso (translation t)
  let b := semilinearCorrection σ φ
  have image := abel_image_pullbacks m b a c diagram
  have ideal : (Scheme.Modules.zeroSchemeIdeal s).comap a.hom =
      (Scheme.Modules.zeroSchemeIdeal s).comap b.hom := by
    rw [power, JacobianVarieties.Picard.Proofs.ThetaVanishingSection.ThetaLocusAux.comap_pow,
      JacobianVarieties.Picard.Proofs.ThetaVanishingSection.ThetaLocusAux.comap_pow, image]
  obtain ⟨lines⟩ := pullback_line_of_ideal hL s cartier a b ideal
  exact (sameClass_translation ab L hL t).congr (Iso.refl _)
    (lines ≪≫ (Scheme.Modules.pullbackComp (underlying φ).hom.left (projection A σ)).symm.app L)

/-- Concrete application to the determinant of the actual signed geometric
Jacobian. No assertion about its line or its multiplicity enters the marking. -/
theorem signed_labelled_of_abel_marking {u : ℚ} (hu : u ∉ ZInQ.contactSet) (z : Qbar)
    (factor : CartierPrimeFactorization) (marked : AbelMarking (rigidMorphism hu).left z) :
    LabelledModuli (geometricJacobian hu) (signedThetaLine hu) z := by
  let J := (geometricJacobian hu).X
  have ab := isAbelianScheme_baseChange (algebraMap ℚ Qbar) (SixJacobian.isAbelian hu)
  let : Smooth J.hom := ab.smooth
  let : IsProper J.hom := ab.proper
  let : CompactSpace J.left := QuasiCompact.compactSpace_of_compactSpace J.hom
  let : IsLocallyNoetherian J.left := LocallyOfFiniteType.isLocallyNoetherian J.hom
  let : IsNoetherian J.left := ⟨⟩
  obtain ⟨n,_,power⟩ := factor J.left (fun x => Smooth.isRegularLocalRing_stalk (f:=J.hom) x)
    _ (signedThetaSection_cartier hu) (signed_theta_support_irreducible hu)
  rw [signedThetaSection_reduced_ideal] at power
  exact abel_marking_to_labelled ab _ z marked (signedThetaLine_invertible hu)
    (signedThetaSection hu) (signedThetaSection_cartier hu) n power

end
end ZInQBlueprint.CMRepair
#print axioms ZInQBlueprint.CMRepair.abel_image_pullbacks
#print axioms ZInQBlueprint.CMRepair.abel_marking_to_labelled
#print axioms ZInQBlueprint.CMRepair.signed_labelled_of_abel_marking
