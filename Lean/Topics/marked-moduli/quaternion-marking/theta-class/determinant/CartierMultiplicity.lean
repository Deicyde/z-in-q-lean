import MovingAbelImage

/-! A Cartier divisor with irreducible support on a regular noetherian
scheme is a positive multiple of its reduction. Both isomorphisms pull
back the same power, so descent of its line needs no multiplicity calculation. -/
open CategoryTheory CategoryTheory.MonoidalCategory AlgebraicGeometry
open scoped CategoryTheory.MonObj ZInQBlueprint.NormalDescent
namespace ZInQBlueprint.ThetaClass
open QuaternionMarking GeometricMarking AbelianModel NormalDescent CanonicalTheta SixAbelMap SixThetaRestriction BinaryCover
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- The one-component case of Stacks, Divisors, Lemma 31.16.11 (tag 0BCP).
Regularity is required at all stalks. -/
def CartierPrimeFactorization : Prop :=
  ∀ (X : Scheme.{0}) [IsNoetherian X], (∀ x : X, IsRegularLocalRing (X.presheaf.stalk x)) →
    ∀ (I : X.IdealSheafData), I.IsInvertible → IsIrreducible (I.support : Set X) →
      ∃ n : ℕ, 0 < n ∧ I = I.radical ^ n

private theorem comap_radical_iso {X Y : Scheme} (I : X.IdealSheafData) (a : Y ≅ X) :
    I.radical.comap a.hom = (I.comap a.hom).radical := by
  ext U : 2
  rw [Scheme.IdealSheafData.ideal_comap_of_isOpenImmersion,Scheme.IdealSheafData.radical_ideal,
      Scheme.IdealSheafData.radical_ideal,Scheme.IdealSheafData.ideal_comap_of_isOpenImmersion,
      Ideal.comap_radical]

theorem comap_eq_of_power_and_support {X Y : Scheme} (I : X.IdealSheafData) (n : ℕ)
    (power : I = I.radical ^ n) (a b : Y ≅ X)
    (same : (I.comap a.hom).support = (I.comap b.hom).support) :
    I.comap a.hom = I.comap b.hom := by
  have rad : (I.comap a.hom).radical = (I.comap b.hom).radical :=
    Scheme.IdealSheafData.vanishingIdeal_support.symm.trans
      ((congrArg Scheme.IdealSheafData.vanishingIdeal same).trans Scheme.IdealSheafData.vanishingIdeal_support)
  have pull (f : Y ≅ X) : I.comap f.hom = (I.comap f.hom).radical ^ n := by
    calc
      _ = (I.radical ^ n).comap f.hom := congrArg (fun J : X.IdealSheafData => J.comap f.hom) power
      _ = _ := by
        rw [JacobianVarieties.Picard.Proofs.ThetaVanishingSection.ThetaLocusAux.comap_pow,
          comap_radical_iso]
  exact (pull a).trans ((congrArg (· ^ n) rad).trans (pull b).symm)

variable {u : ℚ} (hu : u ∉ ZInQ.contactSet)

theorem signed_theta_support_irreducible :
    IsIrreducible ((Scheme.Modules.zeroSchemeIdeal (signedThetaSection hu)).support :
      Set (geometricJacobian hu).X.left) := by
  let := sourceIntegral hu
  let := paper_proper ℚ u
  let : IsProper (paperCurve u).hom := inferInstanceAs
    (IsProper (CategoryTheory.Limits.pullback.snd (paperModel ℚ u).hom (scalarMap ℚ Qbar)))
  have ab := isAbelianScheme_baseChange (algebraMap ℚ Qbar) (SixJacobian.isAbelian hu)
  let : IsProper (geometricJacobian hu).X.hom := ab.proper
  let m := rigidMorphism hu
  let : IsProper (m.left ≫ (geometricJacobian hu).X.hom) := by rw [Over.w]; infer_instance
  let : IsProper m.left := IsProper.of_comp m.left (geometricJacobian hu).X.hom
  rw [←Scheme.IdealSheafData.support_radical, signedThetaSection_reduced_ideal, Scheme.Hom.support_ker]
  change IsIrreducible (closure (Set.range m.left))
  apply IsIrreducible.closure
  simpa only [Set.image_univ] using
    (IrreducibleSpace.isIrreducible_univ (paperCurve u).left).image m.left m.left.continuous.continuousOn

theorem rational_of_prime_factorization (factor : CartierPrimeFactorization)
    (moved : DeckAbelSupport hu) : RationalThetaClass (hu:=hu) (signedThetaLine hu) := by
  let J := (geometricJacobian hu).X
  have ab := isAbelianScheme_baseChange (algebraMap ℚ Qbar) (SixJacobian.isAbelian hu)
  let : Smooth J.hom := ab.smooth
  let : IsProper J.hom := ab.proper
  let : CompactSpace J.left := QuasiCompact.compactSpace_of_compactSpace J.hom
  let : IsLocallyNoetherian J.left := LocallyOfFiniteType.isLocallyNoetherian J.hom
  let : IsNoetherian J.left := ⟨⟩
  let I := Scheme.Modules.zeroSchemeIdeal (signedThetaSection hu)
  obtain ⟨n,_,power⟩ := factor J.left (fun x => Smooth.isRegularLocalRing_stalk (f:=J.hom) x)
    I (signedThetaSection_cartier hu) (signed_theta_support_irreducible hu)
  apply rational_of_deck_translations hu
  intro σ
  obtain ⟨t,ht⟩ := moved σ
  let := isIso_jacobian_deck hu σ
  let a := schemeIso (translation t)
  let b := asIso (deck (SixJacobian.jacobian hu).X.hom σ)
  refine ⟨t,pullback_line_of_ideal (signedThetaLine_invertible hu) _ (signedThetaSection_cartier hu) a b ?_⟩
  apply comap_eq_of_power_and_support I n power
  apply support_eq_of_points J.hom
  intro p
  rw [Scheme.IdealSheafData.support_comap,Scheme.IdealSheafData.support_comap]
  change (p.left ≫ a.hom) (IsLocalRing.closedPoint Qbar) ∈ I.support ↔
    (p.left ≫ b.hom) (IsLocalRing.closedPoint Qbar) ∈ I.support
  refine (ThetaLinearSystem.field_vanishes_iff_mem (p.left ≫ a.hom)
    (signedThetaLine_invertible hu) (signedThetaSection hu)).symm.trans (Iff.trans ?_
    (ThetaLinearSystem.field_vanishes_iff_mem (p.left ≫ b.hom)
      (signedThetaLine_invertible hu) (signedThetaSection hu)))
  let v : JacobianPoints hu := Additive.ofMul p
  have eq := Set.ext_iff.mp (signedThetaSection_zeros hu) (v+t)
  have leftEq := congrArg (fun x : JacobianPoints hu =>
    Scheme.Modules.pullbackSection x.toMul.left (signedThetaSection hu) = 0) (translate_point v t)
  exact (Iff.of_eq leftEq).trans (eq.trans (ht v).symm)
end
end ZInQBlueprint.ThetaClass
#print axioms ZInQBlueprint.ThetaClass.comap_eq_of_power_and_support
#print axioms ZInQBlueprint.ThetaClass.signed_theta_support_irreducible
#print axioms ZInQBlueprint.ThetaClass.rational_of_prime_factorization
