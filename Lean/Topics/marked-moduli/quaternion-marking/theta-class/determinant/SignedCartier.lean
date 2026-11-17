import CartierSupport

/-! Moving the geometric base point in the Abel embedding of the signed
curve. A pointwise transport of its reduced divisor suffices for descent
of its Néron–Severi class. -/
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory AlgebraicGeometry
open scoped CategoryTheory.MonObj ZInQBlueprint.NormalDescent
namespace ZInQBlueprint.ThetaClass
open QuaternionMarking GeometricMarking AbelianModel NormalDescent SixThetaRestriction CanonicalTheta
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable {u : ℚ} (hu : u ∉ ZInQ.contactSet)

/-- On the integral signed Jacobian the section determines an effective
Cartier divisor. Its ideal can be invertible even before reducedness is known. -/
theorem signedThetaSection_cartier : (Scheme.Modules.zeroSchemeIdeal (signedThetaSection hu)).IsInvertible := by
  have ab := isAbelianScheme_baseChange (algebraMap ℚ Qbar) (SixJacobian.isAbelian hu)
  let : Smooth (geometricJacobian hu).X.hom := ab.smooth
  let : GeometricallyConnected (geometricJacobian hu).X.hom := ab.geometricallyConnected
  let := geometricallyIntegral_of_smooth_connected (geometricJacobian hu).X.hom
  let := GeometricallyIntegral.isIntegral_of_subsingleton (geometricJacobian hu).X.hom
  -- The local trivialization argument is also used in NYLL's NonzeroSectionCartier.
  let X := (geometricJacobian hu).X.left
  let s := signedThetaSection hu
  let I := Scheme.Modules.zeroSchemeIdeal s
  have hL := signedThetaLine_invertible hu
  have generic := hL.genericPoint_notMem_support_zeroSchemeIdeal s (signedThetaSection_ne_zero hu)
  intro x
  obtain ⟨U,hx,-,⟨e⟩⟩ := hL.exists_restrict_iso (V:=⊤) (x:=x) trivial
  let V := X.affineBasicOpen (U:=U) (1 : Γ(X,U.1))
  have hxV : x ∈ V.1 := by
    change x ∈ X.basicOpen (1 : Γ(X,U.1))
    simpa only [Scheme.basicOpen_one] using hx
  let : Nonempty V.1 := ⟨⟨x,hxV⟩⟩
  have inc : V.1 ≤ U.1 := X.basicOpen_le _
  let g := X.presheaf.map (homOfLE inc).op (Scheme.Modules.coeff s U.1 e.hom)
  have generator : I.ideal V = Ideal.span {g} := by
    rw [←I.map_ideal inc,((hL.coeffIdeal_le_and_ideal_zeroSchemeIdeal_eq s).2 U e).1,
      Ideal.map_span,Set.image_singleton]
    rfl
  refine ⟨U,1,hxV,g,mem_nonZeroDivisors_iff_ne_zero.mpr ?_,generator⟩
  intro hg
  have hη := ((genericPoint_spec X).mem_open_set_iff V.1.isOpen).mpr ⟨x,Set.mem_univ x,hxV⟩
  apply generic
  apply (Scheme.IdealSheafData.mem_support_iff_of_mem (I:=I) (U:=V) hη).mpr
  rw [generator,hg,Ideal.span_singleton_zero,Scheme.mem_zeroLocus_iff]
  intro f hf
  rw [show f=0 from hf,Scheme.basicOpen_zero]
  exact fun h => h

/-- Pulling back by the rational descent comparison followed by the first
projection gives an isomorphism of the underlying schemes of the Jacobian. -/
theorem isIso_jacobian_deck (σ : Qbar ≃ₐ[ℚ] Qbar) : IsIso (deck (SixJacobian.jacobian hu).X.hom σ) := by
  let A := SixJacobian.jacobian hu
  let E := (CommGrp.forget _ ⋙ Over.forget _).mapIso (rationalGroupComparison A σ)
  let ringIso : CommRingCat.of Qbar ≅ CommRingCat.of Qbar := RingEquiv.toCommRingCatIso σ.toRingEquiv
  let specIso := Scheme.Spec.mapIso ringIso.op
  let : IsIso (Spec.map (CommRingCat.ofHom σ.toRingHom)) := inferInstanceAs (IsIso specIso.hom)
  rw [←comparison_fst A σ]
  exact inferInstanceAs (IsIso (E.hom ≫ pullback.fst (geometricJacobian hu).X.hom (Spec.map (CommRingCat.ofHom σ.toRingHom))))

/-- The Galois action on Abel points, in the contravariant pullback convention.
Vanishing is tested on the composite with the semilinear deck map, whose
domain has the original geometric point. -/
def DeckAbelSupport : Prop :=
  ∀ σ : Qbar ≃ₐ[ℚ] Qbar, ∃ t : JacobianPoints hu, ∀ p : JacobianPoints hu,
    Scheme.Modules.pullbackSection (p.toMul.left ≫ deck (SixJacobian.jacobian hu).X.hom σ)
      (signedThetaSection hu) = 0 ↔ p+t ∈ Set.range (SixAbelMap.rigidDivisors hu).abel

/-- If the Abel translates are conjugate and the determinant divisor is reduced,
then its class is invariant. This comparison allows the chosen base point to move. -/
theorem rational_of_abel_support
    [IsReduced (Scheme.Modules.zeroSchemeIdeal (signedThetaSection hu)).subscheme]
    (moved : DeckAbelSupport hu) : RationalThetaClass (hu:=hu) (signedThetaLine hu) := by
  have ab := isAbelianScheme_baseChange (algebraMap ℚ Qbar) (SixJacobian.isAbelian hu)
  let : Smooth (geometricJacobian hu).X.hom := ab.smooth
  apply rational_of_deck_translations hu
  intro σ
  obtain ⟨t,ht⟩ := moved σ
  let := isIso_jacobian_deck hu σ
  let a := schemeIso (translation t)
  let b := asIso (deck (SixJacobian.jacobian hu).X.hom σ)
  refine ⟨t,pullback_line_of_ideal (signedThetaLine_invertible hu) _ (signedThetaSection_cartier hu) a b ?_⟩
  apply comap_eq_of_reduced_points (geometricJacobian hu).X.hom (signedThetaLine_invertible hu)
  intro p
  let v : JacobianPoints hu := Additive.ofMul p
  have eq := Set.ext_iff.mp (signedThetaSection_zeros hu) (v+t)
  have leftEq := congrArg (fun x : JacobianPoints hu =>
    Scheme.Modules.pullbackSection x.toMul.left (signedThetaSection hu) = 0) (translate_point v t)
  exact (Iff.of_eq leftEq).trans (eq.trans (ht v).symm)

end
end ZInQBlueprint.ThetaClass
#print axioms ZInQBlueprint.ThetaClass.signedThetaSection_cartier
#print axioms ZInQBlueprint.ThetaClass.isIso_jacobian_deck
#print axioms ZInQBlueprint.ThetaClass.rational_of_abel_support
