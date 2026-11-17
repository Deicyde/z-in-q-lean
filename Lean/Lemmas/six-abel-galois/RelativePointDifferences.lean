import GaloisPointBundles

/-! A divisor P-Q belongs to the identity component on *every* geometric fibre of a smooth curve. -/
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory AlgebraicGeometry
open AlgebraicGeometry.RelPicard NeronModelInfra Opposite
namespace ZInQBlueprint.AbelGalois
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable {R : Type} [CommRing R] {C : Scheme} (c : C ⟶ Spec (.of R))
  [IsSeparated c] [SmoothOfRelativeDimension 1 c] [GeometricallyIntegral c]

private theorem class_on_field {k : Type} [Field k] (t : Spec (.of k) ⟶ Spec (.of R))
    (p q : SchemeHomOver t c) :
    IsAlgEquivZero (pullback.snd c t) (differenceBundle c p q).1 := by
  let a := pullback.snd c t
  let pt (x : SchemeHomOver t c) : SchemeHomOver (𝟙 (Spec (.of k))) a :=
    ⟨graphOver c x.1 x.2, graphOver_snd ..⟩
  let : SmoothOfRelativeDimension 1 a := SmoothOfRelativeDimension.pullback_snd 1 c t
  let : GeometricallyIntegral a := inferInstanceAs (GeometricallyIntegral (pullback.snd c t))
  let f := pullback.fst a (𝟙 (Spec (.of k)))
  let ideal (x : SchemeHomOver t c) := (RelEffCartierDiv.ofPoint c x.1 x.2).I
  let after (x : SchemeHomOver t c) := (RelEffCartierDiv.ofPoint a (pt x).1 (pt x).2).I
  have heq (x : SchemeHomOver t c) : (ideal x).comap f = after x :=
    JacobianVarieties.Picard.Proofs.RelEffCartierDiv_isAlgEquivZero_twistModule_fibre.AlgebraicGeometry.K2Aux.ker_comap_fst_eq_ofPoint_I a (pt x).1 (pt x).2
  have beforeInv (x : SchemeHomOver t c) : (ideal x).IsInvertible := RelEffCartierDiv.isInvertible_I _
  have afterInv (x : SchemeHomOver t c) : ((ideal x).comap f).IsInvertible :=
    (heq x).symm ▸ RelEffCartierDiv.isInvertible_I _
  obtain ⟨plus⟩ := Scheme.IdealSheafData.IsInvertible.nonempty_pullback_invModule_iso f (beforeInv p) (afterInv p)
  let := Scheme.IdealSheafData.IsInvertible.isIso_pullbackModuleComparison f (beforeInv q) (afterInv q)
  apply IsAlgEquivZero.of_iso_pointSubBasepoint (pt p) (pt q)
  exact Scheme.Modules.pullbackTensorObjIso f _ _ ≪≫
    ((plus ≪≫ eqToIso (congrArg Scheme.IdealSheafData.invModule (heq p))) ⊗ᵢ
      (asIso ((ideal q).pullbackModuleComparison f) ≪≫ eqToIso (congrArg Scheme.IdealSheafData.module (heq q))))

theorem difference_fibrewise {T : Scheme} {t : T ⟶ Spec (.of R)} (p q : SchemeHomOver t c) :
    Unrigidified.FibrewiseZero (differenceBundle c p q) := by
  intro k _ _ s
  let h : SchemeHomOver (s ≫ t) t := ⟨s,rfl⟩
  let e := pullbackLeftPullbackSndIso c t s
  have hf : e.hom ≫ baseChangeSnd c h = pullback.fst (pullback.snd c t) s := by
    apply pullback.hom_ext
    · simp only [e,baseChangeSnd,Category.assoc,pullback.lift_fst,Category.comp_id,
        pullbackLeftPullbackSndIso_hom_fst]
    · simp only [e,baseChangeSnd,h,Category.assoc,pullback.lift_snd,
        pullbackLeftPullbackSndIso_hom_snd_assoc,pullback.condition]
  have h0 := class_on_field c (s ≫ t) (move c h p) (move c h q)
  obtain ⟨v⟩ := difference_pull c h p q
  have h1 := (h0.of_iso v.symm).pullback e.hom (pullbackLeftPullbackSndIso_hom_snd c t s)
  exact h1.of_iso ((Scheme.Modules.pullbackComp _ _).app _ ≪≫
    (Scheme.Modules.pullbackCongr hf).app _)

end
end ZInQBlueprint.AbelGalois
#print axioms ZInQBlueprint.AbelGalois.difference_fibrewise
