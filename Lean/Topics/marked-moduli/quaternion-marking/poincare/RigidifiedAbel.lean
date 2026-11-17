import SixAbelDivisorMap

/-! A divisor presentation retaining its Poincaré line bundle under the canonical
pointed-to-unpointed comparison. This records which theta polarization is used. -/
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.RelPicard NeronModelInfra
open CategoryTheory.MonoidalCategory
open GoodReductionJacobian AlgebraicCurve JacobianVarieties.Picard.Unpointed
open JacobianVarieties.Picard.Proofs.PicardPointsTransport.PtsIntertwineIso
open scoped CategoryTheory.MonObj
namespace ZInQBlueprint.SixAbelMap
noncomputable section
set_option maxHeartbeats 1200000
variable {K F : Type} [Field K] [IsAlgClosed K] [Field F] [Algebra K F] [IsCurveOver K F]
variable (C : Over (Spec (.of K))) (M : CurveModel K F) (i : M.C ≅ C.left) (hbase : i.hom ≫ C.hom=M.toBase)

variable [IsProper C.hom] [SmoothOfRelativeDimension 1 C.hom] [GeometricallyIntegral C.hom]

/-- Equality with the class of the relative point divisor at every field-valued point,
using the specified Poincaré line bundle of the representing Picard scheme. -/
def IsPointedAbel (ε : SchemeHomOver (𝟙 (Spec (.of K))) C.hom)
    (J : RelativePic0Designation K C.hom) (h : RepresentsRelSubPic C.hom ε (algEquivZeroCut C.hom ε) J)
    (aj : SchemeHomOver C.hom J.toBase) : Prop :=
  ε.1 ≫ aj.1 = J.zeroSection ∧
  ∀ (L : Type) [Field L] (t : Spec (.of L) ⟶ Spec (.of K)) (x : SchemeHomOver t C.hom),
    Nonempty ((h.poincare.pullbackAlong
      ⟨x.1 ≫ aj.1, (Category.assoc _ _ _).trans ((congrArg (x.1 ≫ ·) aj.2).trans x.2)⟩).L ≅
      (RelEffCartierDiv.ofPoint C.hom x.1 x.2).lineBundle ⊗
        (RelEffCartierDiv.ofPoint C.hom (t ≫ ε.1)
          ((Category.assoc _ _ _).trans ((congrArg (t ≫ ·) ε.2).trans (Category.comp_id t)))).idealModule)


/-- The morphism agrees through the designated comparison with the actual classifying
morphism of the point divisors. An arbitrary additive automorphism of the group of
points cannot be inserted in this assertion. -/
def RepresentsPointDivisors (b : base K ⟶ C) (m : C ⟶ (groupScheme K C.hom).X) : Prop :=
  let ε : SchemeHomOver (𝟙 (Spec (.of K))) C.hom := ⟨b.left,b.w⟩
  ∃ (J : RelativePic0Designation K C.hom) (h : RepresentsRelSubPic C.hom ε (algEquivZeroCut C.hom ε) J)
    (aj : SchemeHomOver C.hom J.toBase), IsPointedAbel C ε J h aj ∧
    m ≫ ((presentation K C.hom).pointedComparisonOver ε h).hom = Over.homMk aj.1 aj.2

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
theorem exists_representing_abel (b : base K ⟶ C) :
    ∃ A : AbelPresentation C M i hbase (groupScheme K C.hom) b, RepresentsPointDivisors C b A.morphism := by
  let ε : SchemeHomOver (𝟙 (Spec (.of K))) C.hom := ⟨b.left,b.w⟩
  obtain ⟨J,⟨h⟩,hs,hp,hg⟩ := exists_representsRelSubPic_of_field K C.hom ε
  obtain ⟨aj,hzero,hAJ⟩ := exists_abelJacobi_of_representsRelSubPic K C.hom ε J h
  have H0 := (exists_pic0_equiv_points_of_representsRelSubPic_of_abelJacobi
    K C.hom ε J h hs hp hg aj hAJ).2 K (RingHom.id K) F M
  have ht : Spec.map (CommRingCat.ofHom (RingHom.id K)) = 𝟙 (Spec (.of K)) :=
    Spec.map_id (CommRingCat.of K)
  rw [ht] at H0
  let t := 𝟙 (Spec (.of K))
  let e₀ := asIso (pullback.fst C.hom t)
  let e := i ≪≫ e₀.symm
  have hfst : e.hom ≫ pullback.fst C.hom t = i.hom := by change (i.hom ≫ e₀.inv) ≫ e₀.hom = i.hom; simp
  have hsnd : e.hom ≫ pullback.snd C.hom t = M.toBase := by
    have hh := congrArg (e.hom ≫ ·) (pullback.condition (f:=C.hom) (g:=t))
    rw [←Category.assoc,hfst,hbase] at hh
    simpa only [t,Category.comp_id] using hh.symm
  obtain ⟨pts,hm,hpoint⟩ := H0 e.hom hsnd
  let E := (overHomEquivSchemeHomOver (base K) J.toBase).symm
  let := PGroup C ε h
  let Fpt : Pic0 K F ≃+ Additive (base K ⟶ Over.mk J.toBase) :=
    { toEquiv := pts.trans E
      map_add' := fun x y => by
        change E (pts (x+y)) = E (pts x) * E (pts y)
        rw [hm]
        rfl }
  let comp := (presentation K C.hom).pointedComparisonOver ε h
  let a : C ⟶ (groupScheme K C.hom).X := Over.homMk aj.1 aj.2 ≫ comp.inv
  refine ⟨⟨a, Fpt.trans (pointedPoints C ε h).symm,?_⟩, ?_⟩
  case refine_2 =>
    refine ⟨J,h,aj,⟨hzero,hAJ⟩,?_⟩
    change (Over.homMk aj.1 aj.2 ≫ comp.inv) ≫ comp.hom = _
    simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  intro p
  let lift (q : base K ⟶ C) : {z : Spec (.of K) ⟶ M.C // z ≫ M.toBase = 𝟙 _} :=
    ⟨q.left ≫ i.inv,by rw [←hbase,Category.assoc,i.inv_hom_id_assoc]; exact q.w⟩
  have hcomp (q : base K ⟶ C) : (lift q).1 ≫ e.hom ≫ pullback.fst C.hom t = q.left := by
    rw [hfst]; simp [lift]
  have hb : (lift b).1 ≫ e.hom ≫ pullback.fst C.hom t = t ≫ ε.1 := by
    rw [hcomp]; exact (Category.id_comp _).symm
  obtain ⟨D,hD,hpts⟩ := hpoint (lift p) (lift b) hb
  have heq : difference (pointPlace C M i hbase p) (pointPlace C M i hbase b) = D :=
    Subtype.ext hD.symm
  change (pointedPoints C ε h).symm (Fpt (Pic0.mk _)) = _
  rw [heq]
  apply (pointedPoints C ε h).injective
  rw [AddEquiv.apply_symm_apply]
  change E (pts (Pic0.mk D)) = (p ≫ a) ≫ comp.hom
  have back : (p ≫ a) ≫ comp.hom = p ≫ Over.homMk aj.1 aj.2 := by
    change (p ≫ Over.homMk aj.1 aj.2 ≫ comp.inv) ≫ comp.hom = _
    simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  rw [back]
  apply Over.OverMorphism.ext
  change (pts (Pic0.mk D)).1 = p.left ≫ aj.1
  exact hpts.trans (by simpa only [Category.assoc] using congrArg (· ≫ aj.1) (hcomp p))

end
end ZInQBlueprint.SixAbelMap
#print axioms ZInQBlueprint.SixAbelMap.RepresentsPointDivisors
#print axioms ZInQBlueprint.SixAbelMap.exists_representing_abel
