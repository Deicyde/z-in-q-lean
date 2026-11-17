import SixAbelPointedTransport
import Nyll.AlgebraicCurves.Geometry.Picard.Representability.Pic0EquivPointsPicardRepresentability
import Nyll.AlgebraicCurves.Geometry.Picard.Representability.AbelJacobiPicardRepresentability
import Nyll.JacobianVarieties.Picard.Points.PullbackHomPointsEqPic0Congr

/-! The divisor-class identification and the Abel morphism over an algebraically closed field. -/
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.RelPicard NeronModelInfra
open GoodReductionJacobian AlgebraicCurve JacobianVarieties.Picard.Unpointed
open JacobianVarieties.Picard.Proofs.PicardPointsTransport.PtsIntertwineIso
open scoped CategoryTheory.MonObj
namespace ZInQBlueprint.SixAbelMap
noncomputable section
set_option maxHeartbeats 1200000
variable {K F : Type} [Field K] [IsAlgClosed K] [Field F] [Algebra K F] [IsCurveOver K F]
variable (C : Over (Spec (.of K))) (M : CurveModel K F) (i : M.C ≅ C.left) (hbase : i.hom ≫ C.hom=M.toBase)

def pointPlace : (base K ⟶ C) ≃ Place K F := by
  let p : (base K ⟶ C) ≃ {z : Spec (.of K) ⟶ M.C // z ≫ M.toBase = 𝟙 _} :=
    { toFun := fun x => ⟨x.left ≫ i.inv,by rw [←hbase,Category.assoc,i.inv_hom_id_assoc];exact x.w⟩
      invFun := fun z => Over.homMk (z.1 ≫ i.hom) (by rw [Category.assoc,hbase];exact z.2)
      left_inv := fun x => by ext; simp
      right_inv := fun z => Subtype.ext (by simp) }
  exact p.trans M.pointEquivPlace

abbrev difference (P Q : Place K F) : Divisor.degZero (K:=K) (F:=F) :=
  gen (fun v => IsCurveOver.deg_eq_one_of_isAlgClosed v) Q P

/-- A single geometric morphism and the divisor class map agree at every geometric point. -/
structure AbelPresentation (V : AbelianModel.GroupScheme K) (b : base K ⟶ C) where
  morphism : C ⟶ V.X
  divisorEquiv : Pic0 K F ≃+ Additive (base K ⟶ V.X)
  point_class (p : base K ⟶ C) :
    divisorEquiv (Pic0.mk (difference (pointPlace C M i hbase p) (pointPlace C M i hbase b))) =
      Additive.ofMul (p ≫ morphism)

variable [IsProper C.hom] [SmoothOfRelativeDimension 1 C.hom] [GeometricallyIntegral C.hom]

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
theorem exists_abelPresentation (b : base K ⟶ C) :
    Nonempty (AbelPresentation C M i hbase (groupScheme K C.hom) b) := by
  let ε : SchemeHomOver (𝟙 (Spec (.of K))) C.hom := ⟨b.left,b.w⟩
  obtain ⟨J,⟨h⟩,hs,hp,hg⟩ := exists_representsRelSubPic_of_field K C.hom ε
  obtain ⟨aj,_,hAJ⟩ := exists_abelJacobi_of_representsRelSubPic K C.hom ε J h
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
  refine ⟨⟨a, Fpt.trans (pointedPoints C ε h).symm,?_⟩⟩
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
#print axioms ZInQBlueprint.SixAbelMap.pointPlace
#print axioms ZInQBlueprint.SixAbelMap.exists_abelPresentation
