import ThetaDegreeOne
import RigidifiedAbel
import Nyll.AlgebraicCurves.Geometry.Picard.AbelJacobi.Pic0EquivPointsNontrivialH0IffEllPos
import Nyll.AlgebraicCurves.Geometry.Picard.Cohomology.IsoFibrePullbackFibreModuleTensorSectionTwistIso
import Nyll.AlgebraicCurves.Geometry.Picard.Theta.PullbackSectionThetaBundlePoincareEqZeroIff

/-! The same Picard point correspondence reads both the Abel morphism and the sections of its twisted Poincaré bundle. -/
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.RelPicard
open AlgebraicCurve NeronModelInfra MonoidalCategory GoodReductionJacobian
open scoped CategoryTheory.MonObj
namespace ZInQBlueprint.CanonicalTheta
open SixAbelMap
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1500000
variable {K F : Type} [Field K] [IsAlgClosed K] [Field F] [Algebra K F] [IsCurveOver K F]
  [Algebra.EssFiniteType K F]
variable (C : Over (Spec (.of K))) [IsProper C.hom] [SmoothOfRelativeDimension 1 C.hom]
  [GeometricallyIntegral C.hom] (b : base K ⟶ C)
abbrev schemePoint {c : Over (Spec (.of K))} (p : base K ⟶ c) :
    SchemeHomOver (𝟙 (Spec (.of K))) c.hom := ⟨p.left,p.w⟩

variable {J : RelativePic0Designation K C.hom}
  (h : RepresentsRelSubPic C.hom (schemePoint b) (algEquivZeroCut C.hom (schemePoint b)) J)
  (aj : SchemeHomOver C.hom J.toBase)
abbrev H0test (x : base K ⟶ Over.mk J.toBase) (d : ℕ) : Prop :=
    ∀ W : (pullback (pullback.snd C.hom J.toBase) x.left).TwoAffineOpenCover,
      Nontrivial (W.sectionsOf (fibreAt C.hom J.toBase x.left)
        (fibreModule C.hom J.toBase x.left (h.poincare.L ⊗ sectionTwist C.hom (schemePoint b) J.toBase d))).H0

set_option linter.unusedSectionVars false in
/-- Move nonvanishing through the fibre comparison and the two-affine Čech isomorphism.
The supplied equivalence is retained, so it can also be evaluated at point divisors. -/
theorem fibre_reading (x : base K ⟶ Over.mk J.toBase) (d : ℕ)
    (M : CurveModel K F) (e : M.C ≅ C.left) (T : Prop)
    (H : ∀ V : C.left.TwoAffineOpenCover, Nontrivial (V.sectionsOf C.hom
      ((Scheme.Modules.pullback (pullback.lift (𝟙 C.left) (C.hom ≫ x.left)
        (by rw [Category.id_comp,Category.assoc,show x.left ≫ J.toBase = 𝟙 (Spec (.of K)) from x.w, Category.comp_id]))).obj h.poincare.L ⊗
       (((schemePoint b).1.ker)^d).invModule)).H0 ↔ T) :
    H0test C b h x d ↔ T := by
  obtain ⟨φ, hφ, -, htwist⟩ := exists_iso_fibre_pullback_fibreModule_tensor_sectionTwist_iso
    C.hom (schemePoint b) J.toBase x.left x.w
  obtain ⟨eF⟩ := htwist h.poincare.L d
  obtain ⟨V₁⟩ := JacobianVarieties.Picard.Proofs.PicardEffectiveSections.AlgebraicGeometry.RelPicard.ThetaDictGlue.nonempty_twoAffineOpenCover_curveModel M
  obtain ⟨V⟩ := JacobianVarieties.Picard.Proofs.PicardEffectiveSections.AlgebraicGeometry.RelPicard.ThetaDictGlue.nonempty_twoAffineOpenCover_of_iso (e ≪≫ φ).symm V₁
  constructor
  · intro H0
    obtain ⟨a,b',hab⟩ := H0 V
    obtain ⟨U,-,-,⟨l⟩,-⟩ := Scheme.TwoAffineOpenCover.exists_linearEquiv_sectionsOf_of_iso
      C.hom (fibreAt C.hom J.toBase x.left) φ hφ V _ _ eF.symm
    exact (H U).mp ⟨l.symm a,l.symm b',fun eq => hab (l.symm.injective eq)⟩
  · intro hT V
    obtain ⟨U,-,-,⟨l⟩,-⟩ := Scheme.TwoAffineOpenCover.exists_linearEquiv_sectionsOf_of_iso
      C.hom (fibreAt C.hom J.toBase x.left) φ hφ V _ _ eF.symm
    obtain ⟨a,b',hab⟩ := (H U).mpr hT
    exact ⟨l a,l b',fun eq => hab (l.injective eq)⟩

/-- On the representing pointed group, the Brill–Noether test in degree one
cuts out precisely the normalized Abel image. -/
theorem H0_iff_abel (M : CurveModel K F) (e : M.C ≅ C.left) (he : e.hom ≫ C.hom = M.toBase)
    (H : IsPointedAbel C (schemePoint b) J h aj) (x : base K ⟶ Over.mk J.toBase) :
    H0test C b h x 1 ↔ ∃ p : base K ⟶ C, p.left ≫ aj.1 = x.left := by
  let ε := schemePoint b
  let B : {p : Spec (.of K) ⟶ M.C // p ≫ M.toBase = 𝟙 _} :=
    ⟨ε.1 ≫ e.inv, by rw [←he,Category.assoc,e.inv_hom_id_assoc]; exact ε.2⟩
  have heB : B.1 ≫ e.hom = ε.1 := by change (ε.1 ≫ e.inv) ≫ e.hom = _; simp
  let := (show RepresentsRelSubPic C.hom ε (algEquivZeroGroupCut C.hom ε).toSubPicCondition J from h).grpObj
  obtain ⟨pts,-,onept,sections⟩ :=
    exists_pic0_equiv_points_abelJacobi_of_curveModel K C.hom ε J h M e he B heB
  let bp := M.pointEquivPlace B
  have pointEq (q : {p : Spec (.of K) ⟶ M.C // p ≫ M.toBase = 𝟙 _}) :
      (pts (Pic0.mk (difference (M.pointEquivPlace q) bp))).left = (q.1 ≫ e.hom) ≫ aj.1 := by
    let y : SchemeHomOver (𝟙 (Spec (.of K))) C.hom :=
      ⟨q.1 ≫ e.hom, (Category.assoc _ _ _).trans ((congrArg (q.1 ≫ ·) he).trans q.2)⟩
    let D := difference (M.pointEquivPlace q) bp
    obtain ⟨eq₁⟩ := onept [q] D (by
      change Finsupp.single _ (1:ℤ) - Finsupp.single _ 1 = _
      simp [bp])
    let b' : SchemeHomOver (𝟙 (Spec (.of K))) C.hom :=
      ⟨𝟙 _ ≫ ε.1, by simp [ε]⟩
    have be : b' = ε := Subtype.ext (Category.id_comp _)
    obtain ⟨eq₂⟩ := H.2 K (𝟙 _) y
    change _ ≅ pointSubBasepointModule (a:=C.hom) y b' at eq₂
    rw [be] at eq₂
    have E : schemePoint (pts (Pic0.mk D)) =
        (⟨y.1 ≫ aj.1,(Category.assoc _ _ _).trans ((congrArg (y.1 ≫ ·) aj.2).trans y.2)⟩ :
          SchemeHomOver (𝟙 (Spec (.of K))) J.toBase) := by
      apply h.ext_of_iso
      exact ⟨eq₁ ≪≫ ρ_ (pointSubBasepointModule (a:=C.hom) y ε) ≪≫ eq₂.symm⟩
    exact congrArg Subtype.val E
  obtain ⟨D,hD⟩ := Pic0.mk_surjective (pts.symm x)
  have ex : pts (Pic0.mk D) = x := by rw [hD,pts.apply_symm_apply]
  rw [←ex,fibre_reading C b h _ 1 M e _ (sections D 1)]
  simp only [Nat.cast_one]
  rw [class_ell]
  constructor
  · rintro ⟨P,hP⟩
    obtain ⟨q,rfl⟩ := M.pointEquivPlace.surjective P
    refine ⟨Over.homMk (q.1 ≫ e.hom) ((Category.assoc _ _ _).trans ((congrArg (q.1 ≫ ·) he).trans q.2)),?_⟩
    rw [←hP]
    exact (pointEq q).symm
  · rintro ⟨p,hp⟩
    let q : {r : Spec (.of K) ⟶ M.C // r ≫ M.toBase = 𝟙 _} :=
      ⟨p.left ≫ e.inv,by rw [←he,Category.assoc,e.inv_hom_id_assoc];exact p.w⟩
    refine ⟨M.pointEquivPlace q,pts.injective ?_⟩
    apply Over.OverMorphism.ext
    rw [pointEq]
    change ((p.left ≫ e.inv) ≫ e.hom) ≫ aj.1 = _
    simpa only [Category.assoc,Iso.inv_hom_id_assoc] using hp
end
end ZInQBlueprint.CanonicalTheta
#print axioms ZInQBlueprint.CanonicalTheta.fibre_reading
#print axioms ZInQBlueprint.CanonicalTheta.H0_iff_abel
