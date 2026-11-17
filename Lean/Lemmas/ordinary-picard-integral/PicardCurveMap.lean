import RationalJacobian
import Nyll.AlgebraicCurves.Geometry.Picard.Rigidification.UnrigidifiedGroup

/-! Pullback along an isomorphism of the *curve* induces the usual isomorphism
of the relative Picard-zero group presheaves on its base. -/
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra Opposite
open scoped MonoidalCategory
open AlgebraicGeometry.RelPicard AlgebraicGeometry.RelPicard.Unrigidified
namespace ZInQBlueprint.IntegralPicard.CurveMap
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {R : Type} [CommRing R] {C D : Over (Spec (.of R))} (φ : C ⟶ D)
variable {T : Scheme.{0}} (t : T ⟶ Spec (.of R))

private abbrev onTest := ((Over.pullback t).map φ).left

@[reassoc] private theorem onTest_fst : onTest φ t ≫ pullback.fst D.hom t =
    pullback.fst C.hom t ≫ φ.left := pullback.lift_fst _ _ _
@[reassoc] private theorem onTest_snd : onTest φ t ≫ pullback.snd D.hom t =
    pullback.snd C.hom t := ((Over.pullback t).map φ).w

private def pullBundle (M : LineBundle D.hom t) : LineBundle C.hom t :=
  ⟨(Scheme.Modules.pullback (onTest φ t)).obj M.1, M.2.pullback _⟩

private theorem baseTwist_pullBundle {M N : LineBundle D.hom t} (h : BaseTwist D.hom t M N) :
    BaseTwist C.hom t (pullBundle φ t M) (pullBundle φ t N) := by
  obtain ⟨Q,hQ,⟨e⟩⟩ := h
  let f := onTest φ t
  exact ⟨Q,hQ,⟨(Scheme.Modules.pullback f).mapIso e ≪≫
    Scheme.Modules.pullbackTensorObjIso f _ _ ≪≫
    (((Scheme.Modules.pullbackComp _ _).app Q ≪≫
       (Scheme.Modules.pullbackCongr (onTest_snd φ t)).app Q) ⊗ᵢ Iso.refl _)⟩⟩

private def pullClass : Classes D.hom t → Classes C.hom t :=
  Quot.map (pullBundle φ t) (fun _ _ h => baseTwist_pullBundle φ t h)

private theorem fibrewise_pull {M : LineBundle D.hom t} (hM : FibrewiseZero M) :
    FibrewiseZero (pullBundle φ t M) := by
  intro k _ _ z
  let m := (Over.pullback z).map ((Over.pullback t).map φ)
  have hs : m.left ≫ fibreAt D.hom t z = fibreAt C.hom t z := m.w
  have hf : m.left ≫ pullback.fst (pullback.snd D.hom t) z =
      pullback.fst (pullback.snd C.hom t) z ≫ onTest φ t := pullback.lift_fst _ _ _
  exact ((hM k z).pullback m.left hs).of_iso <|
    (Scheme.Modules.pullbackComp _ _).app _ ≪≫
    (Scheme.Modules.pullbackCongr hf).app _ ≪≫ ((Scheme.Modules.pullbackComp _ _).app _).symm

private theorem zero_pull (x : Classes D.hom t) (hx : classesZero t x) :
    classesZero t (pullClass φ t x) := by
  induction x using Quot.ind with | _ M => exact fibrewise_pull φ t hx

private def pullPoint (T : Over (Spec (.of R))) :
    (zeroCommGrpPresheaf D.hom).obj (op T) →* (zeroCommGrpPresheaf C.hom).obj (op T) :=
  MonoidHom.mk' (fun x => ⟨pullClass φ T.hom x.1, zero_pull φ T.hom x.1 x.2⟩) (by
    rintro ⟨x,hx⟩ ⟨y,hy⟩
    apply Subtype.ext
    induction x using Quot.ind with
    | _ M =>
      induction y using Quot.ind with
      | _ N =>
        exact Quot.sound (baseTwist_of_iso
          (Scheme.Modules.pullbackTensorObjIso (onTest φ T.hom) M.1 N.1)))

@[reassoc] private theorem baseSnd_fst {C : Scheme} (c : C ⟶ Spec (.of R))
    {T' : Scheme} {t' : T' ⟶ Spec (.of R)} (ψ : SchemeHomOver t' t) :
    baseChangeSnd c ψ ≫ pullback.fst c t = pullback.fst c t' := pullback.lift_fst _ _ _

private theorem onTest_natural {T' : Scheme.{0}} {t' : T' ⟶ Spec (.of R)}
    (ψ : SchemeHomOver t' t) :
    baseChangeSnd C.hom ψ ≫ onTest φ t = onTest φ t' ≫ baseChangeSnd D.hom ψ := by
  apply pullback.hom_ext
  · simp only [Category.assoc,onTest_fst,baseSnd_fst_assoc,baseSnd_fst]
  · simp only [Category.assoc,onTest_snd,baseChangeSnd_snd,onTest_snd_assoc]

def pull (φ : C ⟶ D) : zeroCommGrpPresheaf D.hom ⟶ zeroCommGrpPresheaf C.hom where
  app T := by
    letI : CommGroup ((zeroPresheaf D.hom).obj T) := zeroCommGroup T
    letI : CommGroup ((zeroPresheaf C.hom).obj T) := zeroCommGroup T
    exact CommGrpCat.ofHom (pullPoint φ T.unop)
  naturality {X Y} ψ := by
    ext x
    rcases x with ⟨x,hx⟩
    apply Subtype.ext
    induction x using Quot.ind with
    | _ M =>
      let q : SchemeHomOver Y.unop.hom X.unop.hom := ⟨ψ.unop.left, Over.w ψ.unop⟩
      exact Quot.sound (baseTwist_of_iso
        ((Scheme.Modules.pullbackComp (onTest φ Y.unop.hom) (baseChangeSnd D.hom q)).app M.1 ≪≫
          (Scheme.Modules.pullbackCongr (onTest_natural φ X.unop.hom q).symm).app M.1 ≪≫
          ((Scheme.Modules.pullbackComp (baseChangeSnd C.hom q) (onTest φ X.unop.hom)).app M.1).symm))

/-- The Picard presheaf is contravariant with respect to isomorphisms of the curve. -/
def pullIso (e : C ≅ D) : zeroCommGrpPresheaf D.hom ≅ zeroCommGrpPresheaf C.hom where
  hom := pull e.hom
  inv := pull e.inv
  hom_inv_id := by
    ext T x
    rcases x with ⟨x,hx⟩
    apply Subtype.ext
    induction x using Quot.ind with
    | _ M =>
      let eT := (Over.forget _).mapIso ((Over.pullback T.unop.hom).mapIso e)
      exact Quot.sound (baseTwist_of_iso
        ((Scheme.Modules.pullbackComp eT.inv eT.hom).app M.1 ≪≫
          (Scheme.Modules.pullbackCongr eT.inv_hom_id).app M.1 ≪≫
          (Scheme.Modules.pullbackId _).app M.1))
  inv_hom_id := by
    ext T x
    rcases x with ⟨x,hx⟩
    apply Subtype.ext
    induction x using Quot.ind with
    | _ M =>
      let eT := (Over.forget _).mapIso ((Over.pullback T.unop.hom).mapIso e)
      exact Quot.sound (baseTwist_of_iso
        ((Scheme.Modules.pullbackComp eT.hom eT.inv).app M.1 ≪≫
          (Scheme.Modules.pullbackCongr eT.hom_inv_id).app M.1 ≪≫
          (Scheme.Modules.pullbackId _).app M.1))

end
end ZInQBlueprint.IntegralPicard.CurveMap
#print axioms ZInQBlueprint.IntegralPicard.CurveMap.pull
#print axioms ZInQBlueprint.IntegralPicard.CurveMap.pullIso
