import SixRationalQuotient
import SixModularJacobian
import SixAbelianHomDescent

/-! The input for Baba--Granath is on the modular-form equation. The
unmarked comparison to the printed algebraic Jacobian descends in the proof. -/
open CategoryTheory AlgebraicGeometry
open scoped ZInQBlueprint.NormalDescent
namespace ZInQBlueprint.ShimuraAtlas
open QuaternionLift NormalDescent AbelianModel ThetaClass
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000

/-- A representative of a point of the canonical, real-labelled Shimura
quotient, with its full endomorphism ring supplied over ℂ. The last clause
labels the real generator of the geometric coarse class. -/
structure PeriodRepresentative {M : Over (Spec (.of ℚ))} (C : CoarseInterpretation M)
    (chart : Line ⟶ M) (ι : Qbar →+* ℂ) (hom : HomBaseChange ι) (p : ConicPoint) where
  surface : GroupScheme Qbar
  abelian : IsAbelianScheme surface
  theta : surface.X.left.Modules
  principal : EffectivePrincipal abelian theta
  complexOrder : LevelThree.O ≃+* End ((baseChange ι).obj surface)
  represents : C.read (linePoint p.quotientCoordinate ≫ chart) =
    moduliClass (markedObject surface theta (descendedOrder hom surface abelian complexOrder).toRingHom)

/-- At an algebraic ordinary point the period torus is represented by an
abelian variety over Qbar. In the conclusion the complex isomorphism is to
the Picard variety of the *normalized Corollary 3.15 equation*. -/
def ModularComparison {M : Over (Spec (.of ℚ))} (C : CoarseInterpretation M)
    (chart : Line ⟶ M) (ι : Qbar →+* ℂ) (hom : HomBaseChange ι) : Prop :=
  ∀ (u : ℚ) (hu : u ∉ ZInQ.contactSet), OutsideCM (SixContact.J u) →
    ∃ (p : ConicPoint) (hp : FibrePoint u p) (e l : Qbar) (he : e^2 = -6) (hl : l^2=2)
      (w : PeriodRepresentative C chart ι hom p),
      Nonempty ((baseChange ι).obj w.surface ≅ (baseChange ι).obj (modularJacobian hu hp he hl))

theorem unpolarized_of_modular {M : Over (Spec (.of ℚ))} (C : CoarseInterpretation M)
    (chart : Line ⟶ M) (ι : Qbar →+* ℂ) (hom : HomBaseChange ι)
    (uniformization : ModularComparison C chart ι hom) :
    UnpolarizedPrintedComparison (shimuraClassMap C chart) := by
  intro u hu ordinary
  obtain ⟨p,hp,e,l,he,hl,w,⟨period⟩⟩ := uniformization u hu ordinary
  let U := shimuraClassMap C chart
  let o := descendedOrder hom w.surface w.abelian w.complexOrder
  let W : OrdinaryRepresentative U p := ⟨w.surface,w.abelian,w.theta,w.principal,o,w.represents⟩
  let A := (baseChange (algebraMap ℚ Qbar)).obj (SixJacobian.jacobian hu)
  have ab : IsAbelianScheme A := isAbelianScheme_baseChange _ (SixJacobian.isAbelian hu)
  let g := signedModularJacobian hu hp he hl
  let f : W.surface ≅ A := descendIso hom w.abelian ab
    (period ≪≫ (baseChange ι).mapIso g.symm)
  let d := rad (u:=u) (p:=p) (e:=e)
  have hd : d^2=6 := (rad_spec hu hp he hl).1
  exact ⟨p,hp,W,d,hd,⟨f ≪≫ g ≪≫ modularPrintedJacobian hu hp he hl⟩⟩

theorem printedField_of_modular {M : Over (Spec (.of ℚ))} (C : CoarseInterpretation M)
    (chart : Line ⟶ M) (ι : Qbar →+* ℂ) (hom : HomBaseChange ι)
    (uniformization : ModularComparison C chart ι hom) (uniquePol : UniqueD6Polarization)
    {u : ℚ} (hu : u ∉ ZInQ.contactSet) : PrintedField hu :=
  printedField_of_unpolarized _ uniquePol (unpolarized_of_modular C chart ι hom uniformization) hu

end
end ZInQBlueprint.ShimuraAtlas
#print axioms ZInQBlueprint.ShimuraAtlas.unpolarized_of_modular
#print axioms ZInQBlueprint.ShimuraAtlas.printedField_of_modular
