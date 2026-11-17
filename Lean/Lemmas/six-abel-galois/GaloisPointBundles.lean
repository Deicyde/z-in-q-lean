import SixAbelDivisorMap

/-! The class of the difference of two sections on the unpointed Picard functor. -/
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory AlgebraicGeometry
open AlgebraicGeometry.RelPicard NeronModelInfra Opposite
namespace ZInQBlueprint.AbelGalois
noncomputable section
set_option backward.isDefEq.respectTransparency false
variable {R : Type} [CommRing R] {C : Scheme} (c : C ⟶ Spec (.of R))
  [IsSeparated c] [SmoothOfRelativeDimension 1 c]
variable {T T' : Scheme} {t : T ⟶ Spec (.of R)} {t' : T' ⟶ Spec (.of R)}

def differenceBundle (p q : SchemeHomOver t c) : Unrigidified.LineBundle c t :=
  let P := RelEffCartierDiv.ofPoint c p.1 p.2
  let Q := RelEffCartierDiv.ofPoint c q.1 q.2
  ⟨P.lineBundle ⊗ Q.idealModule,
    (RelEffCartierDiv.isInvertible_I P).isInvertible_invModule.tensor (RelEffCartierDiv.isInvertible_I Q).isInvertible_module⟩

def move (s : SchemeHomOver t' t) (p : SchemeHomOver t c) : SchemeHomOver t' c :=
  ⟨s.1 ≫ p.1, (Category.assoc _ _ _).trans ((congrArg (s.1 ≫ ·) p.2).trans s.2)⟩

theorem point_module_pull (s : SchemeHomOver t' t) (p : SchemeHomOver t c) :
    let P := RelEffCartierDiv.ofPoint c p.1 p.2
    let Q := RelEffCartierDiv.ofPoint c (move c s p).1 (move c s p).2
    Nonempty ((Scheme.Modules.pullback (baseChangeSnd c s)).obj P.lineBundle ≅ Q.lineBundle) ∧
    Nonempty ((Scheme.Modules.pullback (baseChangeSnd c s)).obj P.idealModule ≅ Q.idealModule) := by
  intro P Q
  let f := baseChangeSnd c s
  have eq : P.I.comap f = Q.I :=
    congrArg RelEffCartierDiv.I (RelEffCartierDiv.pullbackAlong_ofPoint c p.1 p.2 s.1 s.2)
  have hi := RelEffCartierDiv.isInvertible_I P
  have hj := RelEffCartierDiv.isInvertible_I Q
  have hI : (P.I.comap f).IsInvertible := eq.symm ▸ hj
  obtain ⟨a⟩ := Scheme.IdealSheafData.IsInvertible.nonempty_pullback_invModule_iso f hi hI
  let := Scheme.IdealSheafData.IsInvertible.isIso_pullbackModuleComparison f hi hI
  exact ⟨⟨a ≪≫ eqToIso (congrArg Scheme.IdealSheafData.invModule eq)⟩,
    ⟨asIso (P.I.pullbackModuleComparison f) ≪≫ eqToIso (congrArg Scheme.IdealSheafData.module eq)⟩⟩

theorem difference_pull (s : SchemeHomOver t' t) (p q : SchemeHomOver t c) :
    Nonempty ((Unrigidified.pullbackAlong s (differenceBundle c p q)).1 ≅
      (differenceBundle c (move c s p) (move c s q)).1) := by
  obtain ⟨a⟩ := (point_module_pull c s p).1
  obtain ⟨b⟩ := (point_module_pull c s q).2
  exact ⟨Scheme.Modules.pullbackTensorObjIso _ _ _ ≪≫ (a ⊗ᵢ b)⟩

theorem difference_class_pull (s : SchemeHomOver t' t) (p q : SchemeHomOver t c) :
    Unrigidified.classesMap s (Quot.mk _ (differenceBundle c p q)) =
      Quot.mk _ (differenceBundle c (move c s p) (move c s q)) := by
  obtain ⟨e⟩ := difference_pull c s p q
  exact Quot.sound (Unrigidified.baseTwist_of_iso e)
end
end ZInQBlueprint.AbelGalois
#print axioms ZInQBlueprint.AbelGalois.point_module_pull
#print axioms ZInQBlueprint.AbelGalois.difference_pull
#print axioms ZInQBlueprint.AbelGalois.difference_class_pull
