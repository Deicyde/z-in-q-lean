import Mathlib.AlgebraicGeometry.Birational.RationalMap
import Mathlib.AlgebraicGeometry.ValuativeCriterion

/-! Extension of generic maps from integral schemes whose local rings are valuation rings. -/
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace ZInQBlueprint.CurveExtension
open AlgebraicGeometry.Scheme
noncomputable section
variable {X Y S : Scheme} [AlgebraicGeometry.IsIntegral X]
private abbrev genericArrow (X : Scheme) [IrreducibleSpace X] := X.fromSpecStalk (genericPoint X)
private abbrev localToGeneric (X : Scheme) [IrreducibleSpace X] (x : X) :=
  Spec.map (CommRingCat.ofHom (algebraMap (X.presheaf.stalk x) X.functionField))
theorem local_generic_triangle (x : X) :
    localToGeneric X x ≫ X.fromSpecStalk x = genericArrow X :=
  Scheme.SpecMap_stalkSpecializes_fromSpecStalk (genericPoint_specializes x)

private theorem local_generic_partial (g : X.PartialMap Y) {x : X} (hx : x ∈ g.domain) :
    localToGeneric X x ≫ g.fromSpecStalkOfMem hx = g.fromFunctionField := by
  change localToGeneric X x ≫ g.domain.fromSpecStalkOfMem x hx ≫ g.hom = _ ≫ g.hom
  rw [← Category.assoc]
  congr 1
  apply (cancel_mono g.domain.ι).mp
  rw [Category.assoc, Scheme.Opens.fromSpecStalkOfMem_ι, Scheme.Opens.fromSpecStalkOfMem_ι]
  exact local_generic_triangle x

set_option maxHeartbeats 1200000 in
/-- A map from the generic point to a proper target extends to the stalk at a valuation point. -/
theorem extend_stalk (sX : X ⟶ S) (sY : Y ⟶ S) [IsProper sY]
    (φ : Spec X.functionField ⟶ Y) (hφ : φ ≫ sY = genericArrow X ≫ sX)
    (x : X) [ValuationRing (X.presheaf.stalk x)] :
    ∃ g : Spec (X.presheaf.stalk x) ⟶ Y, localToGeneric X x ≫ g = φ ∧ g ≫ sY = X.fromSpecStalk x ≫ sX := by
  have h := (inferInstance : UniversallyClosed sY)
  rw [UniversallyClosed.eq_valuativeCriterion] at h
  have dom : IsDomain (X.presheaf.stalk x) :=
    Function.Injective.isDomain (algebraMap (X.presheaf.stalk x) X.functionField)
      (IsFractionRing.injective _ _)
  let sq : ValuativeCommSq sY := {
    R := X.presheaf.stalk x
    commRing := inferInstanceAs (CommRing (X.presheaf.stalk x))
    domain := dom
    valuationRing := ‹ValuationRing (X.presheaf.stalk x)›
    K := X.functionField
    field := inferInstanceAs (Field X.functionField)
    algebra := stalkFunctionFieldAlgebra X x
    isFractionRing := inferInstanceAs (IsFractionRing (X.presheaf.stalk x) X.functionField)
    i₁ := φ
    i₂ := X.fromSpecStalk x ≫ sX
    commSq := ⟨hφ.trans ((Category.assoc _ _ _).symm.trans
      (congrArg (fun k => k ≫ sX) (local_generic_triangle x))).symm⟩ }
  obtain ⟨g,hg,hb⟩ := (h.1 sq).exists_lift
  exact ⟨g,hg,hb⟩

/-- Every valuation point belongs to the maximal domain of this rational map. -/
theorem valuationPoint_mem_domain (sX : X ⟶ S) (sY : Y ⟶ S) [IsProper sY]
    (φ : Spec X.functionField ⟶ Y) (hφ : φ ≫ sY = genericArrow X ≫ sX)
    (x : X) [ValuationRing (X.presheaf.stalk x)] :
    x ∈ (Scheme.RationalMap.ofFunctionField sX sY φ hφ).domain := by
  obtain ⟨g,hg,hb⟩ := extend_stalk sX sY φ hφ x
  let f := Scheme.PartialMap.ofFromSpecStalk sX sY g hb
  have hx : x ∈ f.domain := Scheme.PartialMap.mem_domain_ofFromSpecStalk sX sY g hb
  refine Scheme.RationalMap.mem_domain.mpr ⟨f,hx,?_⟩
  apply Scheme.RationalMap.eq_of_fromFunctionField_eq
  rw [Scheme.RationalMap.fromFunctionField_ofFunctionField]
  change f.fromFunctionField = φ
  rw [← local_generic_partial f hx, Scheme.PartialMap.fromSpecStalkOfMem_ofFromSpecStalk]
  exact hg

private theorem global_of_full_domain (f : X.RationalMap Y) [Y.IsSeparated] (hd : f.domain = ⊤) :
    ∃ g : X ⟶ Y, g.toRationalMap = f := by
  have hb (p : X.PartialMap Y) (hp : p.domain = ⊤) : ∃ g : X ⟶ Y, g.toPartialMap = p := by
    obtain ⟨D,hD,F⟩ := p
    change D = ⊤ at hp
    subst D
    refine ⟨X.topIso.inv ≫ F, Scheme.PartialMap.ext _ _ rfl ?_⟩
    simp [Scheme.Hom.toPartialMap]
  obtain ⟨g,hg⟩ := hb f.toPartialMap hd
  exact ⟨g,(congrArg Scheme.PartialMap.toRationalMap hg).trans f.toRationalMap_toPartialMap⟩

private instance generic_dominant : IsDominant (genericArrow X) := by
  constructor
  have h : genericPoint X ∈ Set.range (genericArrow X) :=
    ⟨IsLocalRing.closedPoint _, X.fromSpecStalk_closedPoint⟩
  intro x
  exact closure_mono (Set.singleton_subset_iff.mpr h) ((genericPoint_specializes x).mem_closure)

/-- An integral scheme with valuation stalks admits a unique extension of every generic
map to a proper target over a separated base. -/
theorem extend_generic (sX : X ⟶ S) (sY : Y ⟶ S) [IsProper sY] [Scheme.IsSeparated S]
    (hX : ∀ x : X, ValuationRing (X.presheaf.stalk x))
    (φ : Spec X.functionField ⟶ Y) (hφ : φ ≫ sY = genericArrow X ≫ sX) :
    ∃! g : X ⟶ Y, genericArrow X ≫ g = φ ∧ g ≫ sY = sX := by
  let f := Scheme.RationalMap.ofFunctionField sX sY φ hφ
  have : Scheme.IsSeparated Y := ⟨by
    rw [← terminal.comp_from sY]
    infer_instance⟩
  have hd : f.domain = ⊤ := top_unique fun x _ => by
    let := hX x
    exact valuationPoint_mem_domain sX sY φ hφ x
  obtain ⟨g,hg⟩ := global_of_full_domain f hd
  have hgen : genericArrow X ≫ g = φ := by
    have h := congrArg Scheme.RationalMap.fromFunctionField hg
    rw [Scheme.RationalMap.fromFunctionField_ofFunctionField] at h
    simpa [Scheme.RationalMap.fromFunctionField_toRationalMap] using h
  have hb : g ≫ sY = sX := by
    apply ext_of_isDominant (ι := genericArrow X)
    rw [← Category.assoc,hgen,hφ]
  refine ⟨g,⟨hgen,hb⟩,fun t ht => ?_⟩
  exact ext_of_isDominant_of_isSeparated sY (ht.2.trans hb.symm) (genericArrow X) (ht.1.trans hgen.symm)

end
end ZInQBlueprint.CurveExtension
#print axioms ZInQBlueprint.CurveExtension.extend_stalk
#print axioms ZInQBlueprint.CurveExtension.valuationPoint_mem_domain
#print axioms ZInQBlueprint.CurveExtension.extend_generic
