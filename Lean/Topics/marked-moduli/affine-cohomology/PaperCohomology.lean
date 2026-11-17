import AtlasSections
import MayerVietorisQuotient
import Mathlib.Algebra.Module.Rat

/-! The canonical comparison for the sextic, with its two affine vanishing obligations isolated. -/
open CategoryTheory AlgebraicGeometry TopologicalSpace Opposite CategoryTheory.Limits Polynomial
namespace ZInQBlueprint.BinaryCover.Cech
noncomputable section
set_option maxHeartbeats 1200000
set_option synthInstance.maxHeartbeats 5000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable (k : Type) [Field k] {f g : k[X]} (h : SexticOverlap k f g)
local notation "Xc" => glued k f g h
local notation "Sq" => atlasSquare k f g h
local notation "F" => additiveStructure Xc

private def coordinateChart (i : Bool) : (F).obj.obj (op (atlasOpen k f g h (some i))) ≃+
    Cover (if i then g else f) :=
  (affineSections (atlasMap k f g h (some i))).commRingCatIsoToRingEquiv.toAddEquiv

private def coordinateOverlap : (F).obj.obj (op (atlasOpen k f g h none)) ≃+ Punctured k f :=
  (affineSections (atlasMap k f g h none)).commRingCatIsoToRingEquiv.toAddEquiv

private theorem differential_formula (a : (F).obj.obj (op (Sq).X₂)) (b : (F).obj.obj (op (Sq).X₃)) :
    coordinateOverlap k h (sectionDifference Sq F (a,b)) =
      differential k h (coordinateChart k h false a, coordinateChart k h true b) := by
  let X := glued k f g h
  let j₀ := atlasMap k f g h (some false)
  let j₁ := atlasMap k f g h (some true)
  let j := atlasMap k f g h none
  have e₀ := affineSections_natural (CommRingCat.ofHom (direct k f).toRingHom) j₀ j
    (by rw [direct_spec k f g h]; exact WidePushout.arrow_ι ..) (leOfHom (Sq).f₁₂)
  have e₁ := affineSections_natural (CommRingCat.ofHom (reciprocal k h).toRingHom) j₁ j
    (by rw [reciprocal_spec k f g h]; exact WidePushout.arrow_ι ..) (leOfHom (Sq).f₁₃)
  change coordinateOverlap k h ((F).obj.map (Sq).f₁₂.op a - (F).obj.map (Sq).f₁₃.op b) = _
  rw [(coordinateOverlap k h).map_sub]
  exact congrArg₂ (· - ·) (congrArg (fun (φ : Γ(X,j₀.opensRange) ⟶ CommRingCat.of (Punctured k f)) => φ a) e₀)
    (congrArg (fun (φ : Γ(X,j₁.opensRange) ⟶ CommRingCat.of (Punctured k f)) => φ b) e₁)

/-- Ordinary cochains in the geometric square are precisely the Laurent cochains of the sextic. -/
def coordinateQuotient :
    ((F).obj.obj (op (Sq).X₁) ⧸ (sectionDifference Sq F).range) ≃+
    (Punctured k f ⧸ LinearMap.range (differential k h)) := by
  apply QuotientAddGroup.congr (sectionDifference Sq F).range
    (LinearMap.range (differential k h)).toAddSubgroup (coordinateOverlap k h)
  ext z
  constructor
  · rintro ⟨_, ⟨⟨a,b⟩,rfl⟩,rfl⟩
    exact ⟨_, (differential_formula k h a b).symm⟩
  · rintro ⟨⟨a,b⟩, rfl⟩
    let e := coordinateChart k h false
    let d := coordinateChart k h true
    refine ⟨_,⟨(e.symm a,d.symm b),rfl⟩,?_⟩
    exact (differential_formula k h _ _).trans (congrArg (differential k h)
      (Prod.ext (e.apply_symm_apply a) (d.apply_symm_apply b)))

/-- The Laurent classes inject into actual global H¹ for every binary sextic and field. -/
def curveBoundary : (Punctured k f ⧸ LinearMap.range (differential k h)) →+
    H1 Xc :=
  (terminalCohomology _ (show IsTerminal (Sq).X₄ from isTerminalTop) F 1).toAddMonoidHom.comp
    ((overlapToH1 Sq F).comp (coordinateQuotient k h).symm.toAddMonoidHom)

theorem curveBoundary_injective : Function.Injective (curveBoundary k h) :=
  (terminalCohomology _ (show IsTerminal (Sq).X₄ from isTerminalTop) F 1).injective.comp
    ((overlapToH1_injective Sq F).comp (coordinateQuotient k h).symm.injective)

/-- Vanishing in degree one on the two affine charts is sufficient. -/
theorem curveBoundary_surjective (hv : ∀ i : Bool, Subsingleton ((F).H' 1 (atlasOpen k f g h (some i)))) :
    Function.Surjective (curveBoundary k h) :=
  (terminalCohomology _ (show IsTerminal (Sq).X₄ from isTerminalTop) F 1).surjective.comp
    ((overlapEquivH1 Sq F (hv false) (hv true)).surjective.comp (coordinateQuotient k h).symm.surjective)

variable (u : ℚ)
local notation "p" => (paperModel ℚ u)
local notation "hf" => paper_overlap ℚ u
local notation "D" => (Punctured ℚ (paper ℚ u false) ⧸ LinearMap.range (differential ℚ hf))

/-- The comparison map for the rational paper model uses the actual rational action on H¹. -/
def paperBoundary :
    letI := h1Module (p).hom
    D →ₗ[ℚ] H1 (p).left := by
  letI := h1Module (p).hom
  let b : D →+ H1 (p).left := curveBoundary ℚ hf
  exact { b with map_smul' := map_rat_smul b }

/-- The two distinguished odd Laurent classes give a copy of Q² in H¹ without an affine-vanishing input. -/
theorem paper_two_classes :
    letI := h1Module (p).hom
    ∃ φ : (ℚ × ℚ) →ₗ[ℚ] H1 (p).left, Function.Injective φ := by
  let := h1Module (p).hom
  exact ⟨(paperBoundary u).comp (quotientEquiv ℚ hf).symm.toLinearMap,
    (curveBoundary_injective ℚ hf).comp (quotientEquiv ℚ hf).symm.injective⟩

/-- A precise input in the ambient small Zariski site for the two affine charts. -/
def PaperAffineH1 : Prop :=
  ∀ i : Bool, Subsingleton ((additiveStructure (p).left).H' 1 (atlasOpen ℚ _ _ hf (some i)))

/-- On the paper model the only remaining sufficient cohomological input is affine vanishing. -/
theorem paper_comparison_of_affine (hv : PaperAffineH1 u) : SheafComparison (k := ℚ) u := by
  let := h1Module (p).hom
  exact ⟨LinearEquiv.ofBijective (paperBoundary u)
    ⟨curveBoundary_injective ℚ hf, curveBoundary_surjective ℚ hf hv⟩⟩

theorem paper_dimension_of_affine (hv : PaperAffineH1 u) :
    letI := h1Module (p).hom
    Module.finrank ℚ (H1 (p).left) = 2 :=
  paper_h1_finrank u (paper_comparison_of_affine u hv)

end
end ZInQBlueprint.BinaryCover.Cech
#print axioms ZInQBlueprint.BinaryCover.Cech.coordinateQuotient
#print axioms ZInQBlueprint.BinaryCover.Cech.curveBoundary_injective
#print axioms ZInQBlueprint.BinaryCover.Cech.curveBoundary_surjective
#print axioms ZInQBlueprint.BinaryCover.Cech.paper_two_classes
#print axioms ZInQBlueprint.BinaryCover.Cech.paper_comparison_of_affine
#print axioms ZInQBlueprint.BinaryCover.Cech.paper_dimension_of_affine
