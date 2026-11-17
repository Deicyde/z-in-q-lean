import UnramifiedParameter
import PaperWeightedPoints
import LineValuation
import Mathlib.AlgebraicGeometry.AlgClosed.Basic

/-! The affine point ideals and their generators in the stalk of the complete curve. -/
open CategoryTheory AlgebraicGeometry Polynomial
namespace ZInQBlueprint.WeightedCurvePoints
open BinaryCover
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable {K : Type} [Field K]

def primeAt (f : K[X]) (p : AffineCoords K f) : PrimeSpectrum (Cover f) :=
  ⟨pointIdeal f p,inferInstance⟩

theorem section_support (f : K[X]) (p : AffineCoords K f) :
    (affineSection K f p).left (IsLocalRing.closedPoint K) = primeAt f p := by
  apply PrimeSpectrum.ext
  change (IsLocalRing.maximalIdeal K).comap (coordAlg K f p).toRingHom = _
  rw [IsLocalRing.maximalIdeal_eq_bot]
  rfl

variable (f g : K[X]) (h : SexticOverlap K f g) (i : Bool)
private abbrev chartPoly := if i then g else f
variable (p : AffineCoords K (chartPoly f g i))
abbrev support := (chartSection f g h i p).left (IsLocalRing.closedPoint K)
abbrev pointStalk := (glued K f g h).presheaf.stalk (support f g h i p)

/-- The stalk at the scheme point determined by this section equals the local
ring of its affine evaluation kernel. The isomorphism uses the chart stalk map. -/
def chartStalkEquiv : pointStalk f g h i p ≃+* pointLocal _ p := by
  change (glued K f g h).presheaf.stalk
    ((chartInclusion K f g h i).left ((affineSection K _ p).left (IsLocalRing.closedPoint K))) ≃+* _
  rw [section_support]
  let q := primeAt _ p
  let j := (chartInclusion K f g h i).left
  let e := (asIso (j.stalkMap q)).commRingCatIsoToRingEquiv
  exact e.trans (Spec.stalkIso (.of _) q).commRingCatIsoToRingEquiv

def baseUniformizerGerm : pointStalk f g h i p := (chartStalkEquiv f g h i p).symm
  (localMap _ p (algebraMap K[X] (Cover _) (X-C p.1.1)))

theorem regular_fibre_stalk [CharZero K] (hy : p.1.2 ≠ 0) :
    Ideal.span {baseUniformizerGerm f g h i p} = IsLocalRing.maximalIdeal (pointStalk f g h i p) := by
  let e := (chartStalkEquiv f g h i p).symm
  have loc : Ideal.span {localMap _ p (algebraMap K[X] (Cover (chartPoly f g i)) (X-C p.1.1))} =
      IsLocalRing.maximalIdeal (pointLocal _ p) := regular_local_parameter _ p hy
  have eq := congrArg (Ideal.map e.toRingHom) loc
  have hm := IsLocalRing.map_maximalIdeal_of_surjective e.toRingHom e.surjective
  rw [hm] at eq
  rw [Ideal.map_span,Set.image_singleton] at eq
  exact eq

theorem paper_branch_stalk [CharZero K] {u : ℚ} (hu : u∉ZInQ.contactSet) (j : Bool) (x : K)
    (hx : (paper K u j).IsRoot x) :
    let f₀ := paper K u false
    let g₀ := paper K u true
    let v : AffineCoords K (chartPoly f₀ g₀ j) := by
      cases j <;> exact branchCoords _ x hx
    Ideal.span {baseUniformizerGerm f₀ g₀ (paper_overlap K u) j v} =
      (IsLocalRing.maximalIdeal (pointStalk f₀ g₀ (paper_overlap K u) j v))^2 := by
  have general (a b : K[X]) (o : SexticOverlap K a b) (s : Bool) (y : K)
      (hr : (chartPoly a b s).IsRoot y) (hs : (chartPoly a b s).Separable) :
      let v := branchCoords (chartPoly a b s) y hr
      Ideal.span {baseUniformizerGerm a b o s v} = (IsLocalRing.maximalIdeal (pointStalk a b o s v)) ^ 2 := by
    let v := branchCoords (chartPoly a b s) y hr
    let e := (chartStalkEquiv a b o s v).symm
    have l : Ideal.span {localMap _ v (algebraMap K[X] (Cover _) (X-C y))} =
        (IsLocalRing.maximalIdeal (pointLocal _ v))^2 := by
      obtain ⟨c,hc⟩ := branch_local_parameter _ hs y hr
      rw [branch_maximal _ hs y hr,Ideal.span_singleton_pow,hc,Ideal.span_singleton_mul_left_unit c.isUnit]
    have eq := congrArg (Ideal.map e.toRingHom) l
    have hm := IsLocalRing.map_maximalIdeal_of_surjective e.toRingHom e.surjective
    rw [Ideal.map_pow,hm] at eq
    rw [Ideal.map_span,Set.image_singleton] at eq
    exact eq
  cases j
  · exact general (paper K u false) (paper K u true) (paper_overlap K u) false x hx (paper_chart_regular K hu false).2
  · exact general (paper K u false) (paper K u true) (paper_overlap K u) true x hx (paper_chart_regular K hu true).2

def sectionClosed (C : Over (Spec (.of K))) [IsAlgClosed K] [LocallyOfFiniteType C.hom] :
    Sections K C ≃ closedPoints C.left :=
  Equiv.trans (⟨fun p => ⟨p.left,p.w⟩,fun p => Over.homMk p.1 p.2,fun _ => rfl,fun _ => rfl⟩ :
    Sections K C ≃ {p : Spec (.of K) ⟶ C.left // p ≫ C.hom = 𝟙 _}) (pointEquivClosedPoint C.hom)

def weightedClosed [CharZero K] [IsAlgClosed K] {u : ℚ} (hu : u∉ZInQ.contactSet) :
    CurveChart.Points (F K u) ≃ closedPoints (paperModel K u).left := by
  let _ := paper_proper K u
  exact (weightedSections K hu).trans (sectionClosed _)
end
end ZInQBlueprint.WeightedCurvePoints
#print axioms ZInQBlueprint.WeightedCurvePoints.section_support
#print axioms ZInQBlueprint.WeightedCurvePoints.chartStalkEquiv
#print axioms ZInQBlueprint.WeightedCurvePoints.regular_fibre_stalk
#print axioms ZInQBlueprint.WeightedCurvePoints.paper_branch_stalk
#print axioms ZInQBlueprint.WeightedCurvePoints.weightedClosed
