import PrintedSexticRegular

/-! An isomorphism of the smooth proper models extends the explicit
change on the open where the two translated abscissas are reciprocal. -/
open Polynomial CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace ZInQBlueprint.PrintedModel
open BinaryCover
noncomputable section
variable {K : Type} [Field K] [CharZero K] {u : ℚ} {d : K}

private def punctureOver (f : K[X]) : SpecOver (R := K) (Punctured K f) ⟶ SpecOver (Cover f) := by
  refine Over.homMk (puncture K f) ?_
  change Spec.map _ ≫ Spec.map _ = Spec.map _
  rw [← Spec.map_comp]
  congr 1
  apply CommRingCat.hom_ext
  apply RingHom.ext
  intro r
  exact QuadraticAlgebra.ext (Polynomial.toLaurent_C r) (map_zero _)

private instance (f : K[X]) : IsOpenImmersion (punctureOver f).left :=
  inferInstanceAs (IsOpenImmersion (puncture K f))

private def signedChartIso (hu : u ∉ ZInQ.contactSet) (hd : d^2=6) (v : K) (hv : v^2=factor u d) :
    SpecOver (R := K) (Cover (changed u d)) ≅ SpecOver (Cover (paper K u false)) := by
  have nz : v≠0 := by rintro rfl; exact (units hu hd).2 (by simpa using hv.symm)
  let scale : K[X]ˣ := Units.map (C : K →+* K[X]) (Units.mk0 v nz)
  apply specIso (squareEquiv (algEquivAevalXAddC d) scale ?_)
  change _ = (C v)^2 * changed u d
  rw [← map_pow, hv, paper_translation u hd]

private def printedChartIso (hu : u ∉ ZInQ.contactSet) (hd : d^2=6) :
    SpecOver (R := K) (Cover (translated u d)) ≅ SpecOver (Cover (SexticCalibration.sextic (argument u d))) := by
  let : Invertible (2*d*slope u d) := invertibleOfNonzero (units hu hd).1
  apply specIso (squareEquiv (algEquivCMulXAddC (2*d*slope u d) (slope u d)) 1 ?_)
  simp only [Units.val_one, one_pow, one_mul]
  rfl

abbrev model (hu : u ∉ ZInQ.contactSet) (hd : d^2=6) :=
  sexticCompletion (SexticCalibration.sextic (argument u d)) (printed_degree hu hd)

def signedOpen (hu : u ∉ ZInQ.contactSet) (hd : d^2=6) (v : K) (hv : v^2=factor u d) :
    SpecOver (R := K) (Punctured K (changed u d)) ⟶ paperModel K u :=
  punctureOver _ ≫ (signedChartIso hu hd v hv).hom ≫ chartInclusion K _ _ (paper_overlap K u) false

def printedOpen (hu : u ∉ ZInQ.contactSet) (hd : d^2=6) :
    SpecOver (R := K) (Punctured K (changed u d)) ⟶ model hu hd :=
  (specIso (transition K (overlap u d))).inv ≫ punctureOver _ ≫
    (printedChartIso hu hd).hom ≫ chartInclusion K _ _ (reverse_sextic_overlap (printed_degree hu hd)) false

private instance signed_open (hu : u ∉ ZInQ.contactSet) (hd : d^2=6) (v : K) (hv : v^2=factor u d) :
    IsOpenImmersion (signedOpen hu hd v hv).left := by
  let e := signedChartIso hu hd v hv
  let : IsIso e.hom.left := inferInstanceAs (IsIso (((Over.forget _).mapIso e).hom))
  change IsOpenImmersion ((punctureOver _).left ≫ e.hom.left ≫ (chartInclusion K _ _ _ false).left)
  exact @IsOpenImmersion.comp _ _ _ _ _ (inferInstanceAs (IsOpenImmersion (puncture K (changed u d))))
    (@IsOpenImmersion.comp _ _ _ _ _ (IsOpenImmersion.of_isIso e.hom.left) (chartInclusion_open ..))

private instance printed_open (hu : u ∉ ZInQ.contactSet) (hd : d^2=6) :
    IsOpenImmersion (printedOpen hu hd).left := by
  let e := specIso (transition K (overlap u d))
  let g := printedChartIso hu hd
  let : IsIso e.inv.left := inferInstanceAs (IsIso (((Over.forget _).mapIso e).inv))
  let : IsIso g.hom.left := inferInstanceAs (IsIso (((Over.forget _).mapIso g).hom))
  change IsOpenImmersion (e.inv.left ≫ (punctureOver _).left ≫ g.hom.left ≫ (chartInclusion K _ _ _ false).left)
  exact @IsOpenImmersion.comp _ _ _ _ _ (IsOpenImmersion.of_isIso e.inv.left)
    (@IsOpenImmersion.comp _ _ _ _ _ (inferInstanceAs (IsOpenImmersion (puncture K (translated u d))))
      (@IsOpenImmersion.comp _ _ _ _ _ (IsOpenImmersion.of_isIso g.hom.left) (chartInclusion_open ..)))

/-- The indicated two radicals fix the isomorphism uniquely. -/
theorem unique_printed_iso (hu : u ∉ ZInQ.contactSet) (hd : d^2=6) (v : K) (hv : v^2=factor u d) :
    ∃! e : paperModel K u ≅ model hu hd, signedOpen hu hd v hv ≫ e.hom = printedOpen hu hd := by
  obtain ⟨hI,hP,_,_,hV⟩ := sexticCompletion_geometry (printed_degree hu hd) (printed_separable hu hd)
  let : AlgebraicGeometry.IsIntegral (model hu hd).left := hI
  let : IsProper (model hu hd).hom := hP
  let : AlgebraicGeometry.IsIntegral (paperModel K u).left := paper_reglued_integral K hu
  let : IsProper (paperModel K u).hom := paper_proper K u
  let : Nonempty (SpecOver (R := K) (Punctured K (changed u d))).left :=
    inferInstanceAs (Nonempty (PrimeSpectrum (Punctured K (changed u d))))
  exact CurveExtension.unique_model_iso (signedOpen hu hd v hv) (printedOpen hu hd) (paper_prevaluation K hu) hV

end
end ZInQBlueprint.PrintedModel
#print axioms ZInQBlueprint.PrintedModel.unique_printed_iso
