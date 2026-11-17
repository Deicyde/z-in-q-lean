import FixedCurve
/-! The DDMM chart as an open subscheme of the specific global equation over Q_p. -/
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Polynomial
namespace ZInQBlueprint.BinaryCover
noncomputable section
variable (R : Type) [CommRing R]

def chartInclusion (f g : R[X]) (h : SexticOverlap R f g) (i : Bool) :
    SpecOver (R := R) (Cover (if i then g else f)) ⟶ gluedOver R f g h := by
  refine Over.homMk (WidePushout.ι (arrow R f g h) i) ?_
  exact WidePushout.ι_desc ..

instance chartInclusion_open (f g : R[X]) (h : SexticOverlap R f g) (i : Bool) :
    IsOpenImmersion (chartInclusion R f g h i).left :=
  inferInstanceAs (IsOpenImmersion (colimit.ι (diagram R f g h) (some i)))

/-- The DDMM affine curve opens into the fixed paper scheme over Q_p. Both
charts, including the one over infinity, are opens of this very same scheme. -/
theorem ddmm_open {p : ℕ} [Fact p.Prime] {u : ℚ} (hu : u ∉ ZInQ.contactSet)
    (v a : ℤ_[p]ˣ) (t : ℤ_[p]) (hc : PrimitiveParameters.Coordinates p u t (v : ℤ_[p]) (a : ℤ_[p])) :
    ∃ j : SpecOver (R := ℚ_[p]) (Cover (GoodReductionCharts.polynomial p u v a t)) ⟶
      paperModel ℚ_[p] u, IsOpenImmersion j.left := by
  obtain ⟨i, ⟨e⟩⟩ := local_paper_chart_iso p hu v a t hc
  have go {i : Bool} (e : SpecOver (R := ℚ_[p]) (Cover (GoodReductionCharts.polynomial p u v a t)) ≅
      SpecOver (Cover (if i then paper ℚ_[p] u true else paper ℚ_[p] u false))) :
      ∃ j : SpecOver (R := ℚ_[p]) (Cover (GoodReductionCharts.polynomial p u v a t)) ⟶
        paperModel ℚ_[p] u, IsOpenImmersion j.left := by
    let k := chartInclusion ℚ_[p] _ _ (paper_overlap ℚ_[p] u) i
    refine ⟨e.hom ≫ k, ?_⟩
    let : IsIso e.hom.left := inferInstanceAs (IsIso (((Over.forget _).mapIso e).hom))
    exact @IsOpenImmersion.comp _ _ _ e.hom.left k.left (IsOpenImmersion.of_isIso _)
      (chartInclusion_open ℚ_[p] _ _ _ i)
  cases i
  · exact go (i := false) e
  · exact go (i := true) e


end
end ZInQBlueprint.BinaryCover
#print axioms ZInQBlueprint.BinaryCover.chartInclusion
#print axioms ZInQBlueprint.BinaryCover.ddmm_open
