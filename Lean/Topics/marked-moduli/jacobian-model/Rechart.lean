import ChartOpen

/-! Regluing after a coordinate change on either affine chart. -/
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Polynomial
namespace ZInQBlueprint.BinaryCover
noncomputable section
variable (R : Type) [CommRing R] (f g : R[X]) (h : SexticOverlap R f g)

abbrev chart (i : Bool) : Over (Spec (.of R)) := SpecOver (Cover (if i then g else f))

section Regluing
variable (U : Bool → Over (Spec (.of R))) (e : ∀ i, U i ≅ chart R f g i)

/-- Glue with the actual new coordinate rings on the two charts. The attaching
map changes by the inverse coordinate isomorphism on that chart. -/
private abbrev rechartDiagram := WidePushoutShape.wideSpan (Spec (.of (Punctured R f)))
  (fun i : Bool => (U i).left) (fun i => arrow R f g h i ≫ (e i).inv.left)

private lemma cancel_change {A B C : Scheme} (f : A ⟶ B) (e : C ≅ B) :
    (f ≫ e.inv) ≫ e.hom = 𝟙 _ ≫ f := by simp

private def diagramIso : rechartDiagram R f g h U e ≅ diagram R f g h := by
  refine NatIso.ofComponents (fun j => match j with
    | none => Iso.refl _
    | some i => (Over.forget _).mapIso (e i)) ?_
  intro j k a
  change WidePushoutShape.Hom j k at a
  cases a with
  | id j =>
    change 𝟙 _ ≫ _ = _ ≫ 𝟙 _
    rw [Category.id_comp, Category.comp_id]
  | init i =>
    let b : (U i).left ≅ (chart R f g i).left := (Over.forget _).mapIso (e i)
    exact cancel_change (B := (chart R f g i).left) (arrow R f g h i) b

private instance : HasColimit (rechartDiagram R f g h U e) :=
  hasColimit_of_iso (diagramIso R f g h U e)

private def modelIso : colimit (rechartDiagram R f g h U e) ≅ glued R f g h :=
  HasColimit.isoOfNatIso (diagramIso R f g h U e)

/-- The scheme obtained by gluing these charts over the original base. -/
def rechartModel : Over (Spec (.of R)) :=
  Over.mk ((modelIso R f g h U e).hom ≫ (gluedOver R f g h).hom)

/-- An isomorphism of the complete two-chart models over the base. -/
def rechartIso : rechartModel R f g h U e ≅ gluedOver R f g h :=
  Over.isoMk (modelIso R f g h U e) rfl

/-- On each new chart, the comparison of glued schemes restricts to the
specified change of coordinates. -/
theorem rechart_restrict (i : Bool) :
    colimit.ι (rechartDiagram R f g h U e) (some i) ≫ (rechartIso R f g h U e).hom.left =
      (e i).hom.left ≫ (chartInclusion R f g h i).left :=
  HasColimit.ι_isoOfNatIso_hom (diagramIso R f g h U e) (some i)
end Regluing

/-- Replace chart i by A and keep the other chart. -/
def replaceChart (A : Over (Spec (.of R))) (i j : Bool) : Over (Spec (.of R)) :=
  if j = i then A else chart R f g j

def replaceIso {A : Over (Spec (.of R))} {i : Bool} (e : A ≅ chart R f g i) (j : Bool) :
    replaceChart R f g A i j ≅ chart R f g j := by
  by_cases hj : j = i
  · subst j
    exact (eqToIso (ite_eq_left rfl)) ≪≫ e
  · exact eqToIso (ite_eq_right hj)

/-- Given the local DDMM polynomial, the atlas made from its spectrum and the
other paper chart has colimit isomorphic over Q_p to the fixed paper model. -/
theorem ddmm_reglued {p : ℕ} [Fact p.Prime] {u : ℚ} (hu : u ∉ ZInQ.contactSet)
    (v a : ℤ_[p]ˣ) (t : ℤ_[p]) (hc : PrimitiveParameters.Coordinates p u t (v : ℤ_[p]) (a : ℤ_[p])) :
    let K := ℚ_[p]; let f := paper K u false; let g := paper K u true
    let A := SpecOver (R := K) (Cover (GoodReductionCharts.polynomial p u v a t))
    ∃ (i : Bool) (e : A ≅ chart K f g i),
      Nonempty (rechartModel K f g (paper_overlap K u) (replaceChart K f g A i) (replaceIso K f g e) ≅
        paperModel K u) := by
  dsimp only
  obtain ⟨i, ⟨e⟩⟩ := local_paper_chart_iso p hu v a t hc
  cases i
  · refine ⟨false, e, ⟨?_⟩⟩
    exact rechartIso _ _ _ (paper_overlap ℚ_[p] u) _ (replaceIso _ _ _ (i := false) e)
  · refine ⟨true, e, ⟨?_⟩⟩
    exact rechartIso _ _ _ (paper_overlap ℚ_[p] u) _ (replaceIso _ _ _ (i := true) e)
end
end ZInQBlueprint.BinaryCover
#print axioms ZInQBlueprint.BinaryCover.rechartIso
#print axioms ZInQBlueprint.BinaryCover.rechart_restrict
#print axioms ZInQBlueprint.BinaryCover.ddmm_reglued
