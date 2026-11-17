import LinePoints

/-! The valuative criterion for the two-chart projective line over a field. -/
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Polynomial LaurentPolynomial
namespace ZInQBlueprint.BinaryCover
noncomputable section
variable (k : Type) [Field k]

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

theorem line_compact : CompactSpace (projectiveLine k) := by
  let 𝒰 := lineCover k
  let : Finite 𝒰.I₀ := inferInstanceAs (Finite (Option Bool))
  let : ∀ i, CompactSpace (𝒰.X i) := fun i => by
    change CompactSpace ((lineDiagram k).obj i)
    cases i with
    | none => exact inferInstanceAs (CompactSpace (Spec (.of (LaurentPolynomial k))))
    | some i => exact inferInstanceAs (CompactSpace (Spec (.of k[X])))
  exact 𝒰.compactSpace

private theorem chart_finiteType : LocallyOfFiniteType (scalarMap k k[X]) := by
  change LocallyOfFiniteType (Spec.map (CommRingCat.ofHom (algebraMap k k[X])))
  rw [HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)]
  exact RingHom.finiteType_algebraMap.mpr inferInstance

theorem line_finiteType : LocallyOfFiniteType (lineStructure k) := by
  apply IsZariskiLocalAtSource.of_openCover (lineCover k)
  intro i
  change LocallyOfFiniteType (colimit.ι (lineDiagram k) i ≫ lineStructure k)
  cases i with
  | none =>
    have e : colimit.ι (lineDiagram k) none =
        linePuncture k ≫ inclusion k false := (WidePushout.arrow_ι (lineArrow k) false).symm
    rw [e, Category.assoc, inclusion_structure]
    let := chart_finiteType k
    infer_instance
  | some i =>
    rw [show (colimit.ι (lineDiagram k) (some i) ≫ lineStructure k) = scalarMap k k[X] from inclusion_structure k i]
    exact chart_finiteType k

theorem line_existence : ValuativeCriterion.Existence (lineStructure k) := by
  intro V
  let a := algebraMap V.R V.K
  let b := (Spec.preimage V.i₂).hom
  have eq : Spec.map (CommRingCat.ofHom b) = V.i₂ := Spec.map_preimage _
  have h : V.i₁ ≫ lineStructure k = Spec.map (CommRingCat.ofHom (a.comp b)) := by
    rw [V.commSq.w, ← eq, ← Spec.map_comp]
    rfl
  obtain ⟨i,x,hx⟩ := exists_coordinates k (a.comp b) V.i₁ h
  obtain ⟨y, hy | hy⟩ := (ValuationRing.integers V.R V.K).eq_algebraMap_or_inv_eq_algebraMap x
  · refine ⟨⟨⟨point k b y i, ?_, ?_⟩⟩⟩
    · rw [point_map, ← hx, hy]
    · rw [point_structure, eq]
  · by_cases z : x = 0
    · refine ⟨⟨⟨point k b 0 i, ?_, ?_⟩⟩⟩
      · rw [point_map, map_zero, ← hx, z]
      · rw [point_structure, eq]
    · refine ⟨⟨⟨point k b y (!i), ?_, ?_⟩⟩⟩
      · rw [point_map, ← hx, ← hy]
        exact (point_changeChart k (a.comp b) (Units.mk0 x z) i).symm
      · rw [point_structure, eq]

theorem line_uniqueness : ValuativeCriterion.Uniqueness (lineStructure k) := by
  intro V
  let a := algebraMap V.R V.K
  let b := (Spec.preimage V.i₂).hom
  have eq : Spec.map (CommRingCat.ofHom b) = V.i₂ := Spec.map_preimage _
  have cmp {x y : V.R} (h : point k (a.comp b) (a x) false = point k (a.comp b) (a y) true) :
      point k b x false = point k b y true := by
    have prod : x*y=1 := (IsFractionRing.injective V.R V.K) <| by
      simpa using cross_product k (a.comp b) h
    let v : V.Rˣ := ⟨x,y,prod,(mul_comm y x).trans prod⟩
    exact point_invert k b v
  constructor
  intro l l'
  apply CommSq.LiftStruct.ext
  obtain ⟨i,x,hx⟩ := exists_coordinates k b l.l (l.fac_right.trans eq.symm)
  obtain ⟨j,y,hy⟩ := exists_coordinates k b l'.l (l'.fac_right.trans eq.symm)
  have hs := l.fac_left.trans l'.fac_left.symm
  rw [← hx, ← hy] at hs ⊢
  rw [point_map, point_map] at hs
  cases i <;> cases j
  · exact congrArg (fun z => point k b z false)
      (IsFractionRing.injective V.R V.K (point_injective k _ false hs))
  · exact cmp hs
  · exact (cmp hs.symm).symm
  · exact congrArg (fun z => point k b z true)
      (IsFractionRing.injective V.R V.K (point_injective k _ true hs))

theorem line_proper : IsProper (lineStructure k) := by
  let : CompactSpace (projectiveLine k) := line_compact k
  let : LocallyOfFiniteType (lineStructure k) := line_finiteType k
  let : IsLocallyNoetherian (projectiveLine k) := LocallyOfFiniteType.isLocallyNoetherian (lineStructure k)
  exact IsProper.of_valuativeCriterion _ (ValuativeCriterion.iff.mpr ⟨line_existence k,line_uniqueness k⟩)

/-- The fixed sextic is proper over its field of definition for every parameter. -/
theorem paper_proper (K : Type) [Field K] [CharZero K] (u : ℚ) :
    IsProper (paperModel K u).hom := by
  let h := paper_overlap K u
  change IsProper (gluedOver K _ _ h).hom
  rw [← curve_structure]
  let := finite_toLine K _ _ h
  let := line_proper K
  infer_instance

end
end ZInQBlueprint.BinaryCover
#print axioms ZInQBlueprint.BinaryCover.line_finiteType
#print axioms ZInQBlueprint.BinaryCover.line_existence
#print axioms ZInQBlueprint.BinaryCover.line_uniqueness
#print axioms ZInQBlueprint.BinaryCover.line_proper
#print axioms ZInQBlueprint.BinaryCover.paper_proper

