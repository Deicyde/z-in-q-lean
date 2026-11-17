import ProjectiveSextic
/-! The closed embedding of the actual paper curve over its coefficient field. -/
open CategoryTheory AlgebraicGeometry MvPolynomial HomogeneousLocalization
open ZInQBlueprint.BinaryCover
namespace ZInQBlueprint.SexticEmbedding
noncomputable section
attribute [local instance] MvPolynomial.gradedAlgebra
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable {K : Type} [Field K]
local notation "G" => homogeneousSubmodule (Fin 5) K

/-- The standard projective four-space over K, with its coefficient morphism. -/
def ambientSpace (K : Type) [Field K] : Over (Spec (.of K)) :=
  Over.mk (Proj.toSpecZero (homogeneousSubmodule (Fin 5) K) ≫
    Spec.map (CommRingCat.ofHom (algebraMap K (homogeneousSubmodule (Fin 5) K 0))))

/-- The explicit four-quadric inclusion respects the geometric structure maps. -/
theorem inclusion_over (c : Fin 7 → K) :
    quadricsInclusion c ≫ (ambientSpace K).hom = projectiveStructure c := by
  let f := quotientMap c
  let hf := HomogeneousIdeal.irrelevant_le_map_of_surjective f (Ideal.Quotient.mk_surjective (I := (equationsIdeal c).toIdeal))
  change Proj.map f hf ≫ Proj.toSpecZero G ≫ Spec.map _ = _
  apply (Proj.mapAffineOpenCover f hf).openCover.hom_ext
  intro i
  obtain ⟨i,x,hx⟩ := i
  change Proj.awayι (equationsIdeal c).quotientGrading (f x) (Graded.map_mem f hx) i.pos ≫ Proj.map f hf ≫ Proj.toSpecZero G ≫ Spec.map _ =
    Proj.awayι (equationsIdeal c).quotientGrading (f x) (Graded.map_mem f hx) i.pos ≫ projectiveStructure c
  rw [Proj.awayι_comp_map_assoc f hf i.pos x hx, Proj.awayι_toSpecZero_assoc, projectiveStructure,
    Proj.awayι_toSpecZero_assoc, ← Spec.map_comp, ← Spec.map_comp, ← Spec.map_comp]
  congr 1

def quadricsOverMap (c : Fin 7 → K) : Over.mk (projectiveStructure c) ⟶ ambientSpace K :=
  Over.homMk (quadricsInclusion c) (inclusion_over c)

variable [CharZero K] {u : ℚ}
/-- The unique identification fixing the finite chart of the paper curve. -/
def paperProjectiveIso (hu : u ∉ ZInQ.contactSet) :
    paperModel K u ≅ Over.mk (projectiveStructure (fun i => (paper K u false).coeff i)) :=
  (paper_is_quadrics (K := K) hu).exists.choose

/-- The embedding of the specified paper curve as the four-quadric locus in P^4 over K. -/
def paperEmbedding (hu : u ∉ ZInQ.contactSet) : paperModel K u ⟶ ambientSpace K :=
  (paperProjectiveIso hu).hom ≫ quadricsOverMap _

instance paperEmbedding_closed (hu : u ∉ ZInQ.contactSet) :
    IsClosedImmersion (paperEmbedding (K := K) hu).left := by
  change IsClosedImmersion ((paperProjectiveIso hu).hom.left ≫ quadricsInclusion _)
  infer_instance

/-- On the finite chart this embedding is the given normalized cubic-coordinate map. -/
theorem paperEmbedding_finite (hu : u ∉ ZInQ.contactSet) :
    chartInclusion K _ _ (paper_overlap K u) false ≫ paperEmbedding hu =
      finiteChartMap (paper_degree_six hu false) ≫ quadricsOverMap _ := by
  change _ ≫ (paperProjectiveIso hu).hom ≫ _ = _
  rw [← Category.assoc]
  exact congrArg (fun v => v ≫ _) ((paper_is_quadrics (K := K) hu).exists.choose_spec)

end
end ZInQBlueprint.SexticEmbedding
#print axioms ZInQBlueprint.SexticEmbedding.inclusion_over
#print axioms ZInQBlueprint.SexticEmbedding.paperEmbedding_closed
#print axioms ZInQBlueprint.SexticEmbedding.paperEmbedding_finite
