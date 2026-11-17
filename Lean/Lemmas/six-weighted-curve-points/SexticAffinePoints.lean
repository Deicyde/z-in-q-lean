import SquareRootSmooth
import LinePoints
/-! Coordinates on the scheme-valued points of the affine double cover. -/
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Polynomial
namespace ZInQBlueprint.WeightedCurvePoints
open BinaryCover
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable (K : Type) [Field K]

abbrev source := Over.mk (𝟙 (Spec (.of K)))
abbrev Sections (C : Over (Spec (.of K))) := source K ⟶ C
variable {A : Type} [CommRing A] [Algebra K A]

def sectionOfAlg (s : A →ₐ[K] K) : Sections K (SpecOver (R := K) A) := by
  refine Over.homMk (Spec.map (CommRingCat.ofHom s.toRingHom)) ?_
  change Spec.map _ ≫ Spec.map _ = 𝟙 _
  rw [← Spec.map_comp, ← Spec.map_id]
  congr 1
  exact CommRingCat.hom_ext (RingHom.ext s.commutes)

theorem sectionOfAlg_injective : Function.Injective (sectionOfAlg K (A := A)) := by
  intro a b h
  have eh := congrArg (fun q : Sections K (SpecOver (R := K) A) => q.left) h
  have e : CommRingCat.ofHom a.toRingHom = CommRingCat.ofHom b.toRingHom :=
    Spec.map_injective eh
  exact AlgHom.ext (fun t => congrArg (fun z : CommRingCat.of A ⟶ CommRingCat.of K => z.hom t) e)

theorem sectionOfAlg_surjective : Function.Surjective (sectionOfAlg K (A := A)) := by
  intro m
  let φ := (Spec.preimage m.left).hom
  have hf : Spec.map (CommRingCat.ofHom φ) = m.left := Spec.map_preimage m.left
  have ha : φ.comp (algebraMap K A) = RingHom.id K := by
    refine congrArg (fun z : CommRingCat.of K ⟶ CommRingCat.of K => z.hom) ?_
    apply Spec.map_injective
    change Spec.map (CommRingCat.ofHom (algebraMap K A) ≫ CommRingCat.ofHom φ) = _
    rw [Spec.map_comp, hf]
    change m.left ≫ _ = Spec.map (𝟙 (CommRingCat.of K))
    rw [Spec.map_id]
    exact m.w
  let s : A →ₐ[K] K := { toRingHom := φ, commutes' := fun k => DFunLike.congr_fun ha k }
  exact ⟨s,Over.OverMorphism.ext hf⟩

abbrev AffineCoords (f : K[X]) := {p : K × K // p.2^2 = aeval p.1 f}

def coordAlg (f : K[X]) (p : AffineCoords K f) : Cover f →ₐ[K] K :=
  affinePoint f p.1.1 p.1.2 p.2

def readCoords (f : K[X]) (s : Cover f →ₐ[K] K) : AffineCoords K f :=
  ⟨(s (algebraMap K[X] (Cover f) X), s QuadraticAlgebra.omega), ordinate_square s⟩

theorem read_write (f : K[X]) (p : AffineCoords K f) : readCoords K f (coordAlg K f p) = p := by
  apply Subtype.ext
  apply Prod.ext
  · change aeval p.1.1 X + aeval p.1.1 0 * p.1.2 = p.1.1
    simp
  · change aeval p.1.1 0 + aeval p.1.1 1 * p.1.2 = p.1.2
    simp

theorem write_read (f : K[X]) (s : Cover f →ₐ[K] K) : coordAlg K f (readCoords K f s) = s :=
  AlgHom.ext (fun z => (affinePoint_image s z).symm)

def affineSection (f : K[X]) (p : AffineCoords K f) : Sections K (SpecOver (R := K) (Cover f)) :=
  sectionOfAlg K (coordAlg K f p)

theorem affineSection_bijective (f : K[X]) : Function.Bijective (affineSection K f) := by
  refine ⟨fun p q h => ?_, fun m => ?_⟩
  · have he := congrArg (readCoords K f) (sectionOfAlg_injective K h)
    simpa only [read_write] using he
  · obtain ⟨s,hs⟩ := sectionOfAlg_surjective K m
    exact ⟨readCoords K f s, by rw [affineSection, write_read, hs]⟩

theorem affine_fst (f : K[X]) (p : AffineCoords K f) :
    (affineSection K f p).left ≫ ordinateProjection K f =
      Spec.map (CommRingCat.ofHom (Polynomial.eval₂RingHom (RingHom.id K) p.1.1)) := by
  change Spec.map _ ≫ Spec.map _ = Spec.map _
  rw [← Spec.map_comp]
  congr 1
  apply CommRingCat.hom_ext
  apply RingHom.ext
  intro t
  change aeval p.1.1 t + aeval p.1.1 0 * p.1.2 = _
  simp [Polynomial.aeval_def]
end
end ZInQBlueprint.WeightedCurvePoints
#print axioms ZInQBlueprint.WeightedCurvePoints.affineSection_bijective
#print axioms ZInQBlueprint.WeightedCurvePoints.affine_fst
