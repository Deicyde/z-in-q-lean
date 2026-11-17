import SplitTorsionPoints
import Mathlib.AlgebraicGeometry.Morphisms.Flat

/-! Descent of geometric torsion to completions, including preservation of
the smaller torsion level under descent. -/
open CategoryTheory AlgebraicGeometry GoodReductionJacobian
open GoodReductionJacobian.RelativeGroupLaw
namespace ZInQBlueprint.TorsionHeight
noncomputable section
variable {F K L : Type} [Field F] [Field K] [Field L] [Algebra F K] [Algebra F L]
variable (A : CommGrp (Over (Spec (.of F))))

theorem points_map_injective (i : K →ₐ[F] L) :
    Function.Injective (AlgPoints.map (L:=Law F A) (hc:=LawComm F A) i) := by
  let k := CommRingCat.ofHom i.toRingHom
  have hr : k.hom.FaithfullyFlat := by
    let : Algebra K L := i.toRingHom.toAlgebra
    exact (RingHom.faithfullyFlat_algebraMap_iff (R:=K) (S:=L)).2 inferInstance
  obtain ⟨f,s⟩ := (flat_and_surjective_SpecMap_iff k).2 hr
  let : Flat (Spec.map k) := f
  let : Surjective (Spec.map k) := s
  let : Epi (Spec.map k) := Flat.epi_of_flat_of_surjective _
  intro x y h
  apply AlgPoints.toPoint_injective
  apply Subtype.ext
  apply (cancel_epi (Spec.map k)).1
  exact congrArg (fun t : Points F A L => (AlgPoints.toPoint t).1) h

/-- A level rational over every overfield of K. This quantifies over actual
coefficient homomorphisms and the abelian group's multiplication. -/
def FullLevel (n : ℕ) (K : Type) [Field K] [Algebra F K] : Prop :=
  ∀ (L : Type) [Field L] [Algebra F L] (i : K →ₐ[F] L) (y : Points F A L),
    n • y = 0 → ∃ x : Points F A K, n • x = 0 ∧ AlgPoints.map i x = y

theorem fullLevel_of_dvd {m n : ℕ} (hm : m ∣ n) (h : FullLevel A n K) : FullLevel A m K := by
  intro E _ _ i y hy
  obtain ⟨r,hr⟩ := hm
  have hn : n • y = 0 := by rw [hr,mul_comm,mul_smul,hy,smul_zero]
  obtain ⟨x,_,hx⟩ := h E i y hn
  refine ⟨x,points_map_injective A i ?_,hx⟩
  rw [map_nsmul,map_zero,hx,hy]

theorem fullLevel_overfield {n : ℕ} (h : FullLevel A n K) (i : K →ₐ[F] L) :
    FullLevel A n L := by
  intro E _ _ j y hy
  obtain ⟨x,hx,e⟩ := h E (j.comp i) y hy
  exact ⟨AlgPoints.map i x, by rw [←map_nsmul,hx,map_zero], by
    rw [←e,AlgPoints.map_comp]; rfl⟩

/-- At every local ring, at least one of the two available torsion levels
is invertible, including in residue characteristics two and three. -/
theorem local_level (O : Type*) [CommRing O] [IsLocalRing O] :
    ∃ n : ℕ, n ∣ 12 ∧ 3 ≤ n ∧ IsUnit (n : O) := by
  rcases IsLocalRing.isUnit_or_isUnit_of_add_one (show (4:O)+(-3)=1 by ring) with h|h
  · exact ⟨4,by decide,by decide,by simpa using h⟩
  · exact ⟨3,by decide,by decide,by simpa using h⟩

end
end ZInQBlueprint.TorsionHeight
#print axioms ZInQBlueprint.TorsionHeight.points_map_injective
#print axioms ZInQBlueprint.TorsionHeight.fullLevel_of_dvd
#print axioms ZInQBlueprint.TorsionHeight.fullLevel_overfield
#print axioms ZInQBlueprint.TorsionHeight.local_level
