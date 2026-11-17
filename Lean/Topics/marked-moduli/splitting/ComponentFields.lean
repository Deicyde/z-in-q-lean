import LiteralField
import Mathlib.RingTheory.Spectrum.Prime.RingHom
import Mathlib.RingTheory.Etale.Field
import Mathlib.RingTheory.Ideal.Quotient.Operations

namespace MarkedModuli.Splitting
open IntermediateField

variable (F : Type*) [Field F] (Ω : Type*) [Field Ω] [Algebra F Ω]
variable {ι : Type*} [Finite ι] (E : ι → Type*) [∀ i, CommRing (E i)] [∀ i, Algebra F (E i)]

/-- A point of a finite product over a field factors through one projection.
This also handles the empty product: it has no point over a nonzero field. -/
theorem point_factors (x : Points F Ω (∀ i, E i)) :
    ∃ (i : ι) (y : E i →ₐ[F] Ω), y.comp (Pi.evalAlgHom F E i) = x := by
  let p : PrimeSpectrum (∀ i, E i) := ⟨RingHom.ker x.toRingHom, RingHom.ker_isPrime _⟩
  obtain ⟨i, q, hq⟩ := PrimeSpectrum.exists_comap_evalRingHom_eq p
  let f := Pi.evalAlgHom F E i
  have hsurj : Function.Surjective f := Function.surjective_eval i
  have hker : RingHom.ker f.toRingHom ≤ RingHom.ker x.toRingHom := by
    change RingHom.ker (Pi.evalRingHom E i) ≤ p.asIdeal
    rw [← hq]
    intro a ha
    exact show f a ∈ q.asIdeal from (RingHom.mem_ker.mp ha) ▸ q.asIdeal.zero_mem
  exact ⟨i, AlgHom.liftOfSurjective f hsurj x hker, AlgHom.liftOfSurjective_comp f hsurj x hker⟩

/-- Compositum of the splitting fields of all components, with the embeddings
placed in exactly the same ambient field. -/
theorem pointField_pi :
    pointField F Ω (∀ i, E i) = ⨆ i, pointField F Ω (E i) := by
  apply le_antisymm
  · apply (pointField_le_iff F Ω _ _).mpr
    intro x a
    obtain ⟨i,y,rfl⟩ := point_factors F Ω E x
    exact le_iSup (fun i ↦ pointField F Ω (E i)) i (subset_adjoin F _ ⟨y, a i, rfl⟩)
  · apply iSup_le
    intro i
    apply (pointField_le_iff F Ω _ _).mpr
    intro y a
    obtain ⟨b,hb⟩ := (show Function.Surjective (Pi.evalAlgHom F E i) from Function.surjective_eval i) a
    exact subset_adjoin F _ ⟨y.comp (Pi.evalAlgHom F E i), b, congrArg y hb⟩

/-- An étale presentation by a finite product of separable fields gives the
literal compositum of their normal closures. -/
theorem pointField_congr {A B : Type*} [CommRing A] [CommRing B] [Algebra F A] [Algebra F B]
    (e : A ≃ₐ[F] B) : pointField F Ω A = pointField F Ω B := by
  apply le_antisymm
  · exact (pointField_le_iff F Ω A _).mpr fun x a ↦
      subset_adjoin F _ ⟨x.comp e.symm.toAlgHom, e a, by simp⟩
  · exact (pointField_le_iff F Ω B _).mpr fun x b ↦
      subset_adjoin F _ ⟨x.comp e.toAlgHom, e.symm b, by simp⟩

theorem finiteProduct_normalClosures {κ : Type*} [Finite κ] (K : κ → Type*)
    [∀ i, Field (K i)] [∀ i, Algebra F (K i)]
    {A : Type*} [CommRing A] [Algebra F A] (e : A ≃ₐ[F] (∀ i, K i)) :
    pointField F Ω A = ⨆ i, normalClosure F (K i) Ω := by
  rw [pointField_congr F Ω e, pointField_pi]
  simp_rw [pointField_field]

/-- Over a Galois ambient extension, a finite étale fibre has a finite Galois
splitting subfield, including the empty and disconnected fibres. -/
theorem etale_pointField {A : Type*} [CommRing A] [Algebra F A] [Algebra.Etale F A]
    [IsGalois F Ω] : Module.Finite F (pointField F Ω A) ∧ IsGalois F (pointField F Ω A) := by
  obtain ⟨I, hI, K, hK, hA, e, h⟩ :=
    (Algebra.Etale.iff_exists_algEquiv_prod F A).mp inferInstance
  let : ∀ i, Module.Finite F (K i) := fun i ↦ (h i).1
  rw [finiteProduct_normalClosures F Ω K e]
  constructor
  · apply IntermediateField.finiteDimensional_iSup_of_finite
  · have : Normal F ↥(⨆ i, normalClosure F (K i) Ω) := IntermediateField.normal_iSup F Ω _
    exact {}

end MarkedModuli.Splitting

#print axioms MarkedModuli.Splitting.point_factors
#print axioms MarkedModuli.Splitting.pointField_pi
#print axioms MarkedModuli.Splitting.finiteProduct_normalClosures
#print axioms MarkedModuli.Splitting.etale_pointField
