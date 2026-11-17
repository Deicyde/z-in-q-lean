import Mathlib.RingTheory.Unramified.Basic
import Mathlib.RingTheory.Etale.Basic

open scoped TensorProduct
open Algebra TensorProduct KaehlerDifferential
namespace ZInQBlueprint.LevelExtension

/-- Two points of an essentially finite type formally unramified algebra
over a domain are distinguished by reduction at any proper ideal. -/
theorem hom_ext_of_congr {R S D : Type*} [CommRing R] [CommRing S]
    [CommRing D] [IsDomain D] [Algebra R S] [Algebra R D] [Algebra.EssFiniteType R S]
    [Algebra.FormallyUnramified R S] (P : Ideal D) (proper : P ≠ ⊤)
    (f g : S →ₐ[R] D) (congruent : ∀ s, f s-g s∈P) : f=g := by
  obtain ⟨e,he,gen⟩ : ∃ e,IsIdempotentElem e ∧ KaehlerDifferential.ideal R S = Ideal.span {e} :=
    (Ideal.isIdempotentElem_iff_of_fg _ (KaehlerDifferential.ideal_fg R S)).mp
      ((Ideal.cotangent_subsingleton_iff _).mp (inferInstanceAs (Subsingleton Ω[S⁄R])))
  let F := Algebra.TensorProduct.productMap f g
  have allP : KaehlerDifferential.ideal R S ≤ P.comap F := by
    rw [← KaehlerDifferential.span_range_eq_ideal,Ideal.span_le]
    rintro _ ⟨s,rfl⟩
    change F _ ∈ P
    simpa [F] using P.neg_mem (congruent s)
  have eig : e∈KaehlerDifferential.ideal R S := gen ▸ Ideal.subset_span (Set.mem_singleton _)
  have e0 : F e=0 := by
    rcases IsIdempotentElem.iff_eq_zero_or_one.mp (he.map F) with zero|one
    · exact zero
    · exact (proper ((Ideal.eq_top_iff_one _).mpr (one ▸ (allP eig : F e∈P)))).elim
  have ker : KaehlerDifferential.ideal R S ≤ RingHom.ker F := by
    rw [gen,Ideal.span_singleton_le_iff_mem]
    exact e0
  ext s
  have E := ker (KaehlerDifferential.one_smul_sub_smul_one_mem_ideal R s)
  change F ((1:S)⊗ₜ[R]s - s⊗ₜ[R](1:S))=0 at E
  exact (sub_eq_zero.mp (by simpa [F] using E : g s - f s = 0)).symm

end ZInQBlueprint.LevelExtension
#print axioms ZInQBlueprint.LevelExtension.hom_ext_of_congr
