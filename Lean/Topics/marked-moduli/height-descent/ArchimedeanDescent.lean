import Mathlib.NumberTheory.Height.NumberField

/-! The infinite-place factor of a projective height in a number-field extension. -/
open NumberField
namespace ZInQBlueprint.HeightDescent
noncomputable section
open scoped Classical
variable {K L : Type*} [Field K] [Field L] [NumberField K] [NumberField L] [Algebra K L]

/-- Each embedding of the smaller number field has exactly [L:K] extensions to the larger. -/
theorem embedding_fiber_card (φ : K →+* ℂ) :
    (Finset.univ.filter fun σ : L →+* ℂ => σ.comp (algebraMap K L) = φ).card =
    Module.finrank K L := by
  classical
  let : Algebra K ℂ := φ.toAlgebra
  have : FiniteDimensional K L := FiniteDimensional.right ℚ K L
  rw [← AlgHom.card K L ℂ, Fintype.card]
  apply (Finset.card_nbij AlgHom.toRingHom (fun σ _ => ?_)
    AlgHom.toRingHom_injective.injOn (fun ψ hψ => ?_)).symm
  · apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _,?_⟩
    ext k
    exact σ.commutes k
  · have h := (Finset.mem_filter.mp hψ).2
    refine ⟨⟨ψ, fun k => ?_⟩,Finset.mem_univ _,rfl⟩
    exact RingHom.congr_fun h k

/-- An infinite place occurs with multiplicity equal to its number of complex embeddings. -/
theorem prod_embeddings {M : Type*} [CommMonoid M] (a : InfinitePlace K → M) :
    (∏ φ : K →+* ℂ, a (InfinitePlace.mk φ)) = ∏ w, (a w)^w.mult := by
  classical
  rw [← Finset.prod_fiberwise Finset.univ InfinitePlace.mk]
  apply Finset.prod_congr rfl
  intro w _
  calc
    (∏ σ ∈ Finset.univ.filter (fun σ : K →+* ℂ => InfinitePlace.mk σ = w), a (InfinitePlace.mk σ)) =
        ∏ _σ ∈ Finset.univ.filter (fun σ : K →+* ℂ => InfinitePlace.mk σ = w), a w :=
      Finset.prod_congr rfl fun _ h => congrArg a (Finset.mem_filter.mp h).2
    _ = (a w)^w.mult := by rw [Finset.prod_const,InfinitePlace.card_filter_mk_eq]

/-- A product depending only on restrictions acquires the relative degree as exponent. -/
theorem prod_restricted_embeddings {M : Type*} [CommMonoid M] (a : (K →+* ℂ) → M) :
    (∏ ψ : L →+* ℂ, a (ψ.comp (algebraMap K L))) = (∏ φ : K →+* ℂ, a φ)^Module.finrank K L := by
  classical
  rw [← Finset.prod_fiberwise Finset.univ (fun ψ : L →+* ℂ => ψ.comp (algebraMap K L)),← Finset.prod_pow]
  apply Finset.prod_congr rfl
  intro φ _
  calc
    (∏ ψ ∈ Finset.univ.filter (fun ψ : L →+* ℂ => ψ.comp (algebraMap K L)=φ), a (ψ.comp (algebraMap K L))) =
        ∏ _ψ ∈ Finset.univ.filter (fun ψ : L →+* ℂ => ψ.comp (algebraMap K L)=φ), a φ :=
      Finset.prod_congr rfl fun _ h => congrArg a (Finset.mem_filter.mp h).2
    _ = (a φ)^Module.finrank K L := by rw [Finset.prod_const,embedding_fiber_card]

theorem archimedean_factors {ι : Type*} (x : ι → K) :
    (∏ w : InfinitePlace L, (⨆ i, w (algebraMap K L (x i))) ^ w.mult) =
      (∏ w : InfinitePlace K, (⨆ i, w (x i)) ^ w.mult) ^ Module.finrank K L := by
  rw [← prod_embeddings (fun w : InfinitePlace L => ⨆ i, w (algebraMap K L (x i))),
    ← prod_embeddings (fun w : InfinitePlace K => ⨆ i, w (x i))]
  exact prod_restricted_embeddings (L:=L) (fun φ : K →+* ℂ => ⨆ i, ‖φ (x i)‖)

end
end ZInQBlueprint.HeightDescent
#print axioms ZInQBlueprint.HeightDescent.embedding_fiber_card
#print axioms ZInQBlueprint.HeightDescent.prod_embeddings
#print axioms ZInQBlueprint.HeightDescent.prod_restricted_embeddings
#print axioms ZInQBlueprint.HeightDescent.archimedean_factors
