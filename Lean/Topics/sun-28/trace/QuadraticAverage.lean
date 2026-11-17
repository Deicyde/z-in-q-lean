import TraceValuation
import Mathlib.FieldTheory.NormalizedTrace
import Mathlib.FieldTheory.Galois.Basic

/-! Normalized trace and simultaneous valuation bounds in quadratic fields. -/
namespace Sun28.ScalarTrace
open Algebra
variable {F K : Type*} [Field F] [Field K] [Algebra F K] [CharZero F]
  [IsQuadraticExtension F K]

theorem normalizedTrace_quadratic (σ : K ≃ₐ[F] K) (hσ : σ ≠ 1) (a : K) :
    algebraMap F K (normalizedTrace F K a) = (a+σ a)/2 := by
  classical
  have hcard : Fintype.card (K ≃ₐ[F] K)=2 := by
    rw [←Nat.card_eq_fintype_card,IsGalois.card_aut_eq_finrank,IsQuadraticExtension.finrank_eq_two F K]
  have hu : ({1,σ} : Finset (K ≃ₐ[F] K))=Finset.univ := by
    apply Finset.eq_univ_of_card
    simp [hσ.symm,hcard]
  rw [normalizedTrace_eq_of_finiteDimensional_apply F,IsQuadraticExtension.finrank_eq_two F K,
    smul_eq_mul,map_mul,map_inv₀,trace_eq_sum_automorphisms,←hu]
  simp [hσ.symm,map_ofNat,div_eq_mul_inv,mul_comm]

noncomputable def scalarTheta (r : F) (x y : K) : F :=
  normalizedTrace F K ((weight (algebraMap F K r) x y)⁻¹)

theorem scalarTheta_embeddings (σ : K ≃ₐ[F] K) (hσ : σ ≠ 1) (r : F) (x y : K) :
    algebraMap F K (scalarTheta r x y) =
    average (weight (algebraMap F K r) x y) (weight (algebraMap F K r) (σ x) (σ y)) := by
  rw [scalarTheta,normalizedTrace_quadratic σ hσ]
  simp [average,weight,factor,map_pow,map_div₀,map_inv₀]

/-- The scalar in Sun's two-test certificate. -/
noncomputable def scalarValue (r Γ D₀ : F) (x y : K) : F :=
    (Γ/(1+D₀*r^2))^2*r/(scalarTheta r x y)^2

theorem two_tests_sharp (v : AddValuation K (WithTop ℤ)) (σ : K ≃ₐ[F] K) (hσ : σ ≠ 1)
    {r Γ D₀ : F} {x y : K} {α : ℤ}
    (hr : v (algebraMap F K r)=(α:WithTop ℤ)) (ho : Odd α) (htwo : v (2:K)=0)
    (hfront : v (algebraMap F K (Γ/(1+D₀*r^2)))=0) (hn : scalarTheta r x y ≠ 0)
    (hB : (0:WithTop ℤ) ≤ v (algebraMap F K (scalarValue r Γ D₀ x y))) :
    0 < α ∧ (Precise v α x y ∨ Precise v α (σ x) (σ y)) := by
  have ha := scalarTheta_embeddings σ hσ r x y
  have hne := (map_ne_zero (algebraMap F K)).mpr hn
  rw [ha] at hne
  unfold scalarValue at hB
  rw [map_div₀,map_mul,map_pow,map_pow,ha] at hB
  exact average_soundness v hr ho htwo hfront hne hB

/-- At one of the two conjugate places both prescribed orders hold. -/
theorem two_tests_one_branch (v : AddValuation K (WithTop ℤ)) (σ : K ≃ₐ[F] K) (hσ : σ ≠ 1)
    {r Γ D₀ : F} {x y : K} {α : ℤ}
    (hr : v (algebraMap F K r)=(α:WithTop ℤ)) (ho : Odd α) (htwo : v (2:K)=0)
    (hfront : v (algebraMap F K (Γ/(1+D₀*r^2)))=0) (hn : scalarTheta r x y ≠ 0)
    (hB : (0:WithTop ℤ) ≤ v (algebraMap F K (scalarValue r Γ D₀ x y))) :
    0 < α ∧ ((1:WithTop ℤ) ≤ v x ∧ (48:WithTop ℤ) ≤ v y ∨
      (1:WithTop ℤ) ≤ v (σ x) ∧ (48:WithTop ℤ) ≤ v (σ y)) := by
  obtain ⟨ha,h⟩ := two_tests_sharp v σ hσ hr ho htwo hfront hn hB
  exact ⟨ha,h.imp (fun t => t.orders ha) (fun t => t.orders ha)⟩

end Sun28.ScalarTrace
#print axioms Sun28.ScalarTrace.normalizedTrace_quadratic
#print axioms Sun28.ScalarTrace.scalarTheta_embeddings
#print axioms Sun28.ScalarTrace.two_tests_sharp
#print axioms Sun28.ScalarTrace.two_tests_one_branch
