import CoarseDiscriminant
import RelativeLevelDegree
import Mathlib.Data.ZMod.Basic

namespace ZInQBlueprint.LevelExtension
open Diagonal210 IntermediateField
noncomputable section

/-- The sign of every nonzero radical, with trivial action on a zero radical,
gives a faithful representation into four copies of the order-two group. -/
theorem coarse_degree_dvd_sixteen {s : ℚ} (y : Fibre ℂ coefficient s) :
    Module.finrank ℚ (rootField y) ∣ 16 := by
  classical
  let K := rootField y
  let : IsGalois ℚ K := coordinate_galois y
  let v := generator y
  have e (σ : K ≃ₐ[ℚ] K) (i : Fin 4) : σ (v i)=v i ∨ σ (v i)= -v i := by
    apply sq_eq_sq_iff_eq_or_eq_neg.mp
    rw [←map_pow,show v i^2=algebraMap ℚ K (radicand s i) from generator_sq y i,σ.commutes]
  let t (σ : K ≃ₐ[ℚ] K) (i : Fin 4) : ZMod 2 := if σ (v i)=v i then 0 else 1
  let f : (K ≃ₐ[ℚ] K) →* (Fin 4 → Multiplicative (ZMod 2)) := {
    toFun := fun σ i=>Multiplicative.ofAdd (t σ i)
    map_one' := by ext i; change t 1 i=0; simp [t]
    map_mul' := by
      intro σ τ
      funext i
      change (if σ (τ (v i))=v i then (0:ZMod 2) else 1) = t σ i + t τ i
      by_cases hτ : τ (v i)=v i
      · simp [hτ,t]
      · have nτ := (e τ i).resolve_left hτ
        have nz : -v i≠v i := fun eq=>hτ (nτ.trans eq)
        by_cases hσ : σ (v i)=v i
        · simp [t,hσ,nτ,nz]
        · have nσ := (e σ i).resolve_left hσ
          simp only [t,nσ,nτ,map_neg,neg_neg,ite_eq_right nz]
          decide }
  have injective : Function.Injective f := by
    intro σ τ h
    apply AlgEquiv.coe_toAlgHom_injective
    apply IntermediateField.adjoin_algHom_ext
    rintro _ ⟨i,rfl⟩
    change σ (v i)=τ (v i)
    have c := congrFun h i
    change t σ i=t τ i at c
    by_cases A : σ (v i)=v i <;> by_cases B : τ (v i)=v i
    · exact A.trans B.symm
    · simp [t,A,B] at c
    · simp [t,A,B] at c
    · exact ((e σ i).resolve_left A).trans ((e τ i).resolve_left B).symm
  have div := Subgroup.card_dvd_of_injective f injective
  rw [IsGalois.card_aut_eq_finrank ℚ K] at div
  convert div using 1
  simp [Nat.card_eq_fintype_card, Fintype.card_multiplicative]

/-- Over the concrete signed field, the size-36 level torsor bounds the
relative Galois degree and gives the slope-dependent rational degree bound. -/
theorem degree_dvd_relative_level {s : ℚ} (y : Fibre ℂ coefficient s)
    {L : Type*} [Field L] [NumberField L] [Algebra (rootField y) L]
    [IsScalarTower ℚ (rootField y) L] [IsGalois (rootField y) L]
    {S : Type*} [CommRing S] [Algebra (away (rootField y)) S]
    {Γ : Type*} [Group Γ] [Fintype Γ] (size : Fintype.card Γ=36)
    (lab : Γ ≃ (S →ₐ[away (rootField y)] L)) (T : Γ → S →ₐ[away (rootField y)] S)
    (deck : ∀ a b,lab (a*b)=(lab b).comp (T a))
    (gen : Generates (Set.univ : Set (S →ₐ[away (rootField y)] L))) :
    Module.finrank (rootField y) L∣36 ∧
      Module.finrank ℚ L∣Module.finrank ℚ (rootField y)*36 ∧ Module.finrank ℚ L∣576 := by
  have rel := size ▸ degree_dvd_deck lab T deck gen
  have C:=coarse_degree_dvd_sixteen y
  rw [←Module.finrank_mul_finrank ℚ (rootField y) L]
  exact ⟨rel,Nat.mul_dvd_mul_left _ rel,mul_dvd_mul C rel⟩

end
end ZInQBlueprint.LevelExtension
#print axioms ZInQBlueprint.LevelExtension.coarse_degree_dvd_sixteen
#print axioms ZInQBlueprint.LevelExtension.degree_dvd_relative_level
