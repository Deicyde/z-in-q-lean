import AwayEvaluation
import Mathlib.NumberTheory.NumberField.Discriminant.Different

open NumberField IntermediateField
open scoped NumberField
namespace ZInQBlueprint.LevelExtension
noncomputable section
variable {K L : Type*} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
variable {S : Type*} [CommRing S] [Algebra (away K) S]

/-- The coordinate values of the generic points generate the stated field. -/
def Generates (E : Set (S →ₐ[away K] L)) : Prop :=
  adjoin K {x : L | ∃ f∈E, ∃ a : S, f a=x} = ⊤

/-- A Galois automorphism in inertia fixes the generic point evaluations,
then the field they generate. This step only uses integrality and formal unramifiedness. -/
theorem inertia_eq_bot [Algebra.IsIntegral (away K) S] [Algebra.EssFiniteType (away K) S]
    [Algebra.FormallyUnramified (away K) S] {E : Set (S →ₐ[away K] L)}
    (gen : Generates E) (P : Ideal (𝓞 L)) [P.IsPrime] (good : (210:𝓞 L)∉P) :
    P.inertia (L ≃ₐ[K] L)=⊥ := by
  apply le_antisymm _ bot_le
  intro σ hσ
  rw [Subgroup.mem_bot]
  have fixes (f : S →ₐ[away K] L) (a : S) : σ (f a)=f a := by
    let e := integralPoint f
    have eq := hom_ext_of_congr _ (away_ideal_proper P good) ((actAway σ).comp e) e
      (fun a => inertia_congr_away P σ hσ (e a))
    exact congrArg (fun g : S →ₐ[away K] away L => ((g a:away L):L)) eq
  ext z
  change σ z=z
  have all : z∈adjoin K {x : L | ∃ f∈E, ∃ a : S, f a=x} := by rw [gen]; trivial
  induction all using adjoin_induction with
  | mem x hx => obtain ⟨f,_,a,rfl⟩:=hx; exact fixes f a
  | algebraMap a => exact σ.commutes a
  | add x y _ _ hx hy => rw [map_add,hx,hy]
  | inv x _ hx => rw [map_inv₀,hx]
  | mul x y _ _ hx hy => rw [map_mul,hx,hy]

/-- The splitting field of a finite étale fibre over O_K[1/210] is relatively
unramified at every prime away from 210. -/
theorem relative_unramified [IsGalois K L] [Module.Finite (away K) S] [Algebra.Etale (away K) S]
    {E : Set (S →ₐ[away K] L)} (gen : Generates E)
    (P : Ideal (𝓞 L)) [P.IsPrime] (good : (210:𝓞 L)∉P) : Algebra.IsUnramifiedAt (𝓞 K) P := by
  let Q:=P.under (𝓞 K)
  apply Ideal.ramificationIdx_eq_one_iff.mp
  rw [←Ideal.ramificationIdxIn_eq_ramificationIdx Q P (L ≃ₐ[K] L),
      ←Ideal.card_inertia_eq_ramificationIdxIn (G:=L ≃ₐ[K] L) Q P,inertia_eq_bot gen P good]
  simp

end
end ZInQBlueprint.LevelExtension
#print axioms ZInQBlueprint.LevelExtension.inertia_eq_bot
#print axioms ZInQBlueprint.LevelExtension.relative_unramified
