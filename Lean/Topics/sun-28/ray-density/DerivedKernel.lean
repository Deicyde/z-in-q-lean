import GaussianUnits
import Mathlib.GroupTheory.Commutator.Basic

namespace Sun28.RayDensity
open scoped commutatorElement
noncomputable section
variable {I : Type*} (q : I→ℕ) [∀ i,Fact (q i).Prime]
variable {G G₀ : Type*} [Group G] [Group G₀]

/-- Every tuple of norm-one local units is one commutator with complex conjugation. -/
theorem embedded_norm_kernel (odd : ∀ i,q i≠2) (embed : ((i:I)→GU (q i)) →* G)
    (c : G) (action : ∀ b, c * embed b * c⁻¹ = embed (fun i=>conjugate (q i) (b i)))
    (v : (i:I)→GU (q i)) (one : ∀ i,unitNorm (q i) (v i)=1) :
    embed v ∈ commutator G := by
  have lift (i : I) : v i∈(coboundary (q i)).range := by
    rw [range_coboundary (odd i)];exact one i
  choose a h using lift
  have eq : v = a / (fun i=>conjugate (q i) (a i)) := funext fun i=>(h i).symm
  have e : embed v=⁅embed a,c⁆ := by
    rw [eq,map_div,←action,commutatorElement_def,div_eq_mul_inv]
    group
  rw [e]
  exact Subgroup.commutator_mem_commutator (by trivial : embed a∈(⊤ : Subgroup G))
    (by trivial : c∈(⊤ : Subgroup G))

/-- Input is restriction to the base field and the new cyclotomic characters.
Its elementary exactness and conjugation action suffice to identify the entire derived group. -/
theorem derived_restriction (odd : ∀ i,q i≠2) (embed : ((i:I)→GU (q i)) →* G)
    (c : G) (action : ∀ b, c * embed b * c⁻¹ = embed (fun i=>conjugate (q i) (b i)))
    (r : G →* G₀ × ((i:I)→(ZMod (q i))ˣ)) (onto : Function.Surjective r)
    (kernel : ∀ g∈r.ker, ∃ v : (i:I)→GU (q i), (∀ i,unitNorm (q i) (v i)=1) ∧ embed v=g) :
    commutator G = ((commutator G₀).prod ⊥).comap r := by
  have kerle : r.ker ≤ commutator G := by
    intro g hg;obtain ⟨v,n,rfl⟩:=kernel g hg
    exact embedded_norm_kernel q odd embed c action v n
  have prod_eq : commutator (G₀ × ((i:I)→(ZMod (q i))ˣ))=(commutator G₀).prod ⊥ := by
    rw [commutator_def,←Subgroup.top_prod_top,Subgroup.commutator_prod_prod,←commutator_def,←commutator_def,
      commutator_eq_bot ((i:I)→(ZMod (q i))ˣ)]
  rw [←prod_eq,←map_commutator_of_surjective onto,Subgroup.comap_map_eq_self kerle]

end
end Sun28.RayDensity
#print axioms Sun28.RayDensity.embedded_norm_kernel
#print axioms Sun28.RayDensity.derived_restriction
