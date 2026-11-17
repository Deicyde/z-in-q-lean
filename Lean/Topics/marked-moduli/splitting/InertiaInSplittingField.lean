import EtaleModel
import PolynomialFibre

namespace MarkedModuli.Splitting
open Polynomial IntermediateField Algebra
open scoped TensorProduct

/-- All points already descend to their embedded splitting field; evaluated
there, their values generate the whole field. -/
theorem points_generate_own_field (F Ω A : Type*) [Field F] [Field Ω] [Algebra F Ω]
    [CommRing A] [Algebra F A] : pointField F (pointField F Ω A) A = ⊤ := by
  let S := pointField F Ω A
  let T := pointField F S A
  have h : S ≤ T.map S.val := by
    apply (pointField_le_iff F Ω A _).mpr
    intro x a
    obtain ⟨y,rfl⟩ := (pointField_le_iff_lifts F Ω A S).mp le_rfl x
    exact ⟨y a, subset_adjoin F _ ⟨y,a,rfl⟩, rfl⟩
  apply top_unique
  intro z _
  obtain ⟨t,ht,he⟩ := h z.2
  exact (show t = z from Subtype.ext he) ▸ ht

/-- In the literal splitting field itself, every element of the finite
valuation inertia group is the identity. No passage from absolute to finite
inertia by a presumed surjective restriction map is necessary. -/
theorem finiteModel_inertia_eq_bot
    {R B F Ω : Type*} [CommRing R] [CommRing B] [Algebra R B] [Field F] [Field Ω]
    [Algebra R F] [Algebra F Ω] [Module.Finite R B] [FormallyUnramified R B]
    (v : ValuationSubring (pointField F Ω (F ⊗[R] B))) [Algebra R (pointField F Ω (F ⊗[R] B))]
    [IsScalarTower R F (pointField F Ω (F ⊗[R] B))] [Algebra R v]
    [IsScalarTower R v (pointField F Ω (F ⊗[R] B))] : v.inertiaSubgroup F = ⊥ := by
  apply le_antisymm _ bot_le
  intro d hd
  apply Subgroup.mem_bot.mpr
  apply Subtype.ext
  have hk := integralModel_inertia (R := R) (F := F) (B := B) v
    (show d.1 ∈ inertia F v from ⟨d,hd,rfl⟩)
  rw [pointAction_kernel, points_generate_own_field, IntermediateField.fixingSubgroup_top] at hk
  exact Subgroup.mem_bot.mp hk

/-- The same conclusion in Mathlib's polynomial splitting field, with a
monic valuation-integral model and separable reduction. -/
theorem polynomial_inertia_eq_bot {F : Type*} [Field F] (p : F[X])
    (v : ValuationSubring p.SplittingField) (q : v[X]) (hm : q.Monic)
    (model : p.map (algebraMap F p.SplittingField) = q.map (algebraMap v p.SplittingField))
    (hs : (q.map (IsLocalRing.residue v)).Separable) : v.inertiaSubgroup F = ⊥ := by
  apply le_antisymm _ bot_le
  intro d hd
  apply Subgroup.mem_bot.mpr
  apply Subtype.ext
  have hk := inertia_le_rootFixing F v p q hm model hs
    (show d.1 ∈ inertia F v from ⟨d,hd,rfl⟩)
  have htop : IntermediateField.adjoin F (p.rootSet p.SplittingField) = ⊤ :=
    (isSplittingField_iff_intermediateField.mp (inferInstance : p.IsSplittingField F p.SplittingField)).2
  rw [htop, IntermediateField.fixingSubgroup_top] at hk
  exact Subgroup.mem_bot.mp hk

end MarkedModuli.Splitting

#print axioms MarkedModuli.Splitting.points_generate_own_field
#print axioms MarkedModuli.Splitting.finiteModel_inertia_eq_bot
#print axioms MarkedModuli.Splitting.polynomial_inertia_eq_bot
