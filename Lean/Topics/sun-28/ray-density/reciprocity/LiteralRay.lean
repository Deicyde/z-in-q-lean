import RayCoordinates
import CharacterComparison

namespace Sun28.Reciprocity
open Sun28.RayDensity Sun28.RayDensity.Artin
noncomputable section
variable {I:Type*} [Fintype I] (q:I→ℕ) [∀i,Fact (q i).Prime]
variable (cop:Pairwise (Function.onFun Nat.Coprime (levels q)))

instance residueNontrivial : Nontrivial (GaussianInt ⧸ M q) := by
  apply Ideal.Quotient.nontrivial_iff.mpr
  intro h
  have m : (1:GaussianInt) ∈ M q := (Ideal.eq_top_iff_one _).1 h
  have h16 : (1:GaussianInt) ∈ piece (levels q) none :=
    (iInf_le (piece (levels q)) none) m
  change (1:GaussianInt) ∈ principal ((16:ℕ):GaussianInt) at h16
  rw [←gaussianRed_kernel 16] at h16
  have e : gaussianRed 16 1 = 0 := h16
  rw [map_one] at e
  exact (by decide : (1:ZMod 16)≠0) (congrArg QuadraticAlgebra.re e)

abbrev idealRay := (Con.ker (idealClassHom (M q))).Quotient

def idealCoordinates : idealRay q ≃* RayUnits q :=
  (rayEquiv (M q)).trans (wordEquiv q cop).symm

include cop in
/-- Simultaneous invertibility at the true modulus of an integer with given primary coordinates. -/
theorem generator_unit (z:GaussianInt) (dy:((z.re:ZMod 16),(z.im:ZMod 16))∈primarySet)
    (odd:∀ i,(z.re:ZMod (q i))^2+(z.im:ZMod (q i))^2≠0) :
    IsUnit (residue (M q) z) := by
  let a:=primeTuple q z.re z.im dy odd
  let u:=(crtUnits q cop).symm (tupleRep q a)
  refine ⟨u,?_⟩
  apply (gaussianCRT (levels q) cop).injective
  funext j
  have h:=congrFun ((crtUnits q cop).apply_symm_apply (tupleRep q a)) j
  change (crtUnits q cop u) j = tupleRep q a j at h
  have hv:=congrArg Units.val h
  change gaussianCRT (levels q) cop u.val j = _ at hv
  rw [hv,gaussianCRT_mk]
  cases j with
  | none=>rfl
  | some i=>exact val_unitOf _ _ (odd i)

def principalIdeal (z:GaussianInt) (hz:IsUnit (residue (M q) z)) : coprimeIdeals (M q) :=
  ⟨principal z,(invertible_iff _ _).1 hz⟩

theorem idealCoordinates_generator (z:GaussianInt)
    (dy:((z.re:ZMod 16),(z.im:ZMod 16))∈primarySet)
    (odd:∀ i,(z.re:ZMod (q i))^2+(z.im:ZMod (q i))^2≠0) :
    idealCoordinates q cop (principalIdeal q z (generator_unit q cop z dy odd) : idealRay q)
      = primeTuple q z.re z.im dy odd := by
  apply (wordEquiv q cop).injective
  change (wordEquiv q cop) ((wordEquiv q cop).symm _) = _
  rw [MulEquiv.apply_symm_apply]
  change idealClass (M q) (principalIdeal q z _) = _
  rw [idealClass_spec _ _ z (generator_unit q cop z dy odd) rfl]
  unfold classOf
  apply congrArg (QuotientGroup.mk' _)
  apply (crtUnits q cop).injective
  change crtUnits q cop _=crtUnits q cop ((crtUnits q cop).symm _)
  rw [MulEquiv.apply_symm_apply]
  funext j
  apply Units.ext
  change gaussianCRT (levels q) cop (generator_unit q cop z dy odd).unit.val j = _
  rw [IsUnit.unit_spec,gaussianCRT_mk]
  cases j with
  | none=>rfl
  | some i=>exact (val_unitOf _ _ (odd i)).symm

end
end Sun28.Reciprocity
#print axioms Sun28.Reciprocity.idealCoordinates
#print axioms Sun28.Reciprocity.generator_unit
#print axioms Sun28.Reciprocity.idealCoordinates_generator
