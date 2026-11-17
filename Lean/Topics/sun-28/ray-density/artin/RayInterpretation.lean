import CyclotomicCharacter

namespace Sun28.RayDensity.Artin
open SemidirectProduct
noncomputable section
variable {I:Type*} (q:I→ℕ) [∀i,Fact (q i).Prime]

/-- Conjugacy in an abelian group extended by an involution. -/
theorem normalized_conjugacy {A:Type*} [CommGroup A] (s:MulAut A) (hs:s*s=1)
    (a b:A) :
    IsConj (inl (φ:=act s hs) a) (inl (φ:=act s hs) b) ↔ b=a ∨ b=s a := by
  constructor
  · intro e
    obtain ⟨g,h⟩:=isConj_iff.mp e
    have eq : (act s hs g.right) a=b := by
      have k:=congrArg SemidirectProduct.left h
      simp only [SemidirectProduct.mul_left,SemidirectProduct.mul_right,SemidirectProduct.inv_left,
          left_inl,right_inl,mul_one] at k
      have inv : (act s hs g.right) ((act s hs g.right⁻¹) g.left⁻¹)=g.left⁻¹ := by
        rw [←MulAut.mul_apply,←map_mul,mul_inv_cancel,map_one]; rfl
      rwa [inv,mul_comm g.left, mul_assoc, mul_inv_cancel,mul_one] at k
    rcases two_cases g.right with h|h
    · left
      rw [h,map_one] at eq
      exact eq.symm
    · right
      rw [h] at eq
      change (if flip=1 then (1:MulAut A) else s) a=b at eq
      rw [ite_eq_right (by decide : flip≠1)] at eq
      exact eq.symm
  · rintro (rfl|rfl)
    · exact IsConj.refl _
    · apply isConj_iff.mpr
      refine ⟨inr flip,?_⟩
      have e:=inl_aut (φ:=act s hs) flip a
      have turn : act s hs flip a=s a := by
        change (if flip=1 then (1:MulAut A) else s) a=s a
        rw [ite_eq_right (by decide : flip≠1)]
      rw [turn,map_inv] at e
      exact e.symm

/-- The full conjugacy class of the true ray model has at most two
elements. The odd and dyadic coordinates must all be conjugated together. -/
theorem ray_conjugacy (a b:RayUnits q) :
    IsConj (inl (φ:=rayAction q) a) (inl (φ:=rayAction q) b) ↔
      b=a ∨ b=(dyadicConj a.1,fun i=>conjugate (q i) (a.2 i)) :=
  normalized_conjugacy (joinedAut q dyadicConj) (joined_involution q dyadicConj dyadic_involution) a b

end
end Sun28.RayDensity.Artin
#print axioms Sun28.RayDensity.Artin.normalized_conjugacy
#print axioms Sun28.RayDensity.Artin.ray_conjugacy
