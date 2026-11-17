import SignedCanonicalTheta
import ThetaSupportTransport

/-! A single pair of geometric points represents every degree-zero divisor class. -/
open CategoryTheory AlgebraicGeometry AlgebraicCurve
open scoped CategoryTheory.MonObj ZInQBlueprint.NormalDescent
namespace ZInQBlueprint.DeterminantSections
open SixAbelMap
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable {K F : Type} [Field K] [IsAlgClosed K] [Field F] [Algebra K F] [IsCurveOver K F]

private theorem one_degree (p : Place K F) : Divisor.degree (Finsupp.single p (1 : ℤ)) = 1 := by
  rw [Divisor.degree_single, IsCurveOver.deg_eq_one_of_isAlgClosed]
  norm_num

theorem effective_two (D : Divisor K F) (hD : ∀ v, 0 ≤ D v) (hdeg : D.degree = 2) :
    ∃ P Q, D = Finsupp.single P 1 + Finsupp.single Q 1 := by
  classical
  have hn : ∃ p, 0 < D p := by
    by_contra! h
    have he : D = 0 := Finsupp.ext fun v => le_antisymm (h v) (hD v)
    rw [he, map_zero] at hdeg
    omega
  obtain ⟨p,hp⟩ := hn
  have he : ∀ v, 0 ≤ ((D - Finsupp.single p 1 : Divisor K F) v) := by
    intro v
    by_cases h : p = v
    · subst v
      simp only [Finsupp.sub_apply, Finsupp.single_eq_same]
      omega
    · rw [Finsupp.sub_apply,Finsupp.single_eq_of_ne (Ne.symm h),sub_zero]; exact hD v
  have d : Divisor.degree (D - Finsupp.single p 1) = 1 := by rw [map_sub, hdeg, one_degree]; decide
  obtain ⟨q,hq⟩ := Divisor.exists_single_of_effective_degree_one _ he d
  exact ⟨p,q,by rw [←hq]; abel⟩

theorem genus_two_sums [Algebra.EssFiniteType K F] (M : CurveModel K F)
    (hg : genusFF K F = 2) (b : Place K F) (x : Pic0 K F) :
    ∃ p q, Pic0.mk (difference p b) + Pic0.mk (difference q b) = x := by
  classical
  obtain ⟨D,rfl⟩ := Pic0.mk_surjective x
  obtain ⟨Kc,g,rr⟩ := exists_canonicalDivisor_genus_riemannRoch K F
  have gg := (M.eq_genusFF_of_forall_ell_sub_ell_eq rr).trans hg
  let S : Divisor K F := Finsupp.single b 1
  let B := D.val + S + S
  have dD : Divisor.degree D.val = 0 := D.property
  have dB : Divisor.degree B = 2 := by rw [show B = D.val + S + S by rfl,map_add,map_add,dD,show Divisor.degree S = 1 from one_degree b]; decide
  have ellB : 0 < ell B := by have z := rr B; rw [dB,gg] at z; omega
  have hn : LSpace B ≠ ⊥ := by
    intro h
    change 0 < Module.finrank K (LSpace B) at ellB
    rw [h,finrank_bot] at ellB
    omega
  obtain ⟨f,hL,hf⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hn
  have ho := (mem_lSpace_iff_ord.mp hL).resolve_left hf
  let := IsCurveOver.hasPrincipalDivisors (K:=K) (F:=F)
  obtain ⟨A,ha,hdegA⟩ := HasPrincipalDivisors.exists_divisor (K:=K) f hf
  have heff (v) : 0 ≤ (B + A) v := by rw [Finsupp.add_apply,ha]; have := ho v; omega
  obtain ⟨p,q,eq⟩ := effective_two _ heff (by rw [map_add,dB,hdegA]; decide)
  refine ⟨p,q,?_⟩
  change Pic0.mk (difference p b + difference q b) = Pic0.mk D
  apply QuotientAddGroup.eq_iff_sub_mem.mpr
  change Divisor.IsPrincipal ((Finsupp.single p 1 - S + (Finsupp.single q 1 - S)) - D.val)
  have e : (Finsupp.single p 1 - S + (Finsupp.single q 1 - S)) - D.val = A := by
    calc _ = (Finsupp.single p 1 + Finsupp.single q 1) - B := by dsimp [B]; abel
         _ = A := by rw [←eq]; abel
  rw [e]
  exact ⟨f,hf,ha⟩

theorem abel_sums [Algebra.EssFiniteType K F] {C : Over (Spec (.of K))} {M : CurveModel K F}
    {i : M.C ≅ C.left} {e : i.hom ≫ C.hom = M.toBase} {V : AbelianModel.GroupScheme K}
    {b : base K ⟶ C} (A : AbelPresentation C M i e V b) (hg : genusFF K F = 2)
    (x : Additive (base K ⟶ V.X)) : ∃ p q, A.abel p + A.abel q = x := by
  obtain ⟨p,q,h⟩ := genus_two_sums M hg (pointPlace C M i e b) (A.divisorEquiv.symm x)
  obtain ⟨P,rfl⟩ := (pointPlace C M i e).surjective p
  obtain ⟨Q,rfl⟩ := (pointPlace C M i e).surjective q
  refine ⟨P,Q,?_⟩
  change Additive.ofMul (P ≫ A.morphism) + Additive.ofMul (Q ≫ A.morphism) = x
  rw [←A.point_class,←A.point_class,←map_add,h,A.divisorEquiv.apply_symm_apply]

end
end ZInQBlueprint.DeterminantSections
#print axioms ZInQBlueprint.DeterminantSections.effective_two
#print axioms ZInQBlueprint.DeterminantSections.genus_two_sums
#print axioms ZInQBlueprint.DeterminantSections.abel_sums
