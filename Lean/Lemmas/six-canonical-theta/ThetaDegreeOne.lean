import AbelCanonicalPencil

/-! A degree-one divisor admits a section exactly when its class comes from one place. -/
open CategoryTheory AlgebraicGeometry AlgebraicCurve
open scoped CategoryTheory.MonObj
namespace ZInQBlueprint.CanonicalTheta
open SixAbelMap
noncomputable section
variable {K F : Type} [Field K] [IsAlgClosed K] [Field F] [Algebra K F]
  [IsCurveOver K F] [Algebra.EssFiniteType K F]

theorem degree_one_ell (D : Divisor K F) (deg : D.degree=1) :
    0 < ell D ↔ ∃ p : Place K F, Divisor.IsPrincipal (Finsupp.single p 1 - D) := by
  classical
  obtain ⟨t, ht, hfin, -⟩ := IsCurveOver.exists_separating_transcendental (K:=K) (F:=F)
  have const := constantsAreBase_of_isAlgClosed_of_transcendental t ht
  let : FiniteDimensional K (LSpace (0 : Divisor K F)) := by rw [const]; infer_instance
  let : FiniteDimensional K (LSpace D) := finiteDimensional_lSpace D
  constructor
  · intro h
    have hn : LSpace D ≠ ⊥ := by
      intro he
      change 0 < Module.finrank K (LSpace D) at h
      rw [he,finrank_bot] at h
      omega
    obtain ⟨f,hL,hf⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hn
    have ho := (mem_lSpace_iff_ord.mp hL).resolve_left hf
    let := IsCurveOver.hasPrincipalDivisors (K:=K) (F:=F)
    obtain ⟨A,ha,hd⟩ := HasPrincipalDivisors.exists_divisor (K:=K) f hf
    have heff (v : Place K F) : 0 ≤ (D+A) v := by rw [Finsupp.add_apply,ha]; have := ho v; omega
    have hdeg : (D+A).degree=1 := by rw [map_add,deg,hd,add_zero]
    obtain ⟨P,hP⟩ := Divisor.exists_single_of_effective_degree_one (D+A) heff hdeg
    refine ⟨P,?_⟩
    rw [←hP,add_sub_cancel_left]
    exact ⟨f,hf,ha⟩
  · rintro ⟨P,f,hf,ho⟩
    have hL : f ∈ LSpace D := by
      apply mem_lSpace_iff_ord.mpr
      right
      intro v
      have H := ho v
      rw [Finsupp.sub_apply] at H
      have hS : 0 ≤ (Finsupp.single P (1:ℤ)) v := by simp only [Finsupp.single_apply]; split_ifs <;> norm_num
      omega
    let : Nontrivial (LSpace D) := ⟨⟨⟨f,hL⟩,0,fun h => hf (congrArg Subtype.val h)⟩⟩
    exact Module.finrank_pos

theorem class_ell (D : Divisor.degZero (K:=K) (F:=F)) (b : Place K F) :
    0 < ell ((D : Divisor K F) + Finsupp.single b 1) ↔
      ∃ P : Place K F, Pic0.mk (difference P b) = Pic0.mk D := by
  classical
  have hd : Divisor.degree ((D : Divisor K F) + Finsupp.single b 1) = 1 := by
    rw [map_add,show (D : Divisor K F).degree = 0 from D.property,Divisor.degree_single, IsCurveOver.deg_eq_one_of_isAlgClosed]
    norm_num
  rw [degree_one_ell _ hd]
  apply exists_congr
  intro P
  rw [show Pic0.mk (difference P b) = Pic0.mk D ↔
    difference P b - D ∈ (Divisor.principal (K:=K) (F:=F)).addSubgroupOf (Divisor.degZero (K:=K) (F:=F))
    from QuotientAddGroup.eq_iff_sub_mem]
  change Divisor.IsPrincipal _ ↔ Divisor.IsPrincipal ((Finsupp.single P 1-Finsupp.single b 1) - (D : Divisor K F))
  abel

/-- The test uses any representative of the class and the fixed marking on the complete curve. -/
theorem presentation_W_one {C : Over (Spec (.of K))} {M : CurveModel K F} {i : M.C ≅ C.left}
    {hbase : i.hom ≫ C.hom = M.toBase} {V : AbelianModel.GroupScheme K} {b : base K ⟶ C}
    (A : AbelPresentation C M i hbase V b) (D : Divisor.degZero (K:=K) (F:=F)) :
    0 < ell ((D : Divisor K F) + Finsupp.single (pointPlace C M i hbase b) 1) ↔
      A.divisorEquiv (Pic0.mk D) ∈ Set.range A.abel := by
  rw [class_ell]
  constructor
  · rintro ⟨P,hP⟩
    obtain ⟨p,rfl⟩ := (pointPlace C M i hbase).surjective P
    exact ⟨p,(A.point_class p).symm.trans (congrArg A.divisorEquiv hP)⟩
  · rintro ⟨p,hp⟩
    exact ⟨pointPlace C M i hbase p,A.divisorEquiv.injective ((A.point_class p).trans hp)⟩

end
end ZInQBlueprint.CanonicalTheta
#print axioms ZInQBlueprint.CanonicalTheta.degree_one_ell
#print axioms ZInQBlueprint.CanonicalTheta.class_ell
#print axioms ZInQBlueprint.CanonicalTheta.presentation_W_one
