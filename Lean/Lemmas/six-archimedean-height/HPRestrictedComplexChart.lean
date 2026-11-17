import HPIdenticalComplexFibres

/-! The restricted odd equation is an open affine subscheme of each actual
complex fibre. The quintic and its root ordering are fixed before σ. -/
open CategoryTheory AlgebraicGeometry Polynomial
namespace ZInQBlueprint.ArchimedeanHeight
open BinaryCover OddModel ThetaPeriod
noncomputable section

private theorem quintic_open {r : Fin 6 → ℂ} (hr : Function.Injective r) :
    ∃ j : SpecOver (R:=ℂ) (Cover (quintic r)) ⟶ oddCurve hr, IsOpenImmersion j.left := by
  have e := reverse_infinityChart hr
  let j := chartInclusion ℂ _ _ (reverse_sextic_overlap (infinity_degree hr)) true
  have h : ∃ j : SpecOver (R:=ℂ) (Cover (infinityChart r).reverse) ⟶ oddCurve hr,
      IsOpenImmersion j.left := ⟨j,chartInclusion_open ..⟩
  rwa [e] at h

theorem restricted_chart_every_embedding (K : Type) [Field K] [NumberField K]
    {u : ℚ} (hu : u ∉ ZInQ.contactSet) :
    ∃ r : Fin 6 → ℂ, Function.Injective r ∧ (quintic r).Monic ∧
      (quintic r).natDegree = 5 ∧ (quintic r).Separable ∧
      (∀ i, aeval (r i) (SexticThetaHeight.sextic u 1)=0) ∧
      ∀ σ : K →ₐ[ℚ] ℂ, ∃ j : SpecOver (R:=ℂ) (Cover (quintic r)) ⟶ embeddedCurve u σ,
        IsOpenImmersion j.left := by
  obtain ⟨r,hr,mon,deg,sep,roots,each⟩ := one_restricted_curve (K:=K) hu
  obtain ⟨j,hj⟩ := quintic_open hr
  refine ⟨r,hr,mon,deg,sep,roots,?_⟩
  intro σ
  obtain ⟨e⟩ := each σ
  let : IsIso e.hom.left := inferInstanceAs (IsIso (((Over.forget _).mapIso e).hom))
  exact ⟨j ≫ e.hom,@IsOpenImmersion.comp _ _ _ j.left e.hom.left hj (IsOpenImmersion.of_isIso _)⟩

end
end ZInQBlueprint.ArchimedeanHeight
#print axioms ZInQBlueprint.ArchimedeanHeight.restricted_chart_every_embedding
