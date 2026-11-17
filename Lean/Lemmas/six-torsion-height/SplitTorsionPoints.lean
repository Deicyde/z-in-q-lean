import KernelSplittingField
import Nyll.AbelianVarieties.Tate.FiniteTorsion
import Nyll.AlgebraicCurves.Geometry.Picard.GroupLaw.CommGroupRelativeLaw

/-! A finite extension splitting the actual multiplication kernel, simultaneously
with an auxiliary polynomial, over arbitrary subsequent coefficient fields. -/
open CategoryTheory AlgebraicGeometry GoodReductionJacobian NeronModelInfra Polynomial
open AlgebraicGeometry.FiniteEtale GoodReductionJacobian.RelativeGroupLaw
namespace ZInQBlueprint.TorsionHeight
noncomputable section
variable (F : Type) [Field F] (A : CommGrp (Over (Spec (.of F))))
abbrev Law := commGroupRelativeLaw A
abbrev LawComm : (Law F A).IsCommutative := commGroupRelativeLaw_isCommutative A
abbrev Points (T : Type) [Field T] [Algebra F T] := (Law F A).AlgPoints (LawComm F A) T

private theorem sections_map {K L : Type} [Field K] [Field L] [Algebra F K] [Algebra F L]
    (E : FiniteEtale (Spec (.of F))) (i : K →ₐ[F] L)
    (x : Over.mk (Spec.algebraMap F K) ⟶ E.toComma) (y : Over.mk (Spec.algebraMap F L) ⟶ E.toComma)
    (h : i.comp (pointHomAlgEquiv F K E x) = pointHomAlgEquiv F L E y) :
    Spec.map (CommRingCat.ofHom i.toRingHom) ≫ x.left = y.left := by
  apply (cancel_mono E.left.isoSpec.hom).1
  rw [Category.assoc,←pointHomAlgEquiv_specMap,←pointHomAlgEquiv_specMap,←Spec.map_comp]
  exact congrArg Spec.map (CommRingCat.hom_ext (congrArg AlgHom.toRingHom h))

/-- A full torsion field for a prescribed level and an arbitrary auxiliary
polynomial. The conclusion quantifies over every field and every embedding,
so it applies to the geometric points over the local completions as well. -/
theorem exists_full_level [IsProper A.X.hom] [Smooth A.X.hom] (n : ℕ+) (hn : IsUnit ((n : ℕ) : F))
    (f : F[X]) (hf : f ≠ 0) :
    ∃ (K : Type) (_ : Field K) (_ : Algebra F K) (_ : FiniteDimensional F K),
      (f.map (algebraMap F K)).Splits ∧
      ∀ (L : Type) [Field L] [Algebra F L] (i : K →ₐ[F] L) (y : Points F A L),
        (n : ℕ) • y = 0 → ∃ x : Points F A K, (n : ℕ) • x = 0 ∧ AlgPoints.map i x = y := by
  let G := Law F A
  let hc : G.IsCommutative := LawComm F A
  let E := G.unitTorsionCover hc n hn
  let R := Γ(E.left, ⊤)
  let _ : Module.Finite F R := sections_moduleFinite F E
  obtain ⟨K,kf,ka,kdim,hf,split⟩ := exists_splitting_field F R f hf
  let := kf
  let := ka
  let := kdim
  refine ⟨K,kf,ka,kdim,hf,?_⟩
  intro L _ _ i y hy
  let yt : ProCGroups.torsionLevel (G.AlgPoints hc L) n := ⟨y,hy⟩
  let v := G.torsionLevelEquivKernelSections hc L n hn yt
  obtain ⟨w,hw⟩ := split L i v
  let xt := (G.torsionLevelEquivKernelSections hc K n hn).symm w
  let px := G.torsionLevelEquivUnitKernelPoints hc K n hn xt
  let py := G.torsionLevelEquivUnitKernelPoints hc L n hn yt
  have hx : pointHomAlgEquiv F K E px = w :=
    (G.torsionLevelEquivKernelSections hc K n hn).apply_symm_apply w
  have pulled := sections_map F E i px py (by rw [hx]; exact hw)
  have e := congrArg (fun h => h ≫ Limits.pullback.fst (G.schemeNsmul (n:ℕ))
    (G.one (𝟙 (Spec (.of F)))).1) pulled
  change (Spec.map (CommRingCat.ofHom i.toRingHom) ≫
      (G.torsionLevelEquivAlgSchemeKerPoints hc K n xt).1) ≫ _ =
      (G.torsionLevelEquivAlgSchemeKerPoints hc L n yt).1 ≫ _ at e
  rw [Category.assoc,G.torsionLevelEquivAlgSchemeKerPoints_comp_fst,
    G.torsionLevelEquivAlgSchemeKerPoints_comp_fst] at e
  exact ⟨xt.1,xt.2,AlgPoints.toPoint_injective (Subtype.ext e)⟩

end
end ZInQBlueprint.TorsionHeight
#print axioms ZInQBlueprint.TorsionHeight.exists_full_level
